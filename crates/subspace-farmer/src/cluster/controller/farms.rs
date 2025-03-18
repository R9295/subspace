//! This module exposed implementation of farms maintenance.
//!
//! The goal is to observe farms in a cluster and keep controller's data structures
//! about which pieces are plotted in which sectors of which farm up to date. Implementation
//! automatically handles dynamic farm addition and removal, etc.

#[cfg(test)]
mod tests;

use crate::cluster::controller::ClusterControllerFarmerIdentifyBroadcast;
use crate::cluster::farmer::{
    ClusterFarm, ClusterFarmerFarmDetails, ClusterFarmerFarmDetailsRequest, ClusterFarmerId,
    ClusterFarmerIdentifyBroadcast,
};
use crate::cluster::nats_client::NatsClient;
use crate::farm::plotted_pieces::PlottedPieces;
use crate::farm::{Farm, FarmId, SectorPlottingDetails, SectorUpdate};
use anyhow::anyhow;
use async_lock::RwLock as AsyncRwLock;
use futures::channel::oneshot;
use futures::stream::{FusedStream, FuturesUnordered};
use futures::{select, FutureExt, Stream, StreamExt};
use parking_lot::Mutex;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet, VecDeque};
use std::future::Future;
use std::mem;
use std::pin::{pin, Pin};
use std::sync::Arc;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};
use subspace_core_primitives::hashes::Blake3Hash;
use subspace_core_primitives::sectors::SectorIndex;
use tokio::task;
use tokio::time::MissedTickBehavior;
use tokio_stream::StreamMap;
use tracing::{debug, error, info, warn};

/// Number of farms in a cluster is currently limited to 2^16
pub type FarmIndex = u16;

type AddRemoveResult = Option<(FarmIndex, oneshot::Receiver<()>, ClusterFarm)>;
type AddRemoveFuture<'a, R> = Pin<Box<dyn Future<Output = R> + 'a>>;
type AddRemoveStream<'a, R> = Pin<Box<dyn Stream<Item = R> + Unpin + 'a>>;

type FarmerFarmsDetailsResult =
    anyhow::Result<(KnownFarmerInsertResult, Vec<ClusterFarmerFarmDetails>)>;
type CollectFarmerFarmsFuture = Pin<Box<dyn Future<Output = FarmerFarmsDetailsResult>>>;

/// A FarmsAddRemovetreamMap that keeps track of futures that are currently being processed for each `FarmIndex`.
struct FarmsAddRemoveStreamMap<'a, R> {
    in_progress: StreamMap<FarmIndex, AddRemoveStream<'a, R>>,
    farms_to_add_remove: HashMap<FarmIndex, VecDeque<AddRemoveFuture<'a, R>>>,
}

impl<R> Default for FarmsAddRemoveStreamMap<'_, R> {
    fn default() -> Self {
        Self {
            in_progress: StreamMap::default(),
            farms_to_add_remove: HashMap::default(),
        }
    }
}

impl<'a, R: 'a> FarmsAddRemoveStreamMap<'a, R> {
    /// When pushing a new task, it first checks if there is already a future for the given `FarmIndex` in `in_progress`.
    ///   - If there is, the task is added to `farms_to_add_remove`.
    ///   - If not, the task is directly added to `in_progress`.
    fn push(&mut self, farm_index: FarmIndex, fut: AddRemoveFuture<'a, R>) {
        if self.in_progress.contains_key(&farm_index) {
            let queue = self.farms_to_add_remove.entry(farm_index).or_default();
            queue.push_back(fut);
        } else {
            self.in_progress
                .insert(farm_index, Box::pin(fut.into_stream()) as _);
        }
    }

    /// Polls the next entry in `in_progress` and moves the next task from `farms_to_add_remove` to `in_progress` if there is any.
    /// If there are no more tasks to execute, returns `None`.
    fn poll_next_entry(&mut self, cx: &mut Context<'_>) -> Poll<Option<R>> {
        if let Some((farm_index, res)) = std::task::ready!(self.in_progress.poll_next_unpin(cx)) {
            // Current task completed, remove from in_progress queue and check for more tasks
            self.in_progress.remove(&farm_index);
            self.process_farm_queue(farm_index);
            Poll::Ready(Some(res))
        } else {
            // No more tasks to execute
            assert!(self.farms_to_add_remove.is_empty());
            Poll::Ready(None)
        }
    }

    /// Process the next task from the farm queue for the given `farm_index`
    fn process_farm_queue(&mut self, farm_index: FarmIndex) {
        if let Entry::Occupied(mut next_entry) = self.farms_to_add_remove.entry(farm_index) {
            let task_queue = next_entry.get_mut();
            if let Some(fut) = task_queue.pop_front() {
                self.in_progress
                    .insert(farm_index, Box::pin(fut.into_stream()) as _);
            }

            // Remove the farm index from the map if there are no more tasks
            if task_queue.is_empty() {
                next_entry.remove();
            }
        }
    }
}

impl<'a, R: 'a> Stream for FarmsAddRemoveStreamMap<'a, R> {
    type Item = R;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        this.poll_next_entry(cx)
    }
}

impl<'a, R: 'a> FusedStream for FarmsAddRemoveStreamMap<'a, R> {
    fn is_terminated(&self) -> bool {
        self.in_progress.is_empty() && self.farms_to_add_remove.is_empty()
    }
}

#[derive(Debug)]
struct KnownFarm {
    farm_id: FarmId,
    fingerprint: Blake3Hash,
    expired_sender: oneshot::Sender<()>,
}

struct KnownFarmInsertResult {
    farm_index: FarmIndex,
    farm_id: FarmId,
    total_sectors_count: u16,
    expired_receiver: oneshot::Receiver<()>,
    add: bool,
    remove: bool,
}

impl KnownFarmInsertResult {
    fn process<'a>(
        self,
        nats_client: &'a NatsClient,
        farms_to_add_remove: &mut FarmsAddRemoveStreamMap<'a, AddRemoveResult>,
        plotted_pieces: Arc<AsyncRwLock<PlottedPieces<FarmIndex>>>,
    ) {
        let KnownFarmInsertResult {
            farm_index,
            farm_id,
            total_sectors_count,
            expired_receiver,
            add,
            remove,
        } = self;

        if remove {
            remove_farm(
                farm_id,
                farm_index,
                farms_to_add_remove,
                plotted_pieces.clone(),
            );
        }

        if add {
            farms_to_add_remove.push(
                farm_index,
                Box::pin(async move {
                    match initialize_farm(
                        farm_index,
                        farm_id,
                        total_sectors_count,
                        plotted_pieces.clone(),
                        nats_client,
                    )
                    .await
                    {
                        Ok(farm) => {
                            if remove {
                                info!(
                                    %farm_index,
                                    %farm_id,
                                    "Farm re-initialized successfully"
                                );
                            } else {
                                info!(
                                    %farm_index,
                                    %farm_id,
                                    "Farm initialized successfully"
                                );
                            }

                            Some((farm_index, expired_receiver, farm))
                        }
                        Err(error) => {
                            warn!(
                                %error,
                                "Failed to initialize farm {farm_id}"
                            );
                            None
                        }
                    }
                }),
            );
        }
    }
}

#[derive(Debug)]
struct KnownFarmer {
    farmer_id: ClusterFarmerId,
    fingerprint: Blake3Hash,
    last_identification: Instant,
    known_farms: HashMap<FarmIndex, KnownFarm>,
}

enum KnownFarmerInsertResult {
    Inserted {
        farmer_id: ClusterFarmerId,
        fingerprint: Blake3Hash,
    },
    FingerprintUpdated {
        farmer_id: ClusterFarmerId,
        old_farms: HashMap<FarmId, (FarmIndex, KnownFarm)>,
    },
    NotInserted,
}

impl KnownFarmerInsertResult {
    fn process(
        self,
        farms: Vec<ClusterFarmerFarmDetails>,
        known_farmers: &mut KnownFarmers,
    ) -> Vec<KnownFarmInsertResult> {
        let farm_indices = known_farmers.pick_farmer_index(farms.len());

        match self {
            KnownFarmerInsertResult::Inserted {
                farmer_id,
                fingerprint,
            } => {
                let mut known_farmer = KnownFarmer {
                    farmer_id,
                    fingerprint,
                    last_identification: Instant::now(),
                    known_farms: HashMap::new(),
                };

                let res = farm_indices
                    .into_iter()
                    .zip(farms)
                    .map(|(farm_index, farm_details)| {
                        let ClusterFarmerFarmDetails {
                            farm_id,
                            total_sectors_count,
                            fingerprint,
                        } = farm_details;
                        let (expired_sender, expired_receiver) = oneshot::channel();
                        known_farmer.known_farms.insert(
                            farm_index,
                            KnownFarm {
                                farm_id,
                                fingerprint,
                                expired_sender,
                            },
                        );
                        info!(%farmer_id, %farm_id, %total_sectors_count, "Discovered new farm");
                        KnownFarmInsertResult {
                            farm_index,
                            farm_id,
                            total_sectors_count,
                            expired_receiver,
                            add: true,
                            remove: false,
                        }
                    })
                    .collect::<Vec<_>>();
                known_farmers.known_farmers.push(known_farmer);
                res
            }
            KnownFarmerInsertResult::FingerprintUpdated {
                farmer_id,
                mut old_farms,
            } => {
                farm_indices
                    .into_iter()
                    .zip(farms)
                    .filter_map(|(farm_index, farm_details)| {
                        let ClusterFarmerFarmDetails {
                            farm_id,
                            total_sectors_count,
                            fingerprint,
                        } = farm_details;
                        if let Some((farm_index, mut known_farm)) = old_farms.remove(&farm_id) {
                            let known_farmer = known_farmers
                                .get_known_farmer(farmer_id)
                                .expect("Farmer should be available");
                            if known_farm.fingerprint == fingerprint {
                                // Do nothing if farm is already known
                                known_farmer.known_farms.insert(farm_index, known_farm);
                                None
                            } else {
                                // Update fingerprint
                                let (expired_sender, expired_receiver) = oneshot::channel();
                                known_farm.expired_sender = expired_sender;
                                known_farmer.known_farms.insert(farm_index, known_farm);
                                Some(KnownFarmInsertResult {
                                    farm_index,
                                    farm_id,
                                    total_sectors_count,
                                    expired_receiver,
                                    add: true,
                                    remove: true,
                                })
                            }
                        } else {
                            // Add new farm
                            let (expired_sender, expired_receiver) = oneshot::channel();

                            known_farmers
                                .get_known_farmer(farmer_id)
                                .expect("Farmer should be available")
                                .known_farms
                                .insert(
                                    farm_index,
                                    KnownFarm {
                                        farm_id,
                                        fingerprint,
                                        expired_sender,
                                    },
                                );
                            Some(KnownFarmInsertResult {
                                farm_index,
                                farm_id,
                                total_sectors_count,
                                expired_receiver,
                                add: true,
                                remove: false,
                            })
                        }
                    })
                    .collect::<Vec<_>>()
            }
            KnownFarmerInsertResult::NotInserted => {
                unreachable!("KnownFarmerInsertResult::NotInserted should be handled above")
            }
        }
    }
}

#[derive(Debug)]
struct KnownFarmers {
    identification_broadcast_interval: Duration,
    known_farmers: Vec<KnownFarmer>,
}

impl KnownFarmers {
    fn new(identification_broadcast_interval: Duration) -> Self {
        Self {
            identification_broadcast_interval,
            known_farmers: Vec::new(),
        }
    }

    fn insert_or_update_farmer(
        &mut self,
        farmer_id: ClusterFarmerId,
        fingerprint: Blake3Hash,
        nats_client: &NatsClient,
        farms_in_farmer_collector: &mut FuturesUnordered<CollectFarmerFarmsFuture>,
    ) {
        let result = self
            .known_farmers
            .iter_mut()
            .find_map(|known_farmer| {
                let check_farmer_id = known_farmer.farmer_id == farmer_id;
                let check_fingerprint = known_farmer.fingerprint == fingerprint;
                match (check_farmer_id, check_fingerprint) {
                    (true, true) => {
                        debug!(%farmer_id,"Updating last identification for farmer");
                        known_farmer.last_identification = Instant::now();
                        Some(KnownFarmerInsertResult::NotInserted)
                    }
                    (true, false) => {
                        let old_farms = known_farmer
                            .known_farms
                            .drain()
                            .map(|(farm_index, know_farm)| {
                                (know_farm.farm_id, (farm_index, know_farm))
                            })
                            .collect();
                        known_farmer.fingerprint = fingerprint;
                        known_farmer.last_identification = Instant::now();
                        Some(KnownFarmerInsertResult::FingerprintUpdated {
                            farmer_id,
                            old_farms,
                        })
                    }
                    (false, _) => None,
                }
            })
            .unwrap_or(KnownFarmerInsertResult::Inserted {
                farmer_id,
                fingerprint,
            });

        if let KnownFarmerInsertResult::NotInserted = result {
            return;
        }

        farms_in_farmer_collector.push(collect_farmer_farms(farmer_id, result, nats_client));
    }

    fn get_known_farmer(&mut self, farmer_id: ClusterFarmerId) -> Option<&mut KnownFarmer> {
        self.known_farmers
            .iter_mut()
            .find(|known_farmer| known_farmer.farmer_id == farmer_id)
    }

    fn pick_farmer_index(&self, len: usize) -> Vec<u16> {
        let used_indices = self
            .known_farmers
            .iter()
            .flat_map(|known_farmer| known_farmer.known_farms.keys())
            .collect::<HashSet<_>>();

        let mut available_indices = Vec::with_capacity(len);

        for farm_index in FarmIndex::MIN..=FarmIndex::MAX {
            if !used_indices.contains(&farm_index) {
                if available_indices.len() < len {
                    available_indices.push(farm_index);
                } else {
                    return available_indices;
                }
            }
        }

        warn!(max_supported_farm_index = %FarmIndex::MAX, "Too many farms");
        available_indices
    }

    fn remove_expired(&mut self) -> impl Iterator<Item = (FarmIndex, KnownFarm)> + '_ {
        self.known_farmers
            .extract_if(.., |known_farmer| {
                known_farmer.last_identification.elapsed()
                    > self.identification_broadcast_interval * 2
            })
            .flat_map(|known_farmer| known_farmer.known_farms)
    }

    fn remove_farm(&mut self, farm_index: FarmIndex) {
        self.known_farmers.iter_mut().for_each(|known_farmer| {
            known_farmer.known_farms.remove(&farm_index);
        });
    }
}

/// Utility function for maintaining farms by controller in a cluster environment
pub async fn maintain_farms(
    instance: &str,
    nats_client: &NatsClient,
    plotted_pieces: &Arc<AsyncRwLock<PlottedPieces<FarmIndex>>>,
    identification_broadcast_interval: Duration,
) -> anyhow::Result<()> {
    let mut known_farmers = KnownFarmers::new(identification_broadcast_interval);

    let mut farms_in_farmer_collector = FuturesUnordered::<CollectFarmerFarmsFuture>::new();
    // Stream map for adding/removing farms
    let mut farms_to_add_remove = FarmsAddRemoveStreamMap::default();
    let mut farms = FuturesUnordered::new();

    let farmer_identify_subscription = pin!(nats_client
        .subscribe_to_broadcasts::<ClusterFarmerIdentifyBroadcast>(None, None)
        .await
        .map_err(|error| anyhow!("Failed to subscribe to farmer identify broadcast: {error}"))?);

    // Request farmer to identify themselves
    if let Err(error) = nats_client
        .broadcast(&ClusterControllerFarmerIdentifyBroadcast, instance)
        .await
    {
        warn!(%error, "Failed to send farmer identification broadcast");
    }

    let mut farmer_identify_subscription = farmer_identify_subscription.fuse();
    let mut farm_pruning_interval = tokio::time::interval_at(
        (Instant::now() + identification_broadcast_interval * 2).into(),
        identification_broadcast_interval * 2,
    );
    farm_pruning_interval.set_missed_tick_behavior(MissedTickBehavior::Delay);

    loop {
        select! {
            (farm_index, result) = farms.select_next_some() => {
                known_farmers.remove_farm(farm_index);
                farms_to_add_remove.push(farm_index, Box::pin(async move {
                    let plotted_pieces = Arc::clone(plotted_pieces);

                    let delete_farm_fut = task::spawn_blocking(move || {
                        plotted_pieces.write_blocking().delete_farm(farm_index);
                    });
                    if let Err(error) = delete_farm_fut.await {
                        error!(
                            %farm_index,
                            %error,
                            "Failed to delete farm that exited"
                        );
                    }

                    None
                }));

                match result {
                    Ok(()) => {
                        info!(%farm_index, "Farm exited successfully");
                    }
                    Err(error) => {
                        error!(%farm_index, %error, "Farm exited with error");
                    }
                }
            }
            maybe_identify_message = farmer_identify_subscription.next() => {
                let Some(identify_message) = maybe_identify_message else {
                    return Err(anyhow!("Farmer identify stream ended"));
                };
                let ClusterFarmerIdentifyBroadcast {
                    farmer_id,
                    fingerprint,
                } = identify_message;

                known_farmers.insert_or_update_farmer(
                    farmer_id,
                    fingerprint,
                    nats_client,
                    &mut farms_in_farmer_collector,
                );
            }
            maybe_new_farmer_farms = farms_in_farmer_collector.select_next_some() => {
                let Ok((farmer_insert_result, farms)) = maybe_new_farmer_farms else {
                    // Collecting farmer farms failed, continue
                    continue;
                };

                for farm_insert_result in farmer_insert_result.process(farms, &mut known_farmers)
                {
                    farm_insert_result.process(nats_client, &mut farms_to_add_remove, Arc::clone(plotted_pieces));
                }
            }
            _ = farm_pruning_interval.tick().fuse() => {
                for (farm_index, removed_farm) in known_farmers.remove_expired() {
                    let farm_id = removed_farm.farm_id;

                    if removed_farm.expired_sender.send(()).is_ok() {
                        warn!(
                            %farm_index,
                            %farm_id,
                            "Farm expired and removed"
                        );
                    } else {
                        warn!(
                            %farm_index,
                            %farm_id,
                            "Farm exited before expiration notification"
                        );
                    }

                    farms_to_add_remove.push(farm_index, Box::pin(async move {
                        let plotted_pieces = Arc::clone(plotted_pieces);

                        let delete_farm_fut = task::spawn_blocking(move || {
                            plotted_pieces.write_blocking().delete_farm(farm_index);
                        });
                        if let Err(error) = delete_farm_fut.await {
                            error!(
                                %farm_index,
                                %farm_id,
                                %error,
                                "Failed to delete farm that expired"
                            );
                        }

                        None
                    }));
                }
            }
            result = farms_to_add_remove.select_next_some() => {
                if let Some((farm_index, expired_receiver, farm)) = result {
                    farms.push(async move {
                        select! {
                            result = farm.run().fuse() => {
                                (farm_index, result)
                            }
                            _ = expired_receiver.fuse() => {
                                // Nothing to do
                                (farm_index, Ok(()))
                            }
                        }
                    });
                }
            }
        }
    }
}

/// Collect `ClusterFarmerFarmDetails` from the farmer by sending a stream request
fn collect_farmer_farms(
    farmer_id: ClusterFarmerId,
    result: KnownFarmerInsertResult,
    nats_client: &NatsClient,
) -> CollectFarmerFarmsFuture {
    let nats_client = nats_client.clone();
    Box::pin(async move {
        Ok((
            result,
            nats_client
                .stream_request(
                    &ClusterFarmerFarmDetailsRequest,
                    Some(&farmer_id.to_string()),
                )
                .await
                .inspect_err(|error| {
                    warn!(
                        %error,
                        %farmer_id,
                        "Failed to request farmer farm details"
                    )
                })?
                .collect()
                .await,
        ))
    })
}

fn remove_farm(
    farm_id: FarmId,
    farm_index: FarmIndex,
    farms_to_add_remove: &mut FarmsAddRemoveStreamMap<'_, AddRemoveResult>,
    plotted_pieces: Arc<AsyncRwLock<PlottedPieces<FarmIndex>>>,
) {
    farms_to_add_remove.push(
        farm_index,
        Box::pin(async move {
            let delete_farm_fut = task::spawn_blocking(move || {
                plotted_pieces.write_blocking().delete_farm(farm_index);
            });
            if let Err(error) = delete_farm_fut.await {
                error!(
                    %farm_index,
                    %farm_id,
                    %error,
                    "Failed to delete farm that was replaced",
                );
            }

            None
        }),
    );
}

async fn initialize_farm(
    farm_index: FarmIndex,
    farm_id: FarmId,
    total_sectors_count: SectorIndex,
    plotted_pieces: Arc<AsyncRwLock<PlottedPieces<FarmIndex>>>,
    nats_client: &NatsClient,
) -> anyhow::Result<ClusterFarm> {
    let farm = ClusterFarm::new(farm_id, total_sectors_count, nats_client.clone())
        .await
        .map_err(|error| anyhow!("Failed instantiate cluster farm {farm_id}: {error}"))?;

    // Buffer sectors that are plotted while already plotted sectors are being iterated over
    let plotted_sectors_buffer = Arc::new(Mutex::new(Vec::new()));
    let sector_update_handler = farm.on_sector_update(Arc::new({
        let plotted_sectors_buffer = Arc::clone(&plotted_sectors_buffer);

        move |(_sector_index, sector_update)| {
            if let SectorUpdate::Plotting(SectorPlottingDetails::Finished {
                plotted_sector,
                old_plotted_sector,
                ..
            }) = sector_update
            {
                plotted_sectors_buffer
                    .lock()
                    .push((plotted_sector.clone(), old_plotted_sector.clone()));
            }
        }
    }));

    // Add plotted sectors of the farm to global plotted pieces
    let plotted_sectors = farm.plotted_sectors();
    let mut plotted_sectors = plotted_sectors
        .get()
        .await
        .map_err(|error| anyhow!("Failed to get plotted sectors for farm {farm_id}: {error}"))?;

    {
        plotted_pieces
            .write()
            .await
            .add_farm(farm_index, farm.piece_reader());

        while let Some(plotted_sector_result) = plotted_sectors.next().await {
            let plotted_sector = plotted_sector_result.map_err(|error| {
                anyhow!("Failed to get plotted sector for farm {farm_id}: {error}")
            })?;

            let mut plotted_pieces_guard = plotted_pieces.write().await;
            plotted_pieces_guard.add_sector(farm_index, &plotted_sector);

            // Drop the guard immediately to make sure other tasks are able to access the plotted pieces
            drop(plotted_pieces_guard);

            task::yield_now().await;
        }
    }

    // Add sectors that were plotted while above iteration was happening to plotted sectors
    // too
    drop(sector_update_handler);
    let plotted_sectors_buffer = mem::take(&mut *plotted_sectors_buffer.lock());
    let add_buffered_sectors_fut = task::spawn_blocking(move || {
        let mut plotted_pieces = plotted_pieces.write_blocking();

        for (plotted_sector, old_plotted_sector) in plotted_sectors_buffer {
            if let Some(old_plotted_sector) = old_plotted_sector {
                plotted_pieces.delete_sector(farm_index, &old_plotted_sector);
            }
            // Call delete first to avoid adding duplicates
            plotted_pieces.delete_sector(farm_index, &plotted_sector);
            plotted_pieces.add_sector(farm_index, &plotted_sector);
        }
    });

    add_buffered_sectors_fut
        .await
        .map_err(|error| anyhow!("Failed to add buffered sectors for farm {farm_id}: {error}"))?;

    Ok(farm)
}
