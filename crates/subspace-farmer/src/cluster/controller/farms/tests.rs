use crate::cluster::controller::farms::FarmsAddRemoveStreamMap;
use futures::stream::FusedStream;
use futures::StreamExt;
use std::task::Context;

fn assert_is_terminated<'a, R: 'a>(stream_map: &FarmsAddRemoveStreamMap<'a, R>) {
    assert!(stream_map.in_progress.is_empty());
    assert!(stream_map.farms_to_add_remove.is_empty());
    assert!(stream_map.is_terminated());
}

#[test]
fn test_stream_map_default() {
    let stream_map = FarmsAddRemoveStreamMap::<()>::default();
    assert_is_terminated(&stream_map);
}

#[test]
fn test_stream_map_push() {
    let mut stream_map = FarmsAddRemoveStreamMap::default();

    let farm_index = 1;
    let fut = Box::pin(async {});
    stream_map.push(farm_index, fut);
    assert!(stream_map.farms_to_add_remove.is_empty());
    assert!(stream_map.in_progress.contains_key(&farm_index));
    assert!(!stream_map.is_terminated());
}

#[test]
fn test_stream_map_poll_next_entry() {
    let mut stream_map = FarmsAddRemoveStreamMap::default();

    let fut = Box::pin(async {});
    stream_map.push(0, fut);

    let mut cx = Context::from_waker(futures::task::noop_waker_ref());
    let poll_result = stream_map.poll_next_entry(&mut cx);
    assert!(poll_result.is_ready());
    assert_is_terminated(&stream_map);
}

#[tokio::test]
async fn test_stream_map_stream() {
    let mut stream_map = FarmsAddRemoveStreamMap::default();

    let fut00 = Box::pin(async { 0x00 });
    stream_map.push(0, fut00);

    let next_item = stream_map.next().await;
    assert_eq!(next_item, Some(0x00));
    assert_is_terminated(&stream_map);

    let fut11 = Box::pin(async { 0x11 });
    let fut12 = Box::pin(async { 0x12 });
    let fut13 = Box::pin(async { 0x13 });
    let fut21 = Box::pin(async {
        // Yield the current task three times to ensure that fut22 is polled last.
        for _ in 0..3 {
            tokio::task::yield_now().await;
        }
        0x21
    });
    let fut22 = Box::pin(async { 0x22 });

    // Push 2 futs into the same farm index 1, expect fut11 to be polled first,
    // fut12 should push into the in_progress queue and wait for fut11 to finish
    stream_map.push(1, fut11);
    stream_map.push(1, fut12);
    assert!(!stream_map.is_terminated());
    assert_eq!(stream_map.in_progress.len(), 1);
    assert!(stream_map.in_progress.contains_key(&1));
    assert_eq!(stream_map.farms_to_add_remove.len(), 1);

    // Push fut22 into farm index 2, we have 2 in progress futures now
    stream_map.push(2, fut21);
    assert_eq!(stream_map.in_progress.len(), 2);
    assert!(stream_map.in_progress.contains_key(&2));
    assert_eq!(stream_map.farms_to_add_remove.len(), 1);

    // Push fut22 into farm index 2, in-progress queue length should not change,
    // but the farms_to_add_remove should have 2 entries now
    stream_map.push(2, fut22);
    assert_eq!(stream_map.in_progress.len(), 2);
    assert_eq!(stream_map.farms_to_add_remove.len(), 2);
    assert_eq!(stream_map.farms_to_add_remove[&2].len(), 1);

    // Push fut13 into farm index 1, fut13 should be polled after fut11 and fut12
    stream_map.push(1, fut13);
    assert!(!stream_map.is_terminated());
    assert!(stream_map.in_progress.contains_key(&1));
    assert_eq!(stream_map.in_progress.len(), 2);
    assert_eq!(stream_map.farms_to_add_remove[&1].len(), 2);

    // Poll the next item in the stream, fut11 should be polled first,
    // fut12 should be pushed into the in-progress queue
    let next_item = stream_map.next().await;
    assert!(!stream_map.is_terminated());
    assert_eq!(next_item.unwrap(), 0x11);
    assert!(stream_map.in_progress.contains_key(&1));
    assert!(stream_map.in_progress.contains_key(&2));
    assert_eq!(stream_map.in_progress.len(), 2);
    assert_eq!(stream_map.farms_to_add_remove[&1].len(), 1);

    // Here, fut12 and fut 13 should be polled before fut21 because fut21 has a yield point.
    // Fut13 should be pushed into the in_progress queue.
    // There are no more futures waiting to be polled in farm index 1, so the farm index 1
    // should be removed from the farms_to_add_remove map.
    let next_item = stream_map.next().await;
    assert!(!stream_map.is_terminated());
    assert_eq!(next_item.unwrap(), 0x12);
    assert_eq!(stream_map.in_progress.len(), 2);
    assert!(stream_map.in_progress.contains_key(&1));
    assert!(stream_map.in_progress.contains_key(&2));
    assert!(!stream_map.farms_to_add_remove.contains_key(&1));

    // Poll the next item in the stream, fut13 should be polled next.
    // For now, all futures in farm index 1 have been polled, so farm index 1 should be removed
    // from the in-progress queue.
    let next_item = stream_map.next().await;
    assert!(!stream_map.is_terminated());
    assert_eq!(next_item.unwrap(), 0x13);
    assert_eq!(stream_map.in_progress.len(), 1);
    assert!(!stream_map.in_progress.contains_key(&1));
    assert!(stream_map.in_progress.contains_key(&2));
    assert!(!stream_map.farms_to_add_remove.contains_key(&1));
    assert_eq!(stream_map.farms_to_add_remove[&2].len(), 1);

    // We hope futures with the same index are polled in the order they are pushed,
    // so fut21 should be polled next.
    // fut22 should be pushed into the in-progress queue.
    // There are no more futures waiting to be polled in farm index 2, so the farm index 2
    // should be removed from the farms_to_add_remove map.
    let next_item = stream_map.next().await;
    assert!(!stream_map.is_terminated());
    assert_eq!(next_item.unwrap(), 0x21);
    assert_eq!(stream_map.in_progress.len(), 1);
    assert!(!stream_map.in_progress.contains_key(&1));
    assert!(stream_map.in_progress.contains_key(&2));
    assert!(!stream_map.farms_to_add_remove.contains_key(&1));
    assert!(!stream_map.farms_to_add_remove.contains_key(&2));

    // Poll the next item in the stream, fut22 should be polled next.
    // For now, all futures in farm index 2 have been polled, so farm index 2 should be removed
    // from the in-progress queue.
    // Finally, the stream should be terminated.
    let next_item = stream_map.next().await;
    assert_eq!(next_item, Some(0x22));
    assert_is_terminated(&stream_map);
}
