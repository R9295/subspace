//! Gateway rpc command.
//! This command starts an RPC server to serve object requests from the DSN.
pub(crate) mod server;

use crate::commands::rpc::server::{RPC_DEFAULT_PORT, RpcOptions, launch_rpc_server};
use crate::commands::{GatewayOptions, initialize_object_fetcher};
use clap::Parser;
use futures::{FutureExt, select};
use std::pin::pin;
use subspace_gateway_rpc::{SubspaceGatewayRpc, SubspaceGatewayRpcConfig};
use subspace_networking::utils::{run_future_in_dedicated_thread, shutdown_signal};
use tracing::info;

/// Options for RPC server.
#[derive(Debug, Parser)]
pub(crate) struct RpcCommandOptions {
    #[clap(flatten)]
    gateway_options: GatewayOptions,

    /// Options for RPC
    #[clap(flatten)]
    rpc_options: RpcOptions<RPC_DEFAULT_PORT>,
}

/// Runs an RPC server which fetches DSN objects based on mappings.
pub async fn run(run_options: RpcCommandOptions) -> anyhow::Result<()> {
    let signal = shutdown_signal("gateway");

    let RpcCommandOptions {
        gateway_options,
        rpc_options,
    } = run_options;
    let (object_fetcher, mut dsn_node_runner) = initialize_object_fetcher(gateway_options).await?;
    let dsn_fut = run_future_in_dedicated_thread(
        move || async move { dsn_node_runner.run().await },
        "gateway-networking".to_string(),
    )?;

    let rpc_api = SubspaceGatewayRpc::new(SubspaceGatewayRpcConfig { object_fetcher });
    let rpc_handle = launch_rpc_server(rpc_api, rpc_options).await?;
    let rpc_fut = rpc_handle.stopped();

    // If a spawned future is running for a long time, it can block receiving exit signals.
    // Rather than hunting down every possible blocking future, we give the exit signal itself a
    // dedicated thread to run on.
    let exit_signal_select_fut = run_future_in_dedicated_thread(
        move || async move {
            // This defines order in which things are dropped
            let dsn_fut = dsn_fut;
            let rpc_fut = rpc_fut;

            let dsn_fut = pin!(dsn_fut);
            let rpc_fut = pin!(rpc_fut);

            select! {
                // Signal future
                () = signal.fuse() => {},

                // Networking future
                _ = dsn_fut.fuse() => {
                    info!("DSN network runner exited.");
                },

                // RPC service future
                () = rpc_fut.fuse() => {
                    info!("RPC server exited.");
                },

            }

            anyhow::Ok(())
        },
        "gateway-exit-signal-select".to_string(),
    )?;

    exit_signal_select_fut.await??;

    anyhow::Ok(())
}
