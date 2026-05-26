//! Shared test plumbing. Each test binary (`tests/<file>.rs`) gets its
//! own copy of this module via `mod common;`.

use std::io::{self, Read};
use std::process::{Child, Output};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

/// Result of [`wait_with_timeout`]. `TimedOut` carries whatever bytes the
/// reader threads managed to capture before the child was killed.
pub enum WaitOutcome {
    Exited(Output),
    TimedOut { stdout: Vec<u8>, stderr: Vec<u8> },
}

// Drain stdout/stderr in background threads so the child never blocks on
// a full pipe buffer (~64KB on macOS). `Child::wait_with_output` does
// this internally but has no timeout; the timeout requirement is what
// forces us to hand-roll the drain.
fn spawn_drain<R: Read + Send + 'static>(
    stream: Option<R>,
) -> Option<JoinHandle<io::Result<Vec<u8>>>> {
    stream.map(|mut s| {
        thread::spawn(move || {
            let mut buf = Vec::new();
            s.read_to_end(&mut buf)?;
            Ok(buf)
        })
    })
}

fn join_drain(h: Option<JoinHandle<io::Result<Vec<u8>>>>) -> io::Result<Vec<u8>> {
    match h {
        None => Ok(Vec::new()),
        Some(j) => j
            .join()
            .unwrap_or_else(|_| Err(io::Error::other("reader thread panicked"))),
    }
}

/// Wait for `child` up to `timeout`, returning its `Output` on exit or the
/// captured stdout/stderr on timeout. Reader thread panics and pipe read
/// errors propagate as `io::Error` rather than collapsing to empty output.
pub fn wait_with_timeout(mut child: Child, timeout: Duration) -> io::Result<WaitOutcome> {
    let stdout_h = spawn_drain(child.stdout.take());
    let stderr_h = spawn_drain(child.stderr.take());

    let start = Instant::now();
    let status = loop {
        if let Some(s) = child.try_wait()? {
            break Some(s);
        }
        if start.elapsed() >= timeout {
            if let Err(e) = child.kill() {
                eprintln!("warning: failed to kill timed-out child: {e}");
            }
            let _ = child.wait();
            break None;
        }
        thread::sleep(Duration::from_millis(100));
    };

    let stdout = join_drain(stdout_h)?;
    let stderr = join_drain(stderr_h)?;
    Ok(match status {
        Some(status) => WaitOutcome::Exited(Output { status, stdout, stderr }),
        None => WaitOutcome::TimedOut { stdout, stderr },
    })
}
