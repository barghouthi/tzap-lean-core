//! What tzap is allowed to put on the terminal: whether to color, whether it
//! may redraw in place, and whether to say anything at all.
//!
//! Every escape sequence tzap emits goes out through a [`Ui`], so a run whose
//! stderr is a pipe or a file gets plain text — no color, and above all no
//! cursor motion, which is what turns a live progress box into `^[[6A^M`
//! garbage in a CI log.
//!
//! There is nothing to configure: a stream that is a terminal is styled, and
//! one that isn't, isn't. The two streams are asked separately, because they
//! are redirected separately — `tzap --help | less` must not color its help
//! while stderr is still a terminal.

use std::io::{self, IsTerminal, Write};

/// How much tzap says about what it's doing, as selected by `--quiet`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Verbosity {
    /// Errors only. Requested output (the circuit, `--json`) is never
    /// suppressed — quiet governs the commentary on stderr, not the result.
    Quiet,
    #[default]
    Normal,
}

/// Whether in-place redraws are allowed: something to draw them on, and
/// something to draw. Styling and redrawing follow from the same terminal
/// check but are not the same question — a `--quiet` run on a terminal is
/// still allowed to color the one error it might print.
fn allow_live(is_terminal: bool, verbosity: Verbosity) -> bool {
    is_terminal && verbosity > Verbosity::Quiet
}

/// The terminal capabilities and verbosity one run was configured with. Held
/// by the CLI's `Observer` and consulted by every line it prints; the
/// rendering itself lives in `progress.rs` as further `impl Ui` blocks.
pub(crate) struct Ui {
    /// Color the messaging stream (stderr).
    color: bool,
    /// Color the output stream (stdout) — help text and `--cache-info`, which
    /// are requested output rather than messaging. Asked separately because
    /// the two streams are redirected separately.
    out_color: bool,
    /// Whether in-place redraws (cursor motion, line erasure) are allowed.
    live: bool,
    verbosity: Verbosity,
}

impl Ui {
    pub(crate) fn new(verbosity: Verbosity) -> Ui {
        let stderr_tty = io::stderr().is_terminal();
        Ui {
            color: stderr_tty,
            out_color: io::stdout().is_terminal(),
            live: allow_live(stderr_tty, verbosity),
            verbosity,
        }
    }

    /// A Ui for a non-terminal run: no color, no redraws. The default for
    /// tests and for any embedder that just wants the plain-text rendering.
    #[cfg(test)]
    pub(crate) fn plain() -> Ui {
        Ui {
            color: false,
            out_color: false,
            live: false,
            verbosity: Verbosity::Normal,
        }
    }

    /// A Ui that behaves as though stderr were a terminal: colored, and
    /// allowed to redraw in place. The only way to exercise the live
    /// rendering path from a test, which runs with both streams piped.
    #[cfg(test)]
    pub(crate) fn live_for_tests() -> Ui {
        Ui {
            color: true,
            out_color: true,
            live: true,
            verbosity: Verbosity::Normal,
        }
    }

    /// `code` if stderr is being colored, else nothing — the single gate every
    /// escape sequence in tzap's messaging passes through.
    pub(crate) fn sgr(&self, code: &'static str) -> &'static str {
        if self.color { code } else { "" }
    }

    /// [`Ui::sgr`] for the stdout stream (help, `--cache-info`).
    pub(crate) fn out_sgr(&self, code: &'static str) -> &'static str {
        if self.out_color { code } else { "" }
    }

    /// Reset attributes, or nothing when not coloring. Paired with every
    /// [`Ui::sgr`] that sets one.
    pub(crate) fn reset(&self) -> &'static str {
        self.sgr("\x1b[0m")
    }

    pub(crate) fn out_reset(&self) -> &'static str {
        self.out_sgr("\x1b[0m")
    }

    pub(crate) fn live(&self) -> bool {
        self.live
    }

    pub(crate) fn quiet(&self) -> bool {
        self.verbosity == Verbosity::Quiet
    }

    /// Print a normal-verbosity message to stderr. Suppressed by `--quiet`.
    pub(crate) fn info(&self, text: &str) {
        if !self.quiet() {
            eprintln!("{text}");
        }
    }

    /// A blank separator line, at normal verbosity and above.
    pub(crate) fn blank(&self) {
        self.info("");
    }

    /// Print `text` with no trailing newline (flushed immediately) so a later
    /// [`Ui::finish_inline`] can overwrite it in place once the operation it
    /// describes completes. Without a live terminal there is nothing to
    /// overwrite, so the in-progress half is skipped entirely rather than
    /// left behind as a duplicate line — `finish_inline` alone then reads as
    /// one complete plain-text line.
    pub(crate) fn start_inline(&self, text: &str) {
        if self.live {
            eprint!("{text}");
            let _ = io::stderr().flush();
        }
    }

    /// Write requested output — the circuit, a `--json` report, a
    /// `--cache-info` listing — to stdout.
    ///
    /// A downstream reader closing the pipe (`tzap in.qasm -o - | head`) is a
    /// normal end to a pipeline, not a tzap failure: every Unix tool ends
    /// quietly there, and `println!` would instead panic with "failed
    /// printing to stdout". Any other write error is real and reported.
    ///
    /// Never gated on verbosity: `--quiet` silences commentary, not the
    /// output that was asked for.
    pub(crate) fn write_stdout(&self, text: &str) {
        let mut stdout = io::stdout().lock();
        match stdout
            .write_all(text.as_bytes())
            .and_then(|()| stdout.flush())
        {
            Ok(()) => {}
            Err(e) if e.kind() == io::ErrorKind::BrokenPipe => std::process::exit(0),
            Err(e) => self.abort(&format!("Error writing to stdout: {e}")),
        }
    }

    /// Print `text` to stderr and exit 1. Never suppressed: `--quiet` means
    /// "nothing but errors".
    ///
    /// The leading newline closes an unterminated [`Ui::start_inline`] line,
    /// which only exists on a live terminal — without one, an error arrives
    /// at the start of its own line already, and the extra blank read as a
    /// gap in the output.
    pub(crate) fn abort(&self, text: &str) -> ! {
        if self.live {
            eprintln!();
        }
        eprintln!("{text}");
        std::process::exit(1);
    }

    /// Overwrite an in-progress line started by [`Ui::start_inline`].
    pub(crate) fn finish_inline(&self, text: &str) {
        if self.quiet() {
            return;
        }
        if self.live {
            eprintln!("\r\x1b[2K{text}");
        } else {
            eprintln!("{text}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A redraw needs a terminal to draw on, and quiet has nothing to draw.
    #[test]
    fn redraws_need_both_a_terminal_and_something_to_draw() {
        assert!(allow_live(true, Verbosity::Normal));
        assert!(!allow_live(true, Verbosity::Quiet));
        assert!(!allow_live(false, Verbosity::Normal));
        assert!(!allow_live(false, Verbosity::Quiet));
    }

    #[test]
    fn plain_ui_emits_no_escapes() {
        let ui = Ui::plain();
        assert_eq!(ui.sgr("\x1b[1m"), "");
        assert_eq!(ui.reset(), "");
        assert_eq!(ui.out_sgr("\x1b[1m"), "");
        assert!(!ui.live());
    }
}
