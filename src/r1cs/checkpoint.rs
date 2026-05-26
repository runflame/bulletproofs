//! Checkpoint / rollback support for R1CS constraint systems.
//!
//! A [`Checkpoint`] is a fixed-size snapshot of the constraint-system
//! state. Take one with [`CheckpointableConstraintSystem::checkpoint`],
//! mutate the CS freely, then either:
//!
//! - Drop or [`commit_checkpoint`](CheckpointableConstraintSystem::commit_checkpoint)
//!   the checkpoint to keep the new state, OR
//! - Pass it to [`rollback`](CheckpointableConstraintSystem::rollback) to
//!   revert the CS to its state at the time of the checkpoint.
//!
//! All CS state is append-only except the transcript and a small
//! pending-multiplier flag, so a checkpoint records six small fields
//! plus a clone of the Merlin transcript (~208 bytes); rollback truncates
//! the underlying vectors in place without reallocating.

use merlin::Transcript;

use super::ConstraintSystem;

/// Fixed-size snapshot of a constraint system's state.
///
/// Used by both `Prover` and `Verifier`: the numeric fields cover both
/// the prover's `(a_L,a_R,a_O)` / `(v,v_blinding)` invariant-equal
/// vectors and the verifier's `num_vars` / `V` counters.
pub struct Checkpoint {
    pub(super) transcript: Transcript,
    pub(super) pending_multiplier: Option<usize>,
    pub(super) n_constraints: usize,
    /// Multiplier count: `a_L.len()` for the prover, `num_vars` for the verifier.
    pub(super) n_multipliers: usize,
    /// Committed-variable count: `v.len()` for the prover, `V.len()` for the verifier.
    pub(super) n_committed: usize,
    pub(super) n_deferred: usize,
}

/// Constraint systems that support O(1) checkpoint and rollback.
pub trait CheckpointableConstraintSystem: ConstraintSystem {
    /// Capture the current CS state. Clones the transcript; no other allocation.
    fn checkpoint(&self) -> Checkpoint;

    /// Restore the CS to the state recorded by `cp`. Vector capacities are preserved.
    fn rollback(&mut self, cp: Checkpoint);

    /// Discard a checkpoint, keeping all changes made since it was taken.
    /// Equivalent to dropping the checkpoint; provided for symmetry.
    fn commit_checkpoint(&mut self, cp: Checkpoint) {
        drop(cp);
    }

    /// Run `f`; if it returns `Err`, roll back to the pre-call state.
    fn try_block<F, R, E>(&mut self, f: F) -> Result<R, E>
    where
        F: FnOnce(&mut Self) -> Result<R, E>,
        Self: Sized,
    {
        let cp = self.checkpoint();
        match f(self) {
            Ok(v) => {
                self.commit_checkpoint(cp);
                Ok(v)
            }
            Err(e) => {
                self.rollback(cp);
                Err(e)
            }
        }
    }
}
