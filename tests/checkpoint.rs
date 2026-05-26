#![allow(non_snake_case)]

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;

use bulletproofs::r1cs::{
    CheckpointableConstraintSystem, ConstraintSystem, LinearCombination, Prover, R1CSError,
    Variable, Verifier,
};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

// Basic rollback returns the CS to the multiplier count it had at checkpoint.
#[test]
fn rollback_restores_multipliers() {
    let pc_gens = PedersenGens::default();
    let mut t = Transcript::new(b"checkpoint test");
    let mut prover = Prover::new(&pc_gens, &mut t);

    let cp = prover.checkpoint();
    assert_eq!(prover.multipliers_len(), 0);

    prover
        .allocate_multiplier(Some((Scalar::from(2u64), Scalar::from(3u64))))
        .unwrap();
    prover
        .allocate_multiplier(Some((Scalar::from(4u64), Scalar::from(5u64))))
        .unwrap();
    assert_eq!(prover.multipliers_len(), 2);

    prover.rollback(cp);
    assert_eq!(prover.multipliers_len(), 0);
}

// commit_checkpoint keeps everything done since the checkpoint.
#[test]
fn commit_keeps_changes() {
    let pc_gens = PedersenGens::default();
    let mut t = Transcript::new(b"checkpoint test");
    let mut prover = Prover::new(&pc_gens, &mut t);

    let cp = prover.checkpoint();
    prover
        .allocate_multiplier(Some((Scalar::from(2u64), Scalar::from(3u64))))
        .unwrap();
    prover.commit_checkpoint(cp);
    assert_eq!(prover.multipliers_len(), 1);
}

// try_block returns Ok -> changes persist.
#[test]
fn try_block_ok_keeps_changes() {
    let pc_gens = PedersenGens::default();
    let mut t = Transcript::new(b"checkpoint test");
    let mut prover = Prover::new(&pc_gens, &mut t);

    let res: Result<(), R1CSError> = prover.try_block(|cs| {
        cs.allocate_multiplier(Some((Scalar::from(2u64), Scalar::from(3u64))))?;
        Ok(())
    });
    assert!(res.is_ok());
    assert_eq!(prover.multipliers_len(), 1);
}

// try_block returns Err -> changes are rolled back.
#[test]
fn try_block_err_rolls_back() {
    let pc_gens = PedersenGens::default();
    let mut t = Transcript::new(b"checkpoint test");
    let mut prover = Prover::new(&pc_gens, &mut t);

    let res: Result<(), &'static str> = prover.try_block(|cs| {
        cs.allocate_multiplier(Some((Scalar::from(2u64), Scalar::from(3u64))))
            .map_err(|_| "alloc failed")?;
        Err("intentional")
    });
    assert_eq!(res, Err("intentional"));
    assert_eq!(prover.multipliers_len(), 0);
}

// Rolling back across a pending-multiplier flip restores the half-allocated slot.
#[test]
fn rollback_restores_pending_multiplier() {
    let pc_gens = PedersenGens::default();
    let mut t = Transcript::new(b"pending test");
    let mut prover = Prover::new(&pc_gens, &mut t);

    let left = prover.allocate(Some(Scalar::from(7u64))).unwrap();
    assert_eq!(left, Variable::MultiplierLeft(0));
    // pending_multiplier == Some(0) here.

    let cp = prover.checkpoint();

    // Fill the right slot; pending_multiplier flips to None.
    let right = prover.allocate(Some(Scalar::from(9u64))).unwrap();
    assert_eq!(right, Variable::MultiplierRight(0));

    prover.rollback(cp);

    // After rollback, pending_multiplier should be Some(0) again. The next
    // allocate should target the right slot of the same multiplier.
    let right_again = prover.allocate(Some(Scalar::from(42u64))).unwrap();
    assert_eq!(right_again, Variable::MultiplierRight(0));
    assert_eq!(prover.multipliers_len(), 1);
}

// Nested checkpoints stack independently.
#[test]
fn nested_checkpoints() {
    let pc_gens = PedersenGens::default();
    let mut t = Transcript::new(b"nested");
    let mut prover = Prover::new(&pc_gens, &mut t);

    let outer = prover.checkpoint();
    prover
        .allocate_multiplier(Some((Scalar::one(), Scalar::one())))
        .unwrap();

    let inner = prover.checkpoint();
    prover
        .allocate_multiplier(Some((Scalar::from(2u64), Scalar::from(2u64))))
        .unwrap();
    prover
        .allocate_multiplier(Some((Scalar::from(3u64), Scalar::from(3u64))))
        .unwrap();
    assert_eq!(prover.multipliers_len(), 3);

    prover.rollback(inner);
    assert_eq!(prover.multipliers_len(), 1);

    prover
        .allocate_multiplier(Some((Scalar::from(4u64), Scalar::from(4u64))))
        .unwrap();
    assert_eq!(prover.multipliers_len(), 2);

    prover.rollback(outer);
    assert_eq!(prover.multipliers_len(), 0);
}

// A circuit assembled with rolled-back noise yields a proof that verifies
// against the clean verifier circuit. Exercises constraints, multipliers,
// and transcript revert end-to-end.
#[test]
fn proof_round_trip_with_prover_side_rollback() {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(32, 1);

    let (proof, commitment) = {
        let mut t = Transcript::new(b"round trip");
        let mut prover = Prover::new(&pc_gens, &mut t);
        let (commitment, var) = prover.commit(Scalar::from(7u64), Scalar::from(11u64));

        // Noisy work that should be invisible to the final proof.
        let _: Result<(), R1CSError> = prover.try_block(|cs| {
            cs.allocate_multiplier(Some((Scalar::from(99u64), Scalar::from(99u64))))?;
            cs.constrain(LinearCombination::from(Variable::One()) * Scalar::from(123u64));
            Err(R1CSError::MissingAssignment) // force rollback
        });

        // The "real" circuit: prove that var * var = 49 (so var == 7 or -7).
        let (l, r, o) = prover
            .allocate_multiplier(Some((Scalar::from(7u64), Scalar::from(7u64))))
            .unwrap();
        prover.constrain(LinearCombination::from(l) - var);
        prover.constrain(LinearCombination::from(r) - var);
        prover.constrain(LinearCombination::from(o) - Scalar::from(49u64));

        (prover.prove(&bp_gens).unwrap(), commitment)
    };

    // Clean verifier circuit.
    let mut t = Transcript::new(b"round trip");
    let mut verifier = Verifier::new(&mut t);
    let var = verifier.commit(commitment);
    let (l, r, o) = verifier.allocate_multiplier(None).unwrap();
    verifier.constrain(LinearCombination::from(l) - var);
    verifier.constrain(LinearCombination::from(r) - var);
    verifier.constrain(LinearCombination::from(o) - Scalar::from(49u64));

    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .expect("proof must verify");
}

// Symmetric: verifier does noisy rolled-back work and still accepts a proof
// built by a clean prover.
#[test]
fn proof_round_trip_with_verifier_side_rollback() {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(32, 1);

    let (proof, commitment) = {
        let mut t = Transcript::new(b"round trip 2");
        let mut prover = Prover::new(&pc_gens, &mut t);
        let (commitment, var) = prover.commit(Scalar::from(7u64), Scalar::from(11u64));
        let (l, r, o) = prover
            .allocate_multiplier(Some((Scalar::from(7u64), Scalar::from(7u64))))
            .unwrap();
        prover.constrain(LinearCombination::from(l) - var);
        prover.constrain(LinearCombination::from(r) - var);
        prover.constrain(LinearCombination::from(o) - Scalar::from(49u64));
        (prover.prove(&bp_gens).unwrap(), commitment)
    };

    let mut t = Transcript::new(b"round trip 2");
    let mut verifier = Verifier::new(&mut t);
    let var = verifier.commit(commitment);

    let _: Result<(), R1CSError> = verifier.try_block(|cs| {
        cs.allocate_multiplier(None)?;
        cs.constrain(LinearCombination::from(Variable::One()) * Scalar::from(99u64));
        Err(R1CSError::MissingAssignment)
    });

    let (l, r, o) = verifier.allocate_multiplier(None).unwrap();
    verifier.constrain(LinearCombination::from(l) - var);
    verifier.constrain(LinearCombination::from(r) - var);
    verifier.constrain(LinearCombination::from(o) - Scalar::from(49u64));

    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .expect("proof must verify");
}

// Touching the transcript inside a rolled-back scope must not leak into the
// final proof — exercises the transcript clone/restore path.
#[test]
fn rolled_back_transcript_mutation_does_not_leak() {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(32, 1);

    let (proof, commitment) = {
        let mut t = Transcript::new(b"transcript");
        let mut prover = Prover::new(&pc_gens, &mut t);
        let (commitment, var) = prover.commit(Scalar::from(7u64), Scalar::from(11u64));

        let _: Result<(), R1CSError> = prover.try_block(|cs| {
            // Append junk to the transcript inside the rolled-back scope.
            // The rollback path must restore the pre-call transcript clone.
            cs.transcript().append_message(b"junk", b"will be reverted");
            Err(R1CSError::MissingAssignment)
        });

        let (l, r, o) = prover
            .allocate_multiplier(Some((Scalar::from(7u64), Scalar::from(7u64))))
            .unwrap();
        prover.constrain(LinearCombination::from(l) - var);
        prover.constrain(LinearCombination::from(r) - var);
        prover.constrain(LinearCombination::from(o) - Scalar::from(49u64));

        (prover.prove(&bp_gens).unwrap(), commitment)
    };

    // Verifier never sees the junk; proof must still verify.
    let mut t = Transcript::new(b"transcript");
    let mut verifier = Verifier::new(&mut t);
    let var = verifier.commit(commitment);
    let (l, r, o) = verifier.allocate_multiplier(None).unwrap();
    verifier.constrain(LinearCombination::from(l) - var);
    verifier.constrain(LinearCombination::from(r) - var);
    verifier.constrain(LinearCombination::from(o) - Scalar::from(49u64));

    verifier
        .verify(&proof, &pc_gens, &bp_gens)
        .expect("proof must verify after transcript mutation was rolled back");
}
