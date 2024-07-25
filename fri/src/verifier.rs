use alloc::vec;
use alloc::vec::Vec;

use itertools::{izip, Itertools};
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::Mmcs;
use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_matrix::Dimensions;
use p3_util::{log2_strict_usize, reverse_bits_len, split_bits, VecExt};

use crate::{fold_even_odd_at, FriConfig, FriProof, QueryProof};

#[derive(Debug)]
pub enum FriError<CommitMmcsErr> {
    InvalidProofShape,
    CommitPhaseMmcsError(CommitMmcsErr),
    FinalPolyMismatch,
    InvalidPowWitness,
}

#[derive(Debug)]
pub struct FriChallenges<F> {
    pub query_indices: Vec<usize>,
    pub betas: Vec<F>,
}

/// Verifies the shape of the proof and samples the challenges.
pub fn verify_shape_and_sample_challenges<F, EF, M, Challenger>(
    config: &FriConfig<M>,
    proof: &FriProof<EF, M, Challenger::Witness>,
    challenger: &mut Challenger,
) -> Result<FriChallenges<EF>, FriError<M::Error>>
where
    F: Field,
    EF: ExtensionField<F>,
    M: Mmcs<EF>,
    Challenger: GrindingChallenger + CanObserve<M::Commitment> + FieldChallenger<F>,
{
    assert!(config.log_max_final_poly_len >= config.log_folding_arity);
    let betas: Vec<EF> = proof
        .commit_phase_commits
        .iter()
        .map(|comm| {
            challenger.observe(comm.clone());
            challenger.sample_ext_element()
        })
        .collect();

    for fp in &proof.final_polys {
        for coeff in fp {
            challenger.observe_ext_element(*coeff);
        }
    }
    if proof.query_proofs.len() != config.num_queries {
        return Err(FriError::InvalidProofShape);
    }

    // Check PoW.
    if !challenger.check_witness(config.proof_of_work_bits, proof.pow_witness) {
        return Err(FriError::InvalidPowWitness);
    }

    let query_indices: Vec<usize> = (0..config.num_queries)
        .map(|_| challenger.sample_bits(proof.log_max_height))
        .collect();

    Ok(FriChallenges {
        query_indices,
        betas,
    })
}

pub fn verify_challenges<F, M, Witness>(
    config: &FriConfig<M>,
    proof: &FriProof<F, M, Witness>,
    challenges: &FriChallenges<F>,
    reduced_openings: &[[F; 32]],
) -> Result<(), FriError<M::Error>>
where
    F: TwoAdicField,
    M: Mmcs<F>,
{
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup;
    for (&index, query_proof, ro) in izip!(
        &challenges.query_indices,
        &proof.query_proofs,
        reduced_openings
    ) {
        let folded_evals = verify_query(
            config,
            &proof.commit_phase_commits,
            index,
            query_proof,
            &challenges.betas,
            ro,
            log_max_height,
        )?;

        let generator = F::two_adic_generator()

        if folded_eval != proof.final_poly {
            return Err(FriError::FinalPolyMismatch);
        }
    }

    Ok(())
}

fn verify_query<F, M>(
    config: &FriConfig<M>,
    commit_phase_commits: &[M::Commitment],
    mut index: usize,
    proof: &QueryProof<F, M>,
    betas: &[F],
    inputs: Vec<(usize, F)>,
    log_max_height: usize,
) -> Result<Vec<F>, FriError<M::Error>>
where
    F: TwoAdicField,
    M: Mmcs<F>,
{
    // let mut current = input[log_max_height].as_ref().unwrap().clone();
    let mut steps = izip!(
        commit_phase_commits,
        proof.commit_phase_openings.iter(),
        betas
    );
    let folded_eval = F::zero();
    while let Some(log_height) = inputs
        .last()
        .map(|v| v.0)
        .filter(|&l| l > config.log_blowup + config.log_max_final_poly_len)
    {
        let log_folded_height = log_height - config.log_folding_arity;
        let to_fold = inputs.extract(|v| v.0 > log_folded_height).collect_vec();

        let (commit, opening, beta) = steps.next().unwrap();

        let dims = to_fold
            .iter()
            .map(|(l, _)| Dimensions {
                height: 1 << log_folded_height,
                width: 1 << (l - log_folded_height),
            })
            .collect_vec();

        let (folded_index, index_in_subgroup) = split_bits(index, config.log_folding_arity);
        let mut siblings = opening.siblings.clone();
        for ((_, v), sibs) in izip!(to_fold.iter(), &mut siblings) {
            let bits_reduced = config.log_folding_arity - log2_strict_usize(sibs.len());
            sibs.insert(index_in_subgroup >> bits_reduced, *v);
        }
        config
            .mmcs
            .verify_batch(
                commit,
                &dims,
                folded_index,
                &opening.siblings,
                &opening.opening_proof,
            )
            .map_err(FriError::CommitPhaseMmcsError)?;

        let folded_eval = siblings
            .into_iter()
            .map(|sibs| fold_even_odd_at(sibs, folded_index, *beta, log_folded_height))
            .sum();
        inputs.push((log_folded_height, folded_eval));

        index = folded_index;
    }

    Ok(folded_eval)
}
