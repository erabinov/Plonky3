use alloc::vec;
use alloc::vec::Vec;

use itertools::izip;
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::Mmcs;
use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_matrix::Dimensions;
use p3_util::reverse_bits_len;

use crate::{FriConfig, FriProof, QueryProof};

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
    let betas: Vec<EF> = proof
        .commit_phase_commits
        .iter()
        .map(|comm| {
            challenger.observe(comm.clone());
            challenger.sample_ext_element()
        })
        .collect();
    proof
        .final_poly
        .iter()
        .for_each(|x| challenger.observe_ext_element(*x));
    if proof.query_proofs.len() != config.num_queries {
        return Err(FriError::InvalidProofShape);
    }

    // Check PoW.
    if !challenger.check_witness(config.proof_of_work_bits, proof.pow_witness) {
        return Err(FriError::InvalidPowWitness);
    }

    let log_max_height =
        proof.commit_phase_commits.len() + config.log_blowup + config.log_final_poly_len;

    let query_indices: Vec<usize> = (0..config.num_queries)
        .map(|_| challenger.sample_bits(log_max_height))
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
    let log_max_height =
        proof.commit_phase_commits.len() + config.log_blowup + config.log_final_poly_len;
    for (&index, query_proof, ro) in izip!(
        &challenges.query_indices,
        &proof.query_proofs,
        reduced_openings
    ) {
        let folded_eval = verify_query(
            config,
            &proof.commit_phase_commits,
            index,
            query_proof,
            &challenges.betas,
            ro,
            log_max_height,
        )?;

        let final_poly_index = index >> (proof.commit_phase_commits.len());

        let mut eval = F::zero();
        let x = F::two_adic_generator(log_max_height)
            .exp_u64(reverse_bits_len(final_poly_index, log_max_height) as u64);
        let mut x_pow = F::one();

        for coeff in &proof.final_poly {
            eval += *coeff * x_pow;
            x_pow *= x;
        }

        if eval != folded_eval {
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
    reduced_openings: &[F; 32],
    log_max_height: usize,
) -> Result<F, FriError<M::Error>>
where
    F: TwoAdicField,
    M: Mmcs<F>,
{
    let mut folded_eval = F::zero();
    let mut x = F::two_adic_generator(log_max_height)
        .exp_u64(reverse_bits_len(index, log_max_height) as u64);

    for (log_folded_height, commit, step, &beta) in izip!(
        (0..log_max_height).rev(),
        commit_phase_commits,
        &proof.commit_phase_openings,
        betas,
    ) {
        folded_eval += reduced_openings[log_folded_height + 1];

        let index_sibling = index ^ 1;
        let index_pair = index >> 1;

        let mut evals = vec![folded_eval; 2];
        evals[index_sibling % 2] = step.sibling_value;

        let dims = &[Dimensions {
            width: 2,
            height: 1 << log_folded_height,
        }];
        config
            .mmcs
            .verify_batch(
                commit,
                dims,
                index_pair,
                &[evals.clone()],
                &step.opening_proof,
            )
            .map_err(FriError::CommitPhaseMmcsError)?;

        let mut xs = [x; 2];
        xs[index_sibling % 2] *= F::two_adic_generator(1);
        // interpolate and evaluate at beta
        folded_eval = evals[0] + (beta - xs[0]) * (evals[1] - evals[0]) / (xs[1] - xs[0]);

        index = index_pair;
        x = x.square();
    }

    // debug_assert!(
    //     index < config.blowup() + config.final_poly_len(),
    //     "index was {}",
    //     index
    // );
    // debug_assert_eq!(
    //     x.exp_power_of_2(config.log_blowup + config.log_final_poly_len),
    //     F::one()
    // );

    Ok(folded_eval)
}
