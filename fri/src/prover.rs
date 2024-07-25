use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::Mmcs;
use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_matrix::dense::RowMajorMatrix;
use p3_util::{log2_strict_usize, reverse_slice_index_bits, split_bits, SliceExt, VecExt};
use tracing::{info_span, instrument};

use crate::fold_even_odd::fold_even_odd;
use crate::{CommitPhaseProofStep, FriConfig, FriProof, QueryProof};

#[instrument(name = "FRI prover", skip_all)]
pub fn prove<F, EF, M, Challenger>(
    config: &FriConfig<M>,
    input: Vec<Vec<EF>>,
    challenger: &mut Challenger,
) -> (FriProof<EF, M, Challenger::Witness>, Vec<usize>)
where
    F: Field,
    EF: TwoAdicField + ExtensionField<F>,
    M: Mmcs<EF>,
    Challenger: GrindingChallenger + CanObserve<M::Commitment> + FieldChallenger<F>,
{
    // let log_max_height = input.iter().rposition(Option::is_some).unwrap();

    let commit_phase_result = commit_phase(config, input.clone(), challenger);

    let pow_witness = challenger.grind(config.proof_of_work_bits);

    let query_indices: Vec<usize> = (0..config.num_queries)
        .map(|_| challenger.sample_bits(input.last().unwrap().log_strict_len()))
        .collect();

    let query_proofs = info_span!("query phase").in_scope(|| {
        query_indices
            .iter()
            .map(|&index| answer_query(config, &commit_phase_result.data, index))
            .collect()
    });

    (
        FriProof {
            commit_phase_commits: commit_phase_result.commits,
            query_proofs,
            final_polys: commit_phase_result.final_polys,
            pow_witness,
        },
        query_indices,
    )
}

fn answer_query<F, M>(
    config: &FriConfig<M>,
    commit_phase_commits: &[M::ProverData<RowMajorMatrix<F>>],
    index: usize,
) -> QueryProof<F, M>
where
    F: Field,
    M: Mmcs<F>,
{
    let commit_phase_openings = commit_phase_commits
        .iter()
        .map(|commit| {
            let (folded_index, index_in_subgroup) = split_bits(index, config.log_folding_arity);
            let (mut siblings, proof) = config.mmcs.open_batch(folded_index, commit);
            for sibs in &mut siblings {
                let bits_reduced = config.log_folding_arity - log2_strict_usize(sibs.len());
                sibs.remove(index_in_subgroup >> bits_reduced);
            }
            CommitPhaseProofStep {
                siblings,
                opening_proof: proof,
            }
        })
        .collect();

    QueryProof {
        commit_phase_openings,
    }
}

#[instrument(name = "commit phase", skip_all)]
fn commit_phase<F, EF, M, Challenger>(
    config: &FriConfig<M>,
    mut inputs: Vec<Vec<EF>>,
    challenger: &mut Challenger,
) -> CommitPhaseResult<EF, M>
where
    F: Field,
    EF: TwoAdicField + ExtensionField<F>,
    M: Mmcs<EF>,
    Challenger: CanObserve<M::Commitment> + FieldChallenger<F>,
{
    // let mut current = input[log_max_height].as_ref().unwrap().clone();
    let mut commits = vec![];
    let mut data = vec![];

    while let Some(log_height) = inputs
        .last()
        .map(|v| v.log_strict_len())
        .filter(|&l| l > config.log_blowup + config.log_max_final_poly_len)
    {
        let log_folded_height = log_height - config.log_folding_arity;
        let to_fold = inputs
            .extract(|v| v.log_strict_len() > log_folded_height)
            .collect_vec();
        let leaves = to_fold
            .iter()
            .map(|v| RowMajorMatrix::new(v.clone(), 1 << (v.log_strict_len() - log_folded_height)))
            .collect::<Vec<_>>();
        let (commit, prover_data) = config.mmcs.commit(leaves);
        challenger.observe(commit.clone());
        commits.push(commit);
        data.push(prover_data);

        let mut beta: EF = challenger.sample_ext_element();

        inputs.push(
            to_fold
                .into_iter()
                .map(|mut v| {
                    let mut local_beta = beta;
                    for _ in 0..(v.log_strict_len() - log_folded_height) {
                        v = fold_even_odd(v, local_beta);
                        local_beta = local_beta.square();
                    }
                    v
                })
                .reduce(|mut acc, v| {
                    acc.iter_mut().zip_eq(v).for_each(|(a, b)| *a += b);
                    acc
                })
                .unwrap(),
        );
    }

    /*
    let mut current = input[log_max_height].as_ref().unwrap().clone();
    for log_top_height in (config.log_blowup + config.log_max_final_poly_len..=log_max_height)
        .rev()
        .step_by(config.log_folding_arity)
    {
        let to_fold = (0..config.log_folding_arity)
            .filter_map(|i| match input[log_top_height - i].as_ref() {
                Some(v) => Some((i, v.clone())),
                None => None,
            })
            .collect::<Vec<_>>();
        let leaves = to_fold
            .iter()
            .map(|(i, v)| RowMajorMatrix::new(v.clone(), 1 << (config.log_folding_arity - i)))
            .collect::<Vec<_>>();
        let (commit, prover_data) = config.mmcs.commit(leaves);
        challenger.observe(commit.clone());
        commits.push(commit);
        data.push(prover_data);

        let mut beta: EF = challenger.sample_ext_element();

        (1..config.log_folding_arity + 1).for_each(|j| {
            current = fold_even_odd(current.clone(), beta);
            beta = beta.square();
            if let Some(v) = &input[log_top_height - j] {
                current.iter_mut().zip_eq(v).for_each(|(c, v)| *c += *v);
            }
        });
    }

    reverse_slice_index_bits(&mut current);
    current = Radix2Dit::default().idft(current);
    debug_assert!(current
        .drain(current.len() << config.log_blowup..)
        .all(|x| x.is_zero()));
    // Now all the polynomials in `input` that are at log_height below `config.log_blowup`+`config.log_max_final_poly_len` are sent in the clear.
    let mut final_polys = vec![current];
    (0..=config.log_max_final_poly_len + config.log_blowup).for_each(|i| match input[i].as_ref() {
        Some(v) => {
            let mut new_vec = v.clone();
            reverse_slice_index_bits(&mut new_vec);
            debug_assert!(new_vec
                .drain(new_vec.len() << config.log_blowup..)
                .all(|x| x.is_zero()));
            final_polys.push(Radix2Dit::default().idft(new_vec));
        }
        None => {}
    });
    */

    let final_polys = inputs
        .iter()
        .map(|v| {
            let mut v = v.clone();
            reverse_slice_index_bits(&mut v);
            v = Radix2Dit::default().idft(v);
            debug_assert!(v.drain(v.len() << config.log_blowup..).all(|x| x.is_zero()));
            v
        })
        .collect_vec();
    for fp in &final_polys {
        for coeff in fp {
            challenger.observe_ext_element(*coeff);
        }
    }

    CommitPhaseResult {
        commits,
        data,
        final_polys,
    }
}

struct CommitPhaseResult<F: Field, M: Mmcs<F>> {
    commits: Vec<M::Commitment>,
    data: Vec<M::ProverData<RowMajorMatrix<F>>>,
    final_polys: Vec<Vec<F>>,
}
