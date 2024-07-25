use alloc::vec::Vec;

use p3_commit::Mmcs;
use p3_field::Field;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(
    serialize = "Witness: Serialize",
    deserialize = "Witness: Deserialize<'de>"
))]
pub struct FriProof<F: Field, M: Mmcs<F>, Witness> {
    pub commit_phase_commits: Vec<M::Commitment>,
    pub query_proofs: Vec<QueryProof<F, M>>,
    // This could become Vec<FC::Challenge> if this library was generalized to support non-constant
    // final polynomials.
    pub final_polys: Vec<Vec<F>>,
    pub pow_witness: Witness,
    // pub log_max_height: usize,
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound = "")]
pub struct QueryProof<F: Field, M: Mmcs<F>> {
    /// For each commit phase commitment, this contains openings of a commit phase codeword at the
    /// queried location, along with an opening proof.
    pub commit_phase_openings: Vec<CommitPhaseProofStep<F, M>>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
// #[serde(bound(serialize = "F: Serialize"))]
#[serde(bound = "")]
pub struct CommitPhaseProofStep<F: Field, M: Mmcs<F>> {
    /// The opening of the commit phase codeword at the sibling location.
    // This may change to Vec<FC::Challenge> if the library is generalized to support other FRI
    // folding arities besides 2, meaning that there can be multiple siblings.
    pub siblings: Vec<Vec<F>>,

    pub opening_proof: M::Proof,
}
