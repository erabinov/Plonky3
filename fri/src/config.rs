use alloc::vec::Vec;

#[derive(Debug)]
pub struct FriConfig<M> {
    pub log_blowup: usize,
    pub num_queries: usize,
    pub log_max_final_poly_len: usize,
    pub log_folding_arity: usize,
    pub proof_of_work_bits: usize,
    pub mmcs: M,
}

impl<M> FriConfig<M> {
    pub const fn blowup(&self) -> usize {
        1 << self.log_blowup
    }
}
