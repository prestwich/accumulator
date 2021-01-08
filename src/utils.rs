use ethers_core::types::U256;

pub(crate) fn highest_divisor_power_of_2(n: U256) -> U256 {
    n & (!(n - 1))
}

pub(crate) fn pred(n: U256) -> U256 {
    n - highest_divisor_power_of_2(n)
}
