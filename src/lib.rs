mod simple;
mod utils;

use digest::{generic_array::typenum::consts::U32 as TU32, Digest, Output};
use ethers_core::types::U256;
use std::collections::BTreeMap;

pub type Element<D> = Output<<D as Accumulator>::Digest>;

#[derive(Copy, Clone, Debug)]
pub enum ProverError {
    MissingHistory(U256),
    OutOfBounds,
    WitnessTooShort,
    RiMismatch,
    XiMismatch,
}

pub trait Accumulator: Default + Clone {
    type Digest: Digest<OutputSize = TU32>;

    fn get_digest() -> Self::Digest {
        Self::Digest::new()
    }

    fn from_elements(elements: impl Iterator<Item = Element<Self>>) -> Self
    where
        Self: Sized,
    {
        let mut acc = Self::default();
        elements.for_each(|e| {
            acc.insert(&e);
        });
        acc
    }

    #[doc(hidden)]
    fn state_mut(&mut self) -> &mut BTreeMap<usize, Element<Self>>;

    #[doc(hidden)]
    fn state(&self) -> &BTreeMap<usize, Element<Self>>;

    /// Get the
    fn get_state(&self, i: impl Into<U256>) -> Option<Element<Self>> {
        let i: U256 = i.into();
        if i.is_zero() {
            Some(Default::default())
        } else {
            self.state().get(&(i.trailing_zeros() as usize)).copied()
        }
    }

    fn set_state(&mut self, i: impl Into<U256>, element: &Element<Self>) {
        self.state_mut().insert(i.into().trailing_zeros() as usize, *element);
    }

    fn state_len(&self) -> usize {
        self.state().len()
    }

    /// Returns the number of elements that have been inserted into the
    /// accumulator
    fn len(&self) -> U256;

    fn is_empty(&self) -> bool {
        self.len().is_zero()
    }

    /// Returns the latest state root, or the 0 element if empty
    fn get_root(&self) -> Element<Self> {
        self.get_state(self.len()).unwrap_or_else(Default::default)
    }

    fn insert(&mut self, element: &Element<Self>) -> Element<Self>;

    fn insert_iter(&mut self, elements: impl Iterator<Item = Element<Self>>) -> Element<Self> {
        let mut result = Default::default();
        for e in elements {
            result = self.insert(&e);
        }
        result
    }

    fn insert_data(&mut self, data: impl AsRef<[u8]>) -> Element<Self> {
        self.insert(&Self::Digest::digest(data.as_ref()))
    }
}

pub trait Prover: Accumulator {
    fn elements(&self) -> &BTreeMap<U256, Element<Self>>;

    fn get_element(&self, i: &U256) -> Option<&Element<Self>> {
        self.elements().get(&i)
    }

    fn r(&self) -> &BTreeMap<U256, Element<Self>>;

    fn get_r(&self, i: &U256) -> Option<&Element<Self>> {
        self.r().get(&i)
    }

    fn prove_from(
        &self,
        i: impl Into<U256>,
        j: impl Into<U256>,
    ) -> Result<Vec<Element<Self>>, ProverError>;

    fn prove(&self, j: impl Into<U256>) -> Result<Vec<Element<Self>>, ProverError> {
        self.prove_from(self.state_len(), j)
    }

    fn verify(
        r_i: &Element<Self>,
        i: U256,
        j: U256,
        witness: &[Element<Self>],
        element: &Element<Self>,
    ) -> Result<(), ProverError>;
}
