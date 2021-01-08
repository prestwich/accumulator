mod utils;
use digest::{
    generic_array::{
        typenum::consts::{U256 as TU256, U32 as TU32},
        GenericArray,
    },
    Digest, Output,
};
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

    fn state(&self) -> &[Element<Self>];

    fn get_state(&self, i: impl Into<U256>) -> Option<Element<Self>> {
        let i: U256 = i.into();
        if i.is_zero() {
            Some(Default::default())
        } else {
            self.state().get(i.trailing_zeros() as usize).copied()
        }
    }

    fn len(&self) -> U256;

    fn get_root(&self) -> Option<Element<Self>> {
        self.get_state(self.len())
    }

    fn state_len(&self) -> U256 {
        self.state().len().into()
    }

    fn is_empty(&self) -> bool {
        self.state().is_empty()
    }

    fn insert(&mut self, element: &Element<Self>) -> Element<Self>;

    fn insert_data(&mut self, data: impl AsRef<[u8]>) -> Element<Self> {
        self.insert(&Self::Digest::digest(data.as_ref()))
    }
}

pub trait Prover: Accumulator {
    fn elements(&self) -> &BTreeMap<U256, Element<Self>>;

    fn element(&self, i: U256) -> Option<&Element<Self>> {
        self.elements().get(&i)
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

#[derive(Default, Clone, Debug)]
pub struct SimpleAccumulator<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    k: U256,
    s: GenericArray<Output<D>, TU256>,
}

impl<D> SimpleAccumulator<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    fn set_state_at(&mut self, i: U256, element: Element<Self>) {
        self.s[i.trailing_zeros() as usize] = element;
    }
}

impl<D> Accumulator for SimpleAccumulator<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    type Digest = D;

    fn len(&self) -> U256 {
        self.k
    }

    fn state(&self) -> &[Element<Self>] {
        self.s.as_ref()
    }

    fn insert(&mut self, element: &Element<Self>) -> Element<Self> {
        self.k = self.k + 1;
        let prev = self.get_state(self.k - 1).unwrap();
        let pred = self
            .get_state(self.k - utils::highest_divisor_power_of_2(self.k))
            .unwrap();

        let d = Self::get_digest().chain(element).chain(prev).chain(pred);
        let result = d.finalize();

        self.set_state_at(self.k, result);
        result
    }
}

#[derive(Clone, Debug)]
pub struct SimpleProver<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    accumulator: SimpleAccumulator<D>,
    elements: BTreeMap<U256, Element<SimpleAccumulator<D>>>,
    r: BTreeMap<U256, Element<SimpleAccumulator<D>>>,
}

impl<D> Default for SimpleProver<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    fn default() -> Self {
        let mut p = Self {
            accumulator: Default::default(),
            elements: BTreeMap::new(),
            r: BTreeMap::new(),
        };
        p.elements.insert(U256::zero(), Default::default());
        p.r.insert(U256::zero(), Default::default());
        p
    }
}

impl<D> From<SimpleAccumulator<D>> for SimpleProver<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    fn from(accumulator: SimpleAccumulator<D>) -> Self {
        Self {
            accumulator,
            ..Default::default()
        }
    }
}

impl<D> Accumulator for SimpleProver<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    type Digest = D;

    fn len(&self) -> U256 {
        self.accumulator.len()
    }

    fn state(&self) -> &[Element<Self>] {
        self.accumulator.state()
    }

    fn insert(&mut self, element: &Element<Self>) -> Element<Self> {
        let r = self.accumulator.insert(element);
        self.elements.insert(self.len(), *element);
        self.r.insert(self.len(), r);
        r
    }
}

impl<D> Prover for SimpleProver<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    fn elements(&self) -> &BTreeMap<U256, Element<Self>> {
        &self.elements
    }

    fn prove_from(
        &self,
        i: impl Into<U256>,
        j: impl Into<U256>,
    ) -> Result<Vec<Element<Self>>, ProverError> {
        let (i, j) = (i.into(), j.into());
        if j > i {
            return Err(ProverError::OutOfBounds);
        };

        let pred_i = utils::pred(i);

        let elements_i = self
            .elements
            .get(&i)
            .ok_or_else(|| ProverError::MissingHistory(i))?;
        let prev = self
            .r
            .get(&(i - 1))
            .ok_or_else(|| ProverError::MissingHistory(i - 1))?;
        let pred = self
            .r
            .get(&pred_i)
            .ok_or_else(|| ProverError::MissingHistory(pred_i))?;

        let mut witness = vec![*elements_i, *prev, *pred];
        if i > j {
            if pred_i >= j {
                witness.extend(self.prove_from(pred_i, j)?);
            } else {
                witness.extend(self.prove_from(i - 1, j)?);
            }
        }

        Ok(witness)
    }

    fn verify(
        r_i: &Element<Self>,
        i: U256,
        j: U256,
        witness: &[Element<Self>],
        element: &Element<Self>,
    ) -> Result<(), ProverError> {
        assert!(j <= i);
        if witness.len() < 3 {
            return Err(ProverError::WitnessTooShort);
        }

        let (x_i, r_prev, r_pred) = (&witness[0], &witness[1], &witness[2]);
        let d = Self::get_digest().chain(x_i).chain(r_prev).chain(r_pred);
        let d = d.finalize();
        if d != *r_i {
            return Err(ProverError::RiMismatch);
        }

        if i == j {
            if x_i == element {
                return Ok(());
            } else {
                return Err(ProverError::XiMismatch);
            }
        }
        if utils::pred(i) >= j {
            return Self::verify(r_pred, utils::pred(i), j, &witness[3..], element);
        }
        Self::verify(r_prev, i - 1, j, &witness[3..], element)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2;

    #[test]
    fn it_works() {
        let mut prover = SimpleProver::<sha2::Sha256>::default();
        let plain_elements = ["some", "small", "list", "of", "distinct", "elements"];
        let elements: Vec<_> = plain_elements
            .iter()
            .map(|e| sha2::Sha256::digest(e.as_ref()))
            .collect();

        prover.insert_data(plain_elements[0]);
        prover.insert_data(plain_elements[1]);
        prover.insert_data(plain_elements[2]);
        prover.insert_data(plain_elements[3]);
        let root_4 = prover.get_root().unwrap();

        prover.insert_data(plain_elements[4]);
        prover.insert_data(plain_elements[5]);

        let witness = prover.prove_from(4, 4).unwrap();
        SimpleProver::<sha2::Sha256>::verify(
            &root_4,
            4.into(),
            4.into(),
            &witness,
            &elements[3],
        )
        .unwrap();
    }
}
