use digest::{generic_array::typenum::consts::U32 as TU32, Digest, Output};
use ethers_core::types::U256;
use std::collections::BTreeMap;

use crate::*;

#[derive(Default, Clone, Debug)]
pub struct SimpleAccumulator<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    k: U256,
    s: BTreeMap<usize, Output<D>>,
}


impl<D> std::iter::FromIterator<Output<D>> for SimpleAccumulator<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Element<Self>>,
    {
        let mut acc = Self::default();
        for e in iter {
            acc.insert(&e);
        }
        acc
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

    fn state(&self) -> &BTreeMap<usize, Element<Self>> {
        &self.s
    }

    fn state_mut(&mut self) -> &mut BTreeMap<usize, Element<Self>> {
        &mut self.s
    }

    fn insert(&mut self, element: &Element<Self>) -> Element<Self> {
        self.k = self.k + 1;
        let prev = self.get_state(self.k - 1).unwrap();
        let pred = self
            .get_state(self.k - utils::highest_divisor_power_of_2(self.k))
            .unwrap();

        let d = Self::get_digest().chain(element).chain(prev).chain(pred);
        let result = d.finalize();

        self.set_state(self.k, &result);
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

impl<D> std::iter::FromIterator<Output<D>> for SimpleProver<D>
where
    D: Digest<OutputSize = TU32> + Clone + Default,
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Element<Self>>,
    {
        let mut acc = Self::default();
        for e in iter {
            acc.insert(&e);
        }
        acc
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

    fn state(&self) -> &BTreeMap<usize, Element<Self>> {
        &self.accumulator.s
    }

    fn state_mut(&mut self) -> &mut BTreeMap<usize, Element<Self>> {
        self.accumulator.state_mut()
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

    fn r(&self) -> &BTreeMap<U256, Element<Self>> {
        &self.r
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

        let elements_i = self.get_element(&i).ok_or(ProverError::MissingHistory(i))?;
        let prev = self
            .get_r(&(i - 1))
            .ok_or_else(|| ProverError::MissingHistory(i - 1))?;
        let pred = self
            .get_r(&pred_i)
            .ok_or(ProverError::MissingHistory(pred_i))?;

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
        let root_4 = prover.get_root();

        prover.insert_data(plain_elements[4]);
        prover.insert_data(plain_elements[5]);

        let witness = prover.prove_from(4, 4).unwrap();
        SimpleProver::<sha2::Sha256>::verify(&root_4, 4.into(), 4.into(), &witness, &elements[3])
            .unwrap();
    }
}
