use super::commitment::Params;
use crate::arithmetic::{best_multiexp, parallelize};
use ff::Field;
use group::Group;
use pairing::arithmetic::Engine;

/// A multiscalar multiplication in the polynomial commitment scheme
#[derive(Debug, Clone)]
pub struct MSM<'a, E: Engine> {
    pub(crate) params: &'a Params<E>,
    pub g_scalars: Option<Vec<E::Fr>>,
    pub other_scalars: Vec<E::Fr>,
    pub other_bases: Vec<E::G1Affine>,
}

impl<'a, E: Engine> MSM<'a, E> {
    /// Create a new, empty MSM using the provided parameters.
    pub fn new(params: &'a Params<E>) -> Self {
        let g_scalars = None;
        let other_scalars = vec![];
        let other_bases = vec![];

        MSM {
            params,
            g_scalars,
            other_scalars,
            other_bases,
        }
    }

    /// Add another multiexp into this one
    pub fn add_msm(&mut self, other: &Self) {
        self.other_scalars.extend(other.other_scalars.iter());
        self.other_bases.extend(other.other_bases.iter());

        if let Some(g_scalars) = &other.g_scalars {
            self.add_to_g_scalars(g_scalars);
        }
    }

    /// Add arbitrary term (the scalar and the point)
    pub fn append_term(&mut self, scalar: E::Fr, point: E::G1Affine) {
        self.other_scalars.push(scalar);
        self.other_bases.push(point);
    }

    /// Add a value to the first entry of `g_scalars`.
    pub fn add_constant_term(&mut self, constant: E::Fr) {
        if let Some(g_scalars) = self.g_scalars.as_mut() {
            g_scalars[0] += &constant;
        } else {
            let mut g_scalars = vec![E::Fr::zero(); self.params.n as usize];
            g_scalars[0] += &constant;
            self.g_scalars = Some(g_scalars);
        }
    }

    /// Add a vector of scalars to `g_scalars`. This function will panic if the
    /// caller provides a slice of scalars that is not of length `params.n`.
    pub fn add_to_g_scalars(&mut self, scalars: &[E::Fr]) {
        assert_eq!(scalars.len(), self.params.n as usize);
        if let Some(g_scalars) = &mut self.g_scalars {
            parallelize(g_scalars, |g_scalars, start| {
                for (g_scalar, scalar) in g_scalars.iter_mut().zip(scalars[start..].iter()) {
                    *g_scalar += scalar;
                }
            })
        } else {
            self.g_scalars = Some(scalars.to_vec());
        }
    }

    /// Scale all scalars in the MSM by some scaling factor
    pub fn scale(&mut self, factor: E::Fr) {
        if let Some(g_scalars) = &mut self.g_scalars {
            parallelize(g_scalars, |g_scalars, _| {
                for g_scalar in g_scalars {
                    *g_scalar *= &factor;
                }
            })
        }

        if !self.other_scalars.is_empty() {
            parallelize(&mut self.other_scalars, |other_scalars, _| {
                for other_scalar in other_scalars {
                    *other_scalar *= &factor;
                }
            })
        }
    }

    /// Perform multiexp and check that it results in zero
    pub fn eval(self) -> E::G1 {
        let len = self.g_scalars.as_ref().map(|v| v.len()).unwrap_or(0) + self.other_scalars.len();
        let mut scalars: Vec<E::Fr> = Vec::with_capacity(len);
        let mut bases: Vec<E::G1Affine> = Vec::with_capacity(len);

        scalars.extend(&self.other_scalars);
        bases.extend(&self.other_bases);

        if let Some(g_scalars) = &self.g_scalars {
            scalars.extend(g_scalars);
            bases.extend(self.params.g.iter());
        }

        assert_eq!(scalars.len(), len);

        best_multiexp(&scalars, &bases)
    }

    pub fn check(self) -> bool {
        bool::from(self.eval().is_identity())
    }
}
