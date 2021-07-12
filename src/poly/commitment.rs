use super::{msm::MSM, Coeff, LagrangeCoeff, Polynomial};
use crate::arithmetic::{best_multiexp, CurveAffine};
use ff::Field;
use group::{prime::PrimeCurveAffine, GroupEncoding};
use pairing::arithmetic::Engine;
use rand::RngCore;
use std::io;

// mod msm;
// mod prover;
// mod verifier;

#[derive(Debug)]
pub struct Params<E: Engine> {
    pub k: u32,
    pub n: u64,
    pub g: Vec<E::G1Affine>,
    pub g1: E::G1Affine,
    pub g2: E::G2Affine,
    pub s_g2: E::G2Affine,
}

impl<E> Params<E>
where
    E: Engine,
{
    pub fn setup(k: u32, mut rng: impl RngCore) -> Params<E> {
        assert!(k < 28);
        let n: u64 = 1 << k;

        let s = E::Fr::random(&mut rng);
        let mut bases: Vec<E::G1Affine> = Vec::with_capacity(n as usize);
        let g1 = <E::G1Affine as PrimeCurveAffine>::generator();
        bases.push(g1);
        for i in 1..(n as usize) {
            bases.push((bases[i - 1] * s).into());
        }
        let g2 = <E::G2Affine as PrimeCurveAffine>::generator();
        Params {
            k,
            n,
            g: bases,
            g1,
            g2,
            s_g2: (g2 * s).into(),
        }
    }
}

impl<E: Engine> Params<E> {
    pub fn commit(&self, poly: &Polynomial<E::Fr, Coeff>) -> E::G1Affine {
        let mut scalars = Vec::with_capacity(poly.len() + 1);
        scalars.extend(poly.iter());
        let bases = &self.g;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size]).into()
    }

    pub fn commit_lagrange(&self, poly: &Polynomial<E::Fr, LagrangeCoeff>) -> E::G1Affine {
        let mut scalars = Vec::with_capacity(poly.len() + 1);
        scalars.extend(poly.iter());
        let bases = &self.g;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size]).into()
    }

    /// Generates an empty multiscalar multiplication struct using the
    /// appropriate params.
    pub fn empty_msm(&self) -> MSM<E> {
        MSM::new(self)
    }

    /// Getter for g generators
    pub fn get_g(&self) -> Vec<E::G1Affine> {
        self.g.clone()
    }

    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.k.to_le_bytes())?;
        writer.write_all(&self.n.to_le_bytes())?;
        for g_element in &self.g {
            writer.write_all(g_element.to_bytes().as_ref())?;
        }
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);

        // Interpret n = 0 as this params are for verifier side
        let mut n = [0u8; 8];
        reader.read_exact(&mut n[..])?;
        let n = u64::from_le_bytes(n);
        // TODO: check if n is 1 << n or 0

        let g: Vec<E::G1Affine> = (0..n)
            .map(|_| E::G1Affine::read(reader))
            .collect::<Result<_, _>>()?;

        let g1 = E::G1Affine::read(reader)?;
        let g2 = E::G2Affine::read(reader)?;
        let s_g2 = E::G2Affine::read(reader)?;

        Ok(Params {
            k,
            n,
            g,
            g1,
            g2,
            s_g2,
        })
    }
}
