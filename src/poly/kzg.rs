use super::{LagrangeCoeff, Polynomial};
use crate::arithmetic::{
    best_multiexp, eval_polynomial, kate_division, Engine, Field, LinearCombinationEngine,
    MultiMillerLoop,
};

use group::prime::PrimeCurveAffine;
use group::Group;
use pairing::arithmetic::MillerLoopResult;
use rand::RngCore;
use std::marker::PhantomData;
use subtle::Choice;

pub struct PolyCommitSetup<E>
where
    E: Engine,
{
    prover_key: ProverKey<E>,
    verifier_key: VerifierKey<E>,
}

pub struct ProverKey<E: Engine> {
    bases: Vec<E::G1Affine>,
}

pub struct VerifierKey<E: Engine> {
    g1: E::G1Affine,
    g2: E::G2Affine,
    s_g2: E::G2Affine,
}

pub struct MultiProverInput<E: Engine> {
    challenge: E::Fr,
    z: E::Fr,
    polynomials: Vec<Polynomial<E::Fr, LagrangeCoeff>>,
}

pub struct MultiVerifierInput<E: Engine> {
    challenge: E::Fr,
    z: E::Fr,
    evaluations: Vec<E::Fr>,
    commitments: Vec<E::G1Affine>,
    witness: E::G1Affine,
}

pub struct BaseProver<E: Engine> {
    prover_key: ProverKey<E>,
}

pub struct MultiProver<E: Engine> {
    base_prover: BaseProver<E>,
}

pub struct BaseVerifier<E: MultiMillerLoop> {
    verifier_key: VerifierKey<E>,
}

pub struct MultiVerifier<E: MultiMillerLoop> {
    base_verifier: BaseVerifier<E>,
}

impl<E> PolyCommitSetup<E>
where
    E: Engine,
{
    pub fn new(n: usize, mut rng: impl RngCore) -> PolyCommitSetup<E> {
        let s = E::Fr::random(&mut rng);
        let mut bases: Vec<E::G1Affine> = Vec::with_capacity(n);
        let g1 = <E::G1Affine as PrimeCurveAffine>::generator();
        bases.push(g1);
        for i in 1..n {
            bases.push((bases[i - 1] * s).into());
        }

        let prover_key = ProverKey::<E> { bases };
        let g2 = <E::G2Affine as PrimeCurveAffine>::generator();
        let verifier_key = VerifierKey::<E> {
            g1,
            g2,
            s_g2: (g2 * s).into(),
        };
        PolyCommitSetup {
            prover_key,
            verifier_key,
        }
    }
}

impl<E> BaseProver<E>
where
    E: Engine,
{
    pub fn commit(&self, poly: &Polynomial<E::Fr, LagrangeCoeff>) -> E::G1Affine {
        let mut scalars = Vec::with_capacity(poly.len() + 1);
        scalars.extend(poly.iter());
        let bases = &self.prover_key.bases;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size]).into()
    }

    pub fn witness(&self, poly: &Polynomial<E::Fr, LagrangeCoeff>, z: E::Fr) -> E::G1Affine {
        // TODO: should return eval too?
        let eval = eval_polynomial(poly, z);
        let poly = poly - eval;
        let values = kate_division(&poly.values, z);
        let witness_poly = Polynomial {
            values,
            _marker: PhantomData,
        };
        self.commit(&witness_poly)
    }
}

impl<E> MultiProver<E>
where
    E: Engine,
{
    pub fn commit(&self, poly: &Polynomial<E::Fr, LagrangeCoeff>) -> E::G1Affine {
        self.base_prover.commit(poly)
    }

    pub fn witness(&self, poly: &Polynomial<E::Fr, LagrangeCoeff>, z: E::Fr) -> E::G1Affine {
        self.base_prover.witness(poly, z)
    }

    pub fn witness_multi(&self, inputs: Vec<MultiProverInput<E>>) -> Vec<E::G1Affine> {
        inputs
            .iter()
            .map(|input| {
                let zero = Self::empty_polynomial();
                let mut lc = <E::Fr as Field>::one();
                let poly: Polynomial<E::Fr, LagrangeCoeff> = input
                    .polynomials
                    .iter()
                    .map(|poly| {
                        let poly = poly - eval_polynomial(poly.as_ref(), input.z);
                        poly
                    })
                    .fold(zero, |mut acc, poly| {
                        acc = acc + &(poly * lc);
                        lc *= input.challenge;
                        acc
                    });
                let values = kate_division(&poly.values, input.z);
                let witness_poly = Polynomial {
                    values,
                    _marker: PhantomData,
                };
                self.commit(&witness_poly)
            })
            .collect()
    }

    fn empty_polynomial() -> Polynomial<E::Fr, LagrangeCoeff> {
        let zero = Polynomial {
            values: vec![],
            _marker: PhantomData,
        };
        zero
    }
}

impl<E> BaseVerifier<E>
where
    E: MultiMillerLoop,
{
    pub fn verify(
        &self,
        witness: E::G1Affine,
        commitment: E::G1Affine,
        evaluation: E::Fr,
        z: E::Fr,
    ) -> Choice {
        let e = <E::G1Affine as PrimeCurveAffine>::generator() * -evaluation;
        let wz = witness * z;

        let s_g2_prepared = E::G2Prepared::from(self.verifier_key.s_g2);
        let n_g2_prepared = E::G2Prepared::from(-self.verifier_key.g2);

        let term_1 = (&witness, &s_g2_prepared);
        let term_2 = (&(wz + e + commitment).into(), &n_g2_prepared);
        E::multi_miller_loop(&[term_1, term_2])
            .final_exponentiation()
            .is_identity()
    }

    fn check() {}
}

impl<E> MultiVerifier<E>
where
    E: MultiMillerLoop,
{
    pub fn verify_multi(
        &self,
        inputs: Vec<MultiVerifierInput<E>>,
        multi_point_eval_challenge: E::Fr,
    ) -> Choice {
        let mut f_multi_point_combination = E::PointCombination::new(multi_point_eval_challenge);
        let mut w_multi_point_combination = E::PointCombination::new(multi_point_eval_challenge);
        let mut wz_multi_point_combination = E::PointCombination::new(multi_point_eval_challenge);
        let mut e_multi_eval_combination = E::ScalarCombination::new(multi_point_eval_challenge);

        for input in inputs {
            let f = E::PointCombination::combine(
                input.challenge,
                input.commitments.iter().map(|c| c.to_curve()).collect(),
            );
            let e = E::ScalarCombination::combine(input.challenge, input.evaluations);
            f_multi_point_combination.add(f);
            e_multi_eval_combination.add(e);
            w_multi_point_combination.add(input.witness.to_curve());
            wz_multi_point_combination.add_with_aux(input.witness.to_curve(), input.z);
        }
        let f = f_multi_point_combination.result();
        let g1 = self.base_verifier.verifier_key.g1;
        let e = g1 * e_multi_eval_combination.result();
        let w = w_multi_point_combination.result();
        let wz = wz_multi_point_combination.result();

        let s_g2_prepared = E::G2Prepared::from(self.base_verifier.verifier_key.s_g2);
        let n_g2_prepared = E::G2Prepared::from(-self.base_verifier.verifier_key.g2);

        let term_1 = (&w.into(), &s_g2_prepared);
        let term_2 = (&(wz + e + f).into(), &n_g2_prepared);
        E::multi_miller_loop(&[term_1, term_2])
            .final_exponentiation()
            .is_identity()
    }
}

#[test]
fn test_kzg() {
    use pairing::bn256::Bn256;
    use pairing::bn256::Fr;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    fn rand_poly(n: usize, mut rng: impl RngCore) -> Polynomial<Fr, LagrangeCoeff> {
        let poly = Polynomial {
            values: (0..n).into_iter().map(|_| Fr::random(&mut rng)).collect(),
            _marker: PhantomData,
        };
        poly
    }

    let size = 8;
    let setup = PolyCommitSetup::<Bn256>::new(size, &mut rng);
    let prover = BaseProver {
        prover_key: setup.prover_key,
    };

    let p_x = rand_poly(size, &mut rng);
    let p_comm = prover.commit(&p_x);
    let z = Fr::random(&mut rng);
    let e = eval_polynomial(&p_x, z);
    let witness = prover.witness(&p_x, z);

    let verifier = BaseVerifier {
        verifier_key: setup.verifier_key,
    };

    assert!(bool::from(verifier.verify(witness, p_comm, e, z)));
    assert!(!bool::from(verifier.verify(
        witness,
        p_comm,
        e,
        z + Fr::one()
    )));
}
