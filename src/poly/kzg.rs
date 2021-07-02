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
        let mut witnesses = Vec::with_capacity(inputs.len());
        for input in inputs {
            let mut u_x = Self::empty_polynomial();
            let mut lc = <E::Fr as Field>::one();
            for poly in input.polynomials {
                let poly = &poly - eval_polynomial(poly.as_ref(), input.z);
                u_x = (poly * lc) + &u_x;
                lc *= input.challenge;
            }
            let values = kate_division(&u_x.values, input.z);
            let witness_poly = Polynomial {
                values,
                _marker: PhantomData,
            };
            witnesses.push(self.commit(&witness_poly));
        }
        witnesses
    }

    fn empty_polynomial() -> Polynomial<E::Fr, LagrangeCoeff> {
        let zero = Polynomial {
            values: vec![E::Fr::zero()],
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
        let e = self.verifier_key.g1 * -evaluation;
        let wz = witness * z;

        let s_g2_prepared = E::G2Prepared::from(self.verifier_key.s_g2);
        let n_g2_prepared = E::G2Prepared::from(-self.verifier_key.g2);

        let term_1 = (&witness, &s_g2_prepared);
        let term_2 = (&(wz + e + commitment).into(), &n_g2_prepared);
        E::multi_miller_loop(&[term_1, term_2])
            .final_exponentiation()
            .is_identity()
    }
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
        let e = g1 * -e_multi_eval_combination.result();
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

    let prover = MultiProver {
        base_prover: prover,
    };

    let p00_x = rand_poly(size, &mut rng);
    let p01_x = rand_poly(size, &mut rng);
    let p10_x = rand_poly(size, &mut rng);
    let p11_x = rand_poly(size, &mut rng);
    let z0 = Fr::random(&mut rng);
    let z1 = Fr::random(&mut rng);
    let u0 = Fr::random(&mut rng);
    let u1 = Fr::random(&mut rng);

    let mut inputs: Vec<MultiProverInput<Bn256>> = Vec::with_capacity(2);

    inputs.push(MultiProverInput {
        challenge: u0,
        z: z0,
        polynomials: vec![p00_x.clone(), p01_x.clone()],
    });

    inputs.push(MultiProverInput {
        challenge: u1,
        z: z1,
        polynomials: vec![p10_x.clone(), p11_x.clone()],
    });

    let p00_comm = prover.commit(&p00_x);
    let p01_comm = prover.commit(&p01_x);
    let p10_comm = prover.commit(&p10_x);
    let p11_comm = prover.commit(&p11_x);
    let e00 = eval_polynomial(&p00_x, z0);
    let e01 = eval_polynomial(&p01_x, z0);
    let e10 = eval_polynomial(&p10_x, z1);
    let e11 = eval_polynomial(&p11_x, z1);

    let witnesses = prover.witness_multi(inputs);

    let multi_verifier = MultiVerifier {
        base_verifier: verifier,
    };

    let mut inputs: Vec<MultiVerifierInput<Bn256>> = Vec::with_capacity(2);

    inputs.push(MultiVerifierInput {
        challenge: u0,
        z: z0,
        evaluations: vec![e00, e01],
        commitments: vec![p00_comm, p01_comm],
        witness: witnesses[0],
    });

    inputs.push(MultiVerifierInput {
        challenge: u1,
        z: z1,
        evaluations: vec![e10, e11],
        commitments: vec![p10_comm, p11_comm],
        witness: witnesses[1],
    });

    let multi_point_eval_challenge = Fr::random(&mut rng);

    assert!(bool::from(
        multi_verifier.verify_multi(inputs, multi_point_eval_challenge)
    ));

    let mut inputs: Vec<MultiVerifierInput<Bn256>> = Vec::with_capacity(2);

    inputs.push(MultiVerifierInput {
        challenge: u1,
        z: z0,
        evaluations: vec![e00, e01],
        commitments: vec![p00_comm, p01_comm],
        witness: witnesses[0],
    });

    inputs.push(MultiVerifierInput {
        challenge: u1,
        z: z1,
        evaluations: vec![e10, e11],
        commitments: vec![p10_comm, p11_comm],
        witness: witnesses[1],
    });

    assert!(!bool::from(
        multi_verifier.verify_multi(inputs, multi_point_eval_challenge)
    ));
}
