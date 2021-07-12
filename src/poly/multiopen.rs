//! This module contains an optimisation of the polynomial commitment opening
//! scheme described in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021

use super::*;
use crate::{
    arithmetic::{eval_polynomial, CurveAffine, FieldExt},
    poly::commitment::Params,
    transcript::{ChallengeScalar, Transcript, TranscriptWrite},
};
use std::collections::BTreeMap;

mod prover;
mod verifier;

use pairing::bn256::G1;
pub use prover::create_proof;
pub use verifier::verify_proof;

#[derive(Clone, Copy, Debug)]
struct Z {}
type ChallengeZ<F> = ChallengeScalar<F, Z>;

#[derive(Clone, Copy, Debug)]
struct U {}
type ChallengeU<F> = ChallengeScalar<F, U>;

#[derive(Clone, Copy, Debug)]
struct V {}
type ChallengeV<F> = ChallengeScalar<F, V>;

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct ProverQuery<'a, C: CurveAffine> {
    /// coefficients of polynomial
    pub poly: &'a Polynomial<C::Scalar, Coeff>,
    /// point at which polynomial is queried
    pub point: C::Scalar,
    // evaluation at this
    pub eval: C::Scalar,
}

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct VerifierQuery<'a, C: CurveAffine> {
    /// commitment to polynomial
    pub commitment: &'a C,
    /// point at which polynomial is queried
    pub point: C::Scalar,
    /// evaluation of polynomial at query point
    pub eval: C::Scalar,
}

trait Query<F>: Sized + Copy {
    type Commitment: PartialEq + Copy;
    type Scalar: Clone + Default + Ord + Copy;

    fn get_point(&self) -> Self::Scalar;
    fn get_eval(&self) -> Self::Scalar;
    fn get_commitment(&self) -> Self::Commitment;
}

struct CommitmentData<F, Q: Query<F>> {
    queries: Vec<Q>,
    point: Q::Scalar,
    _marker: PhantomData<F>,
}

fn construct_intermediate_sets<F: FieldExt, I, Q: Query<F>>(queries: I) -> Vec<CommitmentData<F, Q>>
where
    I: IntoIterator<Item = Q> + Clone,
{
    let mut point_query_map: BTreeMap<Q::Scalar, Vec<Q>> = BTreeMap::new();
    for query in queries.clone() {
        if let Some(queries) = point_query_map.get_mut(&query.get_point()) {
            queries.push(query);
        } else {
            point_query_map.insert(query.get_point(), vec![query]);
        }
    }

    point_query_map
        .keys()
        .map(|point| {
            let queries = point_query_map.get(point).unwrap();
            CommitmentData {
                queries: queries.clone(),
                point: point.clone(),
                _marker: PhantomData,
            }
        })
        .collect()
}

#[test]
fn test_multiopen() {
    use crate::transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptRead, TranscriptWrite,
    };
    use pairing::bn256::Bn256;
    use pairing::bn256::Fr;
    use pairing::bn256::G1Affine;
    use rand::RngCore;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[derive(Clone, Copy, Debug)]
    struct Z {}
    /// Challenge for keeping the multi-point quotient polynomial terms linearly independent.
    type ChallengeZ<F> = ChallengeScalar<F, Z>;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    fn rand_poly(n: usize, mut rng: impl RngCore) -> Polynomial<Fr, Coeff> {
        let poly = Polynomial {
            values: (0..n).into_iter().map(|_| Fr::random(&mut rng)).collect(),
            _marker: PhantomData,
        };
        poly
    }

    let k = 3;
    let params = Params::<Bn256>::setup(k, &mut rng);

    // prover

    let p00_x = rand_poly(params.n as usize, &mut rng);
    let p01_x = rand_poly(params.n as usize, &mut rng);
    let p10_x = rand_poly(params.n as usize, &mut rng);
    let p11_x = rand_poly(params.n as usize, &mut rng);

    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    let commitment = params.commit(&p00_x);
    transcript.write_point(commitment).unwrap();

    let z0: ChallengeZ<_> = transcript.squeeze_challenge_scalar();

    let eval = eval_polynomial(&p00_x, *z0);
    transcript.write_scalar(eval).unwrap();

    let q0 = ProverQuery {
        poly: &p00_x,
        point: *z0,
        eval,
    };
    let queries: Vec<ProverQuery<G1Affine>> = vec![q0];
    create_proof(&params, &mut transcript, queries).unwrap();
    let proof = transcript.finalize();

    // verifier

    let mut transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);
    let commitment = &transcript.read_point().unwrap();
    let z0: ChallengeZ<_> = transcript.squeeze_challenge_scalar();
    let eval = transcript.read_scalar().unwrap();

    let q0 = VerifierQuery {
        commitment,
        point: *z0,
        eval,
    };
    let queries: Vec<VerifierQuery<G1Affine>> = vec![q0];
    let ret = verify_proof(&params, &mut transcript, queries).unwrap();
}
