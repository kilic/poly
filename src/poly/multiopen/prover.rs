use super::super::{commitment::Params, Coeff, Polynomial};
use super::{construct_intermediate_sets, ChallengeV, ProverQuery, Query};

use crate::arithmetic::CurveAffine;
use crate::{
    arithmetic::kate_division,
    transcript::{EncodedChallenge, TranscriptWrite},
};

use ff::Field;
use pairing::arithmetic::Engine;
use std::{io, marker::PhantomData};

pub fn create_proof<
    'a,
    I,
    C: Engine,
    E: EncodedChallenge<C::G1Affine>,
    T: TranscriptWrite<C::G1Affine, E>,
>(
    params: &Params<C>,
    transcript: &mut T,
    queries: I,
) -> io::Result<()>
where
    I: IntoIterator<Item = ProverQuery<'a, C::G1Affine>> + Clone,
{
    let v: ChallengeV<_> = transcript.squeeze_challenge_scalar();

    let commitment_data = construct_intermediate_sets(queries);

    let zero = || Polynomial::<C::Fr, Coeff> {
        values: vec![C::Fr::zero(); params.n as usize],
        _marker: PhantomData,
    };

    for commitment_at_a_point in commitment_data.iter() {
        let mut combination_poly = zero();
        let mut combination_eval = C::Fr::zero();
        let z = commitment_at_a_point.point;
        for query in commitment_at_a_point.queries.iter() {
            assert_eq!(query.get_point(), z);

            let poly = query.get_commitment().poly;
            let eval = query.get_eval();

            combination_poly = combination_poly * *v + poly;
            combination_eval = combination_eval * *v + eval;
        }

        let combination_poly = &combination_poly - combination_eval;
        let witness_poly = Polynomial {
            values: kate_division(&combination_poly.values, z),
            _marker: PhantomData,
        };
        // TODO: assert degree
        let w = params.commit(&witness_poly);
        transcript.write_point(w)?;
    }
    Ok(())
}

#[doc(hidden)]
#[derive(Copy, Clone)]
pub struct PolynomialPointer<'a, C: CurveAffine> {
    poly: &'a Polynomial<C::Scalar, Coeff>,
}

impl<'a, C: CurveAffine> PartialEq for PolynomialPointer<'a, C> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.poly, other.poly)
    }
}

impl<'a, C: CurveAffine> Query<C::Scalar> for ProverQuery<'a, C> {
    type Commitment = PolynomialPointer<'a, C>;
    type Scalar = C::Scalar;

    fn get_point(&self) -> C::Scalar {
        self.point
    }
    fn get_eval(&self) -> C::Scalar {
        self.eval
    }
    fn get_commitment(&self) -> Self::Commitment {
        PolynomialPointer { poly: self.poly }
    }
}
