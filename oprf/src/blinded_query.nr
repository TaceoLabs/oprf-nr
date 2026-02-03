use babyjubjub::{BabyJubJubPoint, hash_to_curve::encode};

// Generates the blinded query proof point b_q = encode(client_input) * beta, where beta (the blinding randomness provided by the client) is already given in bits (generated via BabyJubJubPoint::validate_scalar_field_with_bits(beta)).
// The client_input is the input known only to the client, which is encoded to a curve point via the encode() function from the BabyJubJub hash_to_curve module.
// For further details we refer to https://github.com/TaceoLabs/oprf-service/blob/main/docs/oprf.pdf as well as an implementation example in oprf_example/src/main.nr
pub fn blinded_query(beta: Field, client_input: Field) -> BabyJubJubPoint {
    // Validate that beta is non-zero and get its bits
    assert(beta != 0, "Beta cannot be zero");
    let beta_bits = BabyJubJubPoint::validate_scalar_field_with_bits(beta);

    blinded_query_inner(beta_bits, client_input)
}

pub fn blinded_query_inner(beta_bits: [u1; 251], client_input: Field) -> BabyJubJubPoint {
    // Encode query to curve point and perform scalar multiplication
    let (px, py) = encode(client_input);
    // Precondition: encode returns a valid point on the BabyJubJub curve in the prime order subgroup
    let p = BabyJubJubPoint::new(px, py);
    // Return the blinded (encoded) query point
    p.scalar_mul_bits(beta_bits)
}

#[test]
fn oprf_query_kat_test() {
    let beta = 1219447978145766874721695300216900264892278162307712369438981445355514609028;
    let client_input = 387242419257851558984914892096106188402994395767663340643461644969954908901;
    let expected = BabyJubJubPoint::new(
        9674018812144873985515234638873635008708834681175738612597888298086191498827,
        18818965079786157878748649151755578492493325229415754584538271947197071123195,
    );
    let result = blinded_query(beta, client_input);
    assert((result.x == expected.x) & (result.y == expected.y), "OPRF query test failed");
}
