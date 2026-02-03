use super::{blinded_query::blinded_query_inner, dlog::verify_dlog_equality};
use babyjubjub::BabyJubJubPoint;

/// Generates a proof of the full construction, including the initial query proof generation, the Chaum-Pedersen dlog equality proof verification, the unblinding verification, and the final output. For further details we refer to https://github.com/TaceoLabs/oprf-service/blob/main/docs/oprf.pdf
/// Inputs:
/// `beta`: blinding randomness provided by the client.
/// `oprf_pk`: OPRF public key.
/// `dlog_e`, `dlog_s`: Chaum-Pedersen DLog equality proof inputs.
/// `oprf_response_blinded`: Blinded OPRF response from the nodes.
/// `oprf_response`: Unblinded OPRF response (provided by the client to avoid in-circuit inversion).
/// `client_input`: Original client input.
/// `ds_dlog`: Domain separator for the DLog equality proof.
/// `ds_out`: Domain separator for final output.
pub fn verified_oprf(
    beta: Field,
    oprf_pk: BabyJubJubPoint,
    dlog_e: Field,
    dlog_s: Field,
    oprf_response_blinded: BabyJubJubPoint,
    oprf_response: BabyJubJubPoint,
    client_input: Field,
    ds_dlog: Field,
    ds_out: Field,
) -> Field {
    // Validate beta once and reuse the bits
    assert(beta != 0, "Beta cannot be zero");
    let beta_bits = BabyJubJubPoint::validate_scalar_field_with_bits(beta);

    // Show that the original query was computed correctly
    let b_q = blinded_query_inner(beta_bits, client_input);

    // Check the dlog equality proof
    verify_dlog_equality(dlog_e, dlog_s, oprf_pk, b_q, oprf_response_blinded, ds_dlog);

    // Verify that the user unblinded correctly
    // This checks that: oprf_response * beta === oprf_response_blinded
    verify_unblinding(oprf_response, oprf_response_blinded, beta_bits);

    // Compute the final output using the unblinded oprf_response
    generate_output(client_input, oprf_response, ds_out)
}

// Generates the final output as output = Poseidon2(DS_out,query, oprf_response.x, oprf_response.y), where DS_out is a domain separator.
pub fn generate_output(query: Field, oprf_response: BabyJubJubPoint, ds_out: Field) -> Field {
    let state =
        std::hash::poseidon2_permutation([ds_out, query, oprf_response.x, oprf_response.y], 4);

    state[1]
}

pub fn verify_unblinding(
    oprf_response: BabyJubJubPoint,
    oprf_response_blinded: BabyJubJubPoint,
    beta_bits: [u1; 251],
) {
    // Check that oprf_response is on the curve and perform unblinding
    assert(oprf_response.is_on_curve(), "OPRF response must be on curve");
    // We need to check that the response is in the prime order subgroup, otherwise the response may include a small-order component which may get canceled out during unblinding and allow malleability here
    assert(oprf_response.check_sub_group(), "OPRF response must be in prime order subgroup");

    // Verify: oprf_response * beta === oprf_response_blinded
    let reblinded = oprf_response.scalar_mul_bits(beta_bits);
    // Since response point is in the prime order subgroup, reblinded is also in the prime order subgroup.

    assert(
        (reblinded.x == oprf_response_blinded.x) & (reblinded.y == oprf_response_blinded.y),
        "Unblinding verification failed",
    );
}

#[test]
fn verified_oprf_kat_test() {
    let beta = 2387462819376525223098422965806766751285565755980265072594901385662518965922;
    let oprf_pk = BabyJubJubPoint::new(
        16048296497646113681290127133582586009660277510307938775951186660467382774945,
        13451097916688865791218925679662796109386737920791997438101375513111619197164,
    );
    let dlog_e = 5609293693019386176508931649877337091590878173635241438306548223920379307458;
    let dlog_s = 1167493435914595771361530871033173621661932035514996719837354510862251986174;
    let oprf_response_blinded = BabyJubJubPoint::new(
        6882462243439192795495492197995100450516328082301652413647059141168822449465,
        11410248488379662098266045802345135482683496756414401793793460258484335221028,
    );
    let oprf_response = BabyJubJubPoint::new(
        11771927497930831763844779626723106344742708040976110136703486119568919340013,
        19299702061490581533153169629464406607119112637706400365988657399831357218309,
    );
    let client_input =
        16778459034791831994680912315190773394547154204120376000937183272785502542361;
    let ds_dlog = 1523098184080632582082867317389990410064981862;
    let ds_out = 1773399373884719043551596035141478;

    let expected_output =
        21342856517406476000190785734870568200315738457615815351702849709270076362125;

    let verified_output = verified_oprf(
        beta,
        oprf_pk,
        dlog_e,
        dlog_s,
        oprf_response_blinded,
        oprf_response,
        client_input,
        ds_dlog,
        ds_out,
    );
    assert(verified_output == expected_output, "Final output mismatch");
}
