use babyjubjub::BabyJubJubPoint;
use oprf::{blinded_query::blinded_query, oprf_output::verified_oprf};

pub global DS_N: Field = 1330664006; // b"OPRF"
pub global DS_DLOG: Field = 1523098184080632582082867317389990410064981862; // b"DLOG Equality Proof"

/// This circuit demonstrates the general structure of an OPRF service in which a user knows a secret and wants to salt it
/// with a secret provided by the OPRF service. To do so, the user first proves knowledge of the secret by committing to it
/// before engaging in the OPRF protocol. After receiving the OPRF response, the user proves that they unblinded correctly
/// and that the OPRF response is consistent with the initial query. The final output is derived from the OPRF response and
/// the original input via a hash function. The circuit ensures that only a user who knows the secret can produce a valid
/// proof and obtain the final output.
///
/// Concretely, in this example the user:
/// Proves knowledge of a preimage that hashes to a given commitment using a Poseidon2 hash. Since only the user knows the
/// preimage, no one else can produce a proof for the given commitment. In this case, the preimage serves as the user's
/// secret for engaging in the OPRF protocol.
pub fn main(
    // These are the inputs needed for the first part of the OPRF protocol, the query proof.
    commitment: pub Field,
    preimage: Field,
    beta: Field,
    // These are the inputs needed for the second part of the OPRF protocol, proving the full flow.
    oprf_pk: pub BabyJubJubPoint,
    dlog_e: Field,
    dlog_s: Field,
    oprf_response_blinded: BabyJubJubPoint,
    oprf_response: BabyJubJubPoint,
) -> pub (BabyJubJubPoint, Field) {
    // Prove that the client knows the preimage of the given hash.
    let hash = std::hash::poseidon2_permutation([0, preimage, 0, 0], 4)[1];
    assert(hash == commitment, "Hashed message does not match expected value");

    // 1. Generate the query proof point.
    let query = blinded_query(beta, preimage);

    // 2. Generate the final proof on the client side on the output of the OPRF nodes.
    // Note that in a typical scenario, the query proof in 1. would be generated on the client side before sending the resulting request to the OPRF nodes and only after receiving the OPRF response from the nodes, the proof in 2. would be generated. Inside the second proof, the query proof is done again for completeness and verification purposes. We include both parts in this main function for demonstration purposes only.
    let verified_output = verified_oprf(
        beta,
        oprf_pk,
        dlog_e,
        dlog_s,
        oprf_response_blinded,
        oprf_response,
        preimage,
        DS_DLOG,
        DS_N,
    );

    (query, verified_output)
}

#[test]
fn hash_preimage_kat_test() {
    let oprf_pk = BabyJubJubPoint::new(
        5710999305174746446129006558187982651929018212457711080538180123406991257834,
        14822830093014637273720066510303560520096190665043878041612158237057634974510,
    );

    let oprf_response = BabyJubJubPoint::new(
        8239981253288452954319423631647803967161484725248664916163883751103616749641,
        10909431257409573621736924846505941126161080693380329853422959666368005023270,
    );

    let oprf_response_blinded = BabyJubJubPoint::new(
        3155679112931956901250628220045483261937665592711481372076828199008185725288,
        2295756075485931574186491588789693245723103184777309603040062940469350270432,
    );

    let beta = 63865932500786004558985758765891911620034145599124743624338496685411118977;
    let dlog_e = 21651611782908870028415356680205912578677611779857889287526859934595727462023;
    let dlog_s = 813348544856521250944635798658236115440111721634739064595636884345549099749;
    let commitment = 0x13e75fabe371ba4c0ad318cfde3eaac9185d8ad2ce743ea71e038b23abfb7d08;
    let preimage = 42;

    let expected_output =
        652462475809871187303694058326169186632613845657706445893000132676028204998;
    let expected_query_request = BabyJubJubPoint::new(
        8862413567228016424141044651498536845623186939028122849972174286034625708354,
        6472083251782659560632838765641307423815272887581156706952768391781883690924,
    );

    let result = main(
        commitment,
        preimage,
        beta,
        oprf_pk,
        dlog_e,
        dlog_s,
        oprf_response_blinded,
        oprf_response,
    );
    assert(
        (result.0.x == expected_query_request.x) & (result.0.y == expected_query_request.y),
        "Query request point does not match expected value",
    );
    assert(result.1 == expected_output, "Final output does not match expected value");
}
