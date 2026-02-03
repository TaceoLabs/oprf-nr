use babyjubjub::BabyJubJubPoint;
use poseidon2::bn254::perm;

// Verify a Chaum-Pedersen dlog equality proof that shows that A=x*G and C=x*B share the same discrete log x, given A,B,C and proof e,s.
// Point A is a public input in our use case (the OPRF public key and therefore we expect it to be checked to be in the prime order subgroup outside of this circuit)
// For further details we refer to https://link.springer.com/chapter/10.1007/3-540-48071-4_7 and https://github.com/TaceoLabs/oprf-service/blob/main/docs/oprf.pdf
pub fn verify_dlog_equality(
    e: Field,
    s: Field,
    a_point: BabyJubJubPoint,
    b_point: BabyJubJubPoint,
    c_point: BabyJubJubPoint,
    ds_dlog: Field,
) {
    BabyJubJubPoint::validate_babyjubjub_field(s);

    assert(a_point.is_on_curve(), "Point a must be on curve");
    assert(b_point.is_on_curve(), "Point b must be on curve");
    assert(c_point.is_on_curve(), "Point c must be on curve");
    assert(a_point.is_not_identity(), "Point a must not be identity");
    assert(b_point.is_not_identity(), "Point b must not be identity");
    assert(c_point.is_not_identity(), "Point c must not be identity");
    assert(b_point.check_sub_group(), "Point b must be in subgroup");
    assert(c_point.check_sub_group(), "Point c must be in subgroup");

    // Compute r1 = G*s - a*e and r2 = b*s - c*e
    let generator = BabyJubJubPoint::generator();
    let gs = BabyJubJubPoint::generator_scalar_mul(s);
    let ae = a_point.scalar_mul_base_field(e);
    let r1 = gs.subtract(ae);

    let bs = b_point.scalar_mul(s);
    let ce = c_point.scalar_mul_base_field(e);
    let r2 = bs.subtract(ce);

    // Batch check that r1 and r2 are not identity
    assert(r1.is_not_identity() & r2.is_not_identity(), "Computed points cannot be identity");

    // Recompute the challenge hash
    // Hash input: [ds_dlog, a.x, a.y, b.x, b.y, c.x, c.y, G.x, G.y, r1.x, r1.y, r2.x, r2.y, 0, 0, 0]
    let hash_input = [
        ds_dlog,
        a_point.x,
        a_point.y,
        b_point.x,
        b_point.y,
        c_point.x,
        c_point.y,
        generator.x,
        generator.y,
        r1.x,
        r1.y,
        r2.x,
        r2.y,
        0,
        0,
        0,
    ];
    let hash_state = perm::x5_16(hash_input);
    let challenge = hash_state[1];

    // Verify that the recomputed challenge matches e
    assert(challenge == e, "Challenge verification failed");
}

#[test]
fn test_verify_dlog_equality() {
    let ds_dlog: Field = 1523098184080632582082867317389990410064981862; // b"DLOG Equality Proof"
    let oprf_query_key: BabyJubJubPoint = BabyJubJubPoint {
        x: 0x2003f27260a0b5ee81b84f66f8bf2761ea9557262a4bcd16db5ca7abdeee1885,
        y: 0x1eb45d38c97f7e65ac1b76d234db3237d2860f2b25c43e020693ef92b5a5f793,
    };
    let oprf_response_blinded = BabyJubJubPoint::new(
        6882462243439192795495492197995100450516328082301652413647059141168822449465,
        11410248488379662098266045802345135482683496756414401793793460258484335221028,
    );
    let oprf_pk = BabyJubJubPoint::new(
        16048296497646113681290127133582586009660277510307938775951186660467382774945,
        13451097916688865791218925679662796109386737920791997438101375513111619197164,
    );
    let dlog_e: Field =
        5609293693019386176508931649877337091590878173635241438306548223920379307458;
    let dlog_s: Field =
        1167493435914595771361530871033173621661932035514996719837354510862251986174;

    verify_dlog_equality(
        dlog_e,
        dlog_s,
        oprf_pk,
        oprf_query_key,
        oprf_response_blinded,
        ds_dlog,
    );
}
