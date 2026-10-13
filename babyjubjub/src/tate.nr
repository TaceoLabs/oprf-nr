// Prime-order subgroup membership check via the reduced 8-Tate pairing.
//
// Reference: Koshelev, "Subgroup membership testing on elliptic curves via the Tate pairing",
// https://eprint.iacr.org/2022/037. Mirrors the Solidity implementation (and Lean proof) in
// https://github.com/TaceoLabs/babyjubjub-solidity.
//
// BabyJubJub is birational to the Montgomery curve v^2 = u^3 + 168698*u^2 + u via
// u = (1+y)/(1-y), v = (1+y)/((1-y)*x). The curve is cyclic of order 8*R and 8 | Q-1, so with T a
// point of order 8, P is in the prime-order subgroup iff t_8(T, P) = f_{8,T}(P)^((Q-1)/8) == 1.
use super::BabyJubJubPoint;

// T = [R]G8 in Montgomery coordinates, where G8 is the ERC-2494 generator of order 8*R.
global TATE_T_X: Field =
    19799329160503878365519859265345525785148473002902384773314932802961476726446;
// Tangent slope at T.
global TATE_TANGENT_0: Field =
    5125366436769623165205660392107939355810725029703343239946747673935168202680;
// [2]T = (1, TATE_TWO_T_Y); its tangent slope equals TATE_TWO_T_Y.
global TATE_TWO_T_Y: Field =
    14673962723734255200314198873237586429337747973199041533368185129026308523766;
// (Q - 1) / 8
global TATE_FINAL_EXPONENT: Field =
    2736030358979909402780800718157159386068545550052004292962275523321976061952;

// Fq* is cyclic of order Q-1 with 8 | Q-1, so the quotient Fq* / (Fq*)^8 is cyclic of order 8.
// 5 is a quadratic non-residue in Fq, hence 5^((Q-1)/2) = -1 and 5^((Q-1)/8) is a primitive 8th root
// of unity. This means the class of 5 generates the quotient: the cosets 5^k * (Fq*)^8, k in 0..8,
// partition Fq*, and every nonzero m has a unique k with m * 5^k an 8th power.
global NON_RESIDUE: Field = 5;
// 5^((Q-1)/8), a primitive 8th root of unity.
global NON_RESIDUE_FINAL_EXP: Field =
    19540430494807482326159819597004422086093766032135589407132600596362845576832;
// Q - 1 = 2^28 * T_ODD
global TWO_ADICITY: u32 = 28;
global T_ODD: Field = 81540058820840996586704275553141814055101440848469862132140264610111;
global T_ODD_PLUS_ONE_HALF: Field =
    40770029410420498293352137776570907027550720424234931066070132305056;

impl BabyJubJubPoint {
    /// Miller value f_{8,T}(P) = N/D of the reduced 8-Tate pairing, returned as N * D^7 = (N/D) * D^8,
    /// which has the same final exponentiation since D^(Q-1) = 1.
    fn tate_miller_value(self) -> Field {
        // Projective Montgomery coordinates (U : V : W) = ((1+y)*x : 1+y : (1-y)*x).
        let v = 1 + self.y;
        let u = v * self.x;
        let w = (1 - self.y) * self.x;

        // Tangent lines at T and [2]T, folded using TATE_TANGENT_0 * TATE_T_X - TATE_T_Y == TATE_T_X.
        let line0 = v - TATE_TANGENT_0 * u + TATE_T_X * w;
        let line1 = v - TATE_TWO_T_Y * u;
        let line0_sq = line0 * line0;
        let numerator = line0_sq * line0_sq * line1 * line1;

        // D = W * (U-W)^4 * U
        let u_minus_w = u - w;
        let u_minus_w_sq = u_minus_w * u_minus_w;
        let denominator = w * u_minus_w_sq * u_minus_w_sq * u;

        let d_sq = denominator * denominator;
        let d_4 = d_sq * d_sq;
        numerator * d_4 * d_sq * denominator
    }

    /// Checks prime-order subgroup membership using the reduced 8-Tate pairing.
    ///
    /// Precondition: the point must be on the curve, otherwise the result is meaningless.
    ///
    /// The pairing is t_8(T, P) = m^((Q-1)/8) for the Miller value m, and P is in the subgroup iff
    /// this is 1. Computing the ~250-bit exponentiation in-circuit costs ~375 gates, so instead we
    /// use that for nonzero m, m^((Q-1)/8) == 1 iff m is an 8th power in Fq (Fq* is cyclic and the
    /// 8th powers form its unique subgroup of index 8).
    ///
    /// Merely proving "m is an 8th power" with a witness r (r^8 == m) would be one-sided: the prover
    /// could withhold r for a valid point and make the check return false. To make the bool sound in
    /// both directions the prover instead supplies the coset index k in 0..8 (as three bits) and r with
    ///   r^8 == m * 5^k.
    /// Since the cosets of 5^k partition Fq* (see NON_RESIDUE), k is uniquely determined by m, and
    /// m is an 8th power iff k == 0. So the result is simply k == 0 and the prover cannot lie either way.
    ///
    /// The only exception is m == 0, where r == 0 satisfies the equation for every k, so m != 0 is
    /// checked separately. On-curve, m vanishes exactly at the identity (which has no Montgomery image
    /// and is handled by the y == 1 shortcut) and at non-identity torsion points, which must be rejected.
    pub fn check_sub_group_tate(self) -> bool {
        let m = self.tate_miller_value();
        // Safety: k0..k2 are range-constrained to bits, and r is bound by r^8 == m * 5^k below.
        let (r, k0, k1, k2) = unsafe { tate_final_exp_hint(m) };
        // 5^k = 5^k0 * 25^k1 * 625^k2, each factor a linear select on a bit.
        let five_k = (1 + 4 * (k0 as Field)) * (1 + 24 * (k1 as Field)) * (1 + 624 * (k2 as Field));
        let r_sq = r * r;
        let r_4 = r_sq * r_sq;
        assert(r_4 * r_4 - m * five_k == 0, "Tate final exponentiation hint is invalid");
        // On the curve, y == 1 implies x == 0, so this identifies the identity.
        (self.y == 1) | ((m != 0) & !(k0 | k1 | k2))
    }
}

/// Returns (r, k0, k1, k2) with r^8 == m * 5^k for k = k0 + 2*k1 + 4*k2. For m == 0 returns zeros.
unconstrained fn tate_final_exp_hint(m: Field) -> (Field, bool, bool, bool) {
    if m == 0 {
        (0, false, false, false)
    } else {
        // e = m^((Q-1)/8) is an 8th root of unity. Multiplying by eta = 5^((Q-1)/8), a primitive 8th
        // root of unity, cycles through all of them, so e * eta^k == 1 for a unique k in 0..8, and then
        // (m * 5^k)^((Q-1)/8) == 1, i.e. m * 5^k is an 8th power.
        let mut e = pow(m, TATE_FINAL_EXPONENT);
        let mut k: u32 = 0;
        let mut c = m;
        while e != 1 {
            e *= NON_RESIDUE_FINAL_EXP;
            c *= NON_RESIDUE;
            k += 1;
        }
        // c = r^8 is an 8th power, so take three square roots. Each sqrt is only defined up to sign,
        // but since 8 | Q-1, -1 is a 4th power in Fq: both roots +-r^4 of c are 4th powers, and both
        // roots of those are squares. Hence any sign choice at each step still yields an 8th root.
        let r = sqrt(sqrt(sqrt(c)));
        (r, k & 1 == 1, k & 2 == 2, k & 4 == 4)
    }
}

unconstrained fn pow(base: Field, exponent: Field) -> Field {
    let bits: [bool; 254] = exponent.to_le_bits();
    let mut result = 1;
    let mut base = base;
    for i in 0..254 {
        if bits[i] {
            result *= base;
        }
        base *= base;
    }
    result
}

/// Tonelli-Shanks square root. Precondition: n is a square.
unconstrained fn sqrt(n: Field) -> Field {
    let mut m = TWO_ADICITY;
    let mut c = pow(NON_RESIDUE, T_ODD);
    let mut t = pow(n, T_ODD);
    let mut r = pow(n, T_ODD_PLUS_ONE_HALF);
    while t != 1 {
        let mut i: u32 = 0;
        let mut t_sq = t;
        while t_sq != 1 {
            t_sq *= t_sq;
            i += 1;
        }
        let mut b = c;
        for _ in 0..(m - i - 1) {
            b *= b;
        }
        m = i;
        c = b * b;
        t *= c;
        r *= b;
    }
    r
}

#[test]
fn test_tate_subgroup_vectors() {
    // (x, y, expected), generated from multiples of the order-8R ERC-2494 generator G8.
    let vectors: [(Field, Field, bool); 10] = [
        (0, 1, true),
        (super::BABYJUBJUB_GENERATOR_X, super::BABYJUBJUB_GENERATOR_Y, true),
        // [8s]G8
        (
            5922678947608890254381112007025269498600683152527879970551342645395453225481,
            3677721062984866292044616965955759577674274834270214873732205932810262681851, true,
        ),
        // [R]G8 (order 8)
        (
            4342719913949491028786768530115087822524712248835451589697801404893164183326,
            4826523245007015323400664741523384119579596407052839571721035538011798951543, false,
        ),
        // [2R]G8 (order 4)
        (18930368022820495955728484915491405972470733850014661777449844430438130630919, 0, false),
        // [4R]G8 (order 2)
        (0, -1, false),
        // [8s + R]G8, [8s + 2R]G8, [8s + 4R]G8
        (
            12537600754896197818627229178010202916856051828249504713364331778503781348377,
            3359703664929767409891774517209195909162622888019763617719956190276965764694, false,
        ),
        (
            1392596115989014552782522464422261228186878396701956749859658510508330983790,
            20465514082548345370692778753448315171059264580348351240557527622386571355849, false,
        ),
        (
            15965563924230384967865293738232005589947681247888154373146861541180355270136,
            18210521808854408930201788779301515510874089566145819469965998253765545813766, false,
        ),
        (
            4689731437944306428780974070575571025333825310181802403039288057202868837337,
            14792220576807380471707687543579831579477508903129740636298855878394914021491, false,
        ),
    ];
    for v in vectors {
        let p = BabyJubJubPoint::new(v.0, v.1);
        assert_eq(p.check_sub_group_tate(), v.2);
        assert_eq(p.check_sub_group(), v.2);
    }
}

#[test]
fn test_sqrt_and_pow() {
    let x = 123456789;
    // Safety: test only.
    let (s, p) = unsafe { (sqrt(x * x), pow(3, 5)) };
    assert((s == x) | (s == -x));
    assert_eq(p, 243);
}
