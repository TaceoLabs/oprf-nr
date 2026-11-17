// Unconstrained helpers for the BN254 scalar field Fq (the BabyJubJub base field), shared by the
// hash-to-curve and Tate subgroup check hints.

/// 5 is the smallest quadratic non-residue in Fq.
pub(crate) global NON_RESIDUE: Field = 5;
// Q - 1 = 2^TWO_ADICITY * T_ODD with T_ODD odd.
global TWO_ADICITY: u32 = 28;
// (T_ODD - 1) / 2
global T_ODD_MINUS_ONE_HALF: Field =
    40770029410420498293352137776570907027550720424234931066070132305055;
// NON_RESIDUE^T_ODD, a primitive 2^TWO_ADICITY-th root of unity.
global ROOT_OF_UNITY: Field =
    19103219067921713944291392827692070036145651957329286315305642004821462161904;

pub(crate) unconstrained fn pow(base: Field, exponent: Field) -> Field {
    let bits: [bool; 254] = exponent.to_le_bits();
    let mut result = 1;
    for i in 0..254 {
        result *= result;
        if bits[254 - 1 - i] {
            result *= base;
        }
    }
    result
}

/// Legendre symbol of x as a field element in {-1, 0, 1}.
pub(crate) unconstrained fn legendre(x: Field) -> Field {
    if x == 0 {
        0
    } else {
        pow(x, (0 - 1) / 2)
    }
}

/// Tonelli-Shanks square root (constant-shape variant of RFC 9380, appendix I.4). Returns a square
/// root of x if x is a square (0 for x == 0); for a non-square the result is not a square root, so
/// callers must constrain or otherwise validate it.
pub(crate) unconstrained fn sqrt(x: Field) -> Field {
    let mut z = pow(x, T_ODD_MINUS_ONE_HALF);
    let mut t = z * z * x;
    z *= x;
    let mut b = t;
    let mut c = ROOT_OF_UNITY;

    for i in 0..(TWO_ADICITY - 1) {
        for _j in 1..(TWO_ADICITY - i - 1) {
            b *= b;
        }

        z *= if b == 1 { 1 } else { c };

        c *= c;

        t *= if b == 1 { 1 } else { c };

        b = t;
    }

    z
}

#[test]
fn test_pow() {
    // Safety: test only.
    let (p, c) = unsafe { (pow(3, 5), pow(NON_RESIDUE, 2 * T_ODD_MINUS_ONE_HALF + 1)) };
    assert_eq(p, 243);
    assert_eq(c, ROOT_OF_UNITY);
}

#[test]
fn test_sqrt() {
    let x = 123456789;
    // Safety: test only.
    let (s, zero) = unsafe { (sqrt(x * x), sqrt(0)) };
    assert((s == x) | (s == -x));
    assert_eq(zero, 0);
}

#[test]
fn test_legendre() {
    // Safety: test only.
    let (zero, square, non_square) = unsafe { (legendre(0), legendre(4), legendre(NON_RESIDUE)) };
    assert_eq(zero, 0);
    assert_eq(square, 1);
    assert_eq(non_square, -1);
}
