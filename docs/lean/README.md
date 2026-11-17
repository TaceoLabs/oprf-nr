# Lean proof

`BabyJubJubNoirTateProof.lean` is a Lean 4 proof for the witness-based reduced
8-Tate subgroup check `BabyJubJubPoint::check_sub_group_tate` in
`babyjubjub/src/tate.nr`.

It extends the Solidity development in
[TaceoLabs/babyjubjub-solidity](https://github.com/TaceoLabs/babyjubjub-solidity)
(`docs/lean`), which is pulled in as a Lake dependency pinned to a commit. That
development proves that the Solidity predicate
`isInCorrectSubgroupAssumingOnCurveTate`, which evaluates the final
exponentiation `m^((Q-1)/8)` with the ModExp precompile, accepts exactly the
prime-order subgroup.

The Noir circuit replaces the exponentiation by an unconstrained hint: the
prover supplies `r` and a coset index `k` (three bits) with `r^8 == m * 5^k`,
and the circuit returns `y == 1 || (m != 0 && k == 0)`. This file proves:

- the Noir Miller arithmetic is transcribed exactly and returns the same
  `N * D^7` value as the Solidity code, despite the different multiplication
  order (`noirTateMillerValue_eq_tateMillerValue`);
- `(1 + 4*k0) * (1 + 24*k1) * (1 + 624*k2)` equals `5^k`, and the asserted
  constraint is the field equation `r^8 = m * 5^k`;
- for nonzero `m` and any accepted hint, `k = 0` holds exactly when
  `m^((Q-1)/8) = 1` (`coset_index_eq_zero_iff_final_exponentiation_eq_one`);
- on the curve, `y == 1` identifies the identity;
- `noir_tate_check_iff_solidity_tate_accepts`: for every on-curve point and
  every hint accepted by the constraint, the returned boolean equals the
  Solidity predicate;
- `noir_tate_check_iff_prime_order_subgroup` and
  `noir_tate_check_iff_canonical_order_check`: combined with the Solidity
  theorems, the Noir check returns `true` exactly for prime-order-subgroup
  points, equivalently exactly when `[R]P = 0`;
- the prover has no freedom: the result does not depend on the hint
  (`noir_tate_check_independent_of_hint`), and for nonzero `m` the coset bits
  themselves are unique (`noir_hint_bits_unique`);
- concrete accepted hints exist for the base point (`k = 0`, result `true`) and
  the full-order generator (`k = 7`, result `false`), and the `r = 0` hint at a
  torsion point with zero Miller value is rejected.

Run it with:

```sh
lake build
```

from the `docs` directory. The first build fetches the pinned Solidity proof.

## Assumptions

The statements are theorems about every hint that satisfies the circuit
constraint, so the unconstrained Noir code (`tate_final_exp_hint`, `pow`,
`sqrt`) is not modeled and not trusted.

Two things are theorem parameters rather than proven here:

- `FermatLittle`: `a^(Q-1) = 1 (mod Q)` for every `a` not divisible by `Q`.
  This is equivalent to `Q` being prime. The development stays
  dependency-free and carries no primality certificate for `Q`.
- `TateEncodingLaws`, inherited from the Solidity development: the standard
  bilinearity and non-degeneracy of the reduced Tate pairing, and the statement
  that an affine point represents a given discrete-log class. It is only needed
  for the last step, from the Solidity predicate to subgroup membership.

Not covered:

- completeness of the hint for arbitrary points, i.e. that an honest prover can
  always find `(r, k)`. This needs that `F_Q^*` is cyclic and that `5` generates
  `F_Q^* / (F_Q^*)^8`; only the concrete witnesses above are checked;
- the on-curve precondition, which the caller must establish;
- the compilation of Noir to constraints. The proof is about the arithmetic as
  written in `tate.nr`, with `Field` operations modeled as arithmetic modulo
  `Q` on canonical representatives.
