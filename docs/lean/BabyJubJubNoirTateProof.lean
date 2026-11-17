import BabyJubJubTateProof

/-!
Proof for the witness-based reduced 8-Tate subgroup check in
`babyjubjub/src/tate.nr` (`BabyJubJubPoint::check_sub_group_tate`).

The Solidity check proven in `BabyJubJubTateProof` evaluates the final
exponentiation `m^((Q-1)/8)` with the EVM ModExp precompile.  The Noir circuit
avoids that exponentiation: the prover supplies an unconstrained hint `(r, k)`
with `k` given as three bits, and the circuit only checks

  `r^8 == m * 5^k`.

It then returns `y == 1 || (m != 0 && k == 0)`.

This file transcribes the Noir arithmetic and proves that, for *every* hint
accepted by the constraint, the returned boolean equals the Solidity predicate
`solidityTateAccepts`, and hence prime-order subgroup membership.  The hint is
therefore untrusted: a malicious prover can neither make a point outside the
subgroup pass nor make a point inside it fail.

Noir `Field` values are canonical representatives below `Q`, so field `+`, `-`
and `*` are modeled by `addmod`, `submod` and `mulmod`, exactly as in the
Solidity development.
-/

namespace BabyJubJub.NoirTateProof

open BabyJubJub BabyJubJub.TateProof

/-! ## Assumption -/

/-- Fermat's little theorem for the BN254 scalar field modulus `Q`.

This is the single number-theoretic fact used beyond what is computed here.  It
is equivalent to `Q` being prime.  The development is dependency-free and does
not carry a primality certificate for `Q`, so, like `TateEncodingLaws`, the
statement is an explicit theorem parameter rather than a hidden axiom. -/
def FermatLittle : Prop :=
  ∀ a : Nat, a % Q ≠ 0 → a ^ (Q - 1) % Q = 1

/-! ## Miller value -/

/-- Exact transcription of `tate_miller_value`, which returns `N * D^7`
computed as `N * D^4 * D^2 * D` with `N = line0^4 * line1^2`. -/
def noirTateMillerValue (p : Affine) : Nat :=
  let v := addmod 1 p.y Q
  let u := mulmod v p.x Q
  let w := mulmod (submod 1 p.y Q) p.x Q
  let line0 := addmod (submod v (mulmod TateTangent0 u Q) Q) (mulmod TateTX w Q) Q
  let line1 := submod v (mulmod TateTwoTY u Q) Q
  let line0Sq := mulmod line0 line0 Q
  let numerator := mulmod (mulmod (mulmod line0Sq line0Sq Q) line1 Q) line1 Q
  let uMinusW := submod u w Q
  let uMinusWSq := mulmod uMinusW uMinusW Q
  let denominator := mulmod (mulmod (mulmod w uMinusWSq Q) uMinusWSq Q) u Q
  let dSq := mulmod denominator denominator Q
  let d4 := mulmod dSq dSq Q
  mulmod (mulmod (mulmod numerator d4 Q) dSq Q) denominator Q

theorem mulmod_comm (a b : Nat) : mulmod a b Q = mulmod b a Q := by
  simp [mulmod, Nat.mul_comm]

theorem mulmod_assoc (a b c : Nat) :
    mulmod (mulmod a b Q) c Q = mulmod a (mulmod b c Q) Q := by
  simp [mulmod, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

/-- Multiplication in `F_Q`, as a binary operation for `ac_rfl`. -/
def mulQ (a b : Nat) : Nat := mulmod a b Q

theorem mulQ_eq (a b : Nat) : mulQ a b = mulmod a b Q := rfl

instance : Std.Associative mulQ := ⟨mulmod_assoc⟩
instance : Std.Commutative mulQ := ⟨mulmod_comm⟩

/-- The two multiplication orders for `N * D^7` agree.  With `S = (U - W)^2`,
Noir computes `D = ((W * S) * S) * U` and `(L0^2 * L0^2 * L1 * L1) * D^4 * D^2 * D`,
Solidity computes `D = (W * (S * S)) * U` and `((L0 * D)^2 * L1 * D)^2 * D`. -/
theorem miller_product_shape (l0 l1 w s u : Nat) :
    (mulmod (mulmod (mulmod (mulmod (mulmod (mulmod (mulmod l0 l0 Q) (mulmod l0 l0 Q) Q) l1 Q) l1 Q) (mulmod (mulmod (mulmod (mulmod (mulmod w s Q) s Q) u Q) (mulmod (mulmod (mulmod w s Q) s Q) u Q) Q) (mulmod (mulmod (mulmod (mulmod w s Q) s Q) u Q) (mulmod (mulmod (mulmod w s Q) s Q) u Q) Q) Q) Q) (mulmod (mulmod (mulmod (mulmod w s Q) s Q) u Q) (mulmod (mulmod (mulmod w s Q) s Q) u Q) Q) Q) (mulmod (mulmod (mulmod w s Q) s Q) u Q) Q) =
      (mulmod (mulmod (mulmod (mulmod (mulmod (mulmod l0 (mulmod (mulmod w (mulmod s s Q) Q) u Q) Q) (mulmod l0 (mulmod (mulmod w (mulmod s s Q) Q) u Q) Q) Q) l1 Q) (mulmod (mulmod w (mulmod s s Q) Q) u Q) Q) (mulmod (mulmod (mulmod (mulmod l0 (mulmod (mulmod w (mulmod s s Q) Q) u Q) Q) (mulmod l0 (mulmod (mulmod w (mulmod s s Q) Q) u Q) Q) Q) l1 Q) (mulmod (mulmod w (mulmod s s Q) Q) u Q) Q) Q) (mulmod (mulmod w (mulmod s s Q) Q) u Q) Q) := by
  simp only [← mulQ_eq]
  ac_rfl

/-- The Noir circuit and the Solidity contract compute the same Miller value. -/
theorem noirTateMillerValue_eq_tateMillerValue (p : Affine) :
    noirTateMillerValue p = tateMillerValue p := by
  unfold noirTateMillerValue tateMillerValue
  exact miller_product_shape _ _ _ _ _

theorem noirTateMillerValue_lt_q (p : Affine) : noirTateMillerValue p < Q :=
  mulmod_lt_q _ _

/-! ## The constrained hint -/

/-- `k = k0 + 2*k1 + 4*k2`, the coset index supplied by the prover. -/
def cosetIndex (k0 k1 k2 : Bool) : Nat :=
  k0.toNat + 2 * k1.toNat + 4 * k2.toNat

/-- Transcription of
`(1 + 4 * k0) * (1 + 24 * k1) * (1 + 624 * k2)`. -/
def noirFiveK (k0 k1 k2 : Bool) : Nat :=
  mulmod
    (mulmod (addmod 1 (mulmod 4 k0.toNat Q) Q) (addmod 1 (mulmod 24 k1.toNat Q) Q) Q)
    (addmod 1 (mulmod 624 k2.toNat Q) Q) Q

theorem noirFiveK_eq_pow (k0 k1 k2 : Bool) :
    noirFiveK k0 k1 k2 = 5 ^ cosetIndex k0 k1 k2 := by
  cases k0 <;> cases k1 <;> cases k2 <;> native_decide

theorem cosetIndex_lt_eight (k0 k1 k2 : Bool) : cosetIndex k0 k1 k2 < 8 := by
  cases k0 <;> cases k1 <;> cases k2 <;> decide

theorem cosetIndex_eq_zero_iff (k0 k1 k2 : Bool) :
    cosetIndex k0 k1 k2 = 0 ↔ (k0 || k1 || k2) = false := by
  cases k0 <;> cases k1 <;> cases k2 <;> decide

theorem cosetIndex_injective (k0 k1 k2 k0' k1' k2' : Bool)
    (h : cosetIndex k0 k1 k2 = cosetIndex k0' k1' k2') :
    k0 = k0' ∧ k1 = k1' ∧ k2 = k2' := by
  revert h
  cases k0 <;> cases k1 <;> cases k2 <;> cases k0' <;> cases k1' <;> cases k2' <;> decide

/-- Transcription of the only constraint on the hint:
`assert(r_4 * r_4 - m * five_k == 0)`. -/
def noirHintConstraint (m r : Nat) (k0 k1 k2 : Bool) : Prop :=
  submod
    (mulmod (mulmod (mulmod r r Q) (mulmod r r Q) Q) (mulmod (mulmod r r Q) (mulmod r r Q) Q) Q)
    (mulmod m (noirFiveK k0 k1 k2) Q) Q = 0

/-- Transcription of the value returned by `check_sub_group_tate`:
`(self.y == 1) | ((m != 0) & !(k0 | k1 | k2))`. -/
def noirCheckSubGroupTate (p : Affine) (k0 k1 k2 : Bool) : Bool :=
  decide (p.y = 1) || (decide (noirTateMillerValue p ≠ 0) && !(k0 || k1 || k2))

theorem mulmod_self (a : Nat) : mulmod a a Q = a ^ 2 % Q := by
  simp [mulmod, Nat.pow_two]

theorem eighth_power_mulmod (r : Nat) :
    mulmod (mulmod (mulmod r r Q) (mulmod r r Q) Q) (mulmod (mulmod r r Q) (mulmod r r Q) Q) Q =
      r ^ 8 % Q := by
  rw [mulmod_self r, mulmod_self (r ^ 2 % Q), ← Nat.pow_mod, mulmod_self, ← Nat.pow_mod,
    ← Nat.pow_mul, ← Nat.pow_mul]

theorem submod_eq_zero_iff {a b : Nat} (hb : b < Q) :
    submod a b Q = 0 ↔ a = b := by
  simp only [submod]
  split <;> omega

/-- The hint constraint is the field equation `r^8 = m * 5^k`. -/
theorem noirHintConstraint_iff (m r : Nat) (k0 k1 k2 : Bool) :
    noirHintConstraint m r k0 k1 k2 ↔
      r ^ 8 % Q = m * 5 ^ cosetIndex k0 k1 k2 % Q := by
  rw [noirHintConstraint, submod_eq_zero_iff (mulmod_lt_q _ _),
    eighth_power_mulmod, noirFiveK_eq_pow]
  rfl

/-! ## Eighth powers and the cosets of `5` -/

def FiveInverse : Nat :=
  8755297148735710088898562298102910035419345760166413737479281674630323398247

theorem five_inverse : 5 * FiveInverse % Q = 1 := by native_decide

/-- `5^((Q-1)/8)` is the primitive eighth root of unity `NON_RESIDUE_FINAL_EXP`
of the Noir code.  It coincides with `TateGeneratorValue`, the character value
at the full-order generator, whose exact order eight is established by
`small_root_power_eq_one_iff`. -/
theorem five_final_exponentiation : 5 ^ TateFinalExponent % Q = TateGeneratorValue := by
  rw [← modExp_eq_pow_mod]
  native_decide

theorem one_mod_q : 1 % Q = 1 := by native_decide

theorem mul_five_pow_mod_ne_zero {m : Nat} (hm : m % Q ≠ 0) (k : Nat) :
    m * 5 ^ k % Q ≠ 0 := by
  intro h0
  apply hm
  have hinv : 5 ^ k * FiveInverse ^ k % Q = 1 := by
    rw [← Nat.mul_pow, Nat.pow_mod, five_inverse, Nat.one_pow, one_mod_q]
  calc m % Q = m * 1 % Q := by rw [Nat.mul_one]
    _ = m * (5 ^ k * FiveInverse ^ k % Q) % Q := by rw [hinv]
    _ = m * (5 ^ k * FiveInverse ^ k) % Q := Nat.mul_mod_mod _ _ _
    _ = m * 5 ^ k * FiveInverse ^ k % Q := by rw [Nat.mul_assoc]
    _ = m * 5 ^ k % Q * FiveInverse ^ k % Q := (Nat.mod_mul_mod _ _ _).symm
    _ = 0 := by rw [h0, Nat.zero_mul, Nat.zero_mod]

/-- If `r^8 = m * 5^k` with `m` nonzero, then `m^((Q-1)/8) * η^k = 1`, where
`η = 5^((Q-1)/8)`.  This is where Fermat's little theorem enters: the left-hand
side is `r^(Q-1)`. -/
theorem hint_character_relation (fermat : FermatLittle) {m r k : Nat}
    (hm : m % Q ≠ 0) (h : r ^ 8 % Q = m * 5 ^ k % Q) :
    m ^ TateFinalExponent % Q * smallRootPower k % Q = 1 := by
  have hr : r % Q ≠ 0 := by
    intro hr0
    apply mul_five_pow_mod_ne_zero hm k
    rw [← h, Nat.pow_mod, hr0]
    rfl
  have hexp : (r ^ 8) ^ TateFinalExponent = r ^ (Q - 1) := by
    rw [← Nat.pow_mul, final_exponent_is_correct]
  calc m ^ TateFinalExponent % Q * smallRootPower k % Q
      = m ^ TateFinalExponent % Q * ((5 ^ TateFinalExponent % Q) ^ k % Q) % Q := by
        rw [smallRootPower, five_final_exponentiation]
    _ = m ^ TateFinalExponent % Q * ((5 ^ TateFinalExponent) ^ k % Q) % Q := by
        rw [← Nat.pow_mod]
    _ = m ^ TateFinalExponent * (5 ^ TateFinalExponent) ^ k % Q := (Nat.mul_mod _ _ _).symm
    _ = (m * 5 ^ k) ^ TateFinalExponent % Q := by
        rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm k]
    _ = (r ^ 8) ^ TateFinalExponent % Q := by rw [Nat.pow_mod, ← h, ← Nat.pow_mod]
    _ = 1 := by rw [hexp, fermat r hr]

theorem smallRootPower_lt_q (e : Nat) : smallRootPower e < Q := Nat.mod_lt _ q_pos

theorem smallRootPower_zero : smallRootPower 0 = 1 := by native_decide

/-- The core of the verification trick: for nonzero `m`, a hint with
`r^8 = m * 5^k` and `k < 8` has `k = 0` exactly when the final exponentiation
`m^((Q-1)/8)` equals one. -/
theorem coset_index_eq_zero_iff_final_exponentiation_eq_one (fermat : FermatLittle)
    {m r k : Nat} (hm : m % Q ≠ 0) (hk : k < 8) (h : r ^ 8 % Q = m * 5 ^ k % Q) :
    k = 0 ↔ m ^ TateFinalExponent % Q = 1 := by
  have key := hint_character_relation fermat hm h
  constructor
  · intro hzero
    rw [hzero, smallRootPower_zero, Nat.mul_one, Nat.mod_mod] at key
    exact key
  · intro hone
    rw [hone, Nat.one_mul, Nat.mod_eq_of_lt (smallRootPower_lt_q k)] at key
    have hfin := (small_root_power_eq_one_iff ⟨k, hk⟩).mp key
    exact congrArg Fin.val hfin

theorem small_root_power_injective :
    ∀ a b : μ8Exponent, smallRootPower a.val = smallRootPower b.val → a = b := by
  native_decide

/-- The coset index is determined by `m`: the prover has no freedom in `k`. -/
theorem coset_index_unique (fermat : FermatLittle) {m r r' k k' : Nat}
    (hm : m % Q ≠ 0) (hk : k < 8) (hk' : k' < 8)
    (h : r ^ 8 % Q = m * 5 ^ k % Q) (h' : r' ^ 8 % Q = m * 5 ^ k' % Q) :
    k = k' := by
  have key := hint_character_relation fermat hm h
  have key' := hint_character_relation fermat hm h'
  have hpow : smallRootPower k = smallRootPower k' := by
    calc smallRootPower k
        = smallRootPower k * 1 % Q := by
          rw [Nat.mul_one, Nat.mod_eq_of_lt (smallRootPower_lt_q k)]
      _ = smallRootPower k * (m ^ TateFinalExponent % Q * smallRootPower k' % Q) % Q := by
          rw [key']
      _ = smallRootPower k * (m ^ TateFinalExponent % Q * smallRootPower k') % Q :=
          Nat.mul_mod_mod _ _ _
      _ = m ^ TateFinalExponent % Q * smallRootPower k * smallRootPower k' % Q := by
          rw [← Nat.mul_assoc, Nat.mul_comm (smallRootPower k)]
      _ = m ^ TateFinalExponent % Q * smallRootPower k % Q * smallRootPower k' % Q :=
          (Nat.mod_mul_mod _ _ _).symm
      _ = smallRootPower k' := by
          rw [key, Nat.one_mul, Nat.mod_eq_of_lt (smallRootPower_lt_q k')]
  exact congrArg Fin.val (small_root_power_injective ⟨k, hk⟩ ⟨k', hk'⟩ hpow)

/-! ## The identity shortcut -/

theorem sq_mod_eq_zero (fermat : FermatLittle) {x : Nat} (hx : x < Q)
    (h : x * x % Q = 0) : x = 0 := by
  have hmod : x % Q = 0 := by
    apply Classical.byContradiction
    intro hne
    have hone := fermat x hne
    have hsplit : Q - 1 = 2 + (Q - 3) := by native_decide
    rw [hsplit, Nat.pow_add, Nat.pow_two, Nat.mul_mod, h, Nat.zero_mul, Nat.zero_mod] at hone
    omega
  rwa [Nat.mod_eq_of_lt hx] at hmod

def FourInverse : Nat :=
  16416182153879456416684804308942956316411273300312025757773653139931856371713

theorem four_inverse : 4 * FourInverse % Q = 1 := by native_decide

/-- On the curve, `y == 1` identifies the identity, as the Noir comment states:
the curve equation reduces to `(A - D) * x^2 = 4 * x^2 = 0`. -/
theorem on_curve_y_eq_one_iff_identity (fermat : FermatLittle) (p : Affine)
    (hp : OnCurve p) : p.y = 1 ↔ p = identity := by
  constructor
  · intro hy
    rcases hp with ⟨hx, _, hcurve⟩
    rw [hy] at hcurve
    have hfour : 4 * (p.x * p.x) % Q = 0 := by
      have hsub := Nat.sub_mod_eq_zero_of_mod_eq (k := Q)
        (m := A * (p.x * p.x) + 1) (n := 1 + D * (p.x * p.x)) (by
          simpa [addmod, mulmod] using hcurve)
      have hdiff : A * (p.x * p.x) + 1 - (1 + D * (p.x * p.x)) = 4 * (p.x * p.x) := by
        simp only [A, D]
        omega
      rwa [hdiff] at hsub
    have hsq : p.x * p.x % Q = 0 := by
      calc p.x * p.x % Q = p.x * p.x * 1 % Q := by rw [Nat.mul_one]
        _ = p.x * p.x * (4 * FourInverse % Q) % Q := by rw [four_inverse]
        _ = p.x * p.x * (4 * FourInverse) % Q := Nat.mul_mod_mod _ _ _
        _ = 4 * (p.x * p.x) * FourInverse % Q := by
            rw [← Nat.mul_assoc, Nat.mul_comm (p.x * p.x) 4]
        _ = 4 * (p.x * p.x) % Q * FourInverse % Q := (Nat.mod_mul_mod _ _ _).symm
        _ = 0 := by rw [hfour, Nat.zero_mul, Nat.zero_mod]
    have hzero := sq_mod_eq_zero fermat hx hsq
    cases p
    simp_all [identity]
  · intro hid
    rw [hid]
    rfl

/-! ## Main theorems -/

theorem modExp_zero_final_exponent : modExp 0 TateFinalExponent Q = 0 := by native_decide

/-- For every hint accepted by the circuit constraint, the boolean returned by
`check_sub_group_tate` equals the Solidity predicate
`isInCorrectSubgroupAssumingOnCurveTate`. -/
theorem noir_tate_check_iff_solidity_tate_accepts (fermat : FermatLittle)
    (p : Affine) (hp : OnCurve p) (r : Nat) (k0 k1 k2 : Bool)
    (hint : noirHintConstraint (noirTateMillerValue p) r k0 k1 k2) :
    noirCheckSubGroupTate p k0 k1 k2 = true ↔ solidityTateAccepts p := by
  have hidentity := on_curve_y_eq_one_iff_identity fermat p hp
  by_cases hy : p.y = 1
  · constructor
    · intro _
      exact Or.inl (hidentity.mp hy)
    · intro _
      simp [noirCheckSubGroupTate, hy]
  · have hid : p ≠ identity := fun h => hy (hidentity.mpr h)
    rw [solidityTateAccepts, or_iff_right hid, ← noirTateMillerValue_eq_tateMillerValue]
    have hlt := noirTateMillerValue_lt_q p
    by_cases hm : noirTateMillerValue p = 0
    · simp [noirCheckSubGroupTate, hy, hm, modExp_zero_final_exponent]
    · have hmod : noirTateMillerValue p % Q ≠ 0 := by
        rwa [Nat.mod_eq_of_lt hlt]
      have hcore := coset_index_eq_zero_iff_final_exponentiation_eq_one fermat hmod
        (cosetIndex_lt_eight k0 k1 k2) ((noirHintConstraint_iff _ _ _ _ _).mp hint)
      rw [modExp_eq_pow_mod, ← hcore, cosetIndex_eq_zero_iff]
      simp [noirCheckSubGroupTate, hy, hm]

/-- The returned boolean does not depend on the hint: any two hints accepted
for the same point produce the same result. -/
theorem noir_tate_check_independent_of_hint (fermat : FermatLittle)
    (p : Affine) (hp : OnCurve p) (r r' : Nat) (k0 k1 k2 k0' k1' k2' : Bool)
    (hint : noirHintConstraint (noirTateMillerValue p) r k0 k1 k2)
    (hint' : noirHintConstraint (noirTateMillerValue p) r' k0' k1' k2') :
    noirCheckSubGroupTate p k0 k1 k2 = noirCheckSubGroupTate p k0' k1' k2' := by
  have h := noir_tate_check_iff_solidity_tate_accepts fermat p hp r k0 k1 k2 hint
  have h' := noir_tate_check_iff_solidity_tate_accepts fermat p hp r' k0' k1' k2' hint'
  exact Bool.eq_iff_iff.mpr (h.trans h'.symm)

/-- For a nonzero Miller value even the coset bits are forced. -/
theorem noir_hint_bits_unique (fermat : FermatLittle)
    (p : Affine) (hm : noirTateMillerValue p ≠ 0) (r r' : Nat) (k0 k1 k2 k0' k1' k2' : Bool)
    (hint : noirHintConstraint (noirTateMillerValue p) r k0 k1 k2)
    (hint' : noirHintConstraint (noirTateMillerValue p) r' k0' k1' k2') :
    k0 = k0' ∧ k1 = k1' ∧ k2 = k2' := by
  have hmod : noirTateMillerValue p % Q ≠ 0 := by
    rwa [Nat.mod_eq_of_lt (noirTateMillerValue_lt_q p)]
  exact cosetIndex_injective _ _ _ _ _ _
    (coset_index_unique fermat hmod (cosetIndex_lt_eight _ _ _) (cosetIndex_lt_eight _ _ _)
      ((noirHintConstraint_iff _ _ _ _ _).mp hint) ((noirHintConstraint_iff _ _ _ _ _).mp hint'))

/-- The Noir check returns `true` exactly for prime-order-subgroup points,
under the pairing model `TateEncodingLaws` of the Solidity development. -/
theorem noir_tate_check_iff_prime_order_subgroup (fermat : FermatLittle)
    (p : Affine) (index : FullGroupPoint) (laws : TateEncodingLaws p index)
    (r : Nat) (k0 k1 k2 : Bool)
    (hint : noirHintConstraint (noirTateMillerValue p) r k0 k1 k2) :
    noirCheckSubGroupTate p k0 k1 k2 = true ↔ InPrimeOrderSubgroup index :=
  (noir_tate_check_iff_solidity_tate_accepts fermat p laws.on_curve r k0 k1 k2 hint).trans
    (solidity_tate_accepts_iff_prime_order_subgroup p index laws)

/-- The Noir check is equivalent to the canonical `[R]P = 0` order check that
`check_sub_group` implements. -/
theorem noir_tate_check_iff_canonical_order_check (fermat : FermatLittle)
    (p : Affine) (index : FullGroupPoint) (laws : TateEncodingLaws p index)
    (r : Nat) (k0 k1 k2 : Bool)
    (hint : noirHintConstraint (noirTateMillerValue p) r k0 k1 k2) :
    noirCheckSubGroupTate p k0 k1 k2 = true ↔ canonicalOrderCheck index :=
  (noir_tate_check_iff_prime_order_subgroup fermat p index laws r k0 k1 k2 hint).trans
    (canonical_order_check_iff_prime_subgroup index).symm

/-! ## Concrete hints

Non-vacuity witnesses: the constraint is satisfiable, with the expected
result, at a point inside the prime-order subgroup (`k = 0`) and at one outside
it (`k = 7`). -/

def BasePointHintRoot : Nat :=
  13550258995021343809776910267135869298880814746809421608406117968616183275607

def FullGeneratorHintRoot : Nat :=
  8863687884574099614761066814133871052478637731884319884208887704968832392253

theorem base_point_hint_accepted :
    noirHintConstraint (noirTateMillerValue generator) BasePointHintRoot false false false ∧
      noirCheckSubGroupTate generator false false false = true := by
  unfold noirHintConstraint
  native_decide

theorem full_generator_hint_rejected :
    noirHintConstraint (noirTateMillerValue fullGenerator) FullGeneratorHintRoot true true true ∧
      noirCheckSubGroupTate fullGenerator true true true = false := by
  unfold noirHintConstraint
  native_decide

/-- A zero Miller value admits the hint `r = 0` for every `k`, which is why the
circuit checks `m != 0` separately; the result is `false` regardless. -/
theorem torsion_point_zero_hint_rejected :
    ∀ p ∈ nonidentityTorsionPoints, ∀ k0 k1 k2 : Bool,
      noirTateMillerValue p = 0 →
        noirHintConstraint (noirTateMillerValue p) 0 k0 k1 k2 ∧
          noirCheckSubGroupTate p k0 k1 k2 = false := by
  intro p hp k0 k1 k2 hm
  have hy : p.y ≠ 1 := by
    simp [nonidentityTorsionPoints] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide
  constructor
  · rw [noirHintConstraint_iff, hm]
    simp
  · simp [noirCheckSubGroupTate, hy, hm]

end BabyJubJub.NoirTateProof
