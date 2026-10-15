module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Gauss and Jacobi sums of a sextic character of a finite field

The finite-field identities used in the proof of the lemma on the Gauss correction characters
(`lem:gauss-characters` in `verification/stage7-sources/A-02.tex`): the cubic Gauss--Jacobi
relations `eq:cubic-jacobi` (lines 438--454) and the sextic duplication factor (lines 575--594).

Throughout, `k` is a finite field with `Q = Fintype.card k` elements, `χ` is a multiplicative
character of `k` of exact order six (`orderOf χ = 6`) and `ψ` is a primitive additive character
of `k` (`ψ.IsPrimitive`; on a field this is the same as `ψ ≠ 1`). In the notation of the paper

* `G_j = ∑ x, χ(x)^j ψ(x)` is `gaussSum (χ ^ j) ψ`,
* `J(α, β) = ∑ x, α(x) β(1 - x)` is `jacobiSum α β`,
* `ρ = χ²` is `χ ^ 2` and `φ = χ³` is `χ ^ 3`.

The characters take values in an arbitrary commutative domain `R` for the identities without
denominators, and in an arbitrary field `K` for the identities containing `χ(4)⁻¹`. The paper works
over `ℂ`, where `χ(4)⁻¹` is the complex conjugate `\overline{χ(4)}`
(`inv_mulChar_apply_eq_conj`); the three identities containing `\overline{χ(4)}` are restated in
that form at the end of the file.

The only hypotheses are `orderOf χ = 6` and `ψ.IsPrimitive`. Everything else is derived from them:
the powers `χ ^ j`, `0 < j < 6`, are nontrivial, the characteristic of `k` is odd, `χ(4) ≠ 0`,
`Q ≠ 0` in the target, and `χ ^ 3` is the quadratic character of `k`.

## Dictionary with the paper

Preliminaries.
* `mulChar_sq_apply_neg_one`: `ρ(-1) = 1`, the fact used for the first equality of
  `eq:cubic-jacobi`.
* `mulChar_apply_neg_one_pow_three`, `mulChar_pow_three_apply_neg_one`: `χ(-1)³ = χ(-1) = φ(-1)`.
* `six_dvd_card_sub_one_of_orderOf_eq_six`, `ringChar_ne_two_of_orderOf_eq_six`: a character of
  exact order six forces `6 ∣ Q - 1`, so the characteristic of `k` is odd.
* `natCast_card_ne_zero_of_isPrimitive`: `Q ≠ 0` in the target (automatic over `ℂ`).

The cubic relations `eq:cubic-jacobi`.
* `sextic_gaussSum_two_mul_gaussSum_four`: `G₂ G₄ = Q`.
* `sextic_gaussSum_two_sq`: `G₂² = J(ρ, ρ) G₄`.
* `sextic_gaussSum_two_cube`: `G₂³ = Q J(ρ, ρ)`, the unnormalized form of
  `(Q^{-1/2} G₂)³ = Q^{-1/2} J(ρ, ρ)`.
* `sextic_gaussSum_two_cube_mulShift`: replacing `ψ(x)` by `ψ(a x)` for a unit `a` does not
  change `G₂³`; `sextic_gaussSum_two_cube_eq_of_isPrimitive`: `G₂³` is the same for all primitive
  additive characters.

The sextic duplication factor.
* `four_mul_jacobiSum_self_eq_sum`: completing the square, `χ(4) J(χ, χ) = ∑ t, χ(1 - t²)`.
* `sum_one_sub_sq_eq_jacobiSum_quadraticChar`: counting square roots,
  `∑ t, χ(1 - t²) = J(φ, χ)`, where the part without `φ` vanishes because `χ` is nontrivial.
* `sextic_jacobiSum_self`: `J(χ, χ) = χ(4)⁻¹ J(φ, χ)` (denominator-free:
  `sextic_four_mul_jacobiSum_self`).
* `sextic_gaussSum_one_mul_gaussSum_four`: `G₁ G₄ = χ(4)⁻¹ G₂ G₃` (denominator-free:
  `sextic_four_mul_gaussSum_one_mul_gaussSum_four`).
* `sextic_card_mul_gaussSum_one_mul_gaussSum_two`: `Q G₁ G₂ = χ(4)⁻¹ G₃ G₂³`, the unnormalized
  form of `γ₁ γ₂ = \overline{χ(4)} γ₃ γ₂³` (denominator-free:
  `sextic_four_mul_card_mul_gaussSum_one_mul_gaussSum_two`).
* `sextic_gaussSum_three_sq`: `G₃² = χ(-1)³ Q`, the unnormalized form of `γ₃² = χ(-1)³`; and
  `sextic_gaussSum_three_sq_eq_card`: `G₃² = Q` when `4 ∣ Q - 1`, where `χ(-1) = 1`
  (`sextic_apply_neg_one_eq_one`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

/-! ### Elements of order six -/

section OrderSix

variable {G : Type*} [Monoid G] {x : G}

/-- The sixth power of an element of order six is trivial. -/
theorem pow_six_eq_one_of_orderOf_eq_six (hx : orderOf x = 6) : x ^ 6 = 1 :=
  hx ▸ pow_orderOf_eq_one x

/-- The powers `x`, `x²`, `x³`, `x⁴`, `x⁵` of an element of order six are nontrivial. -/
theorem pow_ne_one_of_orderOf_eq_six (hx : orderOf x = 6) {n : ℕ} (hn0 : n ≠ 0) (hn : n < 6) :
    x ^ n ≠ 1 :=
  pow_ne_one_of_lt_orderOf hn0 (hx ▸ hn)

/-- An element of order six is nontrivial. -/
theorem ne_one_of_orderOf_eq_six (hx : orderOf x = 6) : x ≠ 1 := by
  simpa using pow_ne_one_of_orderOf_eq_six hx one_ne_zero (by norm_num)

end OrderSix

/-! ### Values of multiplicative characters at `-1` -/

section NegOne

variable {k : Type*} [CommRing k] {R : Type*} [CommRing R]

/-- An even power of a multiplicative character takes the value `1` at `-1`. -/
theorem mulChar_pow_apply_neg_one_of_even (χ : MulChar k R) {n : ℕ} (hn : Even n) :
    (χ ^ n) (-1) = 1 := by
  rcases eq_or_ne n 0 with rfl | h
  · rw [pow_zero]
    exact MulChar.one_apply_coe (-1)
  · rw [MulChar.pow_apply' χ h, ← map_pow, hn.neg_one_pow, map_one]

/-- `ρ(-1) = 1` for the square `ρ = χ²` of a multiplicative character. -/
theorem mulChar_sq_apply_neg_one (χ : MulChar k R) : (χ ^ 2) (-1) = 1 :=
  mulChar_pow_apply_neg_one_of_even χ even_two

/-- `χ(-1)² = 1`. -/
theorem mulChar_apply_neg_one_sq (χ : MulChar k R) : χ (-1) ^ 2 = 1 := by
  rw [← map_pow, neg_one_sq, map_one]

/-- `χ(-1)³ = χ(-1)`. -/
theorem mulChar_apply_neg_one_pow_three (χ : MulChar k R) : χ (-1) ^ 3 = χ (-1) := by
  rw [pow_succ, mulChar_apply_neg_one_sq, one_mul]

/-- `χ³(-1) = χ(-1)³`. -/
theorem mulChar_pow_three_apply_neg_one (χ : MulChar k R) : (χ ^ 3) (-1) = χ (-1) ^ 3 :=
  MulChar.pow_apply' χ three_ne_zero (-1)

end NegOne

/-! ### Nontrivial additive characters and the size of the field -/

section Card

variable {k : Type*} [Field k] [Fintype k] {R : Type*} [CommRing R] [IsDomain R]

/-- If a finite field `k` has a nontrivial additive character with values in a domain `R`, then
the number of elements of `k` is not zero in `R`: otherwise `R` has the characteristic `p` of `k`,
and the values of the character, being `p`-th roots of unity, are all `1`. -/
theorem natCast_card_ne_zero_of_addChar_ne_one {ψ : AddChar k R} (hψ : ψ ≠ 1) :
    (Fintype.card k : R) ≠ 0 := by
  intro h
  obtain ⟨n, hp, hc⟩ := FiniteField.card k (ringChar k)
  have hp0 : ((ringChar k : ℕ) : R) = 0 := by
    rw [hc, Nat.cast_pow] at h
    exact (pow_eq_zero_iff n.ne_zero).mp h
  have : Fact (ringChar k).Prime := ⟨hp⟩
  have : CharP R (ringChar k) := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
  refine hψ ?_
  ext x
  rw [AddChar.one_apply]
  have h1 : ψ x ^ ringChar k = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
      AddChar.map_zero_eq_one]
  have h2 : (ψ x - 1) ^ ringChar k = 0 := by rw [sub_pow_char, h1, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp h2)

/-- If a finite field `k` has a primitive additive character with values in a domain `R`, then
the number of elements of `k` is not zero in `R`. -/
theorem natCast_card_ne_zero_of_isPrimitive {ψ : AddChar k R} (hψ : ψ.IsPrimitive) :
    (Fintype.card k : R) ≠ 0 :=
  natCast_card_ne_zero_of_addChar_ne_one (ψ := ψ) fun h =>
    hψ one_ne_zero (by rw [AddChar.mulShift_one, h])

end Card

/-! ### The duplication formula for Jacobi sums -/

section Duplication

variable {k : Type*} [Field k] [Fintype k] {R : Type*} [CommRing R]

/-- Completing the square, `4 x (1 - x) = 1 - (2 x - 1)²`: in odd characteristic
`χ(4) J(χ, χ) = ∑ t, χ(1 - t²)`. -/
theorem four_mul_jacobiSum_self_eq_sum (hk : ringChar k ≠ 2) (χ : MulChar k R) :
    χ 4 * jacobiSum χ χ = ∑ t : k, χ (1 - t ^ 2) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  rw [jacobiSum, Finset.mul_sum]
  refine Fintype.sum_equiv ((Equiv.mulLeft₀ (2 : k) h2).trans (Equiv.subRight 1)) _ _ fun x => ?_
  rw [← map_mul, ← map_mul]
  congr 1
  simp only [Equiv.trans_apply, Equiv.mulLeft₀_apply, Equiv.subRight_apply]
  ring

variable [IsDomain R]

/-- A nontrivial multiplicative character of a finite field whose square is trivial is the
quadratic character (with its values `0`, `1`, `-1` read in `R`). -/
theorem mulChar_eq_quadraticChar_of_sq_eq_one [DecidableEq k] {φ : MulChar k R} (hφ : φ ≠ 1)
    (hφ2 : φ ^ 2 = 1) : φ = (quadraticChar k).ringHomComp (Int.castRingHom R) := by
  -- `φ` is `1` on nonzero squares
  have hsq : ∀ b : k, b ≠ 0 → φ (b * b) = 1 := by
    intro b hb
    rw [← pow_two, map_pow, ← MulChar.pow_apply' φ two_ne_zero, hφ2,
      MulChar.one_apply (Ne.isUnit hb)]
  -- a unit `a₀` with `φ a₀ = -1`; it is not a square
  obtain ⟨a₀, ha₀⟩ := MulChar.ne_one_iff.mp hφ
  have ha₀sq : φ a₀ ^ 2 = 1 := by
    rw [← MulChar.pow_apply' φ two_ne_zero, hφ2, MulChar.one_apply_coe]
  have ha₀' : φ a₀ = -1 := (sq_eq_one_iff.mp ha₀sq).resolve_left ha₀
  have ha₀ns : ¬ IsSquare (a₀ : k) := by
    rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
    exact ha₀ (by rw [hb]; exact hsq b hb0)
  ext a
  rw [MulChar.ringHomComp_apply, eq_intCast]
  by_cases h : IsSquare (a : k)
  · obtain ⟨b, hb⟩ := h
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
    rw [(quadraticChar_one_iff_isSquare a.ne_zero).mpr ⟨b, hb⟩, Int.cast_one, hb]
    exact hsq b hb0
  · -- the product of the two nonsquares `a` and `a₀` is a square
    rw [quadraticChar_neg_one_iff_not_isSquare.mpr h, Int.cast_neg, Int.cast_one]
    have hsq' : IsSquare ((a : k) * a₀) := by
      rw [← quadraticChar_one_iff_isSquare (mul_ne_zero a.ne_zero a₀.ne_zero), map_mul,
        quadraticChar_neg_one_iff_not_isSquare.mpr h,
        quadraticChar_neg_one_iff_not_isSquare.mpr ha₀ns]
      norm_num
    obtain ⟨b, hb⟩ := hsq'
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
    have h1 := hsq b hb0
    rw [← hb, map_mul, ha₀', mul_neg, mul_one, neg_eq_iff_eq_neg] at h1
    exact h1

/-- Counting square roots: for a nontrivial character `χ` of a finite field of odd
characteristic, `∑ t, χ(1 - t²) = J(φ, χ)` with the quadratic character `φ`. The element `u` has
`1 + φ(u)` square roots, and the part of the sum without `φ` is `∑ u, χ(1 - u) = 0`. -/
theorem sum_one_sub_sq_eq_jacobiSum_quadraticChar [DecidableEq k] (hk : ringChar k ≠ 2)
    {χ : MulChar k R} (hχ : χ ≠ 1) :
    ∑ t : k, χ (1 - t ^ 2) =
      jacobiSum ((quadraticChar k).ringHomComp (Int.castRingHom R)) χ := by
  have hcount : ∀ u : k, (((Finset.univ.filter fun t : k => t ^ 2 = u).card : ℕ) : R) =
      ((quadraticChar k u : ℤ) : R) + 1 := by
    intro u
    have h := congrArg (Int.cast : ℤ → R) (quadraticChar_card_sqrts hk u)
    rw [Set.toFinset_ofPred] at h
    push_cast at h
    exact h
  have hzero : ∑ u : k, χ (1 - u) = 0 :=
    ((Equiv.subLeft (1 : k)).sum_comp (fun u => χ u)).trans (MulChar.sum_eq_zero_of_ne_one hχ)
  calc ∑ t : k, χ (1 - t ^ 2)
      = ∑ u : k, ∑ t : k with t ^ 2 = u, χ (1 - u) :=
        (Finset.sum_fiberwise' Finset.univ (fun t : k => t ^ 2) (fun u => χ (1 - u))).symm
    _ = ∑ u : k, (((quadraticChar k u : ℤ) : R) + 1) * χ (1 - u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, hcount]
    _ = ∑ u : k, ((quadraticChar k u : ℤ) : R) * χ (1 - u) + ∑ u : k, χ (1 - u) := by
        simp only [add_mul, one_mul, Finset.sum_add_distrib]
    _ = jacobiSum ((quadraticChar k).ringHomComp (Int.castRingHom R)) χ := by
        rw [hzero, add_zero]
        rfl

/-- **Duplication formula for Jacobi sums** over a finite field of odd characteristic:
`χ(4) J(χ, χ) = J(φ, χ)` for a nontrivial character `χ` and the quadratic character `φ`. -/
theorem four_mul_jacobiSum_self_eq_jacobiSum_quadraticChar [DecidableEq k] (hk : ringChar k ≠ 2)
    {χ : MulChar k R} (hχ : χ ≠ 1) :
    χ 4 * jacobiSum χ χ = jacobiSum ((quadraticChar k).ringHomComp (Int.castRingHom R)) χ :=
  (four_mul_jacobiSum_self_eq_sum hk χ).trans (sum_one_sub_sq_eq_jacobiSum_quadraticChar hk hχ)

end Duplication

/-! ### Characters of exact order six: identities without denominators -/

section Sextic

variable {k : Type*} [Field k] {R : Type*} [CommRing R] {χ : MulChar k R}

/-- A multiplicative character of exact order six forces `6 ∣ Q - 1`. -/
theorem six_dvd_card_sub_one_of_orderOf_eq_six [Fintype k] (hχ : orderOf χ = 6) :
    6 ∣ Fintype.card k - 1 :=
  hχ ▸ MulChar.orderOf_dvd_card_sub_one k χ

/-- A finite field with a multiplicative character of exact order six has odd characteristic. -/
theorem ringChar_ne_two_of_orderOf_eq_six [Finite k] (hχ : orderOf χ = 6) : ringChar k ≠ 2 := by
  cases nonempty_fintype k
  intro h
  have h6 := six_dvd_card_sub_one_of_orderOf_eq_six hχ
  have h2 := FiniteField.even_card_of_char_two h
  have h1 : 1 < Fintype.card k := Fintype.one_lt_card
  omega

variable [Fintype k]

/-- If `4 ∣ Q - 1` (for instance if `Q ≡ 1 (mod 12)`), then `χ(-1) = 1` for a character with
`χ⁶ = 1`: `-1 = i²` is a square, so `χ(-1) = χ(-1)³ = χ(i)⁶ = 1`. -/
theorem sextic_apply_neg_one_eq_one (hχ : χ ^ 6 = 1) (h4 : 4 ∣ Fintype.card k - 1) :
    χ (-1) = 1 := by
  have h1 : 1 < Fintype.card k := Fintype.one_lt_card
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.mpr (show Fintype.card k % 4 ≠ 3 by omega)
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  calc χ (-1) = χ (-1) ^ 3 := (mulChar_apply_neg_one_pow_three χ).symm
    _ = χ i ^ 6 := by rw [hi, map_mul, ← pow_two, ← pow_mul]
    _ = 1 := by rw [← MulChar.pow_apply' χ (by norm_num), hχ, MulChar.one_apply (Ne.isUnit hi0)]

/-- Replacing `ψ(x)` by `ψ(a x)` multiplies `G₂` by `ρ(a)⁻¹`, a cube root of unity: the cube
`G₂³` does not change. -/
theorem sextic_gaussSum_two_cube_mulShift (hχ : orderOf χ = 6) (ψ : AddChar k R) (a : kˣ) :
    gaussSum (χ ^ 2) (ψ.mulShift a) ^ 3 = gaussSum (χ ^ 2) ψ ^ 3 := by
  have h6 : (χ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul]
    exact pow_six_eq_one_of_orderOf_eq_six hχ
  have h1 : (χ ^ 2) (a : k) ^ 3 = 1 := by
    rw [← MulChar.pow_apply_coe, h6, MulChar.one_apply_coe]
  rw [← gaussSum_mulShift (χ ^ 2) ψ a, mul_pow, h1, one_mul]

variable [IsDomain R]

/-- The Gauss sums `G_j`, `0 < j < 6`, of a sextic character do not vanish. -/
theorem sextic_gaussSum_ne_zero (hχ : orderOf χ = 6) {ψ : AddChar k R} (hψ : ψ.IsPrimitive)
    {j : ℕ} (hj0 : j ≠ 0) (hj : j < 6) : gaussSum (χ ^ j) ψ ≠ 0 :=
  gaussSum_ne_zero_of_nontrivial (natCast_card_ne_zero_of_isPrimitive hψ)
    (pow_ne_one_of_orderOf_eq_six hχ hj0 hj) hψ

/-- **Gauss inversion** `G₂ G₄ = Q`, the first equality of `eq:cubic-jacobi`. It uses
`ρ(-1) = 1`. -/
theorem sextic_gaussSum_two_mul_gaussSum_four (hχ : orderOf χ = 6) {ψ : AddChar k R}
    (hψ : ψ.IsPrimitive) :
    gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 4) ψ = Fintype.card k := by
  have h4 : χ ^ 4 = (χ ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_add]; exact pow_six_eq_one_of_orderOf_eq_six hχ)
  rw [← mul_gaussSum_inv_eq_gaussSum (χ ^ 4) ψ,
    mulChar_pow_apply_neg_one_of_even χ (by decide), one_mul, h4]
  exact gaussSum_mul_gaussSum_eq_card
    (pow_ne_one_of_orderOf_eq_six hχ two_ne_zero (by norm_num)) hψ

/-- **Gauss--Jacobi identity** `G₂² = J(ρ, ρ) G₄`, the second equality of `eq:cubic-jacobi`. -/
theorem sextic_gaussSum_two_sq (hχ : orderOf χ = 6) (ψ : AddChar k R) :
    gaussSum (χ ^ 2) ψ ^ 2 = jacobiSum (χ ^ 2) (χ ^ 2) * gaussSum (χ ^ 4) ψ := by
  have h22 : χ ^ 2 * χ ^ 2 = χ ^ 4 := (pow_add χ 2 2).symm
  have h4 : χ ^ 2 * χ ^ 2 ≠ 1 := by
    rw [h22]
    exact pow_ne_one_of_orderOf_eq_six hχ four_ne_zero (by norm_num)
  have h := jacobiSum_mul_nontrivial h4 ψ
  rw [h22] at h
  rw [pow_two, ← h, mul_comm]

/-- `G₂³ = Q J(ρ, ρ)`, the third equality `(Q^{-1/2} G₂)³ = Q^{-1/2} J(ρ, ρ)` of
`eq:cubic-jacobi` multiplied by `Q^{3/2}`. -/
theorem sextic_gaussSum_two_cube (hχ : orderOf χ = 6) {ψ : AddChar k R} (hψ : ψ.IsPrimitive) :
    gaussSum (χ ^ 2) ψ ^ 3 = Fintype.card k * jacobiSum (χ ^ 2) (χ ^ 2) := by
  have h2 := sextic_gaussSum_two_mul_gaussSum_four hχ hψ
  have h3 := sextic_gaussSum_two_sq hχ ψ
  linear_combination gaussSum (χ ^ 2) ψ * h3 + jacobiSum (χ ^ 2) (χ ^ 2) * h2

/-- The cube `G₂³` is independent of the primitive additive character. -/
theorem sextic_gaussSum_two_cube_eq_of_isPrimitive (hχ : orderOf χ = 6) {ψ ψ' : AddChar k R}
    (hψ : ψ.IsPrimitive) (hψ' : ψ'.IsPrimitive) :
    gaussSum (χ ^ 2) ψ ^ 3 = gaussSum (χ ^ 2) ψ' ^ 3 := by
  rw [sextic_gaussSum_two_cube hχ hψ, sextic_gaussSum_two_cube hχ hψ']

/-- The cube `φ = χ³` of a sextic character is the quadratic character of `k`. -/
theorem sextic_pow_three_eq_quadraticChar [DecidableEq k] (hχ : orderOf χ = 6) :
    χ ^ 3 = (quadraticChar k).ringHomComp (Int.castRingHom R) :=
  mulChar_eq_quadraticChar_of_sq_eq_one
    (pow_ne_one_of_orderOf_eq_six hχ three_ne_zero (by norm_num))
    (by rw [← pow_mul]; exact pow_six_eq_one_of_orderOf_eq_six hχ)

/-- **Sextic duplication for Jacobi sums**, without denominators: `χ(4) J(χ, χ) = J(φ, χ)`. -/
theorem sextic_four_mul_jacobiSum_self (hχ : orderOf χ = 6) :
    χ 4 * jacobiSum χ χ = jacobiSum (χ ^ 3) χ := by
  classical
  rw [sextic_pow_three_eq_quadraticChar hχ]
  exact four_mul_jacobiSum_self_eq_jacobiSum_quadraticChar
    (ringChar_ne_two_of_orderOf_eq_six hχ) (ne_one_of_orderOf_eq_six hχ)

/-- **Sextic duplication for Gauss sums**, without denominators: `χ(4) G₁ G₄ = G₂ G₃`. Apply the
Gauss--Jacobi identity to both sides of `χ(4) J(χ, χ) = J(φ, χ)` and cancel `G₁ ≠ 0`. -/
theorem sextic_four_mul_gaussSum_one_mul_gaussSum_four (hχ : orderOf χ = 6) {ψ : AddChar k R}
    (hψ : ψ.IsPrimitive) :
    χ 4 * (gaussSum χ ψ * gaussSum (χ ^ 4) ψ) = gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 3) ψ := by
  have h11 : χ * χ = χ ^ 2 := (pow_two χ).symm
  have h31 : χ ^ 3 * χ = χ ^ 4 := (pow_succ χ 3).symm
  -- `G₂ J(χ, χ) = G₁ G₁`
  have hA := jacobiSum_mul_nontrivial (χ := χ) (φ := χ)
    (by rw [h11]; exact pow_ne_one_of_orderOf_eq_six hχ two_ne_zero (by norm_num)) ψ
  -- `G₄ J(φ, χ) = G₃ G₁`
  have hB := jacobiSum_mul_nontrivial (χ := χ ^ 3) (φ := χ)
    (by rw [h31]; exact pow_ne_one_of_orderOf_eq_six hχ four_ne_zero (by norm_num)) ψ
  rw [h11] at hA
  rw [h31] at hB
  have hJ := sextic_four_mul_jacobiSum_self hχ
  have hG : gaussSum χ ψ ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial (natCast_card_ne_zero_of_isPrimitive hψ)
      (ne_one_of_orderOf_eq_six hχ) hψ
  refine mul_left_cancel₀ hG ?_
  linear_combination (-(χ 4 * gaussSum (χ ^ 4) ψ)) * hA + gaussSum (χ ^ 2) ψ * hB +
    (gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 4) ψ) * hJ

/-- `χ(4) Q G₁ G₂ = G₃ G₂³`, without denominators: combine `χ(4) G₁ G₄ = G₂ G₃` with
`G₂ G₄ = Q`. -/
theorem sextic_four_mul_card_mul_gaussSum_one_mul_gaussSum_two (hχ : orderOf χ = 6)
    {ψ : AddChar k R} (hψ : ψ.IsPrimitive) :
    χ 4 * ((Fintype.card k : R) * (gaussSum χ ψ * gaussSum (χ ^ 2) ψ)) =
      gaussSum (χ ^ 3) ψ * gaussSum (χ ^ 2) ψ ^ 3 := by
  have h2 := sextic_gaussSum_two_mul_gaussSum_four hχ hψ
  have h6 := sextic_four_mul_gaussSum_one_mul_gaussSum_four hχ hψ
  linear_combination gaussSum (χ ^ 2) ψ ^ 2 * h6 -
    χ 4 * (gaussSum χ ψ * gaussSum (χ ^ 2) ψ) * h2

/-- **Gauss inversion for the quadratic character** `φ = χ³`: `G₃² = χ(-1)³ Q`. -/
theorem sextic_gaussSum_three_sq (hχ : orderOf χ = 6) {ψ : AddChar k R} (hψ : ψ.IsPrimitive) :
    gaussSum (χ ^ 3) ψ ^ 2 = χ (-1) ^ 3 * Fintype.card k := by
  have hq : (χ ^ 3).IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr
    (by rw [← pow_mul]; exact pow_six_eq_one_of_orderOf_eq_six hχ)
  rw [gaussSum_sq (pow_ne_one_of_orderOf_eq_six hχ three_ne_zero (by norm_num)) hq hψ,
    MulChar.pow_apply' χ three_ne_zero]

/-- `G₃² = Q` when `4 ∣ Q - 1`, where `χ(-1) = 1`. -/
theorem sextic_gaussSum_three_sq_eq_card (hχ : orderOf χ = 6) (h4 : 4 ∣ Fintype.card k - 1)
    {ψ : AddChar k R} (hψ : ψ.IsPrimitive) :
    gaussSum (χ ^ 3) ψ ^ 2 = Fintype.card k := by
  rw [sextic_gaussSum_three_sq hχ hψ,
    sextic_apply_neg_one_eq_one (pow_six_eq_one_of_orderOf_eq_six hχ) h4, one_pow, one_mul]

end Sextic

/-! ### Characters of exact order six with values in a field -/

section SexticField

variable {k : Type*} [Field k] {K : Type*} [Field K] {χ : MulChar k K}

/-- `χ(4) ≠ 0`: the characteristic is odd, so `4` is a unit. -/
theorem sextic_apply_four_ne_zero [Finite k] (hχ : orderOf χ = 6) : χ 4 ≠ 0 := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_orderOf_eq_six hχ)
  have h4 : (4 : k) ≠ 0 := by
    have h : (4 : k) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  exact MulChar.apply_ne_zero_iff.mpr (Ne.isUnit h4)

variable [Fintype k]

/-- **Sextic duplication for Jacobi sums**: `J(χ, χ) = χ(4)⁻¹ J(φ, χ)` with `φ = χ³`. -/
theorem sextic_jacobiSum_self (hχ : orderOf χ = 6) :
    jacobiSum χ χ = (χ 4)⁻¹ * jacobiSum (χ ^ 3) χ := by
  rw [eq_inv_mul_iff_mul_eq₀ (sextic_apply_four_ne_zero hχ)]
  exact sextic_four_mul_jacobiSum_self hχ

/-- **Sextic duplication for Gauss sums**: `G₁ G₄ = χ(4)⁻¹ G₂ G₃`. -/
theorem sextic_gaussSum_one_mul_gaussSum_four (hχ : orderOf χ = 6) {ψ : AddChar k K}
    (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ 4) ψ =
      (χ 4)⁻¹ * gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 3) ψ := by
  rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ (sextic_apply_four_ne_zero hχ)]
  exact sextic_four_mul_gaussSum_one_mul_gaussSum_four hχ hψ

/-- `Q G₁ G₂ = χ(4)⁻¹ G₃ G₂³`, the identity `γ₁ γ₂ = \overline{χ(4)} γ₃ γ₂³` for the normalized
sums `γ_j = Q^{-1/2} G_j` multiplied by `Q²`. -/
theorem sextic_card_mul_gaussSum_one_mul_gaussSum_two (hχ : orderOf χ = 6) {ψ : AddChar k K}
    (hψ : ψ.IsPrimitive) :
    (Fintype.card k : K) * (gaussSum χ ψ * gaussSum (χ ^ 2) ψ) =
      (χ 4)⁻¹ * gaussSum (χ ^ 3) ψ * gaussSum (χ ^ 2) ψ ^ 3 := by
  rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ (sextic_apply_four_ne_zero hχ)]
  exact sextic_four_mul_card_mul_gaussSum_one_mul_gaussSum_two hχ hψ

end SexticField

/-! ### Complex-valued characters: `χ(4)⁻¹` is the complex conjugate of `χ(4)` -/

section Complex

/-- For a complex-valued multiplicative character of a ring with finitely many units, `χ(a)⁻¹`
is the complex conjugate of `χ(a)`: the nonzero values of `χ` are roots of unity. -/
theorem inv_mulChar_apply_eq_conj {A : Type*} [CommRing A] [Finite Aˣ] (χ : MulChar A ℂ)
    (a : A) : (χ a)⁻¹ = (starRingEnd ℂ) (χ a) := by
  rw [← MulChar.inv_apply_eq_inv', ← MulChar.star_apply', RCLike.star_def]

variable {k : Type*} [Field k] [Fintype k] {χ : MulChar k ℂ}

/-- `J(χ, χ) = \overline{χ(4)} J(φ, χ)`. -/
theorem sextic_jacobiSum_self_conj (hχ : orderOf χ = 6) :
    jacobiSum χ χ = (starRingEnd ℂ) (χ 4) * jacobiSum (χ ^ 3) χ := by
  rw [← inv_mulChar_apply_eq_conj]
  exact sextic_jacobiSum_self hχ

/-- `G₁ G₄ = \overline{χ(4)} G₂ G₃`. -/
theorem sextic_gaussSum_one_mul_gaussSum_four_conj (hχ : orderOf χ = 6) {ψ : AddChar k ℂ}
    (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ 4) ψ =
      (starRingEnd ℂ) (χ 4) * gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 3) ψ := by
  rw [← inv_mulChar_apply_eq_conj]
  exact sextic_gaussSum_one_mul_gaussSum_four hχ hψ

/-- `Q G₁ G₂ = \overline{χ(4)} G₃ G₂³`. -/
theorem sextic_card_mul_gaussSum_one_mul_gaussSum_two_conj (hχ : orderOf χ = 6)
    {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) :
    (Fintype.card k : ℂ) * (gaussSum χ ψ * gaussSum (χ ^ 2) ψ) =
      (starRingEnd ℂ) (χ 4) * gaussSum (χ ^ 3) ψ * gaussSum (χ ^ 2) ψ ^ 3 := by
  rw [← inv_mulChar_apply_eq_conj]
  exact sextic_card_mul_gaussSum_one_mul_gaussSum_two hχ hψ

end Complex

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
