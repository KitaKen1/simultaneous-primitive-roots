/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Robert Y. Lewis, Matthew Robert Ballard
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2,
   Mathlib/Data/Nat/Factorization/Defs.lean and
   Mathlib/NumberTheory/Padics/PadicVal/Basic.lean, for Lean/Mathlib v4.33.1. -/
module

public import Compat4331.NatSquares
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace Int

/-- The integer `n` is a square if and only if it is nonnegative,
and for any `p`, the power of `p` in `|n|` is even. -/
theorem isSquare_iff_nonneg_even_factorization {n : ℤ} :
    IsSquare n ↔ 0 ≤ n ∧ ∀ (p : ℕ), p.Prime → Even (n.natAbs.factorization p) := by
  constructor
  · intro ⟨m, hmn⟩
    refine ⟨by rw [hmn]; exact mul_self_nonneg m, fun p hp ↦ ?_⟩
    exact Nat.isSquare_iff_even_factorization.mp ⟨m.natAbs, by rw [hmn, Int.natAbs_mul]⟩ p hp
  · intro ⟨h0, h⟩
    obtain ⟨r, hr⟩ := Nat.isSquare_iff_even_factorization.mpr h
    exact ⟨r, (by rw [← natAbs_of_nonneg h0, hr, Nat.cast_mul])⟩

end Int

namespace Rat

/-- The numerator or denominator of a rational number has zero `p`-adic valuation. -/
theorem num_or_den_zero_padicVal (a : ℚ) {p : ℕ} (hp : p.Prime) :
    padicValInt p a.num = 0 ∨ padicValNat p a.den = 0 := by
  have h := a.reduced
  contrapose! h
  apply Nat.not_coprime_of_dvd_of_dvd hp.one_lt
  · by_contra hnum
    exact h.1 (by simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnum)
  · by_contra hden
    exact h.2 (padicValNat.eq_zero_of_not_dvd hden)

/-- The numerator and denominator of a rational number with even `p`-adic valuation
also have even `p`-adic valuation. -/
theorem num_den_even_padicVal_of_even_padicVal {a : ℚ} {p : ℕ} (hp : p.Prime)
    (h : Even (padicValRat p a)) : Even (padicValInt p a.num) ∧ Even (padicValNat p a.den) := by
  rcases num_or_den_zero_padicVal a hp with (h0 | h0) <;>
    simpa [h0, padicValRat_def] using h

/-- A rational number is a square if and only if it is nonnegative,
and has even `p`-adic valuation for all `p`. -/
theorem isSquare_iff_even_factorization {a : ℚ} :
    IsSquare a ↔ 0 ≤ a ∧ ∀ (p : ℕ), p.Prime → Even (padicValRat p a) := by
  constructor
  · refine fun ⟨r, hr⟩ ↦ ⟨by simpa [hr] using mul_self_nonneg r, fun p hp ↦ ?_⟩
    have : Fact (p.Prime) := ⟨hp⟩
    rw [hr]
    by_cases hr0 : r = 0
    · simp [hr0]
    simp [padicValRat.mul hr0 hr0]
  · intro ⟨hR, hf⟩
    rw [isSquare_iff]
    constructor
    · refine Int.isSquare_iff_nonneg_even_factorization.mpr ⟨num_nonneg.mpr hR, fun p hp ↦ ?_⟩
      have num_even := (num_den_even_padicVal_of_even_padicVal hp (hf p hp)).1
      simpa [Nat.factorization_def _ hp, padicValInt] using num_even
    · refine Nat.isSquare_iff_even_factorization.mpr (fun p hp ↦ ?_)
      have den_even := (num_den_even_padicVal_of_even_padicVal hp (hf p hp)).2
      rwa [Nat.factorization_def _ hp]

end Rat
