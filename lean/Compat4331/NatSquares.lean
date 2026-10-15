/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
/- Backport from Mathlib f6090c7 for Lean/Mathlib v4.33.1. -/
module
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Tactic

public section
namespace Nat
/-- `n` is a square if and only if for any prime `p`, the power of `p` in `n` is even. -/
theorem isSquare_iff_even_factorization {n : ℕ} :
    IsSquare n ↔ ∀ (p : ℕ), p.Prime → Even (n.factorization p) := by
  by_cases h0 : n = 0
  · simp [h0]
  constructor
  · intro ⟨m, hmn⟩ p hp
    have hm : m ≠ 0 := mul_self_ne_zero.mp (hmn ▸ h0)
    simp [hmn, factorization_mul hm hm]
  · refine fun h ↦ ⟨n.factorization.prod fun a b ↦ a ^ (b / 2), ?_⟩
    rw [← pow_two, ← powMonoidHom_apply, map_finsuppProd]
    nth_rw 1 [← prod_factorization_pow_eq_self h0]
    refine Finsupp.prod_congr fun p hp ↦ ?_
    rw [powMonoidHom_apply, ← pow_mul, div_two_mul_two_of_even (h p (prime_of_mem_primeFactors hp))]

end Nat
