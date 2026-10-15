module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.ProductAtom
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Gram
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The collapse of a tuple test (eq:ideal-collapse)

Source: `verification/stage7-sources/S-03.tex`, lines 98–108 (`[S-03:0098–0108]`).

`collapseBound : CollapseBound`. "If `f` is any such `L²` test, supported where
`c₁ U ≤ P_Λ ≤ c₂ U` for fixed `c₁, c₂ > 0`, put `a_n = E[f 1_{P_Λ = n}]`. Cauchy–Schwarz on each
fiber gives `∑_n |a_n|² ≤ ∑_n ρ_Λ(n) E[|f|² 1_{P_Λ = n}] ≤ L^κ / (c₁ U) ‖f‖₂²`. No assumption that
`f` is a function of the product has been made."

* `Collapse.norm_fiberCoeff_sq_le` — Cauchy–Schwarz on the fiber `P_Λ = n`:
  `|a_n|² ≤ ρ_Λ(n) E[|f|² 1_{P_Λ = n}]`.
* `collapseBound_of_atom` — with `ρ_Λ(n) ≤ L^κ / n ≤ L^κ / Y` on the fibers `n ≥ Y` meeting the
  support (the other `a_n` vanish), and `∑_n E[|f|² 1_{P_Λ = n}] ≤ ‖f‖₂²`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Collapse

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] {J : ℕ}

omit [DecidableEq B] in
theorem fiberWeight_nonneg (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) (n : ℕ)
    (t : AuxList 𝔊.big Λ) :
    0 ≤ (if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0) := by
  by_cases hc : tupleProd Λ t = n
  · rw [if_pos hc]
    exact tupleWeight_nonneg 𝔊 Λ t
  · exact (if_neg hc).ge

/-- **Cauchy–Schwarz on a fiber** [S-03:0101–0105]: `|a_n|² ≤ ρ_Λ(n) E[|f|² 1_{P_Λ = n}]`. -/
theorem norm_fiberCoeff_sq_le (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J))
    (F : AuxList 𝔊.big Λ → ℂ) (n : ℕ) :
    ‖fiberCoeff 𝔊.big Λ F n‖ ^ 2 ≤
      atomMass 𝔊.big Λ n * ∑ t : AuxList 𝔊.big Λ,
        (if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0) * ‖F t‖ ^ 2 := by
  have h := Gram.norm_wInner_sq_le
    (w := fun t : AuxList 𝔊.big Λ => if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0)
    (fiberWeight_nonneg 𝔊 Λ n) (fun _ => (1 : ℂ)) F
  have e1 : wInner
      (fun t : AuxList 𝔊.big Λ => if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0)
      (fun _ => (1 : ℂ)) F = fiberCoeff 𝔊.big Λ F n := by
    unfold wInner fiberCoeff
    refine Finset.sum_congr rfl fun t _ => ?_
    dsimp only
    by_cases hc : tupleProd Λ t = n
    · rw [if_pos hc, if_pos hc, map_one, one_mul]
    · rw [if_neg hc, if_neg hc, Complex.ofReal_zero, zero_mul]
  have e2 : wNormSq
      (fun t : AuxList 𝔊.big Λ => if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0)
      (fun _ => (1 : ℂ)) = atomMass 𝔊.big Λ n := by
    unfold wNormSq atomMass
    refine Finset.sum_congr rfl fun t _ => ?_
    dsimp only
    rw [norm_one, one_pow, mul_one]
  rw [e1, e2] at h
  exact h

/-- The fibers are disjoint: `∑_n E[|f|² 1_{P_Λ = n}] ≤ ‖f‖₂²`. -/
theorem sum_fiber_le (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J))
    (F : AuxList 𝔊.big Λ → ℂ) (s : Finset ℕ) :
    ∑ n ∈ s, ∑ t : AuxList 𝔊.big Λ,
        (if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0) * ‖F t‖ ^ 2 ≤
      wNormSq (auxWeight 𝔊.big Λ) F := by
  rw [Finset.sum_comm]
  unfold wNormSq
  refine Finset.sum_le_sum fun t _ => ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [Finset.sum_ite_eq]
  by_cases hc : tupleProd Λ t ∈ s
  · exact (if_pos hc).le
  · rw [if_neg hc]
    exact tupleWeight_nonneg 𝔊 Λ t

end Collapse

/-- **The collapse (eq:ideal-collapse) from the product atom bound** [S-03:0098–0108]. -/
theorem collapseBound_of_atom (hatom : ProductAtomBound) : CollapseBound := by
  intro P m
  obtain ⟨x₁, h₁⟩ := hatom P m
  refine ⟨max x₁ (Real.exp 1), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 J Λ hne hΛ Y hY F hF s
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL0 : 0 < Real.log x := by linarith
  have hκ0 : 0 ≤ Real.log x ^ atomExponent P m := Real.rpow_nonneg hL0.le _
  have hC0 : 0 ≤ Real.log x ^ atomExponent P m / Y := div_nonneg hκ0 hY.le
  have hE0 : ∀ n : ℕ, 0 ≤ ∑ t : AuxList 𝔊.big Λ,
      (if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0) * ‖F t‖ ^ 2 := fun n =>
    Finset.sum_nonneg fun t _ => mul_nonneg (Collapse.fiberWeight_nonneg 𝔊 Λ n t) (sq_nonneg _)
  have hn : ∀ n : ℕ, ‖fiberCoeff 𝔊.big Λ F n‖ ^ 2 ≤
      Real.log x ^ atomExponent P m / Y * ∑ t : AuxList 𝔊.big Λ,
        (if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0) * ‖F t‖ ^ 2 := by
    intro n
    by_cases hnY : Y ≤ (n : ℝ)
    · have hn0 : 0 < n := by
        have h0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hY hnY
        exact_mod_cast h0
      have h2 : atomMass 𝔊.big Λ n ≤ Real.log x ^ atomExponent P m / Y :=
        (h₁ x hx₁ S B 𝔊 J Λ hne hΛ n hn0).trans (div_le_div_of_nonneg_left hκ0 hY hnY)
      exact (Collapse.norm_fiberCoeff_sq_le 𝔊 Λ F n).trans
        (mul_le_mul_of_nonneg_right h2 (hE0 n))
    · have hz : fiberCoeff 𝔊.big Λ F n = 0 := by
        unfold fiberCoeff
        refine Finset.sum_eq_zero fun t _ => ?_
        by_cases hc : tupleProd Λ t = n
        · have hFt : F t = 0 := by
            by_contra hne'
            have h3 : Y ≤ ((tupleProd Λ t : ℕ) : ℝ) := hF t hne'
            rw [hc] at h3
            exact hnY h3
          rw [if_pos hc, hFt, mul_zero]
        · exact if_neg hc
      rw [hz, norm_zero, zero_pow two_ne_zero]
      exact mul_nonneg hC0 (hE0 n)
  calc ∑ n ∈ s, ‖fiberCoeff 𝔊.big Λ F n‖ ^ 2
      ≤ ∑ n ∈ s, Real.log x ^ atomExponent P m / Y * ∑ t : AuxList 𝔊.big Λ,
          (if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0) * ‖F t‖ ^ 2 :=
        Finset.sum_le_sum fun n _ => hn n
    _ = Real.log x ^ atomExponent P m / Y * ∑ n ∈ s, ∑ t : AuxList 𝔊.big Λ,
          (if tupleProd Λ t = n then auxWeight 𝔊.big Λ t else 0) * ‖F t‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ Real.log x ^ atomExponent P m / Y * wNormSq (auxWeight 𝔊.big Λ) F :=
        mul_le_mul_of_nonneg_left (Collapse.sum_fiber_le 𝔊 Λ F s) hC0

/-- **The collapse (eq:ideal-collapse)** [S-03:0098–0108]. -/
theorem collapseBound : CollapseBound := collapseBound_of_atom productAtomBound

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
