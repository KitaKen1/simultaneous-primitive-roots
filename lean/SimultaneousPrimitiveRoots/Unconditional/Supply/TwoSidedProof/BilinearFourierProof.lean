module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.IntegerBilinear

/-!
# The elementary bilinear Fourier estimate

`bilinearFourier : BilinearFourier` (`[P-06:0431–0453]`), with the constant `C = 100`: for
coefficients on `u ∈ [U₁, eU₁]`, `v ∈ [U₂, eU₂]` and a reduced fraction `h/r` with
`|θ - h/r| ≤ r⁻²`,

`|∑_{u,v} α_u β_v e(θ u v)|² ≤ 100 ‖α‖₂² ‖β‖₂² (U₁/r + 1)(U₂ + r log(2r))`.

This is the integer bilinear estimate [S] Lemma 4.2 in its squared form
(`Comparison.Bilinear.bilinear_sq_le`, `Transference/Comparison/IntegerBilinear.lean`: "Cauchy in
the variable on the interval of length `O(U₂)`, expansion, and the geometric-sum bound", then
blocks of diameter at most `r/2`), applied with the Cauchy variable `v` and the other variable
`u`, the intervals `[⌈U₂⌉, ⌈U₂⌉ + 2U₂]` and `[⌈U₁⌉, ⌈U₁⌉ + 2U₁]` (`e ≤ 3`), and

`U₂ + (1 + U₁/r)(U₂ + r log(2r)) ≤ 2 (U₁/r + 1)(U₂ + r log(2r))`.

The two notations for `e(θ) = exp(2πiθ)` agree (`addChar_eq_expUnit`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

/-- `e(θ)` of [P] (`addChar`) is `e(θ)` of [S] (`expUnit`). -/
theorem addChar_eq_expUnit (t : ℝ) : addChar t = expUnit t := by
  unfold addChar expUnit
  congr 1
  ring

/-- **The elementary bilinear Fourier estimate** (`[P-06:0431–0453]`), with the absolute constant
`100`. This is the field `bilinearFourier` of `OpenLeaves d H 𝔅`. -/
theorem bilinearFourier : BilinearFourier := by
  refine ⟨100, ?_⟩
  intro U₁ U₂ hU₁ hU₂ s₁ s₂ α β hs₁ hs₂ θ h r hr hcop hθ
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  -- the supports lie in integer intervals of lengths `2 U₁`, `2 U₂`
  have hs₁' : ∀ u ∈ s₁, ⌈U₁⌉₊ ≤ u ∧ (u : ℝ) ≤ (⌈U₁⌉₊ : ℝ) + 2 * U₁ := by
    intro u hu
    obtain ⟨h1, h2⟩ := hs₁ u hu
    refine ⟨Nat.ceil_le.mpr h1, ?_⟩
    have h3 : U₁ ≤ (⌈U₁⌉₊ : ℝ) := Nat.le_ceil U₁
    have h4 : Real.exp 1 * U₁ ≤ 3 * U₁ := mul_le_mul_of_nonneg_right he (by linarith)
    linarith
  have hs₂' : ∀ v ∈ s₂, ⌈U₂⌉₊ ≤ v ∧ (v : ℝ) ≤ (⌈U₂⌉₊ : ℝ) + 2 * U₂ := by
    intro v hv
    obtain ⟨h1, h2⟩ := hs₂ v hv
    refine ⟨Nat.ceil_le.mpr h1, ?_⟩
    have h3 : U₂ ≤ (⌈U₂⌉₊ : ℝ) := Nat.le_ceil U₂
    have h4 : Real.exp 1 * U₂ ≤ 3 * U₂ := mul_le_mul_of_nonneg_right he (by linarith)
    linarith
  -- the rational approximation
  have hgcd : Int.gcd h (r : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
    exact hcop
  have hcop' : IsCoprime h (r : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have hθ' : θ = (h : ℝ) / (r : ℝ) + (θ - (h : ℝ) / (r : ℝ)) := by ring
  have hβ' : |θ - (h : ℝ) / (r : ℝ)| ≤ ((r : ℝ) ^ 2)⁻¹ := hθ.trans (le_of_eq (one_div _))
  -- [S] Lemma 4.2 with the Cauchy variable `v`
  have hmain : ‖∑ v ∈ s₂, ∑ u ∈ s₁, β v * α u * expUnit (θ * (v : ℝ) * (u : ℝ))‖ ^ 2 ≤
      2 * (1 + 2 * 2) * (2 + 3) * (∑ v ∈ s₂, ‖β v‖ ^ 2) * (∑ u ∈ s₁, ‖α u‖ ^ 2) *
        (U₂ + (1 + U₁ / (r : ℝ)) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ)))) :=
    Comparison.Bilinear.bilinear_sq_le (C := 2) two_pos hU₂ hU₁ s₂ s₁ ⌈U₂⌉₊ ⌈U₁⌉₊ hs₂' hs₁' β α
      hr hcop' hθ' hβ'
  -- the same sum
  have hsum : ∑ u ∈ s₁, ∑ v ∈ s₂, α u * β v * addChar (θ * ((u : ℝ) * (v : ℝ))) =
      ∑ v ∈ s₂, ∑ u ∈ s₁, β v * α u * expUnit (θ * (v : ℝ) * (u : ℝ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
    have hph : θ * ((u : ℝ) * (v : ℝ)) = θ * (v : ℝ) * (u : ℝ) := by ring
    rw [addChar_eq_expUnit, hph, mul_comm (α u) (β v)]
  -- the constants
  have hA0 : 0 ≤ ∑ u ∈ s₁, ‖α u‖ ^ 2 := Finset.sum_nonneg fun u _ => sq_nonneg _
  have hB0 : 0 ≤ ∑ v ∈ s₂, ‖β v‖ ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  have hW : 0 ≤ (r : ℝ) * Real.log (2 * (r : ℝ)) :=
    mul_nonneg hrpos.le (Real.log_nonneg (by linarith))
  have hρ : 0 ≤ U₁ / (r : ℝ) := div_nonneg (by linarith) hrpos.le
  have hT : U₂ + (1 + U₁ / (r : ℝ)) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ))) ≤
      2 * ((U₁ / (r : ℝ) + 1) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ)))) := by
    have h1 : 0 ≤ U₁ / (r : ℝ) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ))) :=
      mul_nonneg hρ (by linarith)
    have h2 : 2 * ((U₁ / (r : ℝ) + 1) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ)))) -
        (U₂ + (1 + U₁ / (r : ℝ)) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ)))) =
        U₁ / (r : ℝ) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ))) +
          (r : ℝ) * Real.log (2 * (r : ℝ)) := by ring
    linarith
  rw [hsum]
  calc ‖∑ v ∈ s₂, ∑ u ∈ s₁, β v * α u * expUnit (θ * (v : ℝ) * (u : ℝ))‖ ^ 2
      ≤ 2 * (1 + 2 * 2) * (2 + 3) * (∑ v ∈ s₂, ‖β v‖ ^ 2) * (∑ u ∈ s₁, ‖α u‖ ^ 2) *
          (U₂ + (1 + U₁ / (r : ℝ)) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ)))) := hmain
    _ ≤ 2 * (1 + 2 * 2) * (2 + 3) * (∑ v ∈ s₂, ‖β v‖ ^ 2) * (∑ u ∈ s₁, ‖α u‖ ^ 2) *
          (2 * ((U₁ / (r : ℝ) + 1) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ))))) :=
        mul_le_mul_of_nonneg_left hT (mul_nonneg (mul_nonneg (by norm_num) hB0) hA0)
    _ = 100 * (∑ u ∈ s₁, ‖α u‖ ^ 2) * (∑ v ∈ s₂, ‖β v‖ ^ 2) *
          ((U₁ / (r : ℝ) + 1) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ)))) := by ring

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
