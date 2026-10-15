module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Auxiliary
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SmoothSum
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Smooth summation in one progression: (ext:crt-count)

`smoothProgressionCount : SmoothProgressionCount` (`Extraction/Auxiliary.lean`, `[P-07:0155–0163]`):
for a cutoff `Φ`,

`| ∑_{y ≥ 1, y ≡ a (mod m)} Φ(ℓ y / x) - x/(ℓ m) · ∫ Φ | ≤ ∫ |Φ'|`,

uniformly in `x > 0`, the dilation `ℓ ≥ 1`, the modulus `m ≥ 1` and the residue `a`: "comparing
each sampling interval with its integral and using the bounded total variation of `Φ`".

It is the first-order comparison `EndpointProof.norm_progression_sum_sub_integral_le` (the
real-valued instance of the lemma behind `EndpointProof.SmoothProgressionSum`) applied to the
dilated cutoff `G(u) = Φ(c u)`, `c = ℓ/x`: `∫ G = c⁻¹ ∫ Φ` and `∫ |G'| = ∫ |Φ'|`. The constant is
the total variation `C = ∫ |Φ'|`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open MeasureTheory

noncomputable section

/-- **(ext:crt-count)** (`[P-07:0155–0163]`), with the constant `C = ∫ |Φ'|`. -/
theorem smoothProgressionCount : SmoothProgressionCount := by
  intro Φ hΦ
  obtain ⟨hΦd, hΦ2⟩ := contDiff_infty_iff_deriv.mp hΦ.smooth
  have hΦ' : Continuous (deriv Φ) := hΦ2.continuous
  obtain ⟨R₀, -, hR₀⟩ := hΦ.exists_upper
  have hΦ0 : ∀ t : ℝ, t ≤ 0 → Φ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hmem => absurd (hΦ.support hmem) (not_lt.mpr ht)
  refine ⟨∫ t, ‖deriv Φ t‖, fun x hx ℓ m a hℓ hm => ?_⟩
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (ℓ : ℝ) / x := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]
    exact div_pos hℓR hx
  have hinv : 0 < c⁻¹ := inv_pos.mpr hc
  -- the dilated cutoff `G(u) = Φ(c u)`
  have hlin : Differentiable ℝ fun u : ℝ => c * u := differentiable_id.const_mul c
  have hlinc : Continuous fun u : ℝ => c * u := continuous_const.mul continuous_id
  have hGd : Differentiable ℝ fun u : ℝ => Φ (c * u) := hΦd.comp hlin
  have hGderiv : ∀ u : ℝ, deriv (fun u : ℝ => Φ (c * u)) u = c * deriv Φ (c * u) := by
    intro u
    rw [deriv_comp_mul_left c Φ u, smul_eq_mul]
  have hG' : Continuous (deriv fun u : ℝ => Φ (c * u)) := by
    have hfun : (deriv fun u : ℝ => Φ (c * u)) = fun u => c * deriv Φ (c * u) :=
      funext hGderiv
    have h2 : Continuous fun u : ℝ => deriv Φ (c * u) := hΦ'.comp hlinc
    rw [hfun]
    exact continuous_const.mul h2
  have hG0 : ∀ u : ℝ, u ≤ 0 → Φ (c * u) = 0 := fun u hu =>
    hΦ0 _ (mul_nonpos_of_nonneg_of_nonpos hc.le hu)
  have hGc : HasCompactSupport fun u : ℝ => Φ (c * u) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := R₀ / c)) fun u hu => ?_
    by_cases hu0 : u < 0
    · exact hG0 u hu0.le
    · have hu1 : R₀ / c < u := by
        by_contra hcon
        exact hu ⟨not_lt.mp hu0, not_lt.mp hcon⟩
      have hu2 : R₀ < c * u := by
        rw [div_lt_iff₀ hc, mul_comm] at hu1
        exact hu1
      exact hR₀ _ hu2
  have hmain : ‖(∑ᶠ n : ℕ, if n ≡ a [MOD m] then Φ (c * (n : ℝ)) else 0) -
      ((m : ℝ)⁻¹ : ℝ) • ∫ u : ℝ, Φ (c * u)‖ ≤
        ∫ u : ℝ, ‖deriv (fun u : ℝ => Φ (c * u)) u‖ :=
    EndpointProof.norm_progression_sum_sub_integral_le hGd hG' hGc hG0 hm a
  -- the three terms in the variables of the statement
  have hsum : (∑ᶠ y : ℕ, if y ≡ a [MOD m] then Φ ((ℓ : ℝ) * (y : ℝ) / x) else 0) =
      ∑ᶠ n : ℕ, if n ≡ a [MOD m] then Φ (c * (n : ℝ)) else 0 := by
    refine finsum_congr fun y => ?_
    rw [hcdef, mul_div_right_comm]
  have hint : ∫ u : ℝ, Φ (c * u) = c⁻¹ * ∫ t, Φ t := by
    rw [MeasureTheory.Measure.integral_comp_mul_left Φ c, abs_of_pos hinv, smul_eq_mul]
  have hD : ∫ u : ℝ, ‖deriv (fun u : ℝ => Φ (c * u)) u‖ = ∫ t, ‖deriv Φ t‖ := by
    have h1 : (fun u : ℝ => ‖deriv (fun u : ℝ => Φ (c * u)) u‖) =
        fun u => c * ‖deriv Φ (c * u)‖ := by
      funext u
      rw [hGderiv u, norm_mul, Real.norm_eq_abs, abs_of_pos hc]
    rw [h1, MeasureTheory.integral_const_mul,
      MeasureTheory.Measure.integral_comp_mul_left (fun t => ‖deriv Φ t‖) c,
      abs_of_pos hinv, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have hcoef : x / ((ℓ : ℝ) * (m : ℝ)) * ∫ t, Φ t = (m : ℝ)⁻¹ * (c⁻¹ * ∫ t, Φ t) := by
    rw [hcdef, inv_div]
    ring
  rw [hint, hD, smul_eq_mul, Real.norm_eq_abs] at hmain
  rw [hsum, hcoef]
  exact hmain

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
