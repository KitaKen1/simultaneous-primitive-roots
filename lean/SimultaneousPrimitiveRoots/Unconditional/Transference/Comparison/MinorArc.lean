module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.MinorArcTools
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Denominators larger than `Q`

Source: `verification/stage7-sources/S-03.tex`, lines 316–337 (`[S-03:0316–0337]`).

`minorArcBound_of : ScaleLowerBound → ProbabilityBilinear → KernelNorm → MinorArcBound`.

"Suppose `r > Q`. Apply (eq:ideal-probability-bilinear) to the raw term. For the comparison term,
move the two separate kernel integrations onto the two tests. Their norms increase by at most `2`
each by (eq:ideal-gram-bound). The resulting tests on `D_A, D_B` are supported in `[U/2, 4U]` and
`[V/2, 4V]` for large `x`, by the log localization. The same bilinear bound therefore applies with
an absolute constant change. … The two scales exceed every fixed power of `L`, and
`log(2r) ≤ L^{d+1}` for large `x`. Since `r > Q` and `r ≤ UV/S`, the bound for either term, apart
from an absolute constant and the two test norms, is `L^κ (o(L^{-A}) + Q⁻¹ + L^{d+1} S⁻¹)^{1/2}`."

The thresholds for `x`: those of `ProbabilityBilinear` (for the windows `[U/4, 8U]`), `KernelNorm`
and `ScaleLowerBound` (with the exponent `q_* + d + 2`), and
`L ≥ max(2, 10 K, (4 m C₀ + 1)²)`, `K` the constant of (eq:ideal-probability-bilinear). The total
is `5 K L^κ · 2 L^{-(B₀+κ+10)} ≤ L^{-B₀}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

/-- **Denominators larger than `Q`** [S-03:0316–0337]. -/
theorem minorArcBound_of (hscale : ScaleLowerBound) (hpb : ProbabilityBilinear)
    (hkn : KernelNorm) : MinorArcBound := by
  intro P m B₀ qs ss hs xs hB₀ hq hss hhs hxs
  have hκ := atomExponent_nonneg P m
  have hd := d_pos P
  have hqs0 : 0 ≤ qs := by linarith
  have hss0 : 0 ≤ ss := by linarith
  obtain ⟨K, hK, x₁, hPB⟩ := hpb P m (1 / 4) 8 (by norm_num) (by norm_num)
  obtain ⟨x₂, hKN⟩ := hkn P m qs hs xs hqs0 hhs hxs
  obtain ⟨x₃, hSC⟩ := hscale P (qs + P.d + 2)
  have hc0 : 0 ≤ 2 * (m : ℝ) * P.C₀ :=
    mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) P.C₀_pos.le
  refine ⟨max (max x₁ x₂) (max x₃ (Real.exp (max (max 2 (10 * K))
    ((2 * (2 * (m : ℝ) * P.C₀) + 1) ^ 2)))), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 hint J A Bs hA hBs hAm hBm a b f g hf hg α ζ β u r hdata hQr
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx₂ : x₂ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx₃ : x₃ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxe : Real.exp (max (max 2 (10 * K)) ((2 * (2 * (m : ℝ) * P.C₀) + 1) ^ 2)) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hLbig : max (max 2 (10 * K)) ((2 * (2 * (m : ℝ) * P.C₀) + 1) ^ 2) ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL2 : 2 ≤ Real.log x := (le_max_left _ _).trans ((le_max_left _ _).trans hLbig)
  have hLK : 10 * K ≤ Real.log x := (le_max_right _ _).trans ((le_max_left _ _).trans hLbig)
  have hLc : (2 * (2 * (m : ℝ) * P.C₀) + 1) ^ 2 ≤ Real.log x := (le_max_right _ _).trans hLbig
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hX : 0 ≤ tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g :=
    mul_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _)
  have hB0 : 0 ≤ Real.log x ^ (-B₀) := Real.rpow_nonneg hL0.le _
  have hE : 0 ≤ Real.log x ^ atomExponent P m := Real.rpow_nonneg hL0.le _
  by_cases hg0 : ∀ t, g t = 0
  · rw [comparisonDefect_eq_zero_of_right 𝔊.big A Bs _ _ _ f hg0 α ζ, norm_zero]
    exact mul_nonneg hB0 hX
  by_cases hf0 : ∀ t, f t = 0
  · rw [Dyadic.defect_eq_zero_of_left 𝔊.big A Bs _ _ _ hf0 g α ζ, norm_zero]
    exact mul_nonneg hB0 hX
  obtain ⟨tA, htA⟩ := not_forall.mp hg0
  obtain ⟨tB, htB⟩ := not_forall.mp hf0
  obtain ⟨hr, hcop, hα, hrle, hβ, -⟩ := hdata
  -- the two dyads contain a tuple
  obtain ⟨hdA1, hdA2⟩ := Minor.dyad_bounds 𝔊 A (hg tA htA)
  obtain ⟨hdB1, hdB2⟩ := Minor.dyad_bounds 𝔊 Bs (hf tB htB)
  have hU1 : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  have hV1 : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have hUE : Real.log x ^ (qs + P.d + 2) ≤ 2 * (2 : ℝ) ^ a := by
    have h1 := (hSC x hx₃ S B 𝔊).2 J A hA tA
    linarith
  have hVE : Real.log x ^ (qs + P.d + 2) ≤ 2 * (2 : ℝ) ^ b := by
    have h1 := (hSC x hx₃ S B 𝔊).2 J Bs hBs tB
    linarith
  -- `log(2r) ≤ L^{d+1}`
  have hR1 : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
  have hℓ0 : 0 ≤ Real.log (2 * (r : ℝ)) := Real.log_nonneg (by linarith)
  have hℓ : Real.log (2 * (r : ℝ)) ≤ Real.log x ^ (P.d + 1) := by
    have hS1 : 1 ≤ Real.log x ^ ss := Real.one_le_rpow hL1 hss0
    have hUV0 : (0 : ℝ) ≤ (2 : ℝ) ^ a * (2 : ℝ) ^ b := by positivity
    have h1 : (r : ℝ) ≤ (2 : ℝ) ^ a * (2 : ℝ) ^ b := hrle.trans (div_le_self hUV0 hS1)
    have hPA : (0 : ℝ) < ((tupleProd A tA : ℕ) : ℝ) := by
      exact_mod_cast tupleProd_pos 𝔊 A tA
    have hPB' : (0 : ℝ) < ((tupleProd Bs tB : ℕ) : ℝ) := by
      exact_mod_cast tupleProd_pos 𝔊 Bs tB
    have h2 : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤
        ((tupleProd A tA : ℕ) : ℝ) * ((tupleProd Bs tB : ℕ) : ℝ) :=
      mul_le_mul hdA1 hdB1 (by positivity) hPA.le
    have h3 : 2 * (r : ℝ) ≤
        2 * (((tupleProd A tA : ℕ) : ℝ) * ((tupleProd Bs tB : ℕ) : ℝ)) := by linarith
    have h4 : Real.log (2 * (r : ℝ)) ≤
        Real.log (2 * (((tupleProd A tA : ℕ) : ℝ) * ((tupleProd Bs tB : ℕ) : ℝ))) :=
      Real.log_le_log (by linarith) h3
    have h5 : Real.log (2 * (((tupleProd A tA : ℕ) : ℝ) * ((tupleProd Bs tB : ℕ) : ℝ))) =
        Real.log 2 + (Real.log ((tupleProd A tA : ℕ) : ℝ) +
          Real.log ((tupleProd Bs tB : ℕ) : ℝ)) := by
      rw [Real.log_mul two_ne_zero (mul_pos hPA hPB').ne', Real.log_mul hPA.ne' hPB'.ne']
    have h6 := log_tupleProd_le_const 𝔊 hL0.le A hAm tA
    have h7 := log_tupleProd_le_const 𝔊 hL0.le Bs hBm tB
    have h8 : Real.log 2 ≤ 1 := by
      have h := Real.log_two_lt_d9
      linarith
    have hLd : 1 ≤ Real.log x ^ P.d := Real.one_le_rpow hL1 hd.le
    have h9 : 2 * (m : ℝ) * P.C₀ * Real.log (Real.log x) + 1 ≤ Real.log x :=
      mul_log_add_one_le hc0 hLc
    have h10 : Real.log x ^ (P.d + 1) = Real.log x ^ P.d * Real.log x :=
      Real.rpow_add_one hL0.ne' P.d
    have h11 : Real.log x ^ P.d * (2 * (m : ℝ) * P.C₀ * Real.log (Real.log x) + 1) ≤
        Real.log x ^ P.d * Real.log x :=
      mul_le_mul_of_nonneg_left h9 (le_trans zero_le_one hLd)
    rw [h10]
    linarith
  -- (eq:ideal-minor-error)
  have hsig := Minor.sigma_sqrt_le (w := B₀ + atomExponent P m + 10) hL2 hd hq hss hUE hVE hQr
    hrle hℓ0 hℓ
  -- the supports of the four tests
  have hGs : ∀ t, g t ≠ 0 → 1 / 4 * (2 : ℝ) ^ a ≤ ((tupleProd A t : ℕ) : ℝ) ∧
      ((tupleProd A t : ℕ) : ℝ) ≤ 8 * (2 : ℝ) ^ a := by
    intro t ht
    obtain ⟨h1, h2⟩ := Minor.dyad_bounds 𝔊 A (hg t ht)
    constructor <;> linarith
  have hfc : DyadSupported 𝔊.big Bs b (fun t => conj (f t)) := by
    intro t ht
    exact hf t fun h0 => ht (by
      show conj (f t) = 0
      rw [h0, map_zero])
  have hFs : ∀ t, conj (f t) ≠ 0 → 1 / 4 * (2 : ℝ) ^ b ≤ ((tupleProd Bs t : ℕ) : ℝ) ∧
      ((tupleProd Bs t : ℕ) : ℝ) ≤ 8 * (2 : ℝ) ^ b := by
    intro t ht
    obtain ⟨h1, h2⟩ := Minor.dyad_bounds 𝔊 Bs (hfc t ht)
    constructor <;> linarith
  have hh0 : 0 < Real.log x ^ (-hs) := Real.rpow_pos_of_pos hL0 _
  have hh1 : Real.log x ^ (-hs) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hGk : ∀ t, kernelIntX 𝔊.big A (Real.log x ^ qs) (Real.log x ^ (-hs))
      (Real.log x ^ (-xs)) g t ≠ 0 → 1 / 4 * (2 : ℝ) ^ a ≤ ((tupleProd A t : ℕ) : ℝ) ∧
      ((tupleProd A t : ℕ) : ℝ) ≤ 8 * (2 : ℝ) ^ a := by
    intro t ht
    by_contra hw
    exact ht (Minor.kernelIntX_eq_zero 𝔊 A hh0 hh1 hg t hw)
  have hFk : ∀ t, kernelIntX 𝔊.big Bs (Real.log x ^ qs) (Real.log x ^ (-hs))
      (Real.log x ^ (-xs)) (fun t => conj (f t)) t ≠ 0 →
      1 / 4 * (2 : ℝ) ^ b ≤ ((tupleProd Bs t : ℕ) : ℝ) ∧
      ((tupleProd Bs t : ℕ) : ℝ) ≤ 8 * (2 : ℝ) ^ b := by
    intro t ht
    by_contra hw
    exact ht (Minor.kernelIntX_eq_zero 𝔊 Bs hh0 hh1 hfc t hw)
  -- the two bilinear forms
  have hraw := hPB x hx₁ S B 𝔊 J A Bs hA hBs hAm hBm ((2 : ℝ) ^ a) ((2 : ℝ) ^ b) hU1 hV1
    (fun t => conj (f t)) g hFs hGs α ζ β u r hr hcop hα hβ
  have hcomp := hPB x hx₁ S B 𝔊 J A Bs hA hBs hAm hBm ((2 : ℝ) ^ a) ((2 : ℝ) ^ b) hU1 hV1
    (kernelIntX 𝔊.big Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
      (fun t => conj (f t)))
    (kernelIntX 𝔊.big A (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs)) g)
    hFk hGk α ζ β u r hr hcop hα hβ
  have hnA := (hKN x hx₂ S B 𝔊 hint J A hA hAm g).2
  have hnB := (hKN x hx₂ S B 𝔊 hint J Bs hBs hBm (fun t => conj (f t))).2
  rw [Minor.tupleNorm_conj 𝔊.big Bs f] at hnB hraw
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = Real.sqrt (1 / (2 : ℝ) ^ b + 1 / (r : ℝ) +
      Real.log (2 * (r : ℝ)) / (2 : ℝ) ^ a +
      (r : ℝ) * Real.log (2 * (r : ℝ)) / ((2 : ℝ) ^ a * (2 : ℝ) ^ b)) := ⟨_, rfl⟩
  rw [← hσ] at hsig hraw hcomp
  have hσ0 : 0 ≤ σ := by
    rw [hσ]
    exact Real.sqrt_nonneg _
  have hKE : 0 ≤ K * Real.log x ^ atomExponent P m := mul_nonneg hK.le hE
  have hcomp' : ‖phaseForm 𝔊.big A Bs
        (kernelIntX 𝔊.big Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
          (fun t => conj (f t)))
        (kernelIntX 𝔊.big A (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs)) g)
        α ζ‖ ≤
      K * Real.log x ^ atomExponent P m * σ *
        (4 * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g)) := by
    refine hcomp.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKE hσ0))
    calc tupleNorm 𝔊.big Bs (kernelIntX 𝔊.big Bs (Real.log x ^ qs) (Real.log x ^ (-hs))
            (Real.log x ^ (-xs)) (fun t => conj (f t))) *
          tupleNorm 𝔊.big A (kernelIntX 𝔊.big A (Real.log x ^ qs) (Real.log x ^ (-hs))
            (Real.log x ^ (-xs)) g)
        ≤ 2 * tupleNorm 𝔊.big Bs f * (2 * tupleNorm 𝔊.big A g) :=
          mul_le_mul hnB hnA (wNorm_nonneg _ _)
            (mul_nonneg zero_le_two (wNorm_nonneg _ _))
      _ = 4 * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g) := by ring
  have hfin := Minor.final_le (κ := atomExponent P m) (B₀ := B₀) hL2 hK hLK
  rw [Minor.defect_eq_sub 𝔊.big A Bs _ _ _ (sum_tupleWeight 𝔊 A) (sum_tupleWeight 𝔊 Bs) f g α ζ]
  refine (norm_sub_le _ _).trans ?_
  calc ‖phaseForm 𝔊.big A Bs (fun t => conj (f t)) g α ζ‖ +
        ‖phaseForm 𝔊.big A Bs
          (kernelIntX 𝔊.big Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
            (fun t => conj (f t)))
          (kernelIntX 𝔊.big A (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs)) g)
          α ζ‖
      ≤ K * Real.log x ^ atomExponent P m * σ *
            (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g) +
          K * Real.log x ^ atomExponent P m * σ *
            (4 * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g)) := add_le_add hraw hcomp'
    _ = 5 * (K * Real.log x ^ atomExponent P m * σ) *
          (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g) := by ring
    _ ≤ 5 * (K * Real.log x ^ atomExponent P m *
          (2 * Real.log x ^ (-(B₀ + atomExponent P m + 10)))) *
          (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsig hKE) (by norm_num)) hX
    _ ≤ Real.log x ^ (-B₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g) :=
        mul_le_mul_of_nonneg_right hfin hX

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
