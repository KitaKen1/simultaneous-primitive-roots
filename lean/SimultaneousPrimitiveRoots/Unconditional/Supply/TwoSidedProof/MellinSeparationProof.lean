module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Auxiliary
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion

/-!
# (cor:insertion-separation) for a complex cutoff

`mellinSeparationComplex : MellinSeparationComplex` (`[P-06:0290–0296]`): "Let `φ(u) = Ψ(e^u)` and
use the convention `φ̂(ζ) = ∫ φ(u) e^{-iζu} du`. Then
`Ψ(n/(xD)) = (1/2π) ∫ φ̂(ζ) (n/x)^{iζ} D^{-iζ} dζ`."

For a smooth `Ψ` with compact support in `(0, ∞)` put `φ(u) = Ψ(e^{2πu})`, a smooth compactly
supported function, hence a Schwartz function (`HasCompactSupport.toSchwartzMap`), and let
`w = 𝓕 φ` be its Fourier transform in Mathlib's normalization `𝓕 φ(v) = ∫ φ(u) e^{-2πiuv} du` (so
`w(v) = φ̂(v)/(2π)` in the manuscript's notation). Then

* `w` is a Schwartz function: continuous, and `|w(v)| (1 + |v|)^N` is bounded for every `N`;
* the Fourier inversion formula (`Continuous.fourierInv_fourier_eq`) at `u = log t / (2π)` is
  `Ψ(t) = φ(u) = ∫ w(v) e^{2πiuv} dv = ∫ w(v) t^{iv} dv` for `t > 0`.

`MellinSep.exists_support_bounds`: the support of `Ψ` lies in some `[c₁, c₂]` with `c₁ > 0`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open MeasureTheory
open scoped ContDiff SchwartzMap FourierTransform

noncomputable section

namespace MellinSep

/-- `(1 + a)^N ≤ 2^N (1 + a^N)` for `a ≥ 0`. -/
theorem one_add_pow_le {a : ℝ} (ha : 0 ≤ a) (N : ℕ) : (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
  have hpN : (0 : ℝ) ≤ a ^ N := pow_nonneg ha N
  have h2N : (0 : ℝ) < 2 ^ N := pow_pos two_pos N
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + a ^ N) := le_mul_of_one_le_right h2N.le (by linarith)
  · calc (1 + a) ^ N ≤ (2 * a) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * a ^ N := mul_pow 2 a N
      _ ≤ 2 ^ N * (1 + a ^ N) := mul_le_mul_of_nonneg_left (by linarith) h2N.le

/-- A function with compact support in `(0, ∞)` vanishes outside some `[c₁, c₂]`, `c₁ > 0`. -/
theorem exists_support_bounds {Ψ : ℝ → ℂ} (hcomp : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ t, Ψ t ≠ 0 → c₁ ≤ t ∧ t ≤ c₂ := by
  obtain ⟨R, hR⟩ := hcomp.isCompact.bddAbove
  have h0 : (0 : ℝ) ∈ (tsupport Ψ)ᶜ := fun h => lt_irrefl (0 : ℝ) (hsupp h)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isClosed_tsupport Ψ).isOpen_compl 0 h0
  refine ⟨ε, max R ε, hε, le_max_right _ _, fun t ht => ?_⟩
  have hmem : t ∈ tsupport Ψ := subset_tsupport Ψ ht
  have ht0 : 0 < t := hsupp hmem
  refine ⟨?_, (hR hmem).trans (le_max_left _ _)⟩
  by_contra hlt
  rw [not_le] at hlt
  have hb : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact hlt
  exact hball hb hmem

end MellinSep

/-- **(cor:insertion-separation) for a complex cutoff** (`[P-06:0290–0296]`): a smooth `Ψ` with
compact support in `(0, ∞)` is `Ψ(t) = ∫ w(v) t^{iv} dv` with a continuous, rapidly decreasing
density `w`. -/
theorem mellinSeparationComplex : MellinSeparationComplex := by
  intro Ψ hΨ hcomp hsupp
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hsup⟩ := MellinSep.exists_support_bounds hcomp hsupp
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  have h2π : (0 : ℝ) < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  -- `φ(u) = Ψ(e^{2πu})` is a Schwartz function
  have hin : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (2 * Real.pi * u)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hφs : ContDiff ℝ ∞ (fun u : ℝ => Ψ (Real.exp (2 * Real.pi * u))) := hΨ.comp hin
  have hφc : HasCompactSupport (fun u : ℝ => Ψ (Real.exp (2 * Real.pi * u))) := by
    refine HasCompactSupport.intro
      (K := Set.Icc (Real.log c₁ / (2 * Real.pi)) (Real.log c₂ / (2 * Real.pi))) isCompact_Icc
      fun u hu => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := hsup _ hne
    refine hu ⟨?_, ?_⟩
    · rw [div_le_iff₀ h2π, mul_comm]
      exact (Real.log_le_iff_le_exp hc₁).mpr h1
    · rw [le_div_iff₀ h2π, mul_comm]
      exact (Real.le_log_iff_exp_le hc₂).mpr h2
  obtain ⟨φS, hφS⟩ : ∃ φS : 𝓢(ℝ, ℂ), ∀ u, φS u = Ψ (Real.exp (2 * Real.pi * u)) :=
    ⟨hφc.toSchwartzMap hφs, fun u => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : 𝓢(ℝ, ℂ), (W : ℝ → ℂ) = 𝓕 (φS : ℝ → ℂ) :=
    ⟨𝓕 φS, SchwartzMap.fourier_coe φS⟩
  refine ⟨⇑W, W.continuous, ?_, ?_⟩
  · -- the decay of a Schwartz function
    intro N
    obtain ⟨C₀, -, hC₀⟩ := W.decay 0 0
    obtain ⟨C₁, -, hC₁⟩ := W.decay N 0
    refine ⟨2 ^ N * (C₀ + C₁), fun v => ?_⟩
    have h0 : ‖W v‖ ≤ C₀ := by
      have h := hC₀ v
      rwa [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
    have h1 : |v| ^ N * ‖W v‖ ≤ C₁ := by
      have h := hC₁ v
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    have h2 : (1 + |v|) ^ N ≤ 2 ^ N * (1 + |v| ^ N) :=
      MellinSep.one_add_pow_le (abs_nonneg v) N
    calc ‖W v‖ * (1 + |v|) ^ N ≤ ‖W v‖ * (2 ^ N * (1 + |v| ^ N)) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = 2 ^ N * (‖W v‖ + |v| ^ N * ‖W v‖) := by ring
      _ ≤ 2 ^ N * (C₀ + C₁) :=
          mul_le_mul_of_nonneg_left (add_le_add h0 h1) (pow_nonneg zero_le_two N)
  · -- Fourier inversion at `u = log t / (2π)`
    intro t ht
    obtain ⟨u, hu⟩ : ∃ u : ℝ, 2 * Real.pi * u = Real.log t :=
      ⟨Real.log t / (2 * Real.pi), by
        rw [mul_comm]
        exact div_mul_cancel₀ _ h2π.ne'⟩
    have hΨt : Ψ t = φS u := by rw [hφS u, hu, Real.exp_log ht]
    have hinv : 𝓕⁻ (𝓕 (φS : ℝ → ℂ)) = (φS : ℝ → ℂ) :=
      Continuous.fourierInv_fourier_eq φS.continuous φS.integrable (by
        rw [← hW]
        exact W.integrable)
    have h1 : 𝓕⁻ (𝓕 (φS : ℝ → ℂ)) u = φS u := congrFun hinv u
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h1
    rw [hΨt, ← h1]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have he : Complex.exp (((-2 * Real.pi * v * -u : ℝ) : ℂ) * Complex.I) =
        (t : ℂ) ^ ((v : ℂ) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]
      congr 1
      have e : -2 * Real.pi * v * -u = Real.log t * v := by
        rw [← hu]
        ring
      rw [e]
      push_cast
      ring
    show Complex.exp (((-2 * Real.pi * v * -u : ℝ) : ℂ) * Complex.I) • 𝓕 (φS : ℝ → ℂ) v =
      W v * (t : ℂ) ^ ((v : ℂ) * Complex.I)
    rw [smul_eq_mul, he, hW]
    exact mul_comm _ _

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
