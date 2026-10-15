module

public import SimultaneousPrimitiveRoots.Hecke.DedekindResidue
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
public import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.Basic

/-!
# A uniform bound for `ζ_K` on `Re s ≥ 2`

* `norm_dedekindZeta_le_re`: `‖ζ_K(s)‖ ≤ ζ_K(re s)` for `re s > 1` (absolute convergence).
* `dedekindZeta_re_le_of_le`: `σ ↦ ζ_K(σ)` is antitone on `(1, ∞)`.
* `dedekindZeta_two_re_le`: `ζ_K(2) ≤ exp (4 n)` with `n = [K : ℚ]`. From the Euler product
  `log ζ_K(2) = Σ_𝔭 -log (1 - N𝔭⁻²) ≤ 2 Σ_𝔭 N𝔭⁻²` and TauCeti's `Σ_𝔭 N𝔭⁻² ≤ 2n` (at most `n`
  primes lie over each rational prime).
* `norm_dedekindZeta_le_exp`, `norm_dedekindZetaEntire_le`: for `re s ≥ 2`,
  `‖ζ_K(s)‖ ≤ exp (4 n)` and `‖(s - 1) ζ_K(s)‖ ≤ ‖s - 1‖ exp (4 n)`.

The constant depends on `K` only through its degree; this is the right edge of the
Phragmén–Lindelöf argument for the growth of `(s - 1) ζ_K(s)` (step D4).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField IsDedekindDomain Module

variable (K : Type*) [Field K] [NumberField K]

/-- `‖ζ_K(s)‖ ≤ ζ_K(re s)` for `re s > 1`. -/
theorem norm_dedekindZeta_le_re {s : ℂ} (hs : 1 < s.re) :
    ‖dedekindZeta K s‖ ≤ (dedekindZeta K s.re).re := by
  have hS := hasSum_zetaTerm K hs
  have hnorm : ∀ n, ‖LSeries.term (fun n => (idealCount K n : ℂ)) s n‖ = zetaTerm K s.re n := by
    intro n
    rw [LSeries.norm_term_eq]
    unfold zetaTerm
    split_ifs with h
    · rfl
    · rw [Complex.norm_natCast, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  rw [dedekindZeta_eq_LSeries, LSeries]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact hS.summable.congr fun n => (hnorm n).symm
  · rw [tsum_congr hnorm, hS.tsum_eq]

/-- `σ ↦ ζ_K(σ)` is antitone on `(1, ∞)`. -/
theorem dedekindZeta_re_le_of_le {σ σ₁ : ℝ} (h1 : 1 < σ₁) (h : σ₁ ≤ σ) :
    (dedekindZeta K σ).re ≤ (dedekindZeta K σ₁).re := by
  refine hasSum_le (fun n => ?_) (hasSum_zetaTerm K (by linarith)) (hasSum_zetaTerm K h1)
  unfold zetaTerm
  split_ifs with hn
  · exact le_rfl
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      (Nat.cast_nonneg _)

/-- **`ζ_K(2) ≤ exp (4 [K : ℚ])`.** -/
theorem dedekindZeta_two_re_le :
    (dedekindZeta K (2 : ℝ)).re ≤ Real.exp (4 * finrank ℚ K) := by
  rw [TauCeti.dedekindZeta_re_eq_exp (by norm_num : (1 : ℝ) < 2)]
  refine Real.exp_le_exp.mpr ?_
  have hs := TauCeti.summable_neg_log_one_sub_absNorm_rpow (K := K) (by norm_num : (1 : ℝ) < 2)
  have hsum2 := TauCeti.summable_absNorm_rpow_primes_of_one_lt (K := K)
    (by norm_num : (1 : ℝ) < 2)
  have hP := TauCeti.tsum_absNorm_rpow_neg_two_le (K := K)
  calc ∑' P : HeightOneSpectrum (𝓞 K), -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)))
      ≤ ∑' P : HeightOneSpectrum (𝓞 K), 2 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
        refine hs.tsum_le_tsum (fun P => ?_) (hsum2.mul_left 2)
        have hx0 : 0 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)) := by positivity
        have hx := P.absNorm_rpow_neg_le_half (by norm_num : (1 : ℝ) ≤ 2)
        nlinarith [Real.neg_log_one_sub_le_add_two_mul_sq hx0 hx]
    _ = 2 * ∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)) :=
        tsum_mul_left
    _ ≤ 2 * (2 * finrank ℚ K) := by gcongr
    _ = 4 * finrank ℚ K := by ring

/-- **`‖ζ_K(s)‖ ≤ exp (4 [K : ℚ])` for `re s ≥ 2`.** -/
theorem norm_dedekindZeta_le_exp {s : ℂ} (hs : 2 ≤ s.re) :
    ‖dedekindZeta K s‖ ≤ Real.exp (4 * finrank ℚ K) :=
  (norm_dedekindZeta_le_re K (by linarith)).trans
    ((dedekindZeta_re_le_of_le K (by norm_num) hs).trans (dedekindZeta_two_re_le K))

/-- The entire function `dedekindZetaEntire K` is `(s - 1) ζ_K(s)` on `re s > 1`. -/
theorem dedekindZetaEntire_eq_mul {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaEntire K s = (s - 1) * dedekindZeta K s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    linarith
  rw [dedekindZetaEntire_eq K hs0 hs1, dedekindZetaHecke_eq K hs]

/-- **Right edge:** `‖(s - 1) ζ_K(s)‖ ≤ ‖s - 1‖ exp (4 [K : ℚ])` for `re s ≥ 2`. -/
theorem norm_dedekindZetaEntire_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖dedekindZetaEntire K s‖ ≤ ‖s - 1‖ * Real.exp (4 * finrank ℚ K) := by
  rw [dedekindZetaEntire_eq_mul K (by linarith), norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_dedekindZeta_le_exp K hs) (norm_nonneg _)

end SimultaneousPrimitiveRoots.Hecke

end
