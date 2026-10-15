module

public import SimultaneousPrimitiveRoots.Hecke.StripBound

/-!
# The growth of `(s - 1) ζ_K(s)` on the whole plane (step D4)

Combining the three regions

* `Re s ≥ 2`: the Dirichlet series (`norm_dedekindZetaEntire_le`),
* `-1 ≤ Re s ≤ 2`: Phragmén–Lindelöf (`norm_dedekindZetaEntire_le_strip`),
* `Re s ≤ -1`: the functional equation (`norm_dedekindZetaEntire_le_left`),

gives the order-two bound, uniform in the number field `K`:

`‖(s - 1) ζ_K(s)‖ ≤ exp (20 (n + log |d_K|) (‖s‖ + 2)²)`  (`norm_dedekindZetaEntire_le_global`),

and on the circles `|z - 2| = 2(U + 2)` of the finite-contour argument,
`‖(z - 1) ζ_K(z)‖ ≤ exp (320 (n + log |d_K|) (U + 3)²)` (`norm_dedekindZetaEntire_le_sphere`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Module Complex Metric
open scoped Real

variable (K : Type*) [Field K] [NumberField K]

/-- **The growth of `(s - 1) ζ_K(s)`:** `‖(s - 1) ζ_K(s)‖ ≤ exp (20 (n + log |d_K|) (‖s‖ + 2)²)`. -/
theorem norm_dedekindZetaEntire_le_global (s : ℂ) :
    ‖dedekindZetaEntire K s‖ ≤
      Real.exp (20 * (finrank ℚ K + Real.log |((discr K : ℤ) : ℝ)|) * (‖s‖ + 2) ^ 2) := by
  set n : ℝ := (finrank ℚ K : ℝ) with hn
  set D : ℝ := |((discr K : ℤ) : ℝ)| with hD
  set R : ℝ := ‖s‖ + 2 with hR
  have hn1 : 1 ≤ n := one_le_finrank_real K
  have hD1 : 1 ≤ D := one_le_abs_discr K
  have hD0 : 0 < D := by linarith
  have hL : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hR2 : 2 ≤ R := by have := norm_nonneg s; linarith
  have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hRexp : R ≤ Real.exp R := by have := Real.add_one_le_exp R; linarith
  have hs1 : ‖s - 1‖ ≤ R := by
    have := norm_sub_le s 1
    rw [norm_one] at this
    linarith
  have hlogR : Real.log R ≤ R := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hR4 : 4 ≤ R ^ 2 := by nlinarith
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hnR : R ^ 2 ≤ n * R ^ 2 := by nlinarith [sq_nonneg R]
  have h4n : 4 * n ≤ n * R ^ 2 := by nlinarith
  have hLR0 : 0 ≤ Real.log D * R ^ 2 := mul_nonneg hL (sq_nonneg R)
  have hLR4 : 4 * Real.log D ≤ Real.log D * R ^ 2 := by nlinarith
  have hexpand : 20 * (n + Real.log D) * R ^ 2 = 20 * (n * R ^ 2) + 20 * (Real.log D * R ^ 2) := by
    ring
  rcases le_or_gt 2 s.re with h2 | h2
  · -- the Dirichlet series region
    refine (norm_dedekindZetaEntire_le K h2).trans ?_
    calc ‖s - 1‖ * Real.exp (4 * n) ≤ Real.exp R * Real.exp (4 * n) := by gcongr; linarith
      _ = Real.exp (R + 4 * n) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (20 * (n + Real.log D) * R ^ 2) := by
          refine Real.exp_le_exp.mpr ?_
          rw [hexpand]
          linarith
  rcases le_or_gt (-1) s.re with h1 | h1
  · -- the strip
    refine (norm_dedekindZetaEntire_le_strip K h1 h2.le).trans ?_
    have hD32 : D ^ (3 / 2 : ℝ) = Real.exp (Real.log D * (3 / 2)) := Real.rpow_def_of_pos hD0 _
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have h22 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have ht2 : s.im ^ 2 ≤ R ^ 2 := by
      have : |s.im| ≤ R := by linarith
      nlinarith [abs_nonneg s.im, sq_abs s.im]
    rw [hD32]
    calc 4 * Real.exp (13 * n) * Real.exp (Real.log D * (3 / 2)) * Real.exp (n * s.im ^ 2)
        ≤ Real.exp 2 * Real.exp (13 * n) * Real.exp (Real.log D * (3 / 2)) *
            Real.exp (n * s.im ^ 2) := by gcongr
      _ = Real.exp (2 + 13 * n + Real.log D * (3 / 2) + n * s.im ^ 2) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (20 * (n + Real.log D) * R ^ 2) := by
          refine Real.exp_le_exp.mpr ?_
          have hnt : n * s.im ^ 2 ≤ n * R ^ 2 := by gcongr
          rw [hexpand]
          linarith
  · -- the functional-equation region
    refine (norm_dedekindZetaEntire_le_left K h1.le).trans ?_
    set x := 1 - s.re with hx
    have hx2 : 2 ≤ x := by linarith
    have hxR : x ≤ R := by
      have : -s.re ≤ ‖s‖ := by have := neg_abs_le s.re; linarith [abs_le.mp hre]
      linarith
    have hx0 : 0 < x := by linarith
    -- `x^{2x} e^{π |t|} ≤ exp (2R² + 4R)`
    have hxx : x ^ (2 * x) ≤ Real.exp (2 * R ^ 2) := by
      rw [Real.rpow_def_of_pos hx0]
      refine Real.exp_le_exp.mpr ?_
      have hlx : Real.log x ≤ R := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
      have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      nlinarith
    have hpit : Real.exp (π * |s.im|) ≤ Real.exp (4 * R) := by
      refine Real.exp_le_exp.mpr ?_
      have := Real.pi_lt_d2
      have : |s.im| ≤ R := by linarith
      nlinarith [abs_nonneg s.im, Real.pi_pos]
    have hbase : x ^ (2 * x) * Real.exp (π * |s.im|) ≤ Real.exp (2 * R ^ 2 + 4 * R) := by
      rw [Real.exp_add]
      gcongr
    have hbase0 : 0 ≤ x ^ (2 * x) * Real.exp (π * |s.im|) := by positivity
    have hpow : (x ^ (2 * x) * Real.exp (π * |s.im|)) ^ n ≤ Real.exp ((2 * R ^ 2 + 4 * R) * n) := by
      rw [Real.exp_mul (2 * R ^ 2 + 4 * R) n]
      exact Real.rpow_le_rpow hbase0 hbase (by linarith)
    have hDpow : D ^ (1 / 2 - s.re) ≤ Real.exp (Real.log D * R) := by
      rw [← Real.rpow_def_of_pos hD0]
      exact Real.rpow_le_rpow_of_exponent_le hD1 (by linarith [abs_le.mp hre])
    calc ‖s - 1‖ * (x ^ (2 * x) * Real.exp (π * |s.im|)) ^ n * D ^ (1 / 2 - s.re) *
          Real.exp (4 * n)
        ≤ Real.exp R * Real.exp ((2 * R ^ 2 + 4 * R) * n) * Real.exp (Real.log D * R) *
            Real.exp (4 * n) := by
          gcongr
          linarith
      _ = Real.exp (R + (2 * R ^ 2 + 4 * R) * n + Real.log D * R + 4 * n) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (20 * (n + Real.log D) * R ^ 2) := by
          refine Real.exp_le_exp.mpr ?_
          have hLR : Real.log D * R ≤ Real.log D * R ^ 2 := by
            exact mul_le_mul_of_nonneg_left hRR hL
          have hRn : 4 * (R * n) ≤ 2 * (n * R ^ 2) := by
            have hn0 : 0 ≤ n := by linarith only [hn1]
            have hR0 : 0 ≤ R := by linarith only [hR2]
            have hmul := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hR2 hR0) hn0
            nlinarith only [hmul]
          have e1 : (2 * R ^ 2 + 4 * R) * n = 2 * (n * R ^ 2) + 4 * (R * n) := by ring
          rw [hexpand, e1]
          linarith

/-- **On the contour circles** `|z - 2| = 2(U + 2)`:
`‖(z - 1) ζ_K(z)‖ ≤ exp (320 (n + log |d_K|) (U + 3)²)`. -/
theorem norm_dedekindZetaEntire_le_sphere {U : ℝ} (hU : 0 ≤ U) {z : ℂ}
    (hz : z ∈ sphere (2 : ℂ) (2 * (U + 2))) :
    ‖dedekindZetaEntire K z‖ ≤
      Real.exp (320 * (finrank ℚ K + Real.log |((discr K : ℤ) : ℝ)|) * (U + 3) ^ 2) := by
  refine (norm_dedekindZetaEntire_le_global K z).trans (Real.exp_le_exp.mpr ?_)
  have hz' : ‖z - 2‖ = 2 * (U + 2) := by simpa [dist_eq_norm] using hz
  have hzn : ‖z‖ ≤ 2 * U + 6 := by
    have := norm_le_norm_add_norm_sub' z 2
    rw [Complex.norm_two] at this
    linarith [norm_sub_rev z 2]
  have hR : (‖z‖ + 2) ^ 2 ≤ 16 * (U + 3) ^ 2 := by
    have h0 := norm_nonneg z
    nlinarith
  have hn1 := one_le_finrank_real K
  have hL : 0 ≤ Real.log |((discr K : ℤ) : ℝ)| := Real.log_nonneg (one_le_abs_discr K)
  have hc : 0 ≤ 20 * ((finrank ℚ K : ℝ) + Real.log |((discr K : ℤ) : ℝ)|) := by positivity
  calc 20 * ((finrank ℚ K : ℝ) + Real.log |((discr K : ℤ) : ℝ)|) * (‖z‖ + 2) ^ 2
      ≤ 20 * ((finrank ℚ K : ℝ) + Real.log |((discr K : ℤ) : ℝ)|) * (16 * (U + 3) ^ 2) := by
        gcongr
    _ = 320 * ((finrank ℚ K : ℝ) + Real.log |((discr K : ℤ) : ℝ)|) * (U + 3) ^ 2 := by ring

end SimultaneousPrimitiveRoots.Hecke

end
