module

public import SimultaneousPrimitiveRoots.Hecke.DirichletBound
public import SimultaneousPrimitiveRoots.Hecke.DedekindFE
public import SimultaneousPrimitiveRoots.Hecke.GammaBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# A uniform bound for `(s - 1) ζ_K(s)` on `Re s ≤ -1`

By the functional equation, `(s - 1) ζ_K(s) = (s - 1) C(s)/C(1 - s) |d_K|^{1/2 - s} ζ_K(1 - s)`
where `C = zetaCoefCommon K` collects the Gamma factors, and `ζ_K(1 - s)` is bounded by
`exp (4 n)` (`norm_dedekindZeta_le_exp`). The Gamma ratio is bounded place by place with
`‖Γ(z)⁻¹‖ ≤ Γ(1 - re z) e^{π |im z|}/π`, `‖Γ(z)‖ ≤ Γ(re z)` and `Γ(x) ≤ x^x` (`x ≥ 1`):

`‖(s - 1) ζ_K(s)‖ ≤ ‖s - 1‖ ((1 - σ)^{2(1 - σ)} e^{π |t|})^n |d_K|^{1/2 - σ} e^{4n}`

for `s = σ + it`, `σ ≤ -1` (`norm_dedekindZetaEntire_le_left`). This is the left edge of the
Phragmén–Lindelöf argument (step D4), uniform in `K` through `n = [K : ℚ]` and `|d_K|`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units Module Complex
open scoped Real

/-- `Γ(x) ≤ x ^ x` for `x ≥ 1`. -/
theorem Gamma_le_rpow_self {x : ℝ} (hx : 1 ≤ x) : Real.Gamma x ≤ x ^ x := by
  have h1 : (1 : ℝ) ≤ x ^ x := Real.one_le_rpow hx (by linarith)
  rcases le_or_gt x 2 with h2 | h2
  · have hseg : x ∈ segment ℝ (1 : ℝ) 2 := by
      rw [segment_eq_Icc (by norm_num)]
      exact ⟨hx, h2⟩
    have := Real.convexOn_Gamma.le_on_segment (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) hseg
    rw [Real.Gamma_one, Real.Gamma_two, max_self] at this
    linarith
  · have hceil : x ≤ ⌈x⌉₊ := Nat.le_ceil x
    have hceil1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
    have hm1 : 1 ≤ ⌈x⌉₊ := by
      have : (1 : ℝ) ≤ ⌈x⌉₊ := by linarith
      exact_mod_cast this
    set m := ⌈x⌉₊ - 1 with hm
    have hmx : (m : ℝ) + 1 = ⌈x⌉₊ := by
      rw [hm, Nat.cast_sub hm1]
      push_cast
      ring
    have hGm : Real.Gamma x ≤ Real.Gamma ((m : ℝ) + 1) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr h2.le)
        (Set.mem_Ici.mpr (by rw [hmx]; linarith)) (by rw [hmx]; exact hceil)
    rw [Real.Gamma_nat_eq_factorial] at hGm
    have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
    have hmle : (m : ℝ) ≤ x := by linarith
    calc Real.Gamma x ≤ m.factorial := hGm
      _ ≤ (m : ℝ) ^ m := hfac
      _ ≤ x ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) hmle m
      _ = x ^ (m : ℝ) := (Real.rpow_natCast x m).symm
      _ ≤ x ^ x := Real.rpow_le_rpow_of_exponent_le hx hmle

/-- `y ↦ y ^ y` is monotone on `[1, ∞)`. -/
theorem rpow_self_le_rpow_self {y x : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) : y ^ y ≤ x ^ x :=
  (Real.rpow_le_rpow (by linarith) hyx (by linarith)).trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hyx)

/-- The Gamma ratio at one place: for `re s ≤ -1` and `1 ≤ m ≤ 2`,
`‖Γ(sm/2)⁻¹‖ ‖Γ((1-s)m/2)‖ ≤ ((1 - σ)^{2(1 - σ)} e^{π |t|})^m`. -/
theorem norm_inv_Gamma_mul_norm_Gamma_le {s : ℂ} (hs : s.re ≤ -1) {m : ℝ} (hm1 : 1 ≤ m)
    (hm2 : m ≤ 2) :
    ‖(Complex.Gamma (s * m / 2))⁻¹‖ * ‖Complex.Gamma ((1 - s) * m / 2)‖ ≤
      ((1 - s.re) ^ (2 * (1 - s.re)) * Real.exp (π * |s.im|)) ^ m := by
  set x := 1 - s.re with hx
  have hx2 : 2 ≤ x := by linarith
  have hre1 : (s * m / 2).re = s.re * m / 2 := by simp
  have him1 : (s * m / 2).im = s.im * m / 2 := by simp
  have hre2 : ((1 - s) * m / 2).re = (1 - s.re) * m / 2 := by simp
  have hA := norm_inv_Gamma_le (s := s * m / 2) (by rw [hre1]; nlinarith)
  have hB := norm_Gamma_le_Gamma_re (s := (1 - s) * m / 2) (by rw [hre2]; nlinarith)
  rw [hre1, him1] at hA
  rw [hre2] at hB
  have hy1 : 1 ≤ 1 - s.re * m / 2 := by nlinarith
  have hy1' : 1 - s.re * m / 2 ≤ x := by nlinarith
  have hz1 : 1 ≤ (1 - s.re) * m / 2 := by nlinarith
  have hz1' : (1 - s.re) * m / 2 ≤ x := by nlinarith
  have hGy : Real.Gamma (1 - s.re * m / 2) ≤ x ^ x :=
    (Gamma_le_rpow_self hy1).trans (rpow_self_le_rpow_self hy1 hy1')
  have hGz : Real.Gamma ((1 - s.re) * m / 2) ≤ x ^ x :=
    (Gamma_le_rpow_self hz1).trans (rpow_self_le_rpow_self hz1 hz1')
  have hxx : 1 ≤ x ^ x := Real.one_le_rpow (by linarith) (by linarith)
  have habs : |s.im * m / 2| = |s.im| * m / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < m), abs_two]
  rw [habs] at hA
  have hexp : Real.exp (π * (|s.im| * m / 2)) ≤ Real.exp (π * |s.im|) ^ m := by
    rw [← Real.exp_mul]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ π * |s.im| * m := by
      have := abs_nonneg s.im
      have := Real.pi_pos
      positivity
    linarith
  have hpi : 1 ≤ π := by linarith [Real.pi_gt_three]
  have hG0 : 0 ≤ Real.Gamma (1 - s.re * m / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hstep1 : ‖(Complex.Gamma (s * m / 2))⁻¹‖ ≤ x ^ x * Real.exp (π * |s.im|) ^ m := by
    refine hA.trans ?_
    rw [div_le_iff₀ Real.pi_pos]
    calc Real.Gamma (1 - s.re * m / 2) * Real.exp (π * (|s.im| * m / 2))
        ≤ x ^ x * Real.exp (π * |s.im|) ^ m := by gcongr
      _ ≤ x ^ x * Real.exp (π * |s.im|) ^ m * π := by
        have : 0 ≤ x ^ x * Real.exp (π * |s.im|) ^ m := by positivity
        nlinarith
  have hpow : x ^ (2 * x) = x ^ x * x ^ x := by
    rw [two_mul, Real.rpow_add (by linarith)]
  calc ‖(Complex.Gamma (s * m / 2))⁻¹‖ * ‖Complex.Gamma ((1 - s) * m / 2)‖
      ≤ (x ^ x * Real.exp (π * |s.im|) ^ m) * x ^ x := by
        gcongr
        exact hB.trans hGz
    _ = x ^ (2 * x) * Real.exp (π * |s.im|) ^ m := by rw [hpow]; ring
    _ ≤ (x ^ (2 * x)) ^ m * Real.exp (π * |s.im|) ^ m := by
        gcongr
        have h2x : 1 ≤ x ^ (2 * x) := Real.one_le_rpow (by linarith) (by linarith)
        calc x ^ (2 * x) = (x ^ (2 * x)) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (x ^ (2 * x)) ^ m := Real.rpow_le_rpow_of_exponent_le h2x hm1
    _ = (x ^ (2 * x) * Real.exp (π * |s.im|)) ^ m := by
        rw [Real.mul_rpow (by positivity) (by positivity)]

/-- The factor of one place of `zetaCoefCommon`. -/
theorem norm_placeFactor_le {s : ℂ} (hs : s.re ≤ -1) {m : ℝ} (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    ‖((m : ℝ) : ℂ) ^ (s * m / 2) * (Complex.Gamma (s * m / 2))⁻¹‖ ≤
      ((1 - s.re) ^ (2 * (1 - s.re)) * Real.exp (π * |s.im|)) ^ m *
        ‖((m : ℝ) : ℂ) ^ ((1 - s) * m / 2) * (Complex.Gamma ((1 - s) * m / 2))⁻¹‖ := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hre2 : 0 < ((1 - s) * m / 2).re := by
    have : ((1 - s) * m / 2).re = (1 - s.re) * m / 2 := by simp
    rw [this]
    nlinarith
  have hG := Complex.Gamma_ne_zero_of_re_pos hre2
  have hGn : 0 < ‖Complex.Gamma ((1 - s) * m / 2)‖ := norm_pos_iff.mpr hG
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hm0,
    Complex.norm_cpow_eq_rpow_re_of_pos hm0, norm_inv (Complex.Gamma ((1 - s) * m / 2))]
  have hre_a : (s * m / 2).re = s.re * m / 2 := by simp
  have hre_b : ((1 - s) * m / 2).re = (1 - s.re) * m / 2 := by simp
  rw [hre_a, hre_b]
  have hmpow : m ^ (s.re * m / 2) ≤ m ^ ((1 - s.re) * m / 2) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by nlinarith)
  have hkey := norm_inv_Gamma_mul_norm_Gamma_le hs hm1 hm2
  set B := ((1 - s.re) ^ (2 * (1 - s.re)) * Real.exp (π * |s.im|)) ^ m
  have hinv : ‖(Complex.Gamma (s * m / 2))⁻¹‖ ≤ B * ‖Complex.Gamma ((1 - s) * m / 2)‖⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hGn]
    exact hkey
  have hB0 : 0 ≤ B := Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.exp_pos _).le) _
  calc m ^ (s.re * m / 2) * ‖(Complex.Gamma (s * m / 2))⁻¹‖
      ≤ m ^ ((1 - s.re) * m / 2) * (B * ‖Complex.Gamma ((1 - s) * m / 2)‖⁻¹) := by
        gcongr
    _ = B * (m ^ ((1 - s.re) * m / 2) * ‖Complex.Gamma ((1 - s) * m / 2)‖⁻¹) := by ring

variable (K : Type*) [Field K] [NumberField K]

theorem placeMult_le_two (o : Option (Fin (rank K))) : placeMult (K := K) o ≤ 2 := by
  unfold placeMult InfinitePlace.mult
  split_ifs <;> norm_num

theorem one_le_placeMult (o : Option (Fin (rank K))) : 1 ≤ placeMult (K := K) o := by
  unfold placeMult
  exact InfinitePlace.one_le_mult

/-- **The Gamma ratio of `ζ_K`:** `‖C(s)‖ ≤ ((1 - σ)^{2(1 - σ)} e^{π |t|})^n ‖C(1 - s)‖` for
`re s ≤ -1`. -/
theorem norm_zetaCoefCommon_le {s : ℂ} (hs : s.re ≤ -1) :
    ‖zetaCoefCommon K s‖ ≤
      ((1 - s.re) ^ (2 * (1 - s.re)) * Real.exp (π * |s.im|)) ^ (finrank ℚ K : ℝ) *
        ‖zetaCoefCommon K (1 - s)‖ := by
  set B := (1 - s.re) ^ (2 * (1 - s.re)) * Real.exp (π * |s.im|)
  have hB0 : 0 < B := mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.exp_pos _)
  have hπ : (0 : ℝ) < π := Real.pi_pos
  unfold zetaCoefCommon
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_prod, norm_prod,
    Complex.norm_cpow_eq_rpow_re_of_pos hπ, Complex.norm_cpow_eq_rpow_re_of_pos hπ]
  have hprod : ∏ o, ‖((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
      (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹‖ ≤
      ∏ o, (B ^ placeMult (K := K) o *
        ‖((placeMult (K := K) o : ℝ) : ℂ) ^ ((1 - s) * placeMult (K := K) o / 2) *
          (Complex.Gamma ((1 - s) * placeMult (K := K) o / 2))⁻¹‖) :=
    Finset.prod_le_prod (fun o _ => norm_nonneg _)
      (fun o _ => norm_placeFactor_le hs (one_le_placeMult K o) (placeMult_le_two K o))
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hB0, sum_placeMult] at hprod
  have hre1 : ((finrank ℚ K : ℂ) * s / 2).re = (finrank ℚ K : ℝ) * s.re / 2 := by simp
  have hre2 : ((finrank ℚ K : ℂ) * (1 - s) / 2).re = (finrank ℚ K : ℝ) * (1 - s.re) / 2 := by
    simp
  rw [hre1, hre2]
  have hπpow : π ^ ((finrank ℚ K : ℝ) * s.re / 2) ≤ π ^ ((finrank ℚ K : ℝ) * (1 - s.re) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
      (by have := finrank_pos_real K; nlinarith)
  have hP0 : 0 ≤ ∏ o, ‖((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
      (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹‖ :=
    Finset.prod_nonneg fun o _ => norm_nonneg _
  have hBn : 0 ≤ B ^ (finrank ℚ K : ℝ) := Real.rpow_nonneg hB0.le _
  rw [div_le_iff₀ (by
    have : (torsionOrder K : ℂ) ≠ 0 := by exact_mod_cast torsionOrder_ne_zero K
    exact norm_pos_iff.mpr this)]
  rw [mul_div_assoc', div_mul_cancel₀ _ (by
    have : (torsionOrder K : ℂ) ≠ 0 := by exact_mod_cast torsionOrder_ne_zero K
    exact (norm_pos_iff.mpr this).ne')]
  calc ‖((|LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K)))| : ℝ) : ℂ)‖ *
        π ^ ((finrank ℚ K : ℝ) * s.re / 2) *
        ∏ o, ‖((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
          (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹‖
      ≤ ‖((|LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K)))| : ℝ) : ℂ)‖ *
        π ^ ((finrank ℚ K : ℝ) * (1 - s.re) / 2) *
        (B ^ (finrank ℚ K : ℝ) *
          ∏ o, ‖((placeMult (K := K) o : ℝ) : ℂ) ^ ((1 - s) * placeMult (K := K) o / 2) *
            (Complex.Gamma ((1 - s) * placeMult (K := K) o / 2))⁻¹‖) := by
        gcongr
    _ = B ^ (finrank ℚ K : ℝ) *
        (‖((|LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K)))| : ℝ) : ℂ)‖ *
          π ^ ((finrank ℚ K : ℝ) * (1 - s.re) / 2) *
          ∏ o, ‖((placeMult (K := K) o : ℝ) : ℂ) ^ ((1 - s) * placeMult (K := K) o / 2) *
            (Complex.Gamma ((1 - s) * placeMult (K := K) o / 2))⁻¹‖) := by ring

/-- `(s - 1) ζ_K(s) = (s - 1) C(s) Ξ_K(s)` away from `0, 1`. -/
theorem dedekindZetaEntire_eq_xi {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    dedekindZetaEntire K s = (s - 1) * (zetaCoefCommon K s * dedekindXi K s) := by
  rw [dedekindZetaEntire_eq K hs0 hs1, dedekindZetaHecke_eq_mul_xi]

/-- **Left edge:** for `re s ≤ -1`,
`‖(s - 1) ζ_K(s)‖ ≤ ‖s - 1‖ ((1 - σ)^{2(1 - σ)} e^{π |t|})^n |d_K|^{1/2 - σ} e^{4n}`. -/
theorem norm_dedekindZetaEntire_le_left {s : ℂ} (hs : s.re ≤ -1) :
    ‖dedekindZetaEntire K s‖ ≤ ‖s - 1‖ *
      ((1 - s.re) ^ (2 * (1 - s.re)) * Real.exp (π * |s.im|)) ^ (finrank ℚ K : ℝ) *
      |((discr K : ℤ) : ℝ)| ^ (1 / 2 - s.re) * Real.exp (4 * finrank ℚ K) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    linarith
  have ht0 : 1 - s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have ht1 : 1 - s ≠ 1 := by
    intro h
    exact hs0 (by linear_combination -h)
  have hre : 1 < (1 - s).re := by simp; linarith
  have hre2 : 2 ≤ (1 - s).re := by simp; linarith
  set D : ℝ := |((discr K : ℤ) : ℝ)| with hD
  have hD0 : 0 < D := by
    rw [hD, abs_pos]
    exact_mod_cast discr_ne_zero K
  -- the functional equation at `1 - s`
  have hFE := dedekindXi_FE K ht0 ht1
  rw [sub_sub_cancel] at hFE
  -- `ζ_K(1 - s) = C(1 - s) Ξ_K(1 - s)`
  have hζ : dedekindZeta K (1 - s) = zetaCoefCommon K (1 - s) * dedekindXi K (1 - s) := by
    rw [← dedekindZetaHecke_eq K hre, dedekindZetaHecke_eq_mul_xi]
  have hζb := norm_dedekindZeta_le_exp K hre2
  have hC := norm_zetaCoefCommon_le K hs
  rw [dedekindZetaEntire_eq_xi K hs0 hs1, hFE]
  have hDn : ‖(D : ℂ) ^ (1 - s - 1 / 2)‖ = D ^ (1 / 2 - s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hD0]
    congr 1
    simp
    ring
  set B := ((1 - s.re) ^ (2 * (1 - s.re)) * Real.exp (π * |s.im|)) ^ (finrank ℚ K : ℝ)
  have hB0 : 0 ≤ B := Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.exp_pos _).le) _
  rw [norm_mul, norm_mul, norm_mul, hDn]
  calc ‖s - 1‖ * (‖zetaCoefCommon K s‖ * (D ^ (1 / 2 - s.re) * ‖dedekindXi K (1 - s)‖))
      ≤ ‖s - 1‖ * ((B * ‖zetaCoefCommon K (1 - s)‖) *
          (D ^ (1 / 2 - s.re) * ‖dedekindXi K (1 - s)‖)) := by gcongr
    _ = ‖s - 1‖ * B * D ^ (1 / 2 - s.re) *
          (‖zetaCoefCommon K (1 - s)‖ * ‖dedekindXi K (1 - s)‖) := by ring
    _ = ‖s - 1‖ * B * D ^ (1 / 2 - s.re) * ‖dedekindZeta K (1 - s)‖ := by
          rw [hζ, norm_mul]
    _ ≤ ‖s - 1‖ * B * D ^ (1 / 2 - s.re) * Real.exp (4 * finrank ℚ K) := by gcongr

end SimultaneousPrimitiveRoots.Hecke

end
