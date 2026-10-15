module

public import SimultaneousPrimitiveRoots.Hecke.StripApriori
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Phragmén–Lindelöf: a uniform bound for `(s - 1) ζ_K(s)` in the strip `-1 ≤ Re s ≤ 2`

Apply `PhragmenLindelof.vertical_strip` to `G(s) = (s - 1) ζ_K(s) e^{n s²}` (`n = [K : ℚ]`). The
Gaussian factor `|e^{n s²}| = e^{n (σ² - t²)}` absorbs the polynomial and `e^{π n |t|}` growth on the
two edges (`norm_dedekindZetaEntire_le`, `norm_dedekindZetaEntire_le_left`), and the a priori
bound `exists_norm_dedekindZetaEntire_le_strip` is far below the Phragmén–Lindelöf threshold. The
result, uniform in `K`:

`‖(s - 1) ζ_K(s)‖ ≤ 4 e^{13 n} |d_K|^{3/2} e^{n t²}` for `-1 ≤ σ ≤ 2`
(`norm_dedekindZetaEntire_le_strip`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Module Complex Set Filter Asymptotics
open scoped Real Topology

/-- `log 16 ≤ 3`. -/
theorem log_sixteen_le_three : Real.log 16 ≤ 3 := by
  have h : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [h]
  have := Real.log_two_lt_d9
  linarith

/-- The left-edge numerics: `(2 + |t|) (16 e^{π|t|})^n e^{4n} e^{n(1 - t²)} ≤ 4 e^{13 n}`. -/
theorem left_edge_aux {n t : ℝ} (hn : 1 ≤ n) :
    (2 + |t|) * (16 * Real.exp (π * |t|)) ^ n * Real.exp (4 * n) * Real.exp (n * (1 - t ^ 2)) ≤
      4 * Real.exp (13 * n) := by
  have h16 : (16 * Real.exp (π * |t|)) ^ n = Real.exp (n * (Real.log 16 + π * |t|)) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp]
    ring_nf
  have h2t : 2 + |t| ≤ 4 * Real.exp (t ^ 2 / 2) := by
    have := Real.add_one_le_exp (t ^ 2 / 2)
    have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [abs_nonneg t, sq_nonneg (|t| - 1 / 4)]
  rw [h16]
  have hl := log_sixteen_le_three
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hexp : t ^ 2 / 2 + n * (Real.log 16 + π * |t|) + 4 * n + n * (1 - t ^ 2) ≤ 13 * n := by
    have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
    have h1 : t ^ 2 / 2 - n * t ^ 2 ≤ -(n * t ^ 2 / 2) := by nlinarith [sq_nonneg t]
    have h2 : n * (π * |t|) - n * t ^ 2 / 2 ≤ n * (π ^ 2 / 2) := by
      nlinarith [sq_nonneg (|t| - π), mul_nonneg (by linarith : (0 : ℝ) ≤ n) (sq_nonneg (|t| - π))]
    have h3 : π ^ 2 / 2 ≤ 5 := by nlinarith
    nlinarith
  calc (2 + |t|) * Real.exp (n * (Real.log 16 + π * |t|)) * Real.exp (4 * n) *
        Real.exp (n * (1 - t ^ 2))
      ≤ (4 * Real.exp (t ^ 2 / 2)) * Real.exp (n * (Real.log 16 + π * |t|)) * Real.exp (4 * n) *
        Real.exp (n * (1 - t ^ 2)) := by gcongr
    _ = 4 * Real.exp (t ^ 2 / 2 + n * (Real.log 16 + π * |t|) + 4 * n + n * (1 - t ^ 2)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]
        ring
    _ ≤ 4 * Real.exp (13 * n) := by gcongr

/-- The right-edge numerics: `(1 + |t|) e^{4n} e^{n(4 - t²)} ≤ 4 e^{13 n}`. -/
theorem right_edge_aux {n t : ℝ} (hn : 1 ≤ n) :
    (1 + |t|) * Real.exp (4 * n) * Real.exp (n * (4 - t ^ 2)) ≤ 4 * Real.exp (13 * n) := by
  have h1t : 1 + |t| ≤ 2 * Real.exp (t ^ 2) := by
    have := Real.add_one_le_exp (t ^ 2)
    have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [abs_nonneg t, sq_nonneg (|t| - 1 / 2)]
  calc (1 + |t|) * Real.exp (4 * n) * Real.exp (n * (4 - t ^ 2))
      ≤ (2 * Real.exp (t ^ 2)) * Real.exp (4 * n) * Real.exp (n * (4 - t ^ 2)) := by gcongr
    _ = 2 * Real.exp (t ^ 2 + 4 * n + n * (4 - t ^ 2)) := by
        rw [Real.exp_add, Real.exp_add]
        ring
    _ ≤ 4 * Real.exp (13 * n) := by
        have : t ^ 2 + 4 * n + n * (4 - t ^ 2) ≤ 13 * n := by nlinarith [sq_nonneg t]
        have := Real.exp_le_exp.mpr this
        have := Real.exp_pos (13 * n)
        linarith

variable (K : Type*) [Field K] [NumberField K]

theorem one_le_abs_discr : (1 : ℝ) ≤ |((discr K : ℤ) : ℝ)| := by
  have h := Int.one_le_abs (discr_ne_zero K)
  have : ((|discr K| : ℤ) : ℝ) = |((discr K : ℤ) : ℝ)| := Int.cast_abs
  rw [← this]
  exact_mod_cast h

theorem one_le_finrank_real : (1 : ℝ) ≤ finrank ℚ K := by
  exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)

theorem norm_exp_mul_sq (n : ℝ) (z : ℂ) :
    ‖Complex.exp (n * z ^ 2)‖ = Real.exp (n * (z.re ^ 2 - z.im ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq]

/-- **Phragmén–Lindelöf in the strip:** for `-1 ≤ Re s ≤ 2`,
`‖(s - 1) ζ_K(s)‖ ≤ 4 e^{13 n} |d_K|^{3/2} e^{n (Im s)²}`. -/
theorem norm_dedekindZetaEntire_le_strip {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖dedekindZetaEntire K s‖ ≤
      4 * Real.exp (13 * finrank ℚ K) * |((discr K : ℤ) : ℝ)| ^ (3 / 2 : ℝ) *
        Real.exp (finrank ℚ K * s.im ^ 2) := by
  set n : ℝ := (finrank ℚ K : ℝ) with hn
  set D : ℝ := |((discr K : ℤ) : ℝ)| with hD
  have hn1 : 1 ≤ n := one_le_finrank_real K
  have hD1 : 1 ≤ D := one_le_abs_discr K
  have hD32 : 1 ≤ D ^ (3 / 2 : ℝ) := Real.one_le_rpow hD1 (by norm_num)
  set M := 4 * Real.exp (13 * n) * D ^ (3 / 2 : ℝ) with hM
  set G : ℂ → ℂ := fun z => dedekindZetaEntire K z * Complex.exp (n * z ^ 2) with hG
  have hGd : Differentiable ℂ G :=
    (differentiable_dedekindZetaEntire K).mul (by fun_prop)
  have hGn : ∀ z, ‖G z‖ = ‖dedekindZetaEntire K z‖ * Real.exp (n * (z.re ^ 2 - z.im ^ 2)) := by
    intro z
    simp only [hG, norm_mul, norm_exp_mul_sq]
  have hPL : ‖G s‖ ≤ M := by
    refine PhragmenLindelof.vertical_strip (a := -1) (b := 2) hGd.diffContOnCl ?_ ?_ ?_ h1 h2
    · -- a priori bound
      obtain ⟨A, B, hAB⟩ := exists_norm_dedekindZetaEntire_le_strip K
      refine ⟨1, ?_, |B|, ?_⟩
      · rw [lt_div_iff₀ (by norm_num)]
        linarith [Real.pi_gt_three]
      refine IsBigO.of_bound (|A| * Real.exp (4 * n)) ?_
      have hev : ∀ᶠ z in comap (_root_.abs ∘ Complex.im) atTop ⊓
          𝓟 (Complex.re ⁻¹' Ioo (-1 : ℝ) 2), 1 ≤ |z.im| ∧ z.re ∈ Ioo (-1 : ℝ) 2 := by
        refine ((tendsto_comap.eventually (eventually_ge_atTop (1 : ℝ))).filter_mono
          inf_le_left).and ?_
        exact (eventually_principal.mpr fun z hz => hz).filter_mono inf_le_right
      filter_upwards [hev] with z ⟨hz1, hzre⟩
      rw [hGn]
      have hzb := hAB z hzre.1.le hzre.2.le hz1
      have hexp : Real.exp (n * (z.re ^ 2 - z.im ^ 2)) ≤ Real.exp (4 * n) := by
        refine Real.exp_le_exp.mpr ?_
        have : z.re ^ 2 ≤ 4 := by nlinarith [hzre.1, hzre.2]
        nlinarith [sq_nonneg z.im]
      have habs : |z.im| ≤ Real.exp |z.im| := by
        have := Real.add_one_le_exp (|z.im|)
        linarith
      have hB : B * |z.im| ≤ |B| * Real.exp (1 * |z.im|) := by
        rw [one_mul]
        calc B * |z.im| ≤ |B| * |z.im| := by
              gcongr
              exact le_abs_self B
          _ ≤ |B| * Real.exp |z.im| := by gcongr
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc ‖dedekindZetaEntire K z‖ * Real.exp (n * (z.re ^ 2 - z.im ^ 2))
          ≤ (|A| * Real.exp (B * |z.im|)) * Real.exp (4 * n) := by
            gcongr
            exact hzb.trans (by gcongr; exact le_abs_self A)
        _ ≤ (|A| * Real.exp (|B| * Real.exp (1 * |z.im|))) * Real.exp (4 * n) := by gcongr
        _ = |A| * Real.exp (4 * n) * Real.exp (|B| * Real.exp (1 * |z.im|)) := by ring
    · -- left edge `Re z = -1`
      intro z hz
      rw [hGn, hz]
      have hb := norm_dedekindZetaEntire_le_left K (s := z) (by rw [hz])
      rw [hz] at hb
      have h16 : (1 - (-1 : ℝ)) ^ (2 * (1 - (-1 : ℝ))) = 16 := by
        rw [show (2 : ℝ) * (1 - (-1)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      rw [h16, show (1 / 2 - (-1) : ℝ) = 3 / 2 by norm_num] at hb
      have hz1 : ‖z - 1‖ ≤ 2 + |z.im| := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
        simp [hz]
        norm_num
      have haux := left_edge_aux (t := z.im) hn1
      have hpos : 0 ≤ (16 * Real.exp (π * |z.im|)) ^ n := Real.rpow_nonneg (by positivity) _
      calc ‖dedekindZetaEntire K z‖ * Real.exp (n * ((-1) ^ 2 - z.im ^ 2))
          ≤ (‖z - 1‖ * (16 * Real.exp (π * |z.im|)) ^ n * D ^ (3 / 2 : ℝ) *
              Real.exp (4 * n)) * Real.exp (n * ((-1) ^ 2 - z.im ^ 2)) := by gcongr
        _ ≤ ((2 + |z.im|) * (16 * Real.exp (π * |z.im|)) ^ n * D ^ (3 / 2 : ℝ) *
              Real.exp (4 * n)) * Real.exp (n * ((-1) ^ 2 - z.im ^ 2)) := by gcongr
        _ = ((2 + |z.im|) * (16 * Real.exp (π * |z.im|)) ^ n * Real.exp (4 * n) *
              Real.exp (n * (1 - z.im ^ 2))) * D ^ (3 / 2 : ℝ) := by ring_nf
        _ ≤ (4 * Real.exp (13 * n)) * D ^ (3 / 2 : ℝ) := by gcongr
    · -- right edge `Re z = 2`
      intro z hz
      rw [hGn, hz]
      have hb := norm_dedekindZetaEntire_le K (s := z) (by rw [hz])
      have hz1 : ‖z - 1‖ ≤ 1 + |z.im| := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
        simp [hz]
        norm_num
      have haux := right_edge_aux (t := z.im) hn1
      calc ‖dedekindZetaEntire K z‖ * Real.exp (n * (2 ^ 2 - z.im ^ 2))
          ≤ (‖z - 1‖ * Real.exp (4 * n)) * Real.exp (n * (2 ^ 2 - z.im ^ 2)) := by gcongr
        _ ≤ ((1 + |z.im|) * Real.exp (4 * n)) * Real.exp (n * (2 ^ 2 - z.im ^ 2)) := by gcongr
        _ = (1 + |z.im|) * Real.exp (4 * n) * Real.exp (n * (4 - z.im ^ 2)) := by norm_num
        _ ≤ 4 * Real.exp (13 * n) := haux
        _ ≤ 4 * Real.exp (13 * n) * D ^ (3 / 2 : ℝ) := by
            have := Real.exp_pos (13 * n)
            nlinarith
  -- undo the Gaussian factor
  rw [hGn] at hPL
  have hpos := Real.exp_pos (n * (s.re ^ 2 - s.im ^ 2))
  have hF : ‖dedekindZetaEntire K s‖ ≤ M * Real.exp (n * (s.im ^ 2 - s.re ^ 2)) := by
    have : Real.exp (n * (s.im ^ 2 - s.re ^ 2)) = (Real.exp (n * (s.re ^ 2 - s.im ^ 2)))⁻¹ := by
      rw [← Real.exp_neg]
      ring_nf
    rw [this, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact hPL
  refine hF.trans ?_
  have hM0 : 0 ≤ M := by positivity
  gcongr
  nlinarith [sq_nonneg s.re]

end SimultaneousPrimitiveRoots.Hecke

end
