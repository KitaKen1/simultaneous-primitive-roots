module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostRowBounds
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

/-!
# Uniform ghost coefficients from the actual q/rho/V source formulas

Internal visits use q and endpoint visits use sqrt(q). The source coefficients
A=q_i/rho^2, D=-(1-q_i)/rho and C=V*D admit one auxiliary weight chosen before
all visits and groups. Birth multipliers in [0,2] include the doubled-birth
version, without changing deletion or continuing-hit coefficients.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

noncomputable def sourceGhostA (qi ρ : ℝ) : ℝ := qi / ρ ^ 2
noncomputable def sourceGhostD (qi ρ : ℝ) : ℝ := -(1 - qi) / ρ
noncomputable def sourceGhostC (V qi ρ : ℝ) : ℝ := V * sourceGhostD qi ρ

theorem source_ghost_visit_range (q qi : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hqi : qi = q ∨ qi = Real.sqrt q) :
    0 ≤ qi ∧ qi ≤ 1 ∧ qi ≤ Real.sqrt q := by
  have hs0 := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1.le
  have hqs : q ≤ Real.sqrt q := by
    have h := mul_nonneg hs0 (sub_nonneg.mpr hs1)
    nlinarith [Real.sq_sqrt hq0.le]
  rcases hqi with rfl | rfl
  · exact ⟨hq0.le, hq1.le, hqs⟩
  · exact ⟨hs0, hs1, le_rfl⟩

theorem source_ghost_A_bounds (q qi ρ : ℝ) (_hρ : 0 < ρ)
    (hqi0 : 0 ≤ qi) (hqi : qi ≤ Real.sqrt q) :
    0 ≤ sourceGhostA qi ρ ∧ sourceGhostA qi ρ ≤ Real.sqrt q / ρ ^ 2 := by
  exact ⟨div_nonneg hqi0 (sq_nonneg ρ),
    div_le_div_of_nonneg_right hqi (sq_nonneg ρ)⟩

theorem source_ghost_D_bound (qi ρ : ℝ) (hρ : 0 < ρ)
    (hqi0 : 0 ≤ qi) (hqi1 : qi ≤ 1) : |sourceGhostD qi ρ| ≤ 1 / ρ := by
  unfold sourceGhostD
  rw [abs_div, abs_neg, abs_of_nonneg (sub_nonneg.mpr hqi1), abs_of_pos hρ]
  exact div_le_div_of_nonneg_right (by linarith) hρ.le

theorem source_ghost_scaled_C_bound (V Vplus qi ρ γ : ℝ) (hρ : 0 < ρ)
    (hqi0 : 0 ≤ qi) (hqi1 : qi ≤ 1) (hV0 : 0 ≤ V) (hV : V ≤ Vplus)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2) :
    |γ * sourceGhostC V qi ρ| ≤ 2 * max 1 Vplus / ρ := by
  have hprod : γ * V ≤ 2 * max 1 Vplus :=
    (mul_le_mul_of_nonneg_right hγ hV0).trans
      (mul_le_mul_of_nonneg_left (hV.trans (le_max_right 1 Vplus)) (by norm_num))
  have hmax : 0 ≤ 2 * max 1 Vplus := by
    have : 1 ≤ max 1 Vplus := le_max_left _ _
    linarith
  rw [sourceGhostC, abs_mul, abs_mul, abs_of_nonneg hγ0, abs_of_nonneg hV0]
  calc
    _ = γ * V * |sourceGhostD qi ρ| := by ring
    _ ≤ (2 * max 1 Vplus) * (1 / ρ) :=
      mul_le_mul hprod (source_ghost_D_bound qi ρ hρ hqi0 hqi1) (abs_nonneg _) hmax
    _ = _ := by ring

theorem source_ghost_Amax_lt_one (q ρ : ℝ) (hρ : 0 < ρ)
    (hgap : Real.sqrt q < ρ ^ 2) : Real.sqrt q / ρ ^ 2 < 1 := by
  exact (div_lt_one (sq_pos_of_pos hρ)).mpr hgap

theorem exists_source_ghost_uniform_weight (q ρ Vplus : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ ^ 2) :
    ∃ v : ℝ, 1 < v ∧ ∀ qi V γ : ℝ,
      (qi = q ∨ qi = Real.sqrt q) → 0 ≤ V → V ≤ Vplus → 0 ≤ γ → γ ≤ 2 →
      0 ≤ sourceGhostA qi ρ ∧
      sourceGhostA qi ρ + |sourceGhostD qi ρ| / v < 1 ∧
      sourceGhostA qi ρ + |γ * sourceGhostC V qi ρ| / v < 1 ∧
      |sourceGhostD qi ρ| ≤ 1 / ρ ∧
      |γ * sourceGhostC V qi ρ| ≤ 2 * max 1 Vplus / ρ := by
  have hd : 0 ≤ 1 / ρ := div_nonneg zero_le_one hρ.le
  have hc : 0 ≤ 2 * max 1 Vplus / ρ := by
    apply div_nonneg _ hρ.le
    have : 1 ≤ max 1 Vplus := le_max_left _ _
    linarith
  obtain ⟨v, hv, hbound⟩ := exists_uniform_ghost_auxiliary_weight
    (Real.sqrt q / ρ ^ 2) (1 / ρ) (2 * max 1 Vplus / ρ)
    (source_ghost_Amax_lt_one q ρ hρ hgap) hd hc
  refine ⟨v, hv, ?_⟩
  intro qi V γ hqi hV0 hV hγ0 hγ
  obtain ⟨hqi0, hqi1, hqis⟩ := source_ghost_visit_range q qi hq0 hq1 hqi
  obtain ⟨hA0, hA⟩ := source_ghost_A_bounds q qi ρ hρ hqi0 hqis
  have hD := source_ghost_D_bound qi ρ hρ hqi0 hqi1
  have hC := source_ghost_scaled_C_bound V Vplus qi ρ γ hρ hqi0 hqi1 hV0 hV hγ0 hγ
  obtain ⟨hbaseD, hbaseC⟩ := hbound (sourceGhostA qi ρ) (sourceGhostD qi ρ)
    (γ * sourceGhostC V qi ρ) hA hD hC
  exact ⟨hA0, hbaseD, hbaseC, hD, hC⟩

end SimultaneousPrimitiveRoots.Unconditional.Graph
