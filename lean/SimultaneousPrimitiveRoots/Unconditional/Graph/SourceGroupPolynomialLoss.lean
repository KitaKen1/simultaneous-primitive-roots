module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourceEventualGhostOperator
import Mathlib.Tactic.Ring

/-!
# Polynomial loss from the number of source prime groups

The small and big families each have at most C0*log(L) members. We retain
the factor two and convert products of uniformly bounded scalar norms to an
explicit power of L. This is a bound for the product of individual norms;
construction and norm identification of the tensor operator remain separate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

noncomputable def sourceGhostNormExponent (ρ Vplus v : ℝ) : ℝ :=
  (2 * max 1 Vplus / ρ + 1 / ρ) * v

theorem source_ghost_norm_exponent_nonneg (ρ Vplus v : ℝ)
    (hρ : 0 < ρ) (hv : 0 ≤ v) : 0 ≤ sourceGhostNormExponent ρ Vplus v := by
  have hmax : 0 ≤ max 1 Vplus := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  exact mul_nonneg (add_nonneg (div_nonneg (mul_nonneg (by norm_num) hmax) hρ.le)
    (div_nonneg zero_le_one hρ.le)) hv

theorem source_ghost_uniform_norm_eq_exp (ρ Vplus v : ℝ) :
    Real.sqrt (Real.exp ((2 * max 1 Vplus / ρ) * v * 2) *
      Real.exp ((1 / ρ) * v * 2)) = Real.exp (sourceGhostNormExponent ρ Vplus v) := by
  have he : Real.exp ((2 * max 1 Vplus / ρ) * v * 2) *
      Real.exp ((1 / ρ) * v * 2) = Real.exp (sourceGhostNormExponent ρ Vplus v) ^ 2 := by
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    unfold sourceGhostNormExponent
    ring
  rw [he, Real.sqrt_sq (Real.exp_pos _).le]

theorem source_finite_norm_product_polynomial {G : Type*} (groups : Finset G)
    (F : G → ℝ) (L B C0 : ℝ) (hL : 0 < L) (hB : 0 ≤ B)
    (hcard : (groups.card : ℝ) ≤ C0 * Real.log L)
    (hF0 : ∀ g ∈ groups, 0 ≤ F g) (hF : ∀ g ∈ groups, F g ≤ Real.exp B) :
    (∏ g ∈ groups, F g) ≤ L ^ (B * C0) := by
  calc
    _ ≤ ∏ _g ∈ groups, Real.exp B := Finset.prod_le_prod hF0 hF
    _ = Real.exp ((groups.card : ℝ) * B) := by rw [← Real.exp_sum]; simp
    _ ≤ Real.exp ((C0 * Real.log L) * B) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard hB)
    _ = _ := by rw [Real.rpow_def_of_pos hL]; congr 1; ring

theorem source_two_family_group_count_bound {G : Type*} [DecidableEq G]
    (small big : Finset G) (L C0 : ℝ)
    (hsmall : (small.card : ℝ) ≤ C0 * Real.log L)
    (hbig : (big.card : ℝ) ≤ C0 * Real.log L) :
    ((small ∪ big).card : ℝ) ≤ (2 * C0) * Real.log L := by
  have hc : ((small ∪ big).card : ℝ) ≤ (small.card : ℝ) + (big.card : ℝ) := by
    exact_mod_cast Finset.card_union_le small big
  linarith

theorem source_two_family_norm_product_polynomial {G : Type*} [DecidableEq G]
    (small big : Finset G) (F : G → ℝ) (L B C0 : ℝ) (hL : 0 < L) (hB : 0 ≤ B)
    (hsmall : (small.card : ℝ) ≤ C0 * Real.log L)
    (hbig : (big.card : ℝ) ≤ C0 * Real.log L)
    (hF0 : ∀ g ∈ small ∪ big, 0 ≤ F g)
    (hF : ∀ g ∈ small ∪ big, F g ≤ Real.exp B) :
    (∏ g ∈ small ∪ big, F g) ≤ L ^ (B * (2 * C0)) :=
  source_finite_norm_product_polynomial (small ∪ big) F L B (2 * C0) hL hB
    (source_two_family_group_count_bound small big L C0 hsmall hbig) hF0 hF

theorem source_ghost_group_norm_product_polynomial {G : Type*} [DecidableEq G]
    (small big : Finset G) (F : G → ℝ) (L C0 ρ Vplus v : ℝ)
    (hL : 0 < L) (hρ : 0 < ρ) (hv : 0 ≤ v)
    (hsmall : (small.card : ℝ) ≤ C0 * Real.log L)
    (hbig : (big.card : ℝ) ≤ C0 * Real.log L)
    (hF0 : ∀ g ∈ small ∪ big, 0 ≤ F g)
    (hF : ∀ g ∈ small ∪ big, F g ≤
      Real.sqrt (Real.exp ((2 * max 1 Vplus / ρ) * v * 2) *
        Real.exp ((1 / ρ) * v * 2))) :
    (∏ g ∈ small ∪ big, F g) ≤ L ^ (sourceGhostNormExponent ρ Vplus v * (2 * C0)) := by
  apply source_two_family_norm_product_polynomial small big F L _ C0 hL
    (source_ghost_norm_exponent_nonneg ρ Vplus v hρ hv) hsmall hbig hF0
  intro g hg
  simpa only [source_ghost_uniform_norm_eq_exp] using hF g hg

end SimultaneousPrimitiveRoots.Unconditional.Graph
