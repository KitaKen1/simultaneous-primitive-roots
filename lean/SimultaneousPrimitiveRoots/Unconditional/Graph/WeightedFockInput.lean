module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.WeightedFockOutput
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostFiniteSupportLinearity
import Mathlib.Tactic.Ring

/-!
# Dense finite-support input in the original factorial-weighted Fock norm

Finite-support inputs embed in counting ell-two after multiplication by the
square root of their original factorial point masses. The embedding is
complex linear, has the exact original weighted square norm, and has dense
range when the point masses are positive. No alternative Finsupp norm is used.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ENNReal Classical

variable {I Z : Type*}

noncomputable def finiteSupportWeightedLp (c : I → ℂ) (g : I →₀ ℂ) :
    lp (fun _ : I => ℂ) 2 :=
  g.sum (fun i a => lp.single (E := fun _ : I => ℂ) 2 i (c i * a))

theorem finite_support_weighted_lp_add (c : I → ℂ) (g h : I →₀ ℂ) :
    finiteSupportWeightedLp c (g + h) = finiteSupportWeightedLp c g +
      finiteSupportWeightedLp c h := by
  classical
  unfold finiteSupportWeightedLp
  apply Finsupp.sum_add_index
  · intro i _
    simp
  · intro i _ a b
    rw [mul_add, lp.single_add]

theorem finite_support_weighted_lp_smul (c : I → ℂ) (a : ℂ) (g : I →₀ ℂ) :
    finiteSupportWeightedLp c (a • g) = a • finiteSupportWeightedLp c g := by
  classical
  unfold finiteSupportWeightedLp
  rw [Finsupp.sum_smul_index (fun _ => by simp)]
  unfold Finsupp.sum
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← lp.single_smul]
  apply congrArg (lp.single (E := fun _ : I => ℂ) 2 i)
  change c i * (a * g i) = a * (c i * g i)
  ring

noncomputable def finiteSupportWeightedLpLinearMap (c : I → ℂ) :
    (I →₀ ℂ) →ₗ[ℂ] lp (fun _ : I => ℂ) 2 where
  toFun := finiteSupportWeightedLp c
  map_add' := finite_support_weighted_lp_add c
  map_smul' a g := finite_support_weighted_lp_smul c a g

theorem finite_support_weighted_lp_apply (c : I → ℂ) (g : I →₀ ℂ) (i : I) :
    finiteSupportWeightedLp c g i = c i * g i := by
  classical
  unfold finiteSupportWeightedLp Finsupp.sum
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]
  by_cases hi : i ∈ g.support
  · rw [if_pos hi]
  · rw [if_neg hi, Finsupp.notMem_support_iff.mp hi, mul_zero]

theorem finite_support_weighted_lp_single (c : I → ℂ) (i : I) (a : ℂ) :
    finiteSupportWeightedLp c (Finsupp.single i a) = lp.single 2 i (c i * a) := by
  classical
  unfold finiteSupportWeightedLp
  exact Finsupp.sum_single_index (by simp)

theorem finite_support_weighted_lp_norm_sq (c : I → ℂ) (g : I →₀ ℂ) :
    ‖finiteSupportWeightedLp c g‖ ^ 2 = ∑ i ∈ g.support, ‖c i * g i‖ ^ 2 := by
  classical
  have h := lp.norm_sum_single (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (fun i => c i * g i) g.support
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, finiteSupportWeightedLp, Finsupp.sum] using h

/-- Nonzero coordinate multipliers retain every finite coordinate vector. -/
theorem finite_support_weighted_lp_dense (c : I → ℂ) (hc : ∀ i, c i ≠ 0) :
    DenseRange (finiteSupportWeightedLpLinearMap c) := by
  classical
  intro f
  have hs (s : Finset I) : (∑ i ∈ s, lp.single 2 i (f i)) ∈
      Set.range (finiteSupportWeightedLpLinearMap c) := by
    refine ⟨∑ i ∈ s, Finsupp.single i (f i / c i), ?_⟩
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change finiteSupportWeightedLp c (Finsupp.single i (f i / c i)) = _
    rw [finite_support_weighted_lp_single, mul_div_cancel₀ _ (hc i)]
  exact mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top f)
    (Filter.Eventually.of_forall hs)

noncomputable def weightedMemoryInputLinearMap (w : Z → ℝ) :
    (InfiniteMemory Z →₀ ℂ) →ₗ[ℂ] lp (fun _ : InfiniteMemory Z => ℂ) 2 :=
  finiteSupportWeightedLpLinearMap (fun x => (Real.sqrt (infiniteMemoryPointMass w x) : ℂ))

theorem weighted_memory_input_apply (w : Z → ℝ) (g : InfiniteMemory Z →₀ ℂ)
    (x : InfiniteMemory Z) :
    weightedMemoryInputLinearMap w g x = weightedMemoryCoordinates w g x :=
  finite_support_weighted_lp_apply _ g x

theorem weighted_memory_input_norm_sq (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (g : InfiniteMemory Z →₀ ℂ) :
    ‖weightedMemoryInputLinearMap w g‖ ^ 2 =
      ∑ x ∈ g.support, infiniteMemoryPointMass w x * ‖g x‖ ^ 2 := by
  classical
  change ‖finiteSupportWeightedLp
    (fun x : InfiniteMemory Z => (Real.sqrt (infiniteMemoryPointMass w x) : ℂ)) g‖ ^ 2 = _
  rw [finite_support_weighted_lp_norm_sq]
  apply Finset.sum_congr rfl
  intro x _
  exact weighted_memory_coordinates_norm_sq w hw g x

theorem weighted_memory_input_dense (w : Z → ℝ) (hw : ∀ z, 0 < w z) :
    DenseRange (weightedMemoryInputLinearMap w) := by
  apply finite_support_weighted_lp_dense
  intro x
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (infinite_memory_point_mass_pos w hw x)).ne'

end SimultaneousPrimitiveRoots.Unconditional.Graph
