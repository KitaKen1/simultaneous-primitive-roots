module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.WeightedFockInput
import Mathlib.Tactic.FieldSimp

/-!
# Inverse original-mass coordinates on the whole weighted Fock space

The square-root point-mass coordinate map is pointwise invertible for
positive original masses. Every ell-two element therefore has an original
weighted-memory function with a summable square norm and exactly the same
norm. This supplies the general-input weighted interpretation, not a
general-input ghost row-series interchange.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ENNReal

variable {Z : Type*}

noncomputable def unweightedMemoryCoordinates (w : Z → ℝ)
    (f : InfiniteMemory Z → ℂ) (x : InfiniteMemory Z) : ℂ :=
  f x / (Real.sqrt (infiniteMemoryPointMass w x) : ℂ)

theorem weighted_unweighted_memory_coordinates (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (f : InfiniteMemory Z → ℂ) (x : InfiniteMemory Z) :
    weightedMemoryCoordinates w (unweightedMemoryCoordinates w f) x = f x := by
  have hc : (Real.sqrt (infiniteMemoryPointMass w x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (infinite_memory_point_mass_pos w hw x)).ne'
  unfold weightedMemoryCoordinates unweightedMemoryCoordinates
  field_simp [hc]

theorem unweighted_weighted_memory_coordinates (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (f : InfiniteMemory Z → ℂ) (x : InfiniteMemory Z) :
    unweightedMemoryCoordinates w (weightedMemoryCoordinates w f) x = f x := by
  have hc : (Real.sqrt (infiniteMemoryPointMass w x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (infinite_memory_point_mass_pos w hw x)).ne'
  unfold weightedMemoryCoordinates unweightedMemoryCoordinates
  field_simp [hc]

theorem unweighted_memory_coordinates_norm_sq (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (f : InfiniteMemory Z → ℂ) (x : InfiniteMemory Z) :
    infiniteMemoryPointMass w x * ‖unweightedMemoryCoordinates w f x‖ ^ 2 = ‖f x‖ ^ 2 := by
  rw [← weighted_memory_coordinates_norm_sq w hw (unweightedMemoryCoordinates w f) x,
    weighted_unweighted_memory_coordinates w hw f x]

theorem unweighted_memory_lp_square_summable (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (f : lp (fun _ : InfiniteMemory Z => ℂ) 2) :
    Summable (fun x => infiniteMemoryPointMass w x *
      ‖unweightedMemoryCoordinates w f x‖ ^ 2) := by
  simp_rw [unweighted_memory_coordinates_norm_sq w hw f]
  have h := (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem unweighted_memory_lp_tsum_square (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (f : lp (fun _ : InfiniteMemory Z => ℂ) 2) :
    (∑' x, infiniteMemoryPointMass w x * ‖unweightedMemoryCoordinates w f x‖ ^ 2) =
      ‖f‖ ^ 2 := by
  simp_rw [unweighted_memory_coordinates_norm_sq w hw f]
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm

end SimultaneousPrimitiveRoots.Unconditional.Graph
