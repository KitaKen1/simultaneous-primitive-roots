module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.LpKernelRows

/-! # Coordinate magnitudes in counting ell-two -/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

variable {I : Type*}

noncomputable def lpCoordinateMagnitude (f : lp (fun _ : I => ℂ) 2) :
    lp (fun _ : I => ℂ) 2 :=
  ⟨fun i => (‖f i‖ : ℂ), (lp.memℓp f).mono' (by intro i; simp)⟩

theorem lp_coordinate_magnitude_apply (f : lp (fun _ : I => ℂ) 2) (i : I) :
    lpCoordinateMagnitude f i = (‖f i‖ : ℂ) := rfl

theorem lp_coordinate_magnitude_coordinate_norm (f : lp (fun _ : I => ℂ) 2) (i : I) :
    ‖lpCoordinateMagnitude f i‖ = ‖f i‖ := by
  simp [lp_coordinate_magnitude_apply]

theorem lp_coordinate_magnitude_norm (f : lp (fun _ : I => ℂ) 2) :
    ‖lpCoordinateMagnitude f‖ = ‖f‖ := by
  apply le_antisymm
  · exact lp.norm_mono (by norm_num) (fun i => (lp_coordinate_magnitude_coordinate_norm f i).le)
  · exact lp.norm_mono (by norm_num) (fun i => (lp_coordinate_magnitude_coordinate_norm f i).ge)

end SimultaneousPrimitiveRoots.Unconditional.Graph
