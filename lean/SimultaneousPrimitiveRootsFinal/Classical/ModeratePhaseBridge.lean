import ArtinPrimitiveRoots.TypeII.PD.Preliminaries
import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ClassicalInputs

/-!
# The moderate-phase estimate ([P] (eq:moderate-phase)) from the vendored formalization

`Supply.EndpointProof.ModeratePhase` (`Supply/EndpointProof/ClassicalInputs.lean`) is the statement
of `ArtinPrimitiveRoots.TypeII.PD.moderate_phase`
(`vendor/ArtinPrimitiveRoots/TypeII/PD/Preliminaries.lean`), with the `let`-bound abbreviations
`L = log x`, `T = exp (L / (log L)^2)` unfolded, `Real.rpow` written `^`, and the sum
`integerResiduePhaseSum` restated in the module part of the project as `residuePhaseSum`.
-/

namespace SimultaneousPrimitiveRoots.Unconditional

/-- The vendored sum over a residue class in an interval is the one of the project. -/
theorem Supply.EndpointProof.integerResiduePhaseSum_eq (q : ℕ) (a : ZMod q) (t l r : ℝ) :
    ArtinPrimitiveRoots.TypeII.PD.integerResiduePhaseSum q a t l r =
      Supply.EndpointProof.residuePhaseSum q a t l r := by
  unfold ArtinPrimitiveRoots.TypeII.PD.integerResiduePhaseSum Supply.EndpointProof.residuePhaseSum
  refine Finset.sum_congr ?_ fun n _ => rfl
  ext n
  simp only [Finset.mem_filter]

/-- **The sum–integral comparison at moderate frequencies** ([P] (eq:moderate-phase)) is a
theorem: the supply-side hypothesis `Supply.EndpointProof.ModeratePhase` holds. -/
theorem Supply.EndpointProof.moderatePhase : Supply.EndpointProof.ModeratePhase := by
  intro δ C hδ hC
  obtain ⟨C₀, cδ, x₀, hC₀, hcδ, hx₀, h⟩ :=
    ArtinPrimitiveRoots.TypeII.PD.moderate_phase δ C hδ hC
  refine ⟨C₀, cδ, x₀, hC₀, hcδ, hx₀, fun x hx N hN q hq hqL a t ht₁ ht₂ l r hl hlr hr => ?_⟩
  have h' := h x hx N hN q hq hqL a t ht₁ ht₂ l r hl hlr hr
  rw [Supply.EndpointProof.integerResiduePhaseSum_eq] at h'
  exact h'

end SimultaneousPrimitiveRoots.Unconditional
