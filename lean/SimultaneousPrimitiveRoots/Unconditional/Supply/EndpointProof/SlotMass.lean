module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SlotBound

/-!
# `C_x = O_ε(1)` for one slot

`slotMassBounded_one : SlotMassBounded 1` (`[P-06:0079]`: "The harmonic prime estimates give
`C_x = O_ε(1)`"), from `Extraction.slotBounded_one` (`Supply/Extraction/SlotBound.lean`), which
bounds `C_x` for one slot by the Chebyshev window bound and needs no Mertens estimate. This
discharges the leaf `slotMass` of `EndpointLeaves 0` (the case of one slot, needed downstream).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter

noncomputable section

/-- **`C_x = O_ε(1)` for one slot**, uniformly in the admissible slots. -/
theorem slotMassBounded_one : SlotMassBounded 1 := by
  intro ε hε
  obtain ⟨B, hB⟩ := Extraction.slotBounded_one ε hε 1 one_pos
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hB
  exact ⟨B, x₀, fun x hx S hS => (hx₀ x hx S hS).1⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
