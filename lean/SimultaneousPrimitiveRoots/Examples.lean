module

public import SimultaneousPrimitiveRoots.OrderObstruction
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Finset.Powerset

@[expose] public section

namespace SimultaneousPrimitiveRoots

/-- A finite certificate checker for SQ; it is equivalent to the original definition. -/
theorem squareCondition_iff_powerset (A : Finset ℕ) :
    SquareCondition A ↔
      ∀ B ∈ A.powerset, Odd B.card → ¬ IsSquare (∏ a ∈ B, a) := by
  simp only [SquareCondition, Finset.mem_powerset]

theorem admissible_two_three : Admissible {2, 3} := by
  refine ⟨by decide, by decide, ?_⟩
  rw [squareCondition_iff_powerset]
  decide +kernel

theorem admissible_three_six : Admissible {3, 6} := by
  refine ⟨by decide, by decide, ?_⟩
  rw [squareCondition_iff_powerset]
  decide +kernel

theorem not_squareCondition_two_three_six : ¬ SquareCondition {2, 3, 6} := by
  rw [squareCondition_iff_powerset]
  decide +kernel

theorem no_two_three_six {p : ℕ} (hp : 2 < p) :
    ¬ SimultaneousAt {2, 3, 6} p :=
  no_simultaneousAt_of_not_squareCondition not_squareCondition_two_three_six hp

end SimultaneousPrimitiveRoots
