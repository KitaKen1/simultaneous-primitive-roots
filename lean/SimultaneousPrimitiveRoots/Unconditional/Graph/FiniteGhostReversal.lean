module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.AnchorMemory
public import SimultaneousPrimitiveRoots.Unconditional.Graph.UnorderedMemory
public import SimultaneousPrimitiveRoots.Unconditional.Graph.FiniteEdgeReversal
import Mathlib.Tactic.Ring

/-!
# Finite ghost joint sectors

The joint expression in [S, eq:ghost-joint-integral] has survivor damping,
one prime weight per terminated/born particle, and factorials k!a!b!.
This file records its exact signed finite-sector transpose, including joint
endpoint restrictions. The identification with every actual ghost row and
extension to the infinite memory space remain separate obligations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {I P K : Type*} {R : P → Type*} {k a b : ℕ}

attribute [local instance] Classical.propDecidable

/-- Number of pending zero-residue hits, counting positions rather than values. -/
noncomputable def ghostZeroCount [Fintype I] [∀ p, Zero (R p)] (u : I → Σ p, R p) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => (u i).2 = 0)).card

/-- Counting prime weight with the continuing-zero damping at this visit. -/
noncomputable def ghostPointWeight [One K] [Mul K] [∀ p, Zero (R p)]
    (ν : P → K) (A : K) (z : Σ p, R p) : K :=
  ν z.1 * (if z.2 = 0 then A else 1)

/-- The survivor product is exactly its prime product times A to the zero count. -/
theorem ghost_survivor_weight [CommMonoid K] [Fintype I] [∀ p, Zero (R p)]
    (ν : P → K) (A : K) (u : I → Σ p, R p) :
    (∏ i, ghostPointWeight ν A (u i)) =
      (∏ i, ν (u i).1) * A ^ ghostZeroCount u := by
  classical
  change (∏ i, ν (u i).1 * (if (u i).2 = 0 then A else 1)) = _
  rw [Finset.prod_mul_distrib]
  congr 1
  simp [ghostZeroCount, Finset.prod_ite]

/-- Signed finite ghost joint sector; D terminates and C creates particles. -/
noncomputable def finiteGhostJointSector [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K) : K :=
  (D ^ a * C ^ b) * finiteEdgeJointSum (ghostPointWeight ν A) ν
    (fun p => ⟨p, 0⟩) (fun p => ⟨p, 0⟩) (Equiv.refl _) E /
      ((k.factorial : K) * (a.factorial : K) * (b.factorial : K))

/-- Sector transposition exchanges the birth/termination coefficients and factorials.
The signed coefficients are retained exactly; no positivity is assumed. -/
theorem finite_ghost_sector_reversal [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K) :
    finiteGhostJointSector ν A D C E =
      finiteGhostJointSector ν A C D (fun y x => E x y) := by
  classical
  unfold finiteGhostJointSector
  rw [finite_edge_joint_reversal (ghostPointWeight ν A) ν _ _ (Equiv.refl _)
    (fun _ => rfl) E]
  rw [mul_comm (D ^ a) (C ^ b), mul_right_comm (k.factorial : K)
    (a.factorial : K) (b.factorial : K)]
  rfl

end SimultaneousPrimitiveRoots.Unconditional.Graph
