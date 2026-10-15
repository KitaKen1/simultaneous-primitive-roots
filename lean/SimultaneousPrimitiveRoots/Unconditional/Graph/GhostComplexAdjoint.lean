module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostSubsetRow
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Complex adjoint pairing for actual finite ghost rows

The finite factorial/counting pairing from [S, eq:ghost-joint-integral]
commutes with field homomorphisms. In particular, conjugation and reversal
exchange birth and termination for real coefficients. This does not assert
an adjoint or norm theorem for the infinite Fock space.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P K L : Type*} {R : P → Type*} {k a b : ℕ}

attribute [local instance] Classical.propDecidable

/-- A field homomorphism preserves all signed finite ghost joint weights. -/
theorem finite_ghost_sector_map [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (φ : K →+* L) (ν : P → K) (A D C : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K) :
    φ (finiteGhostJointSector ν A D C E) =
      finiteGhostJointSector (φ ∘ ν) (φ A) (φ D) (φ C) (fun x y => φ (E x y)) := by
  classical
  unfold finiteGhostJointSector finiteEdgeJointSum ghostPointWeight
  simp only [map_div₀, map_mul, map_pow, map_natCast, map_sum, map_prod,
    Function.comp_apply, apply_ite, map_one]

/-- The actual finite subset-row pairing commutes with a field homomorphism. -/
theorem finite_ghost_subset_joint_map [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (φ : K →+* L) (ν : P → K) (A D C : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (hEold : ∀ (σ : Equiv.Perm (Fin (k + a))) x y, E (x ∘ σ) y = E x y)
    (hEnew : ∀ (σ : Equiv.Perm (Fin (k + b))) x y, E x (y ∘ σ) = E x y) :
    φ (finiteGhostSubsetJoint ν A D C E) =
      finiteGhostSubsetJoint (φ ∘ ν) (φ A) (φ D) (φ C) (fun x y => φ (E x y)) := by
  rw [finite_ghost_subset_joint_identification ν A D C E hEold hEnew,
    finite_ghost_sector_map,
    finite_ghost_subset_joint_identification (φ ∘ ν) (φ A) (φ D) (φ C)
      (fun x y => φ (E x y)) (fun σ x y => congrArg φ (hEold σ x y))
      (fun σ x y => congrArg φ (hEnew σ x y))]

/-- Conjugation gives the adjoint pairing of actual finite ghost rows for real data.
The source and target tests are symmetric Fock functions; signed D/C are unchanged. -/
theorem finite_ghost_complex_pair_adjoint [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ)
    (f : (Fin (k + a) → Σ p, R p) → ℂ)
    (h : (Fin (k + b) → Σ p, R p) → ℂ)
    (hf : ∀ (σ : Equiv.Perm (Fin (k + a))) x, f (x ∘ σ) = f x)
    (hh : ∀ (σ : Equiv.Perm (Fin (k + b))) y, h (y ∘ σ) = h y) :
    finiteGhostSubsetJoint (fun p => (ν p : ℂ)) (A : ℂ) (D : ℂ) (C : ℂ)
      (fun x y => (starRingEnd ℂ) (f x) * h y) =
    (starRingEnd ℂ) (finiteGhostSubsetJoint (fun p => (ν p : ℂ)) (A : ℂ) (C : ℂ) (D : ℂ)
      (fun y x => (starRingEnd ℂ) (h y) * f x)) := by
  rw [finite_ghost_subset_joint_reversal (fun p => (ν p : ℂ)) (A : ℂ) (D : ℂ) (C : ℂ)
    (fun x y => (starRingEnd ℂ) (f x) * h y)
    (fun σ x y => by rw [hf σ x]) (fun σ x y => by rw [hh σ y])]
  rw [finite_ghost_subset_joint_map (starRingEnd ℂ) (fun p => (ν p : ℂ))
    (A : ℂ) (C : ℂ) (D : ℂ) (fun y x => (starRingEnd ℂ) (h y) * f x)
    (fun σ y x => by rw [hh σ y]) (fun σ y x => by rw [hf σ x])]
  simp only [Function.comp_def, Complex.conj_ofReal]
  congr 1
  funext y x
  rw [map_mul, starRingEnd_self_apply]
  exact mul_comm _ _

end SimultaneousPrimitiveRoots.Unconditional.Graph
