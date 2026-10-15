module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.SurvivorPermutations
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity

/-!
# Point tests in the symmetric memory space

The actual ghost row acts on symmetric particle-index functions. A labelled
point indicator is therefore averaged over index permutations before using
it to test a row or column. This file proves that the average reproduces
symmetric weighted functions and retains multiplicity when values repeat.
It does not silently impose symmetry on an arbitrary marked endpoint test.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {Z K : Type*} {n : ℕ}

attribute [local instance] Classical.propDecidable

/-- A point test projected onto symmetric memory functions, counting all n! permutations. -/
noncomputable def symmetricMemoryPoint [Field K] [CharZero K]
    (x y : Fin n → Z) : K := by
  classical
  exact (∑ σ : Equiv.Perm (Fin n), if y ∘ σ = x then 1 else 0) / (n.factorial : K)

/-- The projected point test is invariant under particle-index permutations. -/
theorem symmetric_memory_point_invariant [Field K] [CharZero K]
    (x y : Fin n → Z) (τ : Equiv.Perm (Fin n)) :
    symmetricMemoryPoint (K := K) x (y ∘ τ) = symmetricMemoryPoint x y := by
  classical
  unfold symmetricMemoryPoint
  congr 1
  change (∑ σ : Equiv.Perm (Fin n), if y ∘ (τ * σ) = x then (1 : K) else 0) = _
  exact Equiv.sum_comp (Equiv.mulLeft τ)
    (fun σ : Equiv.Perm (Fin n) => if y ∘ σ = x then (1 : K) else 0)

/-- An averaged point indicator reproduces every symmetric weighted test exactly.
No assumption that the coordinates of x are distinct is used. -/
theorem symmetric_memory_point_reproducing [Field K] [CharZero K] [Fintype Z]
    (W H : (Fin n → Z) → K)
    (hW : ∀ (σ : Equiv.Perm (Fin n)) y, W (y ∘ σ) = W y)
    (hH : ∀ (σ : Equiv.Perm (Fin n)) y, H (y ∘ σ) = H y) (x : Fin n → Z) :
    (∑ y : Fin n → Z, W y * H y * symmetricMemoryPoint x y) = W x * H x := by
  classical
  have hσ (σ : Equiv.Perm (Fin n)) :
      (∑ y : Fin n → Z, W y * H y * (if y ∘ σ = x then (1 : K) else 0)) =
        W x * H x := by
    let e : (Fin n → Z) ≃ (Fin n → Z) := σ.symm.arrowCongr (Equiv.refl Z)
    rw [← e.symm.sum_comp]
    change (∑ y : Fin n → Z, W (y ∘ σ.symm) * H (y ∘ σ.symm) *
      (if (y ∘ σ.symm) ∘ σ = x then (1 : K) else 0)) = _
    have he (y : Fin n → Z) : (y ∘ σ.symm) ∘ σ = y := by
      funext i
      exact congrArg y (σ.symm_apply_apply i)
    simp_rw [he, hW σ.symm, hH σ.symm, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold symmetricMemoryPoint
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [hσ]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_div_cancel_left₀ _ hn

/-- The projected point test is symmetric in its two memory arguments. -/
theorem symmetric_memory_point_transpose [Field K] [CharZero K]
    (x y : Fin n → Z) : symmetricMemoryPoint (K := K) x y = symmetricMemoryPoint y x := by
  classical
  unfold symmetricMemoryPoint
  congr 1
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
  apply Finset.sum_congr rfl
  intro σ _
  change (if y ∘ σ.symm = x then (1 : K) else 0) =
    if x ∘ σ = y then 1 else 0
  have he : y ∘ σ.symm = x ↔ x ∘ σ = y := by
    constructor
    · intro h
      rw [← h]
      funext i
      exact congrArg y (σ.symm_apply_apply i)
    · intro h
      rw [← h]
      funext i
      exact congrArg x (σ.apply_symm_apply i)
  by_cases h : x ∘ σ = y
  · rw [if_pos (he.mpr h), if_pos h]
  · rw [if_neg (fun hy => h (he.mp hy)), if_neg h]

/-- The projected point test has total counting mass one, also for repeated values. -/
theorem symmetric_memory_point_total_mass [Field K] [CharZero K] [Fintype Z]
    (x : Fin n → Z) : (∑ y : Fin n → Z, symmetricMemoryPoint (K := K) x y) = 1 := by
  simpa only [one_mul] using symmetric_memory_point_reproducing
    (fun _ : Fin n → Z => (1 : K)) (fun _ => (1 : K))
    (fun _ _ => rfl) (fun _ _ => rfl) x

/-- This is a nonnegative counting kernel over the reals. -/
theorem symmetric_memory_point_nonneg (x y : Fin n → Z) :
    0 ≤ symmetricMemoryPoint (K := ℝ) x y := by
  classical
  unfold symmetricMemoryPoint
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro σ _
    split_ifs <;> positivity
  · exact Nat.cast_nonneg _

/-- Point mass of the indexed product alphabet in the original factorial memory measure. -/
noncomputable def factorialMemoryPointMass [Field K] [CharZero K]
    (w : Z → K) (x : Fin n → Z) : K :=
  (∏ i, w (x i)) / (n.factorial : K)

theorem factorial_memory_point_mass_invariant [Field K] [CharZero K]
    (w : Z → K) (x : Fin n → Z) (σ : Equiv.Perm (Fin n)) :
    factorialMemoryPointMass w (x ∘ σ) = factorialMemoryPointMass w x := by
  unfold factorialMemoryPointMass
  congr 1
  exact Equiv.prod_comp σ (fun i => w (x i))

/-- In the factorial counting measure a symmetric point test retains the original point mass. -/
theorem factorial_memory_point_reproducing [Field K] [CharZero K] [Fintype Z]
    (w : Z → K) (H : (Fin n → Z) → K)
    (hH : ∀ (σ : Equiv.Perm (Fin n)) y, H (y ∘ σ) = H y) (x : Fin n → Z) :
    (∑ y : Fin n → Z, factorialMemoryPointMass w y * H y * symmetricMemoryPoint x y) =
      factorialMemoryPointMass w x * H x := by
  exact symmetric_memory_point_reproducing (factorialMemoryPointMass w) H
    (fun σ y => factorial_memory_point_mass_invariant w y σ) hH x

end SimultaneousPrimitiveRoots.Unconditional.Graph
