module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The global performed-birth distinctness indicator

An unused address gets its own private label; a performed address gets its
particle value. The equality matrix of these labels has determinant one when
the performed values are pairwise distinct and zero otherwise. Its determinant
expansion is the exact signed permutation formula for any finite address set,
including unused addresses. Equality-rank estimates remain separate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {I Z K : Type*}

/-- Unused addresses never collide with each other or with performed births. -/
def birthLabel (birth : I → Option Z) (i : I) : I ⊕ Z :=
  match birth i with
  | none => Sum.inl i
  | some z => Sum.inr z

/-- Global distinctness compares all performed addresses, including distant visits. -/
def PerformedBirthsDistinct (birth : I → Option Z) : Prop :=
  ∀ i j z, birth i = some z → birth j = some z → i = j

/-- The private-label construction expresses precisely the performed-birth rule. -/
theorem birthLabel_injective_iff (birth : I → Option Z) :
    Function.Injective (birthLabel birth) ↔ PerformedBirthsDistinct birth := by
  constructor
  · intro h i j z hi hj
    apply h
    simp [birthLabel, hi, hj]
  · intro h i j hij
    cases hi : birth i with
    | none =>
      cases hj : birth j with
      | none => simpa [birthLabel, hi, hj] using hij
      | some z => simp [birthLabel, hi, hj] at hij
    | some z =>
      cases hj : birth j with
      | none => simp [birthLabel, hi, hj] at hij
      | some z' =>
        have hz : z = z' := by simpa [birthLabel, hi, hj] using hij
        exact h i j z hi (hj.trans (congrArg some hz.symm))

/-- A value-preserving permutation necessarily fixes every unused address. -/
theorem birthLabel_eq_unused (birth : I → Option Z) (i j : I)
    (hi : birth i = none) : birthLabel birth j = birthLabel birth i ↔ j = i := by
  cases hj : birth j with
  | none => simp [birthLabel, hi, hj]
  | some z =>
    simp only [birthLabel, hi, hj, reduceCtorEq, false_iff]
    intro h
    subst j
    rw [hi] at hj
    cases hj

/-- Equality matrix over addresses, not over a set of distinct particle values. -/
def birthEqualityMatrix [Zero K] [One K] [DecidableEq I] [DecidableEq Z]
    (birth : I → Option Z) : Matrix I I K :=
  fun i j => if birthLabel birth i = birthLabel birth j then 1 else 0

attribute [local instance] Classical.propDecidable

/-- Exact determinant indicator for every finite address set and commutative ring. -/
theorem birth_equality_det [CommRing K] [Fintype I] [DecidableEq I] [DecidableEq Z]
    (birth : I → Option Z) :
    (birthEqualityMatrix (K := K) birth).det =
      if PerformedBirthsDistinct birth then 1 else 0 := by
  classical
  by_cases hd : PerformedBirthsDistinct birth
  · rw [if_pos hd]
    have h : birthEqualityMatrix (K := K) birth = 1 := by
      ext i j
      simp only [birthEqualityMatrix, Matrix.one_apply,
        (birthLabel_injective_iff birth).mpr hd |>.eq_iff]
    rw [h, Matrix.det_one]
  · rw [if_neg hd]
    have hn : ¬ Function.Injective (birthLabel birth) := by
      simpa only [birthLabel_injective_iff] using hd
    obtain ⟨i, j, hlabels, hne⟩ := Function.not_injective_iff.mp hn
    apply Matrix.det_zero_of_row_eq hne
    funext t
    simp only [birthEqualityMatrix, hlabels]

/-- The exact signed permutation expansion restoring global performed-birth distinctness. -/
theorem performed_birth_permutation_expansion
    [CommRing K] [Fintype I] [DecidableEq I] [DecidableEq Z]
    (birth : I → Option Z) :
    (∑ σ : Equiv.Perm I, ((Equiv.Perm.sign σ : ℤ) : K) *
      ∏ i, if birthLabel birth (σ i) = birthLabel birth i then 1 else 0) =
      if PerformedBirthsDistinct birth then 1 else 0 := by
  rw [← birth_equality_det (K := K) birth, Matrix.det_apply']
  rfl

end SimultaneousPrimitiveRoots.Unconditional.Graph
