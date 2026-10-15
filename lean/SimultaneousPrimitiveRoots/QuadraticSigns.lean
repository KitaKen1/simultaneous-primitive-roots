module

public import SimultaneousPrimitiveRoots.SquareClasses
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

namespace SimultaneousPrimitiveRoots

/-- Factorization has finite support, even though squareVector is a function on ℕ. -/
theorem squareVector_eq_sum_basis (a : ℕ) :
    squareVector a = ∑ q ∈ a.factorization.support,
      (a.factorization q : ZMod 2) • Pi.single q (1 : ZMod 2) := by
  classical
  ext q
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single q]
  · simp [squareVector]
  · intro t _ ht
    simp [ht.symm]
  · intro hq
    have hz : a.factorization q = 0 := by
      by_contra h
      exact hq (Finsupp.mem_support_iff.mpr h)
    simp [hz]

/-- SQ yields an actual assignment of binary signs to prime coordinates. -/
theorem exists_squareClass_coefficients {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hSQ : SquareCondition A) :
    ∃ z : ℕ → ZMod 2, ∀ a ∈ A,
      ∑ q ∈ a.factorization.support, (a.factorization q : ZMod 2) * z q = 1 := by
  classical
  obtain ⟨f, hf⟩ := exists_squareClass_functional hpos hSQ
  refine ⟨fun q => f (Pi.single q 1), ?_⟩
  intro a ha
  have h := hf a ha
  rw [squareVector_eq_sum_basis, map_sum] at h
  simpa only [LinearMap.map_smul, smul_eq_mul] using h

end SimultaneousPrimitiveRoots
