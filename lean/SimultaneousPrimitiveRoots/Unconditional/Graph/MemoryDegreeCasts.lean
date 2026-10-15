module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.SymmetricMemoryTests

/-!
# Actual coordinate casts between equal memory degrees

These are bijections of indexed tuples, preserving repeated values and the
original factorial counting mass. They transport symmetric Fock tests without
introducing any new measure factor.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {Z K : Type*} {n m : ℕ}

/-- Coordinate transport, rather than an assumed equality of tuple spaces. -/
def memoryDegreeEquiv (h : n = m) : (Fin n → Z) ≃ (Fin m → Z) :=
  Equiv.arrowCongr (finCongr h) (Equiv.refl Z)

theorem memory_degree_equiv_refl (x : Fin n → Z) : memoryDegreeEquiv rfl x = x := rfl

theorem factorial_memory_point_mass_degree_equiv [Field K] [CharZero K]
    (h : n = m) (w : Z → K) (x : Fin n → Z) :
    factorialMemoryPointMass w (memoryDegreeEquiv h x) = factorialMemoryPointMass w x := by
  cases h
  rfl

theorem factorial_memory_point_mass_degree_equiv_symm [Field K] [CharZero K]
    (h : n = m) (w : Z → K) (y : Fin m → Z) :
    factorialMemoryPointMass w ((memoryDegreeEquiv h).symm y) = factorialMemoryPointMass w y := by
  cases h
  rfl

theorem symmetric_memory_point_degree_equiv [Field K] [CharZero K]
    (h : n = m) (x y : Fin n → Z) :
    symmetricMemoryPoint (K := K) (memoryDegreeEquiv h x) (memoryDegreeEquiv h y) =
      symmetricMemoryPoint x y := by
  cases h
  rfl

theorem memory_degree_equiv_symmetric_test (h : n = m) (H : (Fin m → Z) → K)
    (hH : ∀ (σ : Equiv.Perm (Fin m)) y, H (y ∘ σ) = H y)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → Z) :
    H (memoryDegreeEquiv h (x ∘ σ)) = H (memoryDegreeEquiv h x) := by
  cases h
  exact hH σ x

theorem memory_degree_equiv_symm_symmetric_test (h : n = m) (H : (Fin n → Z) → K)
    (hH : ∀ (σ : Equiv.Perm (Fin n)) x, H (x ∘ σ) = H x)
    (σ : Equiv.Perm (Fin m)) (y : Fin m → Z) :
    H ((memoryDegreeEquiv h).symm (y ∘ σ)) = H ((memoryDegreeEquiv h).symm y) := by
  cases h
  exact hH σ y

end SimultaneousPrimitiveRoots.Unconditional.Graph
