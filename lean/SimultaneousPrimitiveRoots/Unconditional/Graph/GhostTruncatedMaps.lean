module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostTruncatedKernel

/-!
# Field maps of the complete finite ghost kernel

The degree casts, all survivor sectors and the common endpoint cutoff are
preserved. This identifies the real signed kernel with the original complex
finite Fock row, rather than changing the transition measure.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P K L : Type*} {R : P → Type*}

theorem finite_ghost_degree_kernel_map [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype P] [∀ p, Zero (R p)] (φ : K →+* L) (ν : P → K) (A D C : K) (k n m : ℕ)
    (x : Fin n → Σ p, R p) (y : Fin m → Σ p, R p) :
    φ (finiteGhostDegreeKernel ν A D C k n m x y) =
      finiteGhostDegreeKernel (φ ∘ ν) (φ A) (φ D) (φ C) k n m x y := by
  classical
  unfold finiteGhostDegreeKernel
  split_ifs <;> simp only [finite_ghost_sector_counting_kernel_map, map_zero]

theorem finite_ghost_degree_row_map [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype P] [∀ p, Zero (R p)] (φ : K →+* L) (ν : P → K) (A D C : K) (k n m : ℕ)
    (H : (Fin m → Σ p, R p) → K) (x : Fin n → Σ p, R p) :
    φ (finiteGhostDegreeRow ν A D C k n m H x) =
      finiteGhostDegreeRow (φ ∘ ν) (φ A) (φ D) (φ C) k n m (φ ∘ H) x := by
  classical
  unfold finiteGhostDegreeRow
  split_ifs <;> simp only [finite_ghost_sector_row_map, map_zero, Function.comp_def]

theorem finite_ghost_truncated_kernel_map [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype P] [∀ p, Zero (R p)] (φ : K →+* L) (ν : P → K) (A D C : K) (N : ℕ)
    (x y : FiniteMemory N (Σ p, R p)) :
    φ (finiteGhostTruncatedKernel ν A D C N x y) =
      finiteGhostTruncatedKernel (φ ∘ ν) (φ A) (φ D) (φ C) N x y := by
  classical
  unfold finiteGhostTruncatedKernel
  simp only [map_sum, finite_ghost_degree_kernel_map]

theorem finite_ghost_truncated_row_map [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype P] [∀ p, Zero (R p)] (φ : K →+* L) (ν : P → K) (A D C : K) (N : ℕ)
    (H : FiniteMemory N (Σ p, R p) → K) (x : FiniteMemory N (Σ p, R p)) :
    φ (finiteGhostTruncatedRow ν A D C N H x) =
      finiteGhostTruncatedRow (φ ∘ ν) (φ A) (φ D) (φ C) N (φ ∘ H) x := by
  classical
  unfold finiteGhostTruncatedRow
  simp only [map_sum, finite_ghost_degree_row_map, Function.comp_def]

end SimultaneousPrimitiveRoots.Unconditional.Graph
