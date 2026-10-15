module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostCountingKernel

/-!
# Field maps of actual ghost rows and their symmetric counting kernels

This connects the real signed counting kernel to the original complex Fock
row, including its indexed residue/prime weights and factorial birth factor.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P Z K L : Type*} {R : P → Type*} {k a b n : ℕ}

attribute [local instance] Classical.propDecidable

theorem finite_ghost_subset_coefficient_map [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype P] [∀ p, Zero (R p)] (φ : K →+* L) (ν : P → K) (A : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (s : Finset (Fin (k + a))) (x : Fin (k + a) → Σ p, R p) :
    φ (finiteGhostSubsetCoefficient ν A E s x) =
      finiteGhostSubsetCoefficient (φ ∘ ν) (φ A) (fun x y => φ (E x y)) s x := by
  classical
  unfold finiteGhostSubsetCoefficient
  split_ifs <;> simp only [map_mul, map_pow, map_sum, map_prod, map_zero, Function.comp_apply]

theorem finite_ghost_sector_row_map [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype P] [∀ p, Zero (R p)] (φ : K →+* L) (ν : P → K) (A D C : K)
    (H : (Fin (k + b) → Σ p, R p) → K) (x : Fin (k + a) → Σ p, R p) :
    φ (finiteGhostSectorRow ν A D C H x) =
      finiteGhostSectorRow (φ ∘ ν) (φ A) (φ D) (φ C) (φ ∘ H) x := by
  classical
  unfold finiteGhostSectorRow
  simp only [map_mul, map_div₀, map_pow, map_natCast, map_sum,
    finite_ghost_subset_coefficient_map, Function.comp_apply]

theorem symmetric_memory_point_map [Field K] [CharZero K] [Field L] [CharZero L]
    (φ : K →+* L) (x y : Fin n → Z) :
    φ (symmetricMemoryPoint x y) = symmetricMemoryPoint x y := by
  classical
  unfold symmetricMemoryPoint
  simp only [map_div₀, map_natCast, map_sum, apply_ite, map_one, map_zero]

theorem finite_ghost_sector_counting_kernel_map [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype P] [∀ p, Zero (R p)] (φ : K →+* L) (ν : P → K) (A D C : K)
    (x : Fin (k + a) → Σ p, R p) (y : Fin (k + b) → Σ p, R p) :
    φ (finiteGhostSectorCountingKernel ν A D C x y) =
      finiteGhostSectorCountingKernel (φ ∘ ν) (φ A) (φ D) (φ C) x y := by
  unfold finiteGhostSectorCountingKernel
  rw [finite_ghost_sector_row_map]
  simp only [Function.comp_def, symmetric_memory_point_map]

end SimultaneousPrimitiveRoots.Unconditional.Graph
