module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.MemoryDegreeCasts
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostSectorRowBounds
import Lean.Elab.Tactic.Omega

/-!
# Ghost sectors in actual old and new memory degrees

For k survivors, n old particles and m new particles, the sector has n-k
terminations and m-k births. Actual coordinate bijections transport its
counting kernel and row. Inadmissible survivor counts contribute zero.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P K : Type*} {R : P → Type*}

attribute [local instance] Classical.propDecidable

/-- The actual k-survivor sector in memory degrees n and m. -/
noncomputable def finiteGhostDegreeKernel [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (k n m : ℕ)
    (x : Fin n → Σ p, R p) (y : Fin m → Σ p, R p) : K :=
  if hk : k ≤ n ∧ k ≤ m then
    finiteGhostSectorCountingKernel (k := k) (a := n - k) (b := m - k) ν A D C
      ((memoryDegreeEquiv (by omega : k + (n - k) = n)).symm x)
      ((memoryDegreeEquiv (by omega : k + (m - k) = m)).symm y)
  else 0

/-- The original sector row in the same actual degree coordinates. -/
noncomputable def finiteGhostDegreeRow [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (k n m : ℕ)
    (H : (Fin m → Σ p, R p) → K) (x : Fin n → Σ p, R p) : K :=
  if hk : k ≤ n ∧ k ≤ m then
    finiteGhostSectorRow (k := k) (a := n - k) (b := m - k) ν A D C
      (fun z => H (memoryDegreeEquiv (by omega : k + (m - k) = m) z))
      ((memoryDegreeEquiv (by omega : k + (n - k) = n)).symm x)
  else 0

theorem finite_ghost_degree_kernel_inadmissible [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (k n m : ℕ)
    (hk : ¬ (k ≤ n ∧ k ≤ m)) (x : Fin n → Σ p, R p) (y : Fin m → Σ p, R p) :
    finiteGhostDegreeKernel ν A D C k n m x y = 0 := by
  exact dif_neg hk

/-- Degree casts preserve the exact original factorial-mass transpose. -/
theorem finite_ghost_degree_kernel_weighted_transpose [Field K] [CharZero K]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → K) (A D C : K) (k n m : ℕ)
    (x : Fin n → Σ p, R p) (y : Fin m → Σ p, R p) :
    factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
      finiteGhostDegreeKernel ν A D C k n m x y =
    factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) y *
      finiteGhostDegreeKernel ν A C D k m n y x := by
  classical
  by_cases hk : k ≤ n ∧ k ≤ m
  · have hk' : k ≤ m ∧ k ≤ n := hk.symm
    simp only [finiteGhostDegreeKernel, dif_pos hk, dif_pos hk']
    have h := finite_ghost_sector_counting_kernel_weighted_transpose
      (k := k) (a := n - k) (b := m - k) ν A D C
      ((memoryDegreeEquiv (by omega : k + (n - k) = n)).symm x)
      ((memoryDegreeEquiv (by omega : k + (m - k) = m)).symm y)
    simpa only [factorial_memory_point_mass_degree_equiv_symm] using h
  · have hk' : ¬ (k ≤ m ∧ k ≤ n) := fun h => hk h.symm
    simp only [finiteGhostDegreeKernel, dif_neg hk, dif_neg hk', mul_zero]

theorem finite_ghost_degree_kernel_nonneg [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (hν : ∀ p, 0 ≤ ν p)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C) (k n m : ℕ)
    (x : Fin n → Σ p, R p) (y : Fin m → Σ p, R p) :
    0 ≤ finiteGhostDegreeKernel ν A D C k n m x y := by
  classical
  unfold finiteGhostDegreeKernel
  split_ifs with hk
  · exact finite_ghost_sector_counting_kernel_nonneg ν A D C hν hA hD hC _ _
  · exact le_rfl

theorem finite_ghost_degree_kernel_abs [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (k n m : ℕ)
    (x : Fin n → Σ p, R p) (y : Fin m → Σ p, R p) :
    |finiteGhostDegreeKernel ν A D C k n m x y| =
      finiteGhostDegreeKernel ν A |D| |C| k n m x y := by
  classical
  unfold finiteGhostDegreeKernel
  split_ifs with hk
  · exact finite_ghost_sector_counting_kernel_abs ν A D C hν hA _ _
  · exact abs_zero

/-- The cast degree kernel reproduces the original sector row on symmetric tests. -/
theorem finite_ghost_degree_kernel_reproduces [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (k n m : ℕ)
    (H : (Fin m → Σ p, R p) → K)
    (hH : ∀ (σ : Equiv.Perm (Fin m)) y, H (y ∘ σ) = H y)
    (x : Fin n → Σ p, R p) :
    (∑ y : Fin m → Σ p, R p, finiteGhostDegreeKernel ν A D C k n m x y * H y) =
      finiteGhostDegreeRow ν A D C k n m H x := by
  classical
  by_cases hk : k ≤ n ∧ k ≤ m
  · simp only [finiteGhostDegreeKernel, finiteGhostDegreeRow, dif_pos hk]
    let e := memoryDegreeEquiv (Z := Σ p, R p) (by omega : k + (m - k) = m)
    rw [← Equiv.sum_comp e (fun y : Fin m → Σ p, R p =>
      finiteGhostSectorCountingKernel ν A D C
        ((memoryDegreeEquiv (by omega : k + (n - k) = n)).symm x) (e.symm y) * H y)]
    simp only [Equiv.symm_apply_apply]
    exact finite_ghost_sector_counting_kernel_reproduces ν A D C (fun z => H (e z))
      (fun σ z => memory_degree_equiv_symmetric_test _ H hH σ z) _
  · simp only [finiteGhostDegreeKernel, finiteGhostDegreeRow, dif_neg hk, zero_mul,
      Finset.sum_const_zero]

theorem finite_ghost_degree_kernel_source_invariant [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (k n m : ℕ)
    (x : Fin n → Σ p, R p) (y : Fin m → Σ p, R p) (σ : Equiv.Perm (Fin n)) :
    finiteGhostDegreeKernel ν A D C k n m (x ∘ σ) y =
      finiteGhostDegreeKernel ν A D C k n m x y := by
  classical
  unfold finiteGhostDegreeKernel
  split_ifs with hk
  · exact memory_degree_equiv_symm_symmetric_test _
      (fun u => finiteGhostSectorCountingKernel ν A D C u
        ((memoryDegreeEquiv (by omega : k + (m - k) = m)).symm y))
      (fun π u => finite_ghost_sector_counting_kernel_source_invariant ν A D C u _ π) σ x
  · rfl

end SimultaneousPrimitiveRoots.Unconditional.Graph
