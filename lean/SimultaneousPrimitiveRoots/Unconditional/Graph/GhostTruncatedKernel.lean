module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostDegreeKernel
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostSectorNorm
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Actual ghost kernel on a common finite memory cutoff

Both endpoints range over indexed tuples of all degrees up to N. Each degree
block sums every admissible survivor sector exactly once. Its transpose,
original factorial measure, positive majorant and symmetric row action are
proved here. GhostTruncatedRows and GhostTruncatedNorm prove the complete
cutoff-independent bound. The infinite-memory extension remains separate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P Z K : Type*} {R : P → Type*} {N M : ℕ}

/-- All indexed memory tuples up to one common degree cutoff. -/
abbrev FiniteMemory (N : ℕ) (Z : Type*) := Σ n : Fin (N + 1), Fin n.val → Z

/-- The original counting measure point mass, including its degree factorial. -/
noncomputable def finiteMemoryPointMass [Field K] [CharZero K]
    (w : Z → K) (x : FiniteMemory N Z) : K := factorialMemoryPointMass w x.2

/-- Every survivor count compatible with both actual endpoint degrees. -/
noncomputable def finiteGhostTruncatedKernel [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (N : ℕ)
    (x y : FiniteMemory N (Σ p, R p)) : K :=
  ∑ k ∈ Finset.range (min x.1.val y.1.val + 1),
    finiteGhostDegreeKernel ν A D C k x.1.val y.1.val x.2 y.2

/-- The original degree-sector rows, summed over the same two-endpoint cutoff. -/
noncomputable def finiteGhostTruncatedRow [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (N : ℕ)
    (H : FiniteMemory N (Σ p, R p) → K) (x : FiniteMemory N (Σ p, R p)) : K :=
  ∑ m : Fin (N + 1), ∑ k ∈ Finset.range (min x.1.val m.val + 1),
    finiteGhostDegreeRow ν A D C k x.1.val m.val (fun y => H ⟨m, y⟩) x.2

theorem finite_memory_point_mass_pos (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (x : FiniteMemory N Z) : 0 < finiteMemoryPointMass w x :=
  factorial_memory_point_mass_pos w hw x.2

/-- Reversal preserves the common cutoff and every factorial endpoint mass. -/
theorem finite_ghost_truncated_kernel_weighted_transpose [Field K] [CharZero K]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → K) (A D C : K) (N : ℕ) (x y : FiniteMemory N (Σ p, R p)) :
    finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
      finiteGhostTruncatedKernel ν A D C N x y =
    finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) y *
      finiteGhostTruncatedKernel ν A C D N y x := by
  classical
  unfold finiteMemoryPointMass finiteGhostTruncatedKernel
  rw [min_comm y.1.val x.1.val, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact finite_ghost_degree_kernel_weighted_transpose ν A D C k _ _ _ _

theorem finite_ghost_truncated_kernel_weighted_column [Field K] [CharZero K]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → K) (A D C : K) (N : ℕ) (W : FiniteMemory N (Σ p, R p) → K)
    (y : FiniteMemory N (Σ p, R p)) :
    (∑ x : FiniteMemory N (Σ p, R p),
      finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        finiteGhostTruncatedKernel ν A D C N x y * W x) =
    finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) y *
      ∑ x : FiniteMemory N (Σ p, R p), finiteGhostTruncatedKernel ν A C D N y x * W x := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [finite_ghost_truncated_kernel_weighted_transpose, mul_assoc]

theorem finite_ghost_truncated_kernel_nonneg [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (hν : ∀ p, 0 ≤ ν p)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C) (N : ℕ)
    (x y : FiniteMemory N (Σ p, R p)) :
    0 ≤ finiteGhostTruncatedKernel ν A D C N x y := by
  classical
  exact Finset.sum_nonneg (fun k _ =>
    finite_ghost_degree_kernel_nonneg ν A D C hν hA hD hC k _ _ _ _)

/-- The full signed sum is dominated by the actual positive sum of all sectors. -/
theorem finite_ghost_truncated_kernel_abs_le [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (N : ℕ)
    (x y : FiniteMemory N (Σ p, R p)) :
    |finiteGhostTruncatedKernel ν A D C N x y| ≤
      finiteGhostTruncatedKernel ν A |D| |C| N x y := by
  classical
  unfold finiteGhostTruncatedKernel
  calc
    _ ≤ ∑ k ∈ Finset.range (min x.1.val y.1.val + 1),
        |finiteGhostDegreeKernel ν A D C k _ _ x.2 y.2| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp_rw [finite_ghost_degree_kernel_abs ν A D C hν hA]

/-- The complete finite counting kernel reproduces the original row on Fock tests. -/
theorem finite_ghost_truncated_kernel_reproduces [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (N : ℕ)
    (H : FiniteMemory N (Σ p, R p) → K)
    (hH : ∀ (n : Fin (N + 1)) (σ : Equiv.Perm (Fin n.val)) y,
      H ⟨n, y ∘ σ⟩ = H ⟨n, y⟩) (x : FiniteMemory N (Σ p, R p)) :
    (∑ y : FiniteMemory N (Σ p, R p), finiteGhostTruncatedKernel ν A D C N x y * H y) =
      finiteGhostTruncatedRow ν A D C N H x := by
  classical
  unfold finiteGhostTruncatedKernel finiteGhostTruncatedRow
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro m _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact finite_ghost_degree_kernel_reproduces ν A D C k _ _ (fun y => H ⟨m, y⟩)
    (hH m) x.2

theorem finite_ghost_truncated_kernel_source_invariant [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (N : ℕ)
    (x y : FiniteMemory N (Σ p, R p)) (σ : Equiv.Perm (Fin x.1.val)) :
    finiteGhostTruncatedKernel ν A D C N ⟨x.1, x.2 ∘ σ⟩ y =
      finiteGhostTruncatedKernel ν A D C N x y := by
  classical
  unfold finiteGhostTruncatedKernel
  apply Finset.sum_congr rfl
  intro k _
  exact finite_ghost_degree_kernel_source_invariant ν A D C k _ _ _ _ σ

/-- Increase the cutoff while preserving the actual degree and indexed tuple. -/
def finiteMemoryCutoffLift (h : N ≤ M) (x : FiniteMemory N Z) : FiniteMemory M Z :=
  ⟨⟨x.1.val, by omega⟩, x.2⟩

theorem finite_memory_cutoff_lift_injective (h : N ≤ M) :
    Function.Injective (finiteMemoryCutoffLift (Z := Z) h) := by
  intro x y hxy
  rcases x with ⟨n, x⟩
  rcases y with ⟨m, y⟩
  have hnm : n = m := Fin.ext (congrArg (fun z => z.1.val) hxy)
  subst m
  have htuples : x = y := by simpa only [finiteMemoryCutoffLift, Sigma.mk.inj_iff,
    true_and, heq_eq_eq, eq_self_iff_true] using hxy
  subst y
  rfl

theorem finite_memory_point_mass_cutoff_lift [Field K] [CharZero K]
    (h : N ≤ M) (w : Z → K) (x : FiniteMemory N Z) :
    finiteMemoryPointMass w (finiteMemoryCutoffLift h x) = finiteMemoryPointMass w x := rfl

/-- The kernel coefficients stabilize exactly when the common cutoff is enlarged. -/
theorem finite_ghost_truncated_kernel_cutoff_lift [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (h : N ≤ M)
    (x y : FiniteMemory N (Σ p, R p)) :
    finiteGhostTruncatedKernel ν A D C M (finiteMemoryCutoffLift h x)
      (finiteMemoryCutoffLift h y) = finiteGhostTruncatedKernel ν A D C N x y := rfl

end SimultaneousPrimitiveRoots.Unconditional.Graph
