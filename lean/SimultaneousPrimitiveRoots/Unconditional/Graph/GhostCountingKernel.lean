module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostSubsetRow
public import SimultaneousPrimitiveRoots.Unconditional.Graph.SymmetricMemoryTests
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Counting kernels of actual finite ghost rows

The target point test is projected onto the symmetric memory space. Its
counting kernel represents the original subset/birth row on symmetric tests.
The factorial memory masses are used for the transpose, not inserted into
the row action. Unbounded summation and operator norms remain separate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P K T : Type*} {R : P → Type*} {k a b : ℕ}

attribute [local instance] Classical.propDecidable

theorem finite_ghost_subset_coefficient_card_zero [CommSemiring K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (s : Finset (Fin (k + a))) (hs : s.card ≠ a) (x : Fin (k + a) → Σ p, R p) :
    finiteGhostSubsetCoefficient ν A E s x = 0 := by
  unfold finiteGhostSubsetCoefficient
  rw [dif_neg hs]

/-- The card-dependent coefficient already excludes all wrong-sized subsets. -/
theorem finite_ghost_subset_coefficient_sum_all [CommSemiring K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (x : Fin (k + a) → Σ p, R p) :
    (∑ s : Finset (Fin (k + a)) with s.card = a, finiteGhostSubsetCoefficient ν A E s x) =
      ∑ s : Finset (Fin (k + a)), finiteGhostSubsetCoefficient ν A E s x := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s.card = a
  · rw [if_pos hs]
  · rw [if_neg hs, finite_ghost_subset_coefficient_card_zero ν A E s hs]

/-- Multiplying the source endpoint test multiplies the actual coefficient. -/
theorem finite_ghost_subset_coefficient_source_mul [CommSemiring K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A : K)
    (F : (Fin (k + a) → Σ p, R p) → K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (s : Finset (Fin (k + a))) (x : Fin (k + a) → Σ p, R p) :
    finiteGhostSubsetCoefficient ν A (fun x y => F x * E x y) s x =
      F x * finiteGhostSubsetCoefficient ν A E s x := by
  classical
  unfold finiteGhostSubsetCoefficient
  split_ifs
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  all_goals simp only [mul_zero]

/-- The actual subset coefficient commutes with any finite sum of endpoint tests. -/
theorem finite_ghost_subset_coefficient_sum [CommSemiring K] [Fintype P] [Fintype T]
    [∀ p, Zero (R p)] (ν : P → K) (A : K)
    (E : T → (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (s : Finset (Fin (k + a))) (x : Fin (k + a) → Σ p, R p) :
    finiteGhostSubsetCoefficient ν A (fun x y => ∑ t, E t x y) s x =
      ∑ t, finiteGhostSubsetCoefficient ν A (E t) s x := by
  classical
  unfold finiteGhostSubsetCoefficient
  split_ifs
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  all_goals simp only [Finset.sum_const_zero]

/-- The actual finite-sector ghost row, with no factorial mass inserted into transitions. -/
noncomputable def finiteGhostSectorRow [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (H : (Fin (k + b) → Σ p, R p) → K) (x : Fin (k + a) → Σ p, R p) : K := by
  classical
  exact (D ^ a * C ^ b) / (b.factorial : K) *
    ∑ s : Finset (Fin (k + a)), finiteGhostSubsetCoefficient ν A (fun _ y => H y) s x

/-- The actual row applied to a symmetric counting point test at its target. -/
noncomputable def finiteGhostSectorCountingKernel [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (x : Fin (k + a) → Σ p, R p) (y : Fin (k + b) → Σ p, R p) : K :=
  finiteGhostSectorRow ν A D C (fun z => symmetricMemoryPoint y z) x

/-- Subset transport proves source-index invariance of the actual row. -/
theorem finite_ghost_sector_row_invariant [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (H : (Fin (k + b) → Σ p, R p) → K)
    (hH : ∀ (σ : Equiv.Perm (Fin (k + b))) y, H (y ∘ σ) = H y)
    (x : Fin (k + a) → Σ p, R p) (σ : Equiv.Perm (Fin (k + a))) :
    finiteGhostSectorRow ν A D C H (x ∘ σ) = finiteGhostSectorRow ν A D C H x := by
  classical
  unfold finiteGhostSectorRow
  congr 1
  rw [← Equiv.sum_comp (Equiv.finsetCongr σ.symm)
    (fun s => finiteGhostSubsetCoefficient ν A (fun _ y => H y) s (x ∘ σ))]
  apply Finset.sum_congr rfl
  intro s _
  exact finite_ghost_subset_coefficient_covariance ν A (fun _ y => H y)
    (fun _ _ _ => rfl) (fun π _ y => hH π y) σ.symm s x

/-- The actual counting kernel is symmetric in the old particle indices. -/
theorem finite_ghost_sector_counting_kernel_source_invariant [Field K] [CharZero K]
    [Fintype P] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (x : Fin (k + a) → Σ p, R p) (y : Fin (k + b) → Σ p, R p)
    (σ : Equiv.Perm (Fin (k + a))) :
    finiteGhostSectorCountingKernel ν A D C (x ∘ σ) y =
      finiteGhostSectorCountingKernel ν A D C x y := by
  exact finite_ghost_sector_row_invariant ν A D C (fun z => symmetricMemoryPoint y z)
    (fun π z => symmetric_memory_point_invariant y z π) x σ

/-- Summing the actual counting kernel against a symmetric target test gives its row action. -/
theorem finite_ghost_sector_counting_kernel_reproduces [Field K] [CharZero K]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (H : (Fin (k + b) → Σ p, R p) → K)
    (hH : ∀ (σ : Equiv.Perm (Fin (k + b))) y, H (y ∘ σ) = H y)
    (x : Fin (k + a) → Σ p, R p) :
    (∑ y : Fin (k + b) → Σ p, R p, finiteGhostSectorCountingKernel ν A D C x y * H y) =
      finiteGhostSectorRow ν A D C H x := by
  classical
  have hp (z : Fin (k + b) → Σ p, R p) :
      (∑ y : Fin (k + b) → Σ p, R p, H y * symmetricMemoryPoint y z) = H z := by
    calc
      _ = ∑ y : Fin (k + b) → Σ p, R p, H y * symmetricMemoryPoint z y := by
        apply Finset.sum_congr rfl
        intro y _
        exact congrArg (H y * ·) (symmetric_memory_point_transpose y z)
      _ = _ := by
        simpa only [one_mul] using symmetric_memory_point_reproducing
          (fun _ => (1 : K)) H (fun _ _ => rfl) hH z
  have hc (s : Finset (Fin (k + a))) :
      (∑ y : Fin (k + b) → Σ p, R p,
        finiteGhostSubsetCoefficient ν A (fun _ z => symmetricMemoryPoint y z) s x * H y) =
      finiteGhostSubsetCoefficient ν A (fun _ z => H z) s x := by
    calc
      _ = ∑ y : Fin (k + b) → Σ p, R p,
          finiteGhostSubsetCoefficient ν A (fun _ z => H y * symmetricMemoryPoint y z) s x := by
        apply Finset.sum_congr rfl
        intro y _
        rw [finite_ghost_subset_coefficient_source_mul ν A (fun _ => H y)]
        exact mul_comm _ _
      _ = finiteGhostSubsetCoefficient ν A
          (fun _ z => ∑ y : Fin (k + b) → Σ p, R p, H y * symmetricMemoryPoint y z) s x := by
        rw [finite_ghost_subset_coefficient_sum]
      _ = _ := by simp_rw [hp]
  unfold finiteGhostSectorCountingKernel finiteGhostSectorRow
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [hc]

/-- The actual row pairs in the original factorial measure, with no new transition mass. -/
theorem finite_ghost_subset_joint_row_pairing [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (F : (Fin (k + a) → Σ p, R p) → K) (H : (Fin (k + b) → Σ p, R p) → K) :
    finiteGhostSubsetJoint ν A D C (fun x y => F x * H y) =
      ∑ x : Fin (k + a) → Σ p, R p,
        factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x * F x *
          finiteGhostSectorRow ν A D C H x := by
  classical
  unfold finiteGhostSubsetJoint
  rw [Finset.sum_comm]
  simp_rw [finite_ghost_subset_coefficient_source_mul ν A F,
    ← mul_assoc, ← Finset.mul_sum, finite_ghost_subset_coefficient_sum_all]
  unfold finiteGhostSectorRow factorialMemoryPointMass
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A double symmetric point test extracts the actual kernel with its old factorial mass. -/
theorem finite_ghost_sector_counting_kernel_point_pairing [Field K] [CharZero K]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (x : Fin (k + a) → Σ p, R p) (y : Fin (k + b) → Σ p, R p) :
    finiteGhostSubsetJoint ν A D C
      (fun u v => symmetricMemoryPoint x u * symmetricMemoryPoint y v) =
      factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        finiteGhostSectorCountingKernel ν A D C x y := by
  classical
  rw [finite_ghost_subset_joint_row_pairing]
  calc
    _ = ∑ u : Fin (k + a) → Σ p, R p,
        factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) u *
          finiteGhostSectorRow ν A D C (fun v => symmetricMemoryPoint y v) u *
          symmetricMemoryPoint x u := by
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := by
      exact factorial_memory_point_reproducing (fun z : Σ p, R p => ν z.1)
        (finiteGhostSectorRow ν A D C (fun v => symmetricMemoryPoint y v))
        (fun σ u => finite_ghost_sector_row_invariant ν A D C
          (fun v => symmetricMemoryPoint y v)
          (fun π v => symmetric_memory_point_invariant y v π) u σ) x

/-- The actual counting kernels transpose with precisely their factorial endpoint masses.
This identity also covers zero prime weights; no inverse endpoint mass is used. -/
theorem finite_ghost_sector_counting_kernel_weighted_transpose [Field K] [CharZero K]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (x : Fin (k + a) → Σ p, R p) (y : Fin (k + b) → Σ p, R p) :
    factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
      finiteGhostSectorCountingKernel ν A D C x y =
    factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) y *
      finiteGhostSectorCountingKernel ν A C D y x := by
  rw [← finite_ghost_sector_counting_kernel_point_pairing ν A D C x y,
    finite_ghost_subset_joint_reversal ν A D C
      (fun u v => symmetricMemoryPoint x u * symmetricMemoryPoint y v)
      (fun σ u v => by rw [symmetric_memory_point_invariant x u σ])
      (fun σ u v => by rw [symmetric_memory_point_invariant y v σ])]
  have hE : (fun v u => symmetricMemoryPoint (K := K) x u * symmetricMemoryPoint y v) =
      (fun v u => symmetricMemoryPoint y v * symmetricMemoryPoint x u) := by
    funext v u
    exact mul_comm _ _
  rw [hE, finite_ghost_sector_counting_kernel_point_pairing ν A C D y x]

/-- The actual column sum is the coefficient-swapped row, with its endpoint mass retained. -/
theorem finite_ghost_sector_counting_kernel_weighted_column [Field K] [CharZero K]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (W : (Fin (k + a) → Σ p, R p) → K) (y : Fin (k + b) → Σ p, R p) :
    (∑ x : Fin (k + a) → Σ p, R p,
      factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        finiteGhostSectorCountingKernel ν A D C x y * W x) =
    factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) y *
      ∑ x : Fin (k + a) → Σ p, R p, finiteGhostSectorCountingKernel ν A C D y x * W x := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [finite_ghost_sector_counting_kernel_weighted_transpose, mul_assoc]

/-- The actual coefficient is positive for a positive endpoint test and positive data. -/
theorem finite_ghost_subset_coefficient_nonneg [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A : ℝ)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hE : ∀ x y, 0 ≤ E x y)
    (s : Finset (Fin (k + a))) (x : Fin (k + a) → Σ p, R p) :
    0 ≤ finiteGhostSubsetCoefficient ν A E s x := by
  classical
  unfold finiteGhostSubsetCoefficient
  split_ifs
  · apply mul_nonneg (pow_nonneg hA _)
    apply Finset.sum_nonneg
    intro q _
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => hν (q i))) (hE _ _)
  all_goals exact le_rfl

theorem finite_ghost_sector_row_nonneg [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (H : (Fin (k + b) → Σ p, R p) → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hH : ∀ y, 0 ≤ H y) (x : Fin (k + a) → Σ p, R p) :
    0 ≤ finiteGhostSectorRow ν A D C H x := by
  classical
  unfold finiteGhostSectorRow
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro s _
    exact finite_ghost_subset_coefficient_nonneg ν A (fun _ y => H y)
      hν hA (fun _ y => hH y) s x

theorem finite_ghost_sector_counting_kernel_nonneg [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (hν : ∀ p, 0 ≤ ν p)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (x : Fin (k + a) → Σ p, R p) (y : Fin (k + b) → Σ p, R p) :
    0 ≤ finiteGhostSectorCountingKernel ν A D C x y := by
  exact finite_ghost_sector_row_nonneg ν A D C (fun z => symmetricMemoryPoint y z)
    hν hA hD hC (fun z => symmetric_memory_point_nonneg y z) x

end SimultaneousPrimitiveRoots.Unconditional.Graph
