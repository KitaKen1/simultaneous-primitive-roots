module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostDegreeKernel
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Lean.Elab.Tactic.Omega

/-!
# Fixed-degree ghost pairings and the unrestricted sector address bijection

The original counting-kernel pairing is exactly the source factorial sector
on symmetric endpoints. Actual degrees n=k+t and m=k+b retain repeated
particle values and the k!t!b! measure. The address bijection is purely
algebraic; exchanging unrestricted sums still requires absolute convergence.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P K : Type*} {R : P → Type*} {k a b : ℕ}

theorem finite_ghost_sector_counting_joint [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (F : (Fin (k + a) → Σ p, R p) → K) (H : (Fin (k + b) → Σ p, R p) → K)
    (hF : ∀ (σ : Equiv.Perm (Fin (k + a))) x, F (x ∘ σ) = F x)
    (hH : ∀ (σ : Equiv.Perm (Fin (k + b))) y, H (y ∘ σ) = H y) :
    (∑ x : Fin (k + a) → Σ p, R p, ∑ y : Fin (k + b) → Σ p, R p,
      factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x * F x *
        finiteGhostSectorCountingKernel ν A D C x y * H y) =
    finiteGhostJointSector ν A D C (fun x y => F x * H y) := by
  classical
  calc
    _ = ∑ x : Fin (k + a) → Σ p, R p,
        factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x * F x *
          finiteGhostSectorRow ν A D C H x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← finite_ghost_sector_counting_kernel_reproduces ν A D C H hH x]
      simp only [Finset.mul_sum, mul_assoc]
    _ = finiteGhostSubsetJoint ν A D C (fun x y => F x * H y) :=
      (finite_ghost_subset_joint_row_pairing ν A D C F H).symm
    _ = _ := finite_ghost_subset_joint_identification ν A D C _
      (fun σ x y => by rw [hF σ x]) (fun σ x y => by rw [hH σ y])

/-- Pairing in arbitrary actual degrees, with both tuple transports explicit. -/
theorem finite_ghost_degree_joint_sector [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (k n m : ℕ) (hk : k ≤ n ∧ k ≤ m)
    (F : (Fin n → Σ p, R p) → K) (H : (Fin m → Σ p, R p) → K)
    (hF : ∀ (σ : Equiv.Perm (Fin n)) x, F (x ∘ σ) = F x)
    (hH : ∀ (σ : Equiv.Perm (Fin m)) y, H (y ∘ σ) = H y) :
    (∑ x : Fin n → Σ p, R p, ∑ y : Fin m → Σ p, R p,
      factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x * F x *
        finiteGhostDegreeKernel ν A D C k n m x y * H y) =
    finiteGhostJointSector (k := k) (a := n - k) (b := m - k) ν A D C
      (fun x y => F (memoryDegreeEquiv (by omega : k + (n - k) = n) x) *
        H (memoryDegreeEquiv (by omega : k + (m - k) = m) y)) := by
  classical
  let e := memoryDegreeEquiv (Z := Σ p, R p) (by omega : k + (n - k) = n)
  let d := memoryDegreeEquiv (Z := Σ p, R p) (by omega : k + (m - k) = m)
  calc
    _ = ∑ x : Fin n → Σ p, R p,
        factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x * F x *
          finiteGhostDegreeRow ν A D C k n m H x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← finite_ghost_degree_kernel_reproduces ν A D C k n m H hH x]
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ x : Fin n → Σ p, R p,
        factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x * F x *
          finiteGhostSectorRow ν A D C (fun y => H (d y)) (e.symm x) := by
      simp only [finiteGhostDegreeRow, dif_pos hk]
      rfl
    _ = ∑ x : Fin (k + (n - k)) → Σ p, R p,
        factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x * F (e x) *
          finiteGhostSectorRow ν A D C (fun y => H (d y)) x := by
      rw [← Equiv.sum_comp e]
      simp only [Equiv.symm_apply_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [show factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) (e x) =
        factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x from
          factorial_memory_point_mass_degree_equiv _ _ x]
    _ = finiteGhostSubsetJoint ν A D C (fun x y => F (e x) * H (d y)) :=
      (finite_ghost_subset_joint_row_pairing ν A D C (fun x => F (e x))
        (fun y => H (d y))).symm
    _ = _ := finite_ghost_subset_joint_identification ν A D C _
      (fun σ x y => by rw [memory_degree_equiv_symmetric_test _ F hF σ x])
      (fun σ x y => by rw [memory_degree_equiv_symmetric_test _ H hH σ y])

/-- Addresses (old degree, new degree, survivor count) with admissible survivors. -/
abbrev GhostSurvivorDegrees := {z : ℕ × ℕ × ℕ // z.2.2 ≤ z.1 ∧ z.2.2 ≤ z.2.1}

/-- All (k,t,b) correspond exactly to admissible (n,m,k), without a cutoff. -/
def ghostSectorDegreeEquiv : (ℕ × ℕ × ℕ) ≃ GhostSurvivorDegrees where
  toFun z := ⟨(z.1 + z.2.1, z.1 + z.2.2, z.1), by
    change z.1 ≤ z.1 + z.2.1 ∧ z.1 ≤ z.1 + z.2.2
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩⟩
  invFun z := (z.val.2.2, z.val.1 - z.val.2.2, z.val.2.1 - z.val.2.2)
  left_inv z := by
    rcases z with ⟨k, t, b⟩
    simp
  right_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨n, m, k⟩, hk⟩
    change k ≤ n ∧ k ≤ m at hk
    apply Prod.ext
    · dsimp
      omega
    · apply Prod.ext
      · dsimp
        omega
      · rfl

theorem ghost_sector_degree_equiv_apply (k t b : ℕ) :
    (ghostSectorDegreeEquiv (k, t, b)).val = (k + t, k + b, k) := rfl

theorem ghost_sector_degree_equiv_symm_apply (z : GhostSurvivorDegrees) :
    ghostSectorDegreeEquiv.symm z = (z.val.2.2, z.val.1 - z.val.2.2,
      z.val.2.1 - z.val.2.2) := rfl

theorem ghost_sector_degree_summable_iff {L : Type*} [AddCommMonoid L]
    [TopologicalSpace L] (f : GhostSurvivorDegrees → L) :
    Summable (fun z : ℕ × ℕ × ℕ => f (ghostSectorDegreeEquiv z)) ↔ Summable f :=
  ghostSectorDegreeEquiv.summable_iff

theorem ghost_sector_degree_tsum {L : Type*} [AddCommMonoid L] [TopologicalSpace L]
    (f : GhostSurvivorDegrees → L) :
    (∑' z : ℕ × ℕ × ℕ, f (ghostSectorDegreeEquiv z)) = ∑' z, f z :=
  ghostSectorDegreeEquiv.tsum_eq f

end SimultaneousPrimitiveRoots.Unconditional.Graph
