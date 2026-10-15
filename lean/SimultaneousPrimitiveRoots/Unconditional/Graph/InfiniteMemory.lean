module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostTruncatedKernel
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Lean.Elab.Tactic.Omega

/-!
# Infinite indexed memory and its exact finite cutoffs

Every degree is retained, with the original factorial counting point mass.
Each degree-pair coefficient is the existing finite survivor-sector sum.
The action on a finitely supported input sums only over that input support;
its output is not assumed to have finite support. This file identifies the
finite cutoff action and measure without invoking an infinite sum interchange.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {Z P K : Type*} {R : P → Type*} {N : ℕ}

abbrev InfiniteMemory (Z : Type*) := Σ n : ℕ, Fin n → Z

def finiteMemoryToInfinite (x : FiniteMemory N Z) : InfiniteMemory Z := ⟨x.1.val, x.2⟩

theorem finite_memory_to_infinite_injective :
    Function.Injective (finiteMemoryToInfinite (N := N) (Z := Z)) := by
  intro x y hxy
  rcases x with ⟨n, x⟩
  rcases y with ⟨m, y⟩
  have hnm : n = m := Fin.ext (congrArg Sigma.fst hxy)
  subst m
  have htuples : x = y := by
    simpa only [finiteMemoryToInfinite, Sigma.mk.inj_iff, true_and,
      heq_eq_eq, eq_self_iff_true] using hxy
  subst y
  rfl

def finiteMemoryEmbedding : FiniteMemory N Z ↪ InfiniteMemory Z :=
  ⟨finiteMemoryToInfinite, finite_memory_to_infinite_injective⟩

noncomputable def infiniteMemoryCutoff [Fintype Z] (N : ℕ) : Finset (InfiniteMemory Z) :=
  (Finset.univ : Finset (FiniteMemory N Z)).map finiteMemoryEmbedding

theorem infinite_memory_mem_cutoff [Fintype Z] (x : InfiniteMemory Z) :
    x ∈ infiniteMemoryCutoff N ↔ x.1 ≤ N := by
  classical
  unfold infiniteMemoryCutoff
  constructor
  · intro hx
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
    have hd : y.1.val = x.1 := congrArg Sigma.fst hy
    have := y.1.isLt
    omega
  · intro hx
    rcases x with ⟨n, x⟩
    change n ≤ N at hx
    exact Finset.mem_map.mpr ⟨⟨⟨n, by omega⟩, x⟩, Finset.mem_univ _, rfl⟩

theorem infinite_memory_finset_degree_bound (s : Finset (InfiniteMemory Z))
    (x : InfiniteMemory Z) (hx : x ∈ s) : x.1 ≤ s.sup Sigma.fst :=
  Finset.le_sup hx

theorem infinite_memory_finset_subset_cutoff [Fintype Z] (s : Finset (InfiniteMemory Z))
    (hs : ∀ x ∈ s, x.1 ≤ N) : s ⊆ infiniteMemoryCutoff N :=
  fun x hx => (infinite_memory_mem_cutoff x).mpr (hs x hx)

theorem infinite_memory_cutoff_sum [Fintype Z] [AddCommMonoid K]
    (f : InfiniteMemory Z → K) :
    (∑ x ∈ infiniteMemoryCutoff N, f x) =
      ∑ x : FiniteMemory N Z, f (finiteMemoryToInfinite x) := by
  classical
  exact Finset.sum_map (Finset.univ : Finset (FiniteMemory N Z)) finiteMemoryEmbedding f

/-- An exact support-to-cutoff identity for any zero-preserving summand. -/
theorem infinite_memory_support_sum [Fintype Z] [Zero K] {L : Type*} [AddCommMonoid L]
    (g : InfiniteMemory Z →₀ K) (hs : ∀ y ∈ g.support, y.1 ≤ N)
    (f : InfiniteMemory Z → K → L) (hf : ∀ y, f y 0 = 0) :
    (∑ y ∈ g.support, f y (g y)) =
      ∑ y : FiniteMemory N Z, f (finiteMemoryToInfinite y) (g (finiteMemoryToInfinite y)) := by
  classical
  rw [← infinite_memory_cutoff_sum (N := N) (fun y => f y (g y))]
  apply Finset.sum_subset (infinite_memory_finset_subset_cutoff g.support hs)
  intro y _ hy
  rw [Finsupp.notMem_support_iff.mp hy, hf]

theorem infinite_memory_finset_sum_le_cutoff [Fintype Z] (f : InfiniteMemory Z → ℝ)
    (hf : ∀ x, 0 ≤ f x) (s : Finset (InfiniteMemory Z)) (hs : ∀ x ∈ s, x.1 ≤ N) :
    (∑ x ∈ s, f x) ≤ ∑ x : FiniteMemory N Z, f (finiteMemoryToInfinite x) := by
  classical
  rw [← infinite_memory_cutoff_sum (N := N) f]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (infinite_memory_finset_subset_cutoff s hs) (fun x _ _ => hf x)

noncomputable def infiniteMemoryPointMass [Field K] [CharZero K]
    (w : Z → K) (x : InfiniteMemory Z) : K := factorialMemoryPointMass w x.2

theorem infinite_memory_point_mass_pos (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (x : InfiniteMemory Z) : 0 < infiniteMemoryPointMass w x :=
  factorial_memory_point_mass_pos w hw x.2

theorem infinite_memory_point_mass_cutoff [Field K] [CharZero K]
    (w : Z → K) (x : FiniteMemory N Z) :
    infiniteMemoryPointMass w (finiteMemoryToInfinite x) = finiteMemoryPointMass w x := rfl

noncomputable def infiniteGhostKernel [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (x y : InfiniteMemory (Σ p, R p)) : K :=
  ∑ k ∈ Finset.range (min x.1 y.1 + 1),
    finiteGhostDegreeKernel ν A D C k x.1 y.1 x.2 y.2

theorem infinite_ghost_kernel_cutoff [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (x y : FiniteMemory N (Σ p, R p)) :
    infiniteGhostKernel ν A D C (finiteMemoryToInfinite x) (finiteMemoryToInfinite y) =
      finiteGhostTruncatedKernel ν A D C N x y := rfl

theorem infinite_ghost_kernel_weighted_transpose [Field K] [CharZero K]
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (x y : InfiniteMemory (Σ p, R p)) :
    infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x * infiniteGhostKernel ν A D C x y =
    infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) y * infiniteGhostKernel ν A C D y x := by
  classical
  unfold infiniteMemoryPointMass infiniteGhostKernel
  rw [min_comm y.1 x.1, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact finite_ghost_degree_kernel_weighted_transpose ν A D C k _ _ _ _

theorem infinite_ghost_kernel_source_invariant [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (x y : InfiniteMemory (Σ p, R p)) (σ : Equiv.Perm (Fin x.1)) :
    infiniteGhostKernel ν A D C ⟨x.1, x.2 ∘ σ⟩ y = infiniteGhostKernel ν A D C x y := by
  classical
  unfold infiniteGhostKernel
  apply Finset.sum_congr rfl
  intro k _
  exact finite_ghost_degree_kernel_source_invariant ν A D C k _ _ _ _ σ

noncomputable def infiniteGhostFiniteSupportAction [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (g : InfiniteMemory (Σ p, R p) →₀ ℂ)
    (x : InfiniteMemory (Σ p, R p)) : ℂ :=
  ∑ y ∈ g.support, ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) * g y

theorem infinite_ghost_finite_support_action_cutoff [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) (hs : ∀ y ∈ g.support, y.1 ≤ N)
    (x : FiniteMemory N (Σ p, R p)) :
    infiniteGhostFiniteSupportAction ν A D C g (finiteMemoryToInfinite x) =
      ∑ y : FiniteMemory N (Σ p, R p),
        ((finiteGhostTruncatedKernel ν A D C N x y : ℝ) : ℂ) * g (finiteMemoryToInfinite y) := by
  classical
  unfold infiniteGhostFiniteSupportAction
  rw [infinite_memory_support_sum g hs _ (fun _ => mul_zero _)]
  simp_rw [infinite_ghost_kernel_cutoff]

theorem infinite_ghost_finite_support_action_symmetric [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (g : InfiniteMemory (Σ p, R p) →₀ ℂ)
    (x : InfiniteMemory (Σ p, R p)) (σ : Equiv.Perm (Fin x.1)) :
    infiniteGhostFiniteSupportAction ν A D C g ⟨x.1, x.2 ∘ σ⟩ =
      infiniteGhostFiniteSupportAction ν A D C g x := by
  classical
  unfold infiniteGhostFiniteSupportAction
  simp_rw [infinite_ghost_kernel_source_invariant]

end SimultaneousPrimitiveRoots.Unconditional.Graph
