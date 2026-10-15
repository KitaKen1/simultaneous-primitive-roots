module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.InfiniteMemory
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostTruncatedNorm

/-!
# Infinite-output ghost action on the finite-support Fock domain

The cutoff-independent complex square estimate bounds every finite subset of
the full infinite indexed memory. Hence the original factorial-weighted
output square sum is summable and satisfies the same bound. The input is
finitely supported; the output may occupy infinitely many degrees. On
symmetric inputs the cutoff identity is the original complex ghost row.
GhostContinuousOperator and SymmetricFockOperator separately construct the
bounded pure-ghost completion. Unbounded row/joint interchanges, tensor
products, and conditional edge/history estimates remain open.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P : Type*} {R : P → Type*}

theorem infinite_ghost_finite_support_partial_sq_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) (s : Finset (InfiniteMemory (Σ p, R p))) :
    (∑ x ∈ s, infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
      ‖infiniteGhostFiniteSupportAction ν A D C g x‖ ^ 2) ≤
    Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) *
      ∑ y ∈ g.support, infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) y * ‖g y‖ ^ 2 := by
  classical
  let N := (s ∪ g.support).sup Sigma.fst
  have hs : ∀ x ∈ s, x.1 ≤ N := fun x hx =>
    infinite_memory_finset_degree_bound _ x (Finset.mem_union_left _ hx)
  have hg : ∀ y ∈ g.support, y.1 ≤ N := fun y hy =>
    infinite_memory_finset_degree_bound _ y (Finset.mem_union_right _ hy)
  have hpos (x : InfiniteMemory (Σ p, R p)) :
      0 ≤ infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        ‖infiniteGhostFiniteSupportAction ν A D C g x‖ ^ 2 :=
    mul_nonneg (infinite_memory_point_mass_pos _ (fun z => hν z.1) x).le (sq_nonneg _)
  have hcut :
      (∑ x : FiniteMemory N (Σ p, R p),
        infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) (finiteMemoryToInfinite x) *
          ‖infiniteGhostFiniteSupportAction ν A D C g (finiteMemoryToInfinite x)‖ ^ 2) ≤
      Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) *
        ∑ y : FiniteMemory N (Σ p, R p),
          infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) (finiteMemoryToInfinite y) *
            ‖g (finiteMemoryToInfinite y)‖ ^ 2 := by
    simp_rw [infinite_memory_point_mass_cutoff,
      infinite_ghost_finite_support_action_cutoff ν A D C g hg]
    exact finite_ghost_truncated_projected_complex_sq_bound ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM N (fun y => g (finiteMemoryToInfinite y))
  calc
    _ ≤ _ := infinite_memory_finset_sum_le_cutoff _ hpos s hs
    _ ≤ _ := hcut
    _ = _ := by
      rw [← infinite_memory_support_sum g hg
        (fun y a => infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) y * ‖a‖ ^ 2)
        (fun _ => by simp)]

/-- Infinite output square summability is obtained from all finite partial sums. -/
theorem infinite_ghost_finite_support_sq_summable [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) :
    Summable (fun x : InfiniteMemory (Σ p, R p) =>
      infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        ‖infiniteGhostFiniteSupportAction ν A D C g x‖ ^ 2) := by
  have hpos (x : InfiniteMemory (Σ p, R p)) :
      0 ≤ infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        ‖infiniteGhostFiniteSupportAction ν A D C g x‖ ^ 2 :=
    mul_nonneg (infinite_memory_point_mass_pos _ (fun z => hν z.1) x).le (sq_nonneg _)
  exact summable_of_sum_le hpos
    (infinite_ghost_finite_support_partial_sq_bound ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g)

theorem infinite_ghost_finite_support_tsum_sq_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) :
    (∑' x : InfiniteMemory (Σ p, R p),
      infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        ‖infiniteGhostFiniteSupportAction ν A D C g x‖ ^ 2) ≤
    Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) *
      ∑ y ∈ g.support, infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) y * ‖g y‖ ^ 2 := by
  have hpos (x : InfiniteMemory (Σ p, R p)) :
      0 ≤ infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        ‖infiniteGhostFiniteSupportAction ν A D C g x‖ ^ 2 :=
    mul_nonneg (infinite_memory_point_mass_pos _ (fun z => hν z.1) x).le (sq_nonneg _)
  exact Real.tsum_le_of_sum_le hpos
    (infinite_ghost_finite_support_partial_sq_bound ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g)

/-- For symmetric Fock inputs the finite-support action is the original complex row. -/
theorem infinite_ghost_finite_support_actual_row_cutoff [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ) (N : ℕ)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) (hs : ∀ y ∈ g.support, y.1 ≤ N)
    (hg : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) y, g ⟨n, y ∘ σ⟩ = g ⟨n, y⟩)
    (x : FiniteMemory N (Σ p, R p)) :
    infiniteGhostFiniteSupportAction ν A D C g (finiteMemoryToInfinite x) =
      finiteGhostTruncatedRow (fun p => (ν p : ℂ)) (A : ℂ) (D : ℂ) (C : ℂ) N
        (fun y => g (finiteMemoryToInfinite y)) x := by
  rw [infinite_ghost_finite_support_action_cutoff ν A D C g hs]
  exact (finite_ghost_truncated_real_complex_row ν A D C N
    (fun y => g (finiteMemoryToInfinite y)) (fun n σ y => hg n.val σ y) x).symm

end SimultaneousPrimitiveRoots.Unconditional.Graph
