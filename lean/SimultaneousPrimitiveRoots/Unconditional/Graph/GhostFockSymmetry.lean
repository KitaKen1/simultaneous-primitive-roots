module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostContinuousOperator

/-!
# Symmetric Fock output of the continuous ghost completion

The original factorial point mass is invariant under particle-index
permutations, including repeated values. The finite-support ghost action
has symmetric weighted coordinates. Density and continuous coordinate
evaluation then preserve that symmetry for every input of the continuous
completion. This does not identify arbitrary nonsymmetric marked row tests.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {Z P : Type*} {R : P → Type*}

theorem infinite_memory_point_mass_invariant (w : Z → ℝ) (x : InfiniteMemory Z)
    (σ : Equiv.Perm (Fin x.1)) :
    infiniteMemoryPointMass w ⟨x.1, x.2 ∘ σ⟩ = infiniteMemoryPointMass w x :=
  factorial_memory_point_mass_invariant w x.2 σ

theorem infinite_ghost_weighted_domain_symmetric [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) (x : InfiniteMemory (Σ p, R p))
    (σ : Equiv.Perm (Fin x.1)) :
    infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g ⟨x.1, x.2 ∘ σ⟩ =
    infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g x := by
  change (Real.sqrt (infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1)
      ⟨x.1, x.2 ∘ σ⟩) : ℂ) *
      infiniteGhostFiniteSupportAction ν A D C g ⟨x.1, x.2 ∘ σ⟩ =
    (Real.sqrt (infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x) : ℂ) *
      infiniteGhostFiniteSupportAction ν A D C g x
  rw [infinite_memory_point_mass_invariant, infinite_ghost_finite_support_action_symmetric]

theorem infinite_ghost_continuous_operator_symmetric [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (x : InfiniteMemory (Σ p, R p)) (σ : Equiv.Perm (Fin x.1)) :
    infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f ⟨x.1, x.2 ∘ σ⟩ =
    infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f x := by
  let T := infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM
  have hd := weighted_memory_input_dense (fun z : Σ p, R p => ν z.1)
    (fun z => hν z.1)
  change T f ⟨x.1, x.2 ∘ σ⟩ = T f x
  refine hd.induction_on (p := fun a => T a ⟨x.1, x.2 ∘ σ⟩ = T a x) f ?_ ?_
  · exact isClosed_eq
      ((lp.evalCLM ℂ (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2
        ⟨x.1, x.2 ∘ σ⟩).continuous.comp T.continuous)
      ((lp.evalCLM ℂ (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2 x).continuous.comp T.continuous)
  · intro g
    simp only [T, infinite_ghost_continuous_operator_on_finite_support]
    exact infinite_ghost_weighted_domain_symmetric ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g x σ

end SimultaneousPrimitiveRoots.Unconditional.Graph
