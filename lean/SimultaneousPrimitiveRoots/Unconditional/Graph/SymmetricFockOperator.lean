module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostFockSymmetry
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The source symmetric Fock Hilbert space and its pure ghost completion

The closed particle-index invariant subspace of counting ell-two represents
the original factorial-weighted Fock space through the proved square-root
point-mass coordinates. Repeated particle values and the degree-zero sector
are retained. The pure ghost completion restricts to a bounded operator on
this complete symmetric space. Symmetric finite-support density, general-input single rows and the reversed
bounded adjoint are certified separately. Flat joint-sum interchange and the
full conditional transference operator remain open.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {Z P : Type*} {R : P → Type*}

def symmetricMemoryFock (Z : Type*) : Submodule ℂ (lp (fun _ : InfiniteMemory Z => ℂ) 2) where
  carrier := {f | ∀ (x : InfiniteMemory Z) (σ : Equiv.Perm (Fin x.1)),
    f ⟨x.1, x.2 ∘ σ⟩ = f x}
  zero_mem' := fun _ _ => rfl
  add_mem' {f} {g} hf hg x σ := by
    change f ⟨x.1, x.2 ∘ σ⟩ + g ⟨x.1, x.2 ∘ σ⟩ = f x + g x
    rw [hf x σ, hg x σ]
  smul_mem' c f hf x σ := by
    change c * f ⟨x.1, x.2 ∘ σ⟩ = c * f x
    rw [hf x σ]

theorem symmetric_memory_fock_isClosed : IsClosed (symmetricMemoryFock Z :
    Set (lp (fun _ : InfiniteMemory Z => ℂ) 2)) := by
  change IsClosed {f : lp (fun _ : InfiniteMemory Z => ℂ) 2 |
    ∀ (x : InfiniteMemory Z) (σ : Equiv.Perm (Fin x.1)), f ⟨x.1, x.2 ∘ σ⟩ = f x}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro σ
  exact isClosed_eq
    (lp.evalCLM ℂ (fun _ : InfiniteMemory Z => ℂ) 2 ⟨x.1, x.2 ∘ σ⟩).continuous
    (lp.evalCLM ℂ (fun _ : InfiniteMemory Z => ℂ) 2 x).continuous

theorem symmetric_memory_fock_complete : CompleteSpace (symmetricMemoryFock Z) :=
  symmetric_memory_fock_isClosed.completeSpace_coe

theorem weighted_memory_input_mem_symmetric (w : Z → ℝ)
    (g : InfiniteMemory Z →₀ ℂ)
    (hg : ∀ (x : InfiniteMemory Z) (σ : Equiv.Perm (Fin x.1)),
      g ⟨x.1, x.2 ∘ σ⟩ = g x) : weightedMemoryInputLinearMap w g ∈ symmetricMemoryFock Z := by
  intro x σ
  rw [weighted_memory_input_apply, weighted_memory_input_apply]
  unfold weightedMemoryCoordinates
  rw [infinite_memory_point_mass_invariant, hg x σ]

noncomputable def infiniteGhostSymmetricFockOperator [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) :
    symmetricMemoryFock (Σ p, R p) →L[ℂ] symmetricMemoryFock (Σ p, R p) :=
  ((infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM).codRestrict (symmetricMemoryFock (Σ p, R p))
      (fun f => infinite_ghost_continuous_operator_symmetric ν A D C v cmax dmax Mmax
        hν hA hv hbaseD hbaseC hC hD hM f)).comp (symmetricMemoryFock (Σ p, R p)).subtypeL

theorem infinite_ghost_symmetric_fock_norm_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (f : symmetricMemoryFock (Σ p, R p)) :
    ‖infiniteGhostSymmetricFockOperator ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f‖ ≤
    Real.sqrt (Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax)) * ‖f‖ :=
  infinite_ghost_continuous_operator_norm_bound ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f.val

theorem infinite_ghost_symmetric_fock_opnorm_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) :
    ‖infiniteGhostSymmetricFockOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM‖ ≤
    Real.sqrt (Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax)) := by
  apply ContinuousLinearMap.opNorm_le_bound
    (infiniteGhostSymmetricFockOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM) (Real.sqrt_nonneg _)
  exact infinite_ghost_symmetric_fock_norm_bound ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM

end SimultaneousPrimitiveRoots.Unconditional.Graph
