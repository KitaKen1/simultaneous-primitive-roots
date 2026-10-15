module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.SymmetricFockOperator
public import SimultaneousPrimitiveRoots.Unconditional.Graph.WeightedFockCoordinates
public import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Degree-cutoff density in the original symmetric Fock space

Whole degree cutoffs retain repeated particles and permutation orbits. Their
coordinate sums converge in ell-two. Positive original factorial masses give
exact symmetric finite-support preimages, so the density assertion holds in
the closed symmetric subspace itself, with the original measure.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ENNReal Classical
open Filter

variable {Z : Type*} [Fintype Z]

theorem infinite_memory_cutoff_monotone : Monotone (infiniteMemoryCutoff (Z := Z)) := by
  intro N M hNM x hx
  exact (infinite_memory_mem_cutoff x).mpr
    (le_trans ((infinite_memory_mem_cutoff x).mp hx) hNM)

theorem infinite_memory_cutoff_tendsto :
    Tendsto (infiniteMemoryCutoff (Z := Z)) atTop atTop :=
  infinite_memory_cutoff_monotone.tendsto_atTop_finset
    (fun x => ⟨x.1, (infinite_memory_mem_cutoff x).mpr le_rfl⟩)

noncomputable def memoryDegreeCutoffLp (N : ℕ)
    (f : lp (fun _ : InfiniteMemory Z => ℂ) 2) : lp (fun _ : InfiniteMemory Z => ℂ) 2 :=
  ∑ x ∈ infiniteMemoryCutoff N, lp.single 2 x (f x)

theorem memory_degree_cutoff_lp_apply (N : ℕ)
    (f : lp (fun _ : InfiniteMemory Z => ℂ) 2) (x : InfiniteMemory Z) :
    memoryDegreeCutoffLp N f x = if x.1 ≤ N then f x else 0 := by
  classical
  unfold memoryDegreeCutoffLp
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single,
    infinite_memory_mem_cutoff]

theorem memory_degree_cutoff_lp_tendsto (f : lp (fun _ : InfiniteMemory Z => ℂ) 2) :
    Tendsto (fun N => memoryDegreeCutoffLp N f) atTop (nhds f) :=
  (lp.hasSum_single ENNReal.ofNat_ne_top f).comp infinite_memory_cutoff_tendsto

theorem memory_degree_cutoff_lp_symmetric (N : ℕ) (f : symmetricMemoryFock Z) :
    memoryDegreeCutoffLp N f.val ∈ symmetricMemoryFock Z := by
  intro x σ
  rw [memory_degree_cutoff_lp_apply, memory_degree_cutoff_lp_apply]
  change (if x.1 ≤ N then f.val ⟨x.1, x.2 ∘ σ⟩ else 0) = _
  rw [f.property x σ]

noncomputable def memoryDegreeCutoffFock (N : ℕ) (f : symmetricMemoryFock Z) :
    symmetricMemoryFock Z :=
  ⟨memoryDegreeCutoffLp N f.val, memory_degree_cutoff_lp_symmetric N f⟩

theorem memory_degree_cutoff_fock_tendsto (f : symmetricMemoryFock Z) :
    Tendsto (fun N => memoryDegreeCutoffFock N f) atTop (nhds f) := by
  apply tendsto_subtype_rng.mpr
  exact memory_degree_cutoff_lp_tendsto f.val

noncomputable def memoryDegreeCutoffInput (w : Z → ℝ) (N : ℕ)
    (f : lp (fun _ : InfiniteMemory Z => ℂ) 2) : InfiniteMemory Z →₀ ℂ :=
  Finsupp.onFinset (infiniteMemoryCutoff N)
    (fun x => if x.1 ≤ N then unweightedMemoryCoordinates w f x else 0)
    (by
      intro x hx
      apply (infinite_memory_mem_cutoff x).mpr
      by_contra h
      exact hx (if_neg h))

theorem memory_degree_cutoff_input_apply (w : Z → ℝ) (N : ℕ)
    (f : lp (fun _ : InfiniteMemory Z => ℂ) 2) (x : InfiniteMemory Z) :
    memoryDegreeCutoffInput w N f x =
      if x.1 ≤ N then unweightedMemoryCoordinates w f x else 0 := rfl

theorem memory_degree_cutoff_input_weighted (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (N : ℕ) (f : lp (fun _ : InfiniteMemory Z => ℂ) 2) :
    weightedMemoryInputLinearMap w (memoryDegreeCutoffInput w N f) =
      memoryDegreeCutoffLp N f := by
  apply lp.ext
  funext x
  rw [weighted_memory_input_apply, memory_degree_cutoff_lp_apply]
  unfold weightedMemoryCoordinates
  rw [memory_degree_cutoff_input_apply]
  by_cases h : x.1 ≤ N
  · rw [if_pos h, if_pos h]
    exact weighted_unweighted_memory_coordinates w hw f x
  · rw [if_neg h, if_neg h, mul_zero]

theorem memory_degree_cutoff_input_symmetric (w : Z → ℝ) (N : ℕ)
    (f : symmetricMemoryFock Z) (x : InfiniteMemory Z) (σ : Equiv.Perm (Fin x.1)) :
    memoryDegreeCutoffInput w N f.val ⟨x.1, x.2 ∘ σ⟩ =
      memoryDegreeCutoffInput w N f.val x := by
  rw [memory_degree_cutoff_input_apply, memory_degree_cutoff_input_apply]
  unfold unweightedMemoryCoordinates
  rw [infinite_memory_point_mass_invariant, f.property x σ]

/-- Density specifically inside the source symmetric Fock space, with exact
original weighted finite-support inputs rather than arbitrary ambient inputs. -/
theorem symmetric_fock_weighted_finite_support_dense (w : Z → ℝ) (hw : ∀ z, 0 < w z) :
    Dense {f : symmetricMemoryFock Z | ∃ g : InfiniteMemory Z →₀ ℂ,
      (∀ (x : InfiniteMemory Z) (σ : Equiv.Perm (Fin x.1)),
        g ⟨x.1, x.2 ∘ σ⟩ = g x) ∧ weightedMemoryInputLinearMap w g = f.val} := by
  intro f
  apply mem_closure_of_tendsto (memory_degree_cutoff_fock_tendsto f)
  apply Filter.Eventually.of_forall
  intro N
  exact ⟨memoryDegreeCutoffInput w N f.val,
    memory_degree_cutoff_input_symmetric w N f, memory_degree_cutoff_input_weighted w hw N f.val⟩

end SimultaneousPrimitiveRoots.Unconditional.Graph
