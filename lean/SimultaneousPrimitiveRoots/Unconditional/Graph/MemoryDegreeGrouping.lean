module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.InfiniteMemory
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Grouping an absolutely convergent memory-pair/survivor sum by degrees

The explicit bijection retains every indexed particle tuple, even when values
repeat. Absolute convergence permits grouping by (old degree,new degree,k).
Finite tuple sums in each degree block are therefore legitimate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {Z : Type*}

def memoryPairSurvivorDegreeEquiv (Z : Type*) :
    ((InfiniteMemory Z × InfiniteMemory Z) × ℕ) ≃
      (Σ d : ℕ × ℕ × ℕ, (Fin d.1 → Z) × (Fin d.2.1 → Z)) where
  toFun z := ⟨(z.1.1.1, z.1.2.1, z.2), (z.1.1.2, z.1.2.2)⟩
  invFun z := ((⟨z.1.1, z.2.1⟩, ⟨z.1.2.1, z.2.2⟩), z.1.2.2)
  left_inv z := by rcases z with ⟨⟨⟨n, x⟩, ⟨m, y⟩⟩, k⟩; rfl
  right_inv z := by rcases z with ⟨⟨n, m, k⟩, ⟨x, y⟩⟩; rfl

theorem memory_pair_survivor_degree_equiv_symm (d : ℕ × ℕ × ℕ)
    (x : Fin d.1 → Z) (y : Fin d.2.1 → Z) :
    (memoryPairSurvivorDegreeEquiv Z).symm ⟨d, (x, y)⟩ =
      ((⟨d.1, x⟩, ⟨d.2.1, y⟩), d.2.2) := rfl

noncomputable def memoryDegreeSurvivorSum [Fintype Z]
    (F : (InfiniteMemory Z × InfiniteMemory Z) × ℕ → ℂ) (d : ℕ × ℕ × ℕ) : ℂ :=
  ∑ x : Fin d.1 → Z, ∑ y : Fin d.2.1 → Z, F ((⟨d.1, x⟩, ⟨d.2.1, y⟩), d.2.2)

theorem memory_degree_survivor_norm_total [Fintype Z]
    (F : (InfiniteMemory Z × InfiniteMemory Z) × ℕ → ℂ) (d : ℕ × ℕ × ℕ) :
    (∑' xy : (Fin d.1 → Z) × (Fin d.2.1 → Z),
      ‖F ((⟨d.1, xy.1⟩, ⟨d.2.1, xy.2⟩), d.2.2)‖) =
    ∑ x : Fin d.1 → Z, ∑ y : Fin d.2.1 → Z,
      ‖F ((⟨d.1, x⟩, ⟨d.2.1, y⟩), d.2.2)‖ := by
  classical
  rw [Summable.tsum_prod (Summable.of_finite (f := fun xy :
    (Fin d.1 → Z) × (Fin d.2.1 → Z) =>
      ‖F ((⟨d.1, xy.1⟩, ⟨d.2.1, xy.2⟩), d.2.2)‖))]
  simp only [tsum_fintype]

theorem memory_degree_survivor_norm_le [Fintype Z]
    (F : (InfiniteMemory Z × InfiniteMemory Z) × ℕ → ℂ) (d : ℕ × ℕ × ℕ) :
    ‖memoryDegreeSurvivorSum F d‖ ≤
    ∑ x : Fin d.1 → Z, ∑ y : Fin d.2.1 → Z,
      ‖F ((⟨d.1, x⟩, ⟨d.2.1, y⟩), d.2.2)‖ := by
  classical
  unfold memoryDegreeSurvivorSum
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _ => norm_sum_le _ _))

theorem memory_degree_survivor_absolute_blocks_summable [Fintype Z]
    (F : (InfiniteMemory Z × InfiniteMemory Z) × ℕ → ℂ)
    (hF : Summable (fun z => ‖F z‖)) :
    Summable (fun d : ℕ × ℕ × ℕ => ∑ x : Fin d.1 → Z, ∑ y : Fin d.2.1 → Z,
      ‖F ((⟨d.1, x⟩, ⟨d.2.1, y⟩), d.2.2)‖) := by
  have hs := (memoryPairSurvivorDegreeEquiv Z).symm.summable_iff.mpr hF
  have hb := hs.sigma
  change Summable (fun d : ℕ × ℕ × ℕ => ∑' xy : (Fin d.1 → Z) × (Fin d.2.1 → Z),
    ‖F ((⟨d.1, xy.1⟩, ⟨d.2.1, xy.2⟩), d.2.2)‖) at hb
  simpa only [memory_degree_survivor_norm_total] using hb

theorem memory_degree_survivor_sum_norm_summable [Fintype Z]
    (F : (InfiniteMemory Z × InfiniteMemory Z) × ℕ → ℂ)
    (hF : Summable (fun z => ‖F z‖)) :
    Summable (fun d => ‖memoryDegreeSurvivorSum F d‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (memory_degree_survivor_norm_le F) (memory_degree_survivor_absolute_blocks_summable F hF)

theorem memory_degree_survivor_sum_tsum [Fintype Z]
    (F : (InfiniteMemory Z × InfiniteMemory Z) × ℕ → ℂ)
    (hF : Summable (fun z => ‖F z‖)) :
    (∑' d, memoryDegreeSurvivorSum F d) = ∑' z, F z := by
  have hs := (memoryPairSurvivorDegreeEquiv Z).symm.summable_iff.mpr hF.of_norm
  calc
    _ = ∑' d : ℕ × ℕ × ℕ, ∑' xy : (Fin d.1 → Z) × (Fin d.2.1 → Z),
        F ((⟨d.1, xy.1⟩, ⟨d.2.1, xy.2⟩), d.2.2) := by
      apply tsum_congr
      intro d
      rw [Summable.tsum_prod (Summable.of_finite (f := fun xy :
        (Fin d.1 → Z) × (Fin d.2.1 → Z) =>
          F ((⟨d.1, xy.1⟩, ⟨d.2.1, xy.2⟩), d.2.2)))]
      simp only [memoryDegreeSurvivorSum, tsum_fintype]
    _ = ∑' a, F ((memoryPairSurvivorDegreeEquiv Z).symm a) := hs.tsum_sigma.symm
    _ = _ := (memoryPairSurvivorDegreeEquiv Z).symm.tsum_eq F

end SimultaneousPrimitiveRoots.Unconditional.Graph
