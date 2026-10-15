module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.PrimeGroupMass
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostInfiniteSupportNorm

/-!
# Actual lifespan-tilted prime groups in the ghost square bound

The source prime law 1/(V*p*b(p)) discharges the strict positive prime
mass and total-mass hypotheses with Mmax = 2. The coefficient hypotheses
and the explicit prime-size condition remain visible. In particular, this
does not supply eventual prime groups or the complete transference norm.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

theorem tilted_prime_group_subtype_pos {I : Type*} (s : Finset ℕ) (hne : s.Nonempty)
    (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I) (η : I → ℝ)
    (hη : ∀ i ∈ visits, η i ≤ 1) (hsize : ∀ p ∈ s, 2 * visits.card ≤ p) :
    ∀ p : s, 0 < tiltedPrimeGroupLaw s visits η p.val := by
  intro p
  have hb := prime_lifespan_baseline_half visits η hη p.val
    (hp p.val p.property).pos (hsize p.val p.property)
  exact tilted_prime_group_law_pos s hne hp visits η p.val p.property (by linarith)

theorem tilted_prime_group_subtype_total_le_two {I : Type*} (s : Finset ℕ)
    (hne : s.Nonempty) (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I) (η : I → ℝ)
    (hη : ∀ i ∈ visits, η i ≤ 1) (hsize : ∀ p ∈ s, 2 * visits.card ≤ p) :
    (∑ p : s, tiltedPrimeGroupLaw s visits η p.val) ≤ 2 := by
  rw [Finset.sum_coe_sort]
  exact tilted_prime_group_law_total_le_two s hne hp visits η hη hsize

theorem tilted_prime_group_ghost_finite_cutoff_sq_bound {I : Type*} (s : Finset ℕ)
    (hne : s.Nonempty) (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I) (η : I → ℝ)
    (hη : ∀ i ∈ visits, η i ≤ 1) (hsize : ∀ p ∈ s, 2 * visits.card ≤ p)
    (R : s → Type*) [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (A D C v cmax dmax : ℝ) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (N : ℕ)
    (g : FiniteMemory N (Σ p, R p) → ℂ)
    (hg : ∀ (n : Fin (N + 1)) (σ : Equiv.Perm (Fin n.val)) y,
      g ⟨n, y ∘ σ⟩ = g ⟨n, y⟩) :
    (∑ x : FiniteMemory N (Σ p, R p),
      finiteMemoryPointMass (fun z : Σ p, R p => tiltedPrimeGroupLaw s visits η z.1.val) x *
        ‖finiteGhostTruncatedRow (fun p : s => (tiltedPrimeGroupLaw s visits η p.val : ℂ))
          (A : ℂ) (D : ℂ) (C : ℂ) N g x‖ ^ 2) ≤
    Real.exp (cmax * v * 2) * Real.exp (dmax * v * 2) *
      ∑ y : FiniteMemory N (Σ p, R p),
        finiteMemoryPointMass (fun z : Σ p, R p => tiltedPrimeGroupLaw s visits η z.1.val) y *
          ‖g y‖ ^ 2 :=
  finite_ghost_truncated_actual_complex_sq_bound _ A D C v cmax dmax 2
    (tilted_prime_group_subtype_pos s hne hp visits η hη hsize) hA hv hbaseD hbaseC hC hD
    (tilted_prime_group_subtype_total_le_two s hne hp visits η hη hsize) N g hg

theorem tilted_prime_group_ghost_infinite_support_tsum_sq_bound {I : Type*} (s : Finset ℕ)
    (hne : s.Nonempty) (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I) (η : I → ℝ)
    (hη : ∀ i ∈ visits, η i ≤ 1) (hsize : ∀ p ∈ s, 2 * visits.card ≤ p)
    (R : s → Type*) [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (A D C v cmax dmax : ℝ) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (g : InfiniteMemory (Σ p, R p) →₀ ℂ) :
    (∑' x : InfiniteMemory (Σ p, R p),
      infiniteMemoryPointMass (fun z : Σ p, R p => tiltedPrimeGroupLaw s visits η z.1.val) x *
        ‖infiniteGhostFiniteSupportAction (fun p : s => tiltedPrimeGroupLaw s visits η p.val)
          A D C g x‖ ^ 2) ≤
    Real.exp (cmax * v * 2) * Real.exp (dmax * v * 2) *
      ∑ y ∈ g.support,
        infiniteMemoryPointMass (fun z : Σ p, R p => tiltedPrimeGroupLaw s visits η z.1.val) y *
          ‖g y‖ ^ 2 :=
  infinite_ghost_finite_support_tsum_sq_bound _ A D C v cmax dmax 2
    (tilted_prime_group_subtype_pos s hne hp visits η hη hsize) hA hv hbaseD hbaseC hC hD
    (tilted_prime_group_subtype_total_le_two s hne hp visits η hη hsize) g

end SimultaneousPrimitiveRoots.Unconditional.Graph
