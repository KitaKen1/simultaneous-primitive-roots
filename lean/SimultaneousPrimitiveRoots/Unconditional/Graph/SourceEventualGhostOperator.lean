module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourcePrimeUniformity
public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourcePrimeGroupOperator

/-!
# One completed source ghost bound before all sufficiently large lengths

The common auxiliary weight precedes L, prime groups, growing visit types,
visit subsets and q/sqrt(q) choices. Original reciprocal-prime masses and
coefficients are used. This supplies the pure-ghost part of the source ideal
operator bound, without identifying the full conditional or marked kernels.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open Filter

theorem exists_eventual_source_prime_group_continuous_operators
    (R : ℕ → Type*) [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (c q ρ Vplus : ℝ) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1) (hρ : 0 < ρ)
    (hgap : Real.sqrt q < ρ ^ 2) :
    ∃ v : ℝ, 1 < v ∧ ∀ᶠ L : ℝ in atTop, ∀ (I : Type*) (s : Finset ℕ),
      s.Nonempty → (∀ p ∈ s, Nat.Prime p) → ∀ (visits : Finset I) (η : I → ℝ),
      visits.card ≤ sourceMemoryLength L + 1 → (∀ i ∈ visits, η i ≤ 1) →
      (∀ p ∈ s, sourcePrimeLowerBound c L ≤ (p : ℝ)) →
      primeGroupReciprocalMass s ≤ Vplus → ∀ (qi γ : ℝ),
      (qi = q ∨ qi = Real.sqrt q) → 0 ≤ γ → γ ≤ 2 →
      ∃ T : lp (fun _ : InfiniteMemory (Σ p : s, R p.val) => ℂ) 2 →L[ℂ]
        lp (fun _ : InfiniteMemory (Σ p : s, R p.val) => ℂ) 2,
        ‖T‖ ≤ Real.sqrt (Real.exp ((2 * max 1 Vplus / ρ) * v * 2) *
          Real.exp ((1 / ρ) * v * 2)) ∧
        (∀ x y, T (lpCoordinateVector y) x =
          normalizedInfiniteGhostKernel (fun p : s => tiltedPrimeGroupLaw s visits η p.val)
            (sourceGhostA qi ρ) (sourceGhostD qi ρ)
            (γ * sourceGhostC (primeGroupReciprocalMass s) qi ρ) x y) ∧
        (∀ f (x : InfiniteMemory (Σ p : s, R p.val)) (σ : Equiv.Perm (Fin x.1)),
          T f ⟨x.1, x.2 ∘ σ⟩ = T f x) := by
  obtain ⟨v, hv, hcoef⟩ := exists_source_ghost_uniform_weight q ρ Vplus hq0 hq1 hρ hgap
  refine ⟨v, hv, ?_⟩
  filter_upwards [source_prime_eventually_dominates_visits c hc] with L hsize
  intro I s hne hp visits η hcard hη hplower hV qi γ hqi hγ0 hγ
  have hnat : ∀ p ∈ s, 2 * visits.card ≤ p := fun p hps =>
    source_visits_size_from_prime_lower_bound L c visits hcard hsize p (hplower p hps)
  have hV0 : 0 ≤ primeGroupReciprocalMass s :=
    (prime_group_reciprocal_mass_pos s hne hp).le
  obtain ⟨hA, hbaseD, hbaseC, hD, hC⟩ :=
    hcoef qi (primeGroupReciprocalMass s) γ hqi hV0 hV hγ0 hγ
  let ν : s → ℝ := fun p => tiltedPrimeGroupLaw s visits η p.val
  have hν : ∀ p, 0 < ν p := tilted_prime_group_subtype_pos s hne hp visits η hη hnat
  have hM : ∑ p, ν p ≤ 2 := tilted_prime_group_subtype_total_le_two s hne hp visits η hη hnat
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  let T := infiniteGhostContinuousOperator (R := fun p : s => R p.val) ν
    (sourceGhostA qi ρ) (sourceGhostD qi ρ)
    (γ * sourceGhostC (primeGroupReciprocalMass s) qi ρ)
    v (2 * max 1 Vplus / ρ) (1 / ρ) 2 hν hA hv0 hbaseD.le hbaseC.le hC hD hM
  refine ⟨T, ?_, ?_, ?_⟩
  · exact infinite_ghost_continuous_operator_opnorm_bound ν _ _ _
      v (2 * max 1 Vplus / ρ) (1 / ρ) 2 hν hA hv0 hbaseD.le hbaseC.le hC hD hM
  · intro x y
    exact infinite_ghost_continuous_operator_matrix ν _ _ _
      v (2 * max 1 Vplus / ρ) (1 / ρ) 2 hν hA hv0 hbaseD.le hbaseC.le hC hD hM x y
  · intro f x σ
    exact infinite_ghost_continuous_operator_symmetric ν _ _ _
      v (2 * max 1 Vplus / ρ) (1 / ρ) 2 hν hA hv0 hbaseD.le hbaseC.le hC hD hM f x σ

end SimultaneousPrimitiveRoots.Unconditional.Graph
