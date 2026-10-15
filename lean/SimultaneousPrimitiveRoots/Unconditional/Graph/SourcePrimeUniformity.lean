module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourcePrimeGrowth
public import SimultaneousPrimitiveRoots.Unconditional.Graph.PrimeGroupPerturbation
public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourceGhostCoefficients

/-!
# Uniform source lifespan perturbations with the original growing length

The onset in L precedes every finite prime group, visit subset and choice of
coefficients in [0,1]. The actual source coefficients eta_i=1-q_i are included.
Prime groups are assumed to meet the source ranges; their existence and the
full conditional history kernel are separate obligations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open Filter

theorem source_visit_coefficients_range {I : Type*} (q : ℝ) (qi : I → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hqi : ∀ i, qi i = q ∨ qi i = Real.sqrt q) :
    ∀ i, 0 ≤ 1 - qi i ∧ 1 - qi i ≤ 1 := by
  intro i
  obtain ⟨h0, h1, _⟩ := source_ghost_visit_range q (qi i) hq0 hq1 (hqi i)
  constructor <;> linarith

theorem source_visits_size_from_prime_lower_bound {I : Type*} (L c : ℝ)
    (visits : Finset I) (hcard : visits.card ≤ sourceMemoryLength L + 1)
    (hsize : 2 * ((sourceMemoryLength L : ℝ) + 1) ≤ sourcePrimeLowerBound c L)
    (p : ℕ) (hp : sourcePrimeLowerBound c L ≤ (p : ℝ)) :
    2 * visits.card ≤ p := by
  have hc : (visits.card : ℝ) ≤ (sourceMemoryLength L : ℝ) + 1 := by exact_mod_cast hcard
  have hr : 2 * (visits.card : ℝ) ≤ (p : ℝ) := by linarith
  exact_mod_cast hr

theorem source_visit_ratio_le {I : Type*} (L c : ℝ) (visits : Finset I)
    (hcard : visits.card ≤ sourceMemoryLength L + 1) :
    2 * (visits.card : ℝ) / sourcePrimeLowerBound c L ≤
      2 * ((sourceMemoryLength L : ℝ) + 1) / sourcePrimeLowerBound c L := by
  apply div_le_div_of_nonneg_right _ (source_prime_lower_bound_pos c L).le
  have hc : (visits.card : ℝ) ≤ (sourceMemoryLength L : ℝ) + 1 := by exact_mod_cast hcard
  linarith

theorem eventually_source_prime_group_law_uniform (c ε : ℝ)
    (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Type*) (s : Finset ℕ), s.Nonempty →
      (∀ p ∈ s, Nat.Prime p) → ∀ (visits : Finset I) (η : I → ℝ),
      visits.card ≤ sourceMemoryLength L + 1 →
      (∀ i ∈ visits, 0 ≤ η i) → (∀ i ∈ visits, η i ≤ 1) →
      ∀ p ∈ s, sourcePrimeLowerBound c L ≤ (p : ℝ) →
      0 < primeLifespanBaseline visits η p ∧
      1 ≤ tiltedPrimeGroupLaw s visits η p / primeGroupLaw s p ∧
      tiltedPrimeGroupLaw s visits η p / primeGroupLaw s p ≤ 1 + ε := by
  filter_upwards [source_prime_eventually_dominates_visits c hc,
    source_visit_ratio_eventually_small c ε hc hε] with L hsize hratio
  intro I s hne hp visits η hcard hη0 hη1 p hps hplower
  have hnat := source_visits_size_from_prime_lower_bound L c visits hcard hsize p hplower
  have hsmall : 2 * (visits.card : ℝ) ≤ sourcePrimeLowerBound c L := by
    have hc : (visits.card : ℝ) ≤ (sourceMemoryLength L : ℝ) + 1 := by exact_mod_cast hcard
    linarith
  have hb := prime_lifespan_baseline_half visits η hη1 p (hp p hps).pos hnat
  have hbounds := tilted_prime_group_law_ratio_bounds s hne hp visits η hη0 hη1 p hps
    (sourcePrimeLowerBound c L) (source_prime_lower_bound_pos c L) hsmall hplower
  refine ⟨by linarith, hbounds.1, hbounds.2.trans ?_⟩
  have hratio' := (source_visit_ratio_le L c visits hcard).trans hratio.le
  linarith

theorem eventually_source_log_prime_group_law_uniform (c ε : ℝ)
    (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : Type*) (s : Finset ℕ), s.Nonempty →
      (∀ p ∈ s, Nat.Prime p) → ∀ (visits : Finset I) (η : I → ℝ),
      visits.card ≤ sourceMemoryLength (Real.log x) + 1 →
      (∀ i ∈ visits, 0 ≤ η i) → (∀ i ∈ visits, η i ≤ 1) →
      ∀ p ∈ s, sourcePrimeLowerBound c (Real.log x) ≤ (p : ℝ) →
      0 < primeLifespanBaseline visits η p ∧
      1 ≤ tiltedPrimeGroupLaw s visits η p / primeGroupLaw s p ∧
      tiltedPrimeGroupLaw s visits η p / primeGroupLaw s p ≤ 1 + ε :=
  Real.tendsto_log_atTop.eventually (eventually_source_prime_group_law_uniform c ε hc hε)

theorem eventually_source_actual_visit_law_uniform (c q ε : ℝ)
    (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (s : Finset ℕ), s.Nonempty →
      (∀ p ∈ s, Nat.Prime p) →
      ∀ (visits : Finset (Fin (sourceMemoryLength L + 1)))
        (qi : Fin (sourceMemoryLength L + 1) → ℝ),
      (∀ i, qi i = q ∨ qi i = Real.sqrt q) →
      ∀ p ∈ s, sourcePrimeLowerBound c L ≤ (p : ℝ) →
      0 < primeLifespanBaseline visits (fun i => 1 - qi i) p ∧
      1 ≤ tiltedPrimeGroupLaw s visits (fun i => 1 - qi i) p / primeGroupLaw s p ∧
      tiltedPrimeGroupLaw s visits (fun i => 1 - qi i) p / primeGroupLaw s p ≤ 1 + ε := by
  filter_upwards [eventually_source_prime_group_law_uniform c ε hc hε] with L hL
  intro s hne hp visits qi hqi p hps hplower
  have hη := source_visit_coefficients_range q qi hq0 hq1 hqi
  apply hL (Fin (sourceMemoryLength L + 1)) s hne hp visits (fun i => 1 - qi i)
    (by simpa using Finset.card_le_univ visits)
    (fun i _ => (hη i).1) (fun i _ => (hη i).2) p hps hplower

theorem eventually_source_lifespan_relative_error (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Type*) (s : Finset ℕ), s.Nonempty →
      (∀ p ∈ s, Nat.Prime p) → ∀ (visits : Finset I) (η : I → ℝ),
      visits.card ≤ sourceMemoryLength L + 1 →
      (∀ i ∈ visits, 0 ≤ η i) → (∀ i ∈ visits, η i ≤ 1) →
      ∀ p ∈ s, sourcePrimeLowerBound c L ≤ (p : ℝ) →
      |tiltedPrimeGroupLaw s visits η p / primeGroupLaw s p - 1| ≤
        4 * (sourceMemoryLength L : ℝ) / sourcePrimeLowerBound c L := by
  filter_upwards [source_prime_eventually_dominates_visits c hc,
    eventually_gt_atTop (0 : ℝ)] with L hsize hL
  intro I s hne hp visits η hcard hη0 hη1 p hps hplower
  have hN : (1 : ℝ) ≤ sourceMemoryLength L := by
    exact_mod_cast source_memory_length_pos L hL
  have hcard' : (visits.card : ℝ) ≤ (sourceMemoryLength L : ℝ) + 1 := by
    exact_mod_cast hcard
  have hsmall : 2 * (visits.card : ℝ) ≤ sourcePrimeLowerBound c L := by linarith
  have hbounds := tilted_prime_group_law_ratio_bounds s hne hp visits η hη0 hη1 p hps
    (sourcePrimeLowerBound c L) (source_prime_lower_bound_pos c L) hsmall hplower
  rw [abs_of_nonneg (by linarith [hbounds.1])]
  have hratio : 2 * (visits.card : ℝ) / sourcePrimeLowerBound c L ≤
      4 * (sourceMemoryLength L : ℝ) / sourcePrimeLowerBound c L :=
    div_le_div_of_nonneg_right (by linarith) (source_prime_lower_bound_pos c L).le
  linarith [hbounds.2]

end SimultaneousPrimitiveRoots.Unconditional.Graph
