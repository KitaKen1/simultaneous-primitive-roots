module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.PrimeGroupMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Explicit uniform perturbation of the source reciprocal-prime law

[S, eq:lifespan-baseline] states nu/mu = 1 + O(N/P_*). We prove the
finite quantitative bound 1 <= nu/mu <= 1 + 2*visit_count/Pmin whenever
every prime is at least Pmin >= 2*visit_count and 0<=eta<=1. Pmin is a
real lower bound, so the source P_*=exp(L^c) can be inserted directly.
The eventual choice of x and prime groups is not supplied here.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

theorem prime_lifespan_baseline_uniform_lower {I : Type*} (visits : Finset I)
    (η : I → ℝ) (hη : ∀ i ∈ visits, η i ≤ 1) (p : ℕ) (Pmin : ℝ)
    (hPmin : 0 < Pmin) (hp : Pmin ≤ (p : ℝ)) :
    1 - (visits.card : ℝ) / Pmin ≤ primeLifespanBaseline visits η p := by
  have hp0 : 0 < (p : ℝ) := hPmin.trans_le hp
  have h1 := div_le_div_of_nonneg_right (prime_visit_hit_mass_le_card visits η hη) hp0.le
  have h2 := div_le_div_of_nonneg_left (Nat.cast_nonneg visits.card : (0 : ℝ) ≤ visits.card)
    hPmin hp
  unfold primeLifespanBaseline
  linarith

theorem tilted_prime_group_law_ge {I : Type*} (s : Finset ℕ) (hne : s.Nonempty)
    (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I) (η : I → ℝ)
    (hη : ∀ i ∈ visits, 0 ≤ η i) (p : ℕ) (hps : p ∈ s)
    (hb : 0 < primeLifespanBaseline visits η p) :
    primeGroupLaw s p ≤ tiltedPrimeGroupLaw s visits η p := by
  rw [tilted_prime_group_law_eq_div]
  apply (le_div_iff₀ hb).mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (prime_lifespan_baseline_le_one visits η p hη) (prime_group_law_pos s hne hp p hps).le

theorem tilted_prime_group_law_ratio {I : Type*} (s : Finset ℕ) (hne : s.Nonempty)
    (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I) (η : I → ℝ)
    (p : ℕ) (hps : p ∈ s) (hb : 0 < primeLifespanBaseline visits η p) :
    tiltedPrimeGroupLaw s visits η p / primeGroupLaw s p =
      1 / primeLifespanBaseline visits η p := by
  rw [tilted_prime_group_law_eq_div]
  field_simp [(prime_group_law_pos s hne hp p hps).ne', hb.ne']

theorem inverse_baseline_perturbation_le (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    1 / (1 - δ) ≤ 1 + 2 * δ := by
  apply (div_le_iff₀ (by linarith : 0 < 1 - δ)).mpr
  nlinarith

theorem tilted_prime_group_law_ratio_bounds {I : Type*} (s : Finset ℕ)
    (hne : s.Nonempty) (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I) (η : I → ℝ)
    (hη0 : ∀ i ∈ visits, 0 ≤ η i) (hη1 : ∀ i ∈ visits, η i ≤ 1)
    (p : ℕ) (hps : p ∈ s) (Pmin : ℝ) (hPmin : 0 < Pmin)
    (hsmall : 2 * (visits.card : ℝ) ≤ Pmin) (hplower : Pmin ≤ (p : ℝ)) :
    1 ≤ tiltedPrimeGroupLaw s visits η p / primeGroupLaw s p ∧
      tiltedPrimeGroupLaw s visits η p / primeGroupLaw s p ≤
        1 + 2 * (visits.card : ℝ) / Pmin := by
  let δ := (visits.card : ℝ) / Pmin
  have hδ0 : 0 ≤ δ := div_nonneg (Nat.cast_nonneg _) hPmin.le
  have hδ : δ ≤ 1 / 2 := (div_le_iff₀ hPmin).mpr (by linarith)
  have hb0 := prime_lifespan_baseline_uniform_lower visits η hη1 p Pmin hPmin hplower
  have hb : 0 < primeLifespanBaseline visits η p := by change 1 - δ ≤ _ at hb0; linarith
  rw [tilted_prime_group_law_ratio s hne hp visits η p hps hb]
  constructor
  · apply (le_div_iff₀ hb).mpr
    simpa only [one_mul] using prime_lifespan_baseline_le_one visits η p hη0
  · calc
      _ ≤ 1 / (1 - δ) := one_div_le_one_div_of_le (by linarith) hb0
      _ ≤ 1 + 2 * δ := inverse_baseline_perturbation_le δ hδ0 hδ
      _ = _ := by simp only [δ, mul_div_assoc]

end SimultaneousPrimitiveRoots.Unconditional.Graph
