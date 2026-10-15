module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual reciprocal-prime laws and lifespan-tilted masses

[S, eq:prime-group-ranges, eq:lifespan-baseline] uses V = sum 1/p,
mu(p) = 1/(V*p), b(p) = 1 - sum eta/p, and nu(p) = 1/(V*p*b(p)).
We retain those formulas and prove positivity, normalization, and the total
tilted-mass bound under explicit finite visit and prime-size hypotheses.
The eventual choice of prime groups and the remaining arithmetic coefficient
bounds are separate obligations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

noncomputable def primeGroupReciprocalMass (s : Finset ℕ) : ℝ :=
  ∑ p ∈ s, 1 / (p : ℝ)

noncomputable def primeGroupLaw (s : Finset ℕ) (p : ℕ) : ℝ :=
  1 / (primeGroupReciprocalMass s * (p : ℝ))

noncomputable def primeLifespanBaseline {I : Type*} (visits : Finset I)
    (η : I → ℝ) (p : ℕ) : ℝ := 1 - (∑ i ∈ visits, η i) / (p : ℝ)

noncomputable def tiltedPrimeGroupLaw {I : Type*} (s : Finset ℕ)
    (visits : Finset I) (η : I → ℝ) (p : ℕ) : ℝ :=
  1 / (primeGroupReciprocalMass s * (p : ℝ) * primeLifespanBaseline visits η p)

theorem prime_group_reciprocal_mass_pos (s : Finset ℕ) (hne : s.Nonempty)
    (hp : ∀ p ∈ s, Nat.Prime p) : 0 < primeGroupReciprocalMass s := by
  apply Finset.sum_pos
  · intro p hps
    exact one_div_pos.mpr (by exact_mod_cast (hp p hps).pos)
  · exact hne

theorem prime_group_law_pos (s : Finset ℕ) (hne : s.Nonempty)
    (hp : ∀ p ∈ s, Nat.Prime p) (p : ℕ) (hps : p ∈ s) :
    0 < primeGroupLaw s p :=
  one_div_pos.mpr (mul_pos (prime_group_reciprocal_mass_pos s hne hp)
    (by exact_mod_cast (hp p hps).pos))

theorem prime_group_law_sum (s : Finset ℕ) (hne : s.Nonempty)
    (hp : ∀ p ∈ s, Nat.Prime p) : (∑ p ∈ s, primeGroupLaw s p) = 1 := by
  have hV := (prime_group_reciprocal_mass_pos s hne hp).ne'
  unfold primeGroupLaw
  simp_rw [← one_div_mul_one_div]
  rw [← Finset.mul_sum]
  change 1 / primeGroupReciprocalMass s * primeGroupReciprocalMass s = 1
  exact one_div_mul_cancel hV

theorem prime_lifespan_baseline_lower {I : Type*} (visits : Finset I) (η : I → ℝ)
    (p : ℕ) (hp : 0 < p) (δ : ℝ) (hη : ∑ i ∈ visits, η i ≤ δ * (p : ℝ)) :
    1 - δ ≤ primeLifespanBaseline visits η p := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have h := (div_le_iff₀ hpR).mpr hη
  unfold primeLifespanBaseline
  linarith

theorem prime_lifespan_baseline_pos {I : Type*} (visits : Finset I) (η : I → ℝ)
    (p : ℕ) (hp : 0 < p) (δ : ℝ) (hδ : δ < 1)
    (hη : ∑ i ∈ visits, η i ≤ δ * (p : ℝ)) :
    0 < primeLifespanBaseline visits η p := by
  have h := prime_lifespan_baseline_lower visits η p hp δ hη
  linarith

theorem prime_lifespan_baseline_le_one {I : Type*} (visits : Finset I) (η : I → ℝ)
    (p : ℕ) (hη : ∀ i ∈ visits, 0 ≤ η i) :
    primeLifespanBaseline visits η p ≤ 1 := by
  have h := div_nonneg (Finset.sum_nonneg hη) (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  unfold primeLifespanBaseline
  linarith

/-- Exact comparison with the original law; no asymptotic error is assumed. -/
theorem tilted_prime_group_law_eq_div {I : Type*} (s : Finset ℕ)
    (visits : Finset I) (η : I → ℝ) (p : ℕ) :
    tiltedPrimeGroupLaw s visits η p = primeGroupLaw s p /
      primeLifespanBaseline visits η p := by
  unfold tiltedPrimeGroupLaw primeGroupLaw
  rw [div_div]

theorem tilted_prime_group_law_pos {I : Type*} (s : Finset ℕ) (hne : s.Nonempty)
    (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I) (η : I → ℝ)
    (p : ℕ) (hps : p ∈ s) (hb : 0 < primeLifespanBaseline visits η p) :
    0 < tiltedPrimeGroupLaw s visits η p := by
  rw [tilted_prime_group_law_eq_div]
  exact div_pos (prime_group_law_pos s hne hp p hps) hb

theorem tilted_prime_group_law_le {I : Type*} (s : Finset ℕ) (hne : s.Nonempty)
    (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I) (η : I → ℝ)
    (p : ℕ) (hps : p ∈ s) (δ : ℝ) (hδ : δ < 1)
    (hb : 1 - δ ≤ primeLifespanBaseline visits η p) :
    tiltedPrimeGroupLaw s visits η p ≤ primeGroupLaw s p / (1 - δ) := by
  rw [tilted_prime_group_law_eq_div]
  exact div_le_div_of_nonneg_left (prime_group_law_pos s hne hp p hps).le
    (by linarith) hb

theorem tilted_prime_group_law_total_le {I : Type*} (s : Finset ℕ)
    (hne : s.Nonempty) (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I)
    (η : I → ℝ) (δ : ℝ) (hδ : δ < 1)
    (hb : ∀ p ∈ s, 1 - δ ≤ primeLifespanBaseline visits η p) :
    (∑ p ∈ s, tiltedPrimeGroupLaw s visits η p) ≤ 1 / (1 - δ) := by
  calc
    _ ≤ ∑ p ∈ s, primeGroupLaw s p / (1 - δ) :=
      Finset.sum_le_sum (fun p hps => tilted_prime_group_law_le
        s hne hp visits η p hps δ hδ (hb p hps))
    _ = _ := by rw [← Finset.sum_div, prime_group_law_sum s hne hp]

theorem prime_visit_hit_mass_le_card {I : Type*} (visits : Finset I) (η : I → ℝ)
    (hη : ∀ i ∈ visits, η i ≤ 1) : (∑ i ∈ visits, η i) ≤ (visits.card : ℝ) := by
  calc
    _ ≤ ∑ _i ∈ visits, (1 : ℝ) := Finset.sum_le_sum hη
    _ = _ := by simp

/-- Finite visit count supplies a concrete lower bound, including visits 0,...,N. -/
theorem prime_lifespan_baseline_half {I : Type*} (visits : Finset I) (η : I → ℝ)
    (hη : ∀ i ∈ visits, η i ≤ 1) (p : ℕ) (hp : 0 < p)
    (hsize : 2 * visits.card ≤ p) : 1 / 2 ≤ primeLifespanBaseline visits η p := by
  have hc : 2 * (visits.card : ℝ) ≤ (p : ℝ) := by exact_mod_cast hsize
  have hs := prime_visit_hit_mass_le_card visits η hη
  have h := prime_lifespan_baseline_lower visits η p hp (1 / 2) (by linarith)
  norm_num at h ⊢
  exact h

theorem tilted_prime_group_law_total_le_two {I : Type*} (s : Finset ℕ)
    (hne : s.Nonempty) (hp : ∀ p ∈ s, Nat.Prime p) (visits : Finset I)
    (η : I → ℝ) (hη : ∀ i ∈ visits, η i ≤ 1)
    (hsize : ∀ p ∈ s, 2 * visits.card ≤ p) :
    (∑ p ∈ s, tiltedPrimeGroupLaw s visits η p) ≤ 2 := by
  have h := tilted_prime_group_law_total_le s hne hp visits η (1 / 2) (by norm_num)
    (fun p hps => by
      norm_num
      exact prime_lifespan_baseline_half visits η hη p (hp p hps).pos (hsize p hps))
  norm_num at h
  exact h

end SimultaneousPrimitiveRoots.Unconditional.Graph
