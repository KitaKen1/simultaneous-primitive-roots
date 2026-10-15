module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.KernelCosts
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealSanity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The sizes of the big primes and of the selected products

Source: `verification/stage7-sources/S-03.tex` (`[S-03:…]`).

Elementary facts used throughout the proof of [S] Lemma 4.3:

* `tupleWeight_pos`, `sum_tupleWeight` — the law of a label tuple is a positive probability
  measure.
* `tupleProd_pos`, `label_dvd_tupleProd`, `label_le_tupleProd` — a selected product is positive
  and at least each of its labels.
* `scaleLowerBound : ScaleLowerBound` — "the two scales exceed every fixed power of `L`"
  [S-03:0327]: every big prime is at least `exp(L^c)`, which exceeds `L^E` for large `x`.
* `log_tupleProd_le_const` — "each selected product lies between `exp(L^c)` and
  `exp(m C₀ T L^d)`" [S-03:0296–0297]: the upper bound.
* `mul_log_add_one_le` — `c log L + 1 ≤ L` for `L ≥ (2c + 1)²`, the elementary inequality behind
  "at most `L^{d+1}` dyads" [S-03:0298], "`log(2r) ≤ L^{d+1}`" [S-03:0328] and
  "`N_A, N_B ≤ L^{d+1+h_*}`" [S-03:0429].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

theorem c_pos (P : GroupParams) : 0 < P.c := by
  linarith [P.a_pos, P.a_lt_b, P.b_lt_c]

/-! ### An elementary inequality -/

/-- `c log L + 1 ≤ L` for `L ≥ (2c + 1)²`, `c ≥ 0`. -/
theorem mul_log_add_one_le {c L : ℝ} (hc : 0 ≤ c) (hL : (2 * c + 1) ^ 2 ≤ L) :
    c * Real.log L + 1 ≤ L := by
  have hL1 : 1 ≤ L := by nlinarith [mul_nonneg hc hc]
  have hL0 : 0 < L := by linarith
  obtain ⟨s, hs0, hs2⟩ : ∃ s : ℝ, 0 ≤ s ∧ s * s = L :=
    ⟨Real.sqrt L, Real.sqrt_nonneg L, Real.mul_self_sqrt hL0.le⟩
  have hsc : 2 * c + 1 ≤ s := by
    by_contra hlt
    have hlt' : s < 2 * c + 1 := not_le.mp hlt
    have h5 : s * s < (2 * c + 1) * (2 * c + 1) := mul_self_lt_mul_self hs0 hlt'
    nlinarith
  have hs1 : 1 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hlog : Real.log L ≤ 2 * (s - 1) := by
    have h6 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
    have h7 : Real.log L = 2 * Real.log s := by
      rw [← hs2, Real.log_mul hspos.ne' hspos.ne']
      ring
    linarith
  have h8 : c * Real.log L ≤ c * (2 * (s - 1)) := mul_le_mul_of_nonneg_left hlog hc
  have h9 : (2 * c + 1) * s ≤ s * s := mul_le_mul_of_nonneg_right hsc hs0
  nlinarith

/-- `L^E ≤ exp(L^c)` for all large `L`. -/
theorem exists_rpow_le_sourcePrimeLowerBound (c : ℝ) (hc : 0 < c) (E : ℝ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → L ^ E ≤ Graph.sourcePrimeLowerBound c L := by
  have h1 : ∀ᶠ L : ℝ in Filter.atTop, L ^ E / Graph.sourcePrimeLowerBound c L < 1 :=
    (Graph.source_rpow_div_prime_lower_bound_tendsto E c hc).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp h1
  refine ⟨max L₀ 1, le_max_right _ _, fun L hL => ?_⟩
  have h2 := hL₀ L ((le_max_left _ _).trans hL)
  exact ((div_lt_one (Graph.source_prime_lower_bound_pos c L)).mp h2).le

/-! ### Weights and products of label tuples -/

section Tuples

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] {J : ℕ}

omit [DecidableEq B] in
/-- The law of a label tuple is positive. -/
theorem tupleWeight_pos (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J))
    (t : AuxList 𝔊.big Λ) : 0 < auxWeight 𝔊.big Λ t := by
  unfold auxWeight
  exact Finset.prod_pos fun g _ => Finset.prod_pos fun i _ =>
    𝔊.big_law_pos g (t g i) (t g i).2

omit [DecidableEq B] in
theorem tupleWeight_nonneg (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J))
    (t : AuxList 𝔊.big Λ) : 0 ≤ auxWeight 𝔊.big Λ t := (tupleWeight_pos 𝔊 Λ t).le

/-- The label tuples of type `Λ` have total probability one. -/
theorem sum_tupleWeight (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) :
    ∑ t : AuxList 𝔊.big Λ, auxWeight 𝔊.big Λ t = 1 :=
  sum_auxWeight 𝔊.big_law_sum Λ

omit [DecidableEq B] in
theorem tupleProd_pos (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J))
    (t : AuxList 𝔊.big Λ) : 0 < tupleProd Λ t := by
  unfold tupleProd
  exact Finset.prod_pos fun g _ => Finset.prod_pos fun i _ =>
    (𝔊.prime_big g (t g i) (t g i).2).pos

omit [DecidableEq B] in
/-- Every label divides the product of its tuple. -/
theorem label_dvd_tupleProd {big : B → Finset ℕ} (Λ : B → Finset (Fin J)) (t : AuxList big Λ)
    (g : B) (i : {i : Fin J // i ∈ Λ g}) : (t g i : ℕ) ∣ tupleProd Λ t := by
  unfold tupleProd
  exact (Finset.dvd_prod_of_mem (fun i' : {i : Fin J // i ∈ Λ g} => (t g i' : ℕ))
      (Finset.mem_univ i)).trans
    (Finset.dvd_prod_of_mem (fun g' : B => ∏ i' : {i : Fin J // i ∈ Λ g'}, (t g' i' : ℕ))
      (Finset.mem_univ g))

omit [DecidableEq B] in
theorem label_le_tupleProd (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J))
    (t : AuxList 𝔊.big Λ) (g : B) (i : {i : Fin J // i ∈ Λ g}) :
    (t g i : ℕ) ≤ tupleProd Λ t :=
  Nat.le_of_dvd (tupleProd_pos 𝔊 Λ t) (label_dvd_tupleProd Λ t g i)

omit [DecidableEq B] in
/-- "Each selected product lies between `exp(L^c)` and `exp(m C₀ T L^d)`" [S-03:0296–0297]: the
upper bound, `log P_Λ ≤ m C₀ T L^d`. -/
theorem log_tupleProd_le_const (𝔊 : PrimeGroups P x S B) (hL : 0 ≤ Real.log x)
    (Λ : B → Finset (Fin J)) {m : ℕ} (hΛ : ∀ g, (Λ g).card ≤ m) (t : AuxList 𝔊.big Λ) :
    Real.log ((tupleProd Λ t : ℕ) : ℝ) ≤
      (m : ℝ) * P.C₀ * Real.log (Real.log x) * Real.log x ^ P.d := by
  have hLd : 0 ≤ Real.log x ^ P.d := Real.rpow_nonneg hL _
  have hsum : (∑ g, ((Λ g).card : ℝ)) ≤ (m : ℝ) * P.C₀ * Real.log (Real.log x) := by
    calc (∑ g, ((Λ g).card : ℝ)) ≤ ∑ _g : B, (m : ℝ) :=
          Finset.sum_le_sum fun g _ => by exact_mod_cast hΛ g
      _ = (Fintype.card B : ℝ) * m := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (P.C₀ * Real.log (Real.log x)) * m :=
          mul_le_mul_of_nonneg_right 𝔊.card_big_le (Nat.cast_nonneg _)
      _ = (m : ℝ) * P.C₀ * Real.log (Real.log x) := by ring
  exact (log_tupleProd_le 𝔊 Λ t).trans (mul_le_mul_of_nonneg_right hsum hLd)

end Tuples

/-! ### The scales exceed every power of `L` -/

/-- **The big primes and the selected products exceed every fixed power of `L`**
[S-03:0251–0252, 0312, 0327]. -/
theorem scaleLowerBound : ScaleLowerBound := by
  intro P E
  obtain ⟨L₀, -, hL₀⟩ := exists_rpow_le_sourcePrimeLowerBound P.c (c_pos P) E
  refine ⟨Real.exp L₀, ?_⟩
  intro x hx S B _ _ _ _ 𝔊
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : L₀ ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hprime : ∀ (g : B) (p : ℕ), p ∈ 𝔊.big g → Real.log x ^ E ≤ (p : ℝ) :=
    fun g p hp => (hL₀ _ hL).trans (𝔊.big_ge g p hp)
  refine ⟨hprime, ?_⟩
  intro J Λ hΛ t
  obtain ⟨g, i, hi⟩ := hΛ
  have h1 := hprime g (t g ⟨i, hi⟩) (t g ⟨i, hi⟩).2
  have h2 : (((t g ⟨i, hi⟩ : ℕ) : ℕ) : ℝ) ≤ ((tupleProd Λ t : ℕ) : ℝ) := by
    exact_mod_cast label_le_tupleProd 𝔊 Λ t g ⟨i, hi⟩
  exact h1.trans h2

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
