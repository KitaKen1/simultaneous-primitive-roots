module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.AllocationIdentityProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CandidateAdmissibleProof

/-!
# The integers with a large candidate part

(ext:removed-log-mean) and its consequence (`[P-07:0352–0361]`): "the number [of `m ≍ H_i`] with
`log(m/m̄) > L^{.9}` is `O(H_i L^{-.45})`", where `m̄` removes the candidate prime-power parts
of `m`.

The manuscript bounds the mean of `log(m/m̄)`. Here the exceptional set is described without
valuations: `m` is *good* if no square of a candidate prime divides `m` and at most `Λ₀` candidate
primes divide `m`.

* `good_le`: a good `m` satisfies `m ≤ m̄ exp(Λ₀ E)` when the candidate primes are `≤ exp(E)`
  (`m = m̄ ∏_{p ∣ m} p`, `eq_prod_filter_mul_freePart`).
* `bad_count_le`: `#{m ≤ t : m not good} ≤ t (∑_p 1/p² + V/Λ₀)` (multiples of `p²`, and Markov's
  inequality for the number of candidate prime divisors).
* `candidatePrimes_facts`: the candidate primes are primes in `[exp(L^{.28}), exp(L^{.45})]`;
  `reciprocalMass_candidatePrimes_le`: their reciprocal mass is `≤ log(L^{.45}) + 2C`, from
  Mertens' estimate on one window.

The declarations are in the namespace `Extraction.Strip`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip

noncomputable section

/-- `m` is good for the set `P`: no square of a prime of `P` divides `m`, and at most `Λ₀` primes
of `P` divide `m`. -/
def Good (P : Finset ℕ) (Λ₀ : ℝ) (m : ℕ) : Prop :=
  (∀ p ∈ P, ¬ p ^ 2 ∣ m) ∧ (primeHits P m : ℝ) ≤ Λ₀

/-- A good `m` has a small `P`-part: `m ≤ m_* exp(Λ₀ E)` when the primes of `P` are `≤ exp(E)`. -/
theorem good_le {P : Finset ℕ} {E Λ₀ : ℝ} (hE : 0 ≤ E)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ Real.exp E) {m : ℕ} (hm : m ≠ 0) (hg : Good P Λ₀ m) :
    (m : ℝ) ≤ (freePart P m : ℝ) * Real.exp (Λ₀ * E) := by
  have hfac := eq_prod_filter_mul_freePart hm (fun p hp => (hP p hp).1) hg.1
  have hcast : (m : ℝ) = (∏ p ∈ P.filter (fun p => p ∣ m), (p : ℝ)) * (freePart P m : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.cast_mul, hfac]
  have hprod : ∏ p ∈ P.filter (fun p => p ∣ m), (p : ℝ) ≤ Real.exp (Λ₀ * E) :=
    calc ∏ p ∈ P.filter (fun p => p ∣ m), (p : ℝ)
        ≤ ∏ _p ∈ P.filter (fun p => p ∣ m), Real.exp E :=
          Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p)
            (fun p hp => (hP p (Finset.mem_filter.mp hp).1).2)
      _ = Real.exp E ^ primeHits P m := by
          unfold primeHits
          exact Finset.prod_const _
      _ = Real.exp ((primeHits P m : ℝ) * E) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (Λ₀ * E) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hg.2 hE)
  rw [hcast, mul_comm]
  exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)

/-- `#{1 ≤ m ≤ t : d ∣ m} ≤ t/d`. -/
theorem sum_dvd_indicator_le (d t : ℕ) :
    ∑ m ∈ Finset.Icc 1 t, (if d ∣ m then (1 : ℝ) else 0) ≤ (t : ℝ) / (d : ℝ) := by
  have hIcc : Finset.Icc 1 t = Finset.Ioc 0 t := by
    ext m
    rw [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [Finset.sum_boole, hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le

open _root_.Classical in
/-- **The exceptional integers are few**: `#{m ≤ t : m not good} ≤ t (∑_{p ∈ P} 1/p² + V_P/Λ₀)`. -/
theorem bad_count_le {P : Finset ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) (t : ℕ) :
    ∑ m ∈ Finset.Icc 1 t, (if Good P Λ₀ m then (0 : ℝ) else 1) ≤
      (∑ p ∈ P, 1 / (p : ℝ) ^ 2 + reciprocalMass P / Λ₀) * (t : ℝ) := by
  have hind : ∀ (c : Prop) [Decidable c], (0 : ℝ) ≤ if c then (1 : ℝ) else 0 := fun c _ => by
    by_cases h : c
    · rw [if_pos h]
      exact zero_le_one
    · rw [if_neg h]
  have hpt : ∀ m : ℕ, (if Good P Λ₀ m then (0 : ℝ) else 1) ≤
      ∑ p ∈ P, (if p ^ 2 ∣ m then (1 : ℝ) else 0) +
        (∑ p ∈ P, (if p ∣ m then (1 : ℝ) else 0)) / Λ₀ := by
    intro m
    have hs1 : 0 ≤ ∑ p ∈ P, (if p ^ 2 ∣ m then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun p _ => hind _
    have hs2 : 0 ≤ (∑ p ∈ P, (if p ∣ m then (1 : ℝ) else 0)) / Λ₀ :=
      div_nonneg (Finset.sum_nonneg fun p _ => hind _) hΛ.le
    by_cases hg : Good P Λ₀ m
    · rw [if_pos hg]
      exact add_nonneg hs1 hs2
    · rw [if_neg hg]
      by_cases hsq : ∀ p ∈ P, ¬ p ^ 2 ∣ m
      · have hhits : Λ₀ < (primeHits P m : ℝ) := not_le.mp fun h => hg ⟨hsq, h⟩
        have hcard : (primeHits P m : ℝ) = ∑ p ∈ P, (if p ∣ m then (1 : ℝ) else 0) := by
          unfold primeHits
          rw [Finset.sum_boole]
        rw [← hcard]
        have h1 : 1 ≤ (primeHits P m : ℝ) / Λ₀ := (one_le_div hΛ).mpr hhits.le
        linarith
      · obtain ⟨p, hp'⟩ := not_forall.mp hsq
        obtain ⟨hp, hpm⟩ := _root_.not_imp.mp hp'
        have hpm' : p ^ 2 ∣ m := not_not.mp hpm
        have h2 : (if p ^ 2 ∣ m then (1 : ℝ) else 0) ≤
            ∑ p ∈ P, (if p ^ 2 ∣ m then (1 : ℝ) else 0) :=
          Finset.single_le_sum (f := fun p => if p ^ 2 ∣ m then (1 : ℝ) else 0)
            (fun p _ => hind _) hp
        rw [if_pos hpm'] at h2
        linarith
  have e1 : ∑ m ∈ Finset.Icc 1 t, ∑ p ∈ P, (if p ^ 2 ∣ m then (1 : ℝ) else 0) =
      ∑ p ∈ P, ∑ m ∈ Finset.Icc 1 t, (if p ^ 2 ∣ m then (1 : ℝ) else 0) := Finset.sum_comm
  have e2 : ∑ m ∈ Finset.Icc 1 t, ∑ p ∈ P, (if p ∣ m then (1 : ℝ) else 0) =
      ∑ p ∈ P, ∑ m ∈ Finset.Icc 1 t, (if p ∣ m then (1 : ℝ) else 0) := Finset.sum_comm
  have e3 : ∑ p ∈ P, (t : ℝ) / ((p ^ 2 : ℕ) : ℝ) = (∑ p ∈ P, 1 / (p : ℝ) ^ 2) * (t : ℝ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by
      rw [Nat.cast_pow]
      ring
  have e4 : ∑ p ∈ P, (t : ℝ) / (p : ℝ) = reciprocalMass P * (t : ℝ) := by
    unfold reciprocalMass
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  calc ∑ m ∈ Finset.Icc 1 t, (if Good P Λ₀ m then (0 : ℝ) else 1)
      ≤ ∑ m ∈ Finset.Icc 1 t, (∑ p ∈ P, (if p ^ 2 ∣ m then (1 : ℝ) else 0) +
          (∑ p ∈ P, (if p ∣ m then (1 : ℝ) else 0)) / Λ₀) := Finset.sum_le_sum fun m _ => hpt m
    _ = ∑ p ∈ P, ∑ m ∈ Finset.Icc 1 t, (if p ^ 2 ∣ m then (1 : ℝ) else 0) +
          (∑ p ∈ P, ∑ m ∈ Finset.Icc 1 t, (if p ∣ m then (1 : ℝ) else 0)) / Λ₀ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, e1, e2]
    _ ≤ ∑ p ∈ P, (t : ℝ) / ((p ^ 2 : ℕ) : ℝ) + (∑ p ∈ P, (t : ℝ) / (p : ℝ)) / Λ₀ :=
        add_le_add (Finset.sum_le_sum fun p _ => sum_dvd_indicator_le (p ^ 2) t)
          (div_le_div_of_nonneg_right
            (Finset.sum_le_sum fun p _ => sum_dvd_indicator_le p t) hΛ.le)
    _ = (∑ p ∈ P, 1 / (p : ℝ) ^ 2 + reciprocalMass P / Λ₀) * (t : ℝ) := by
        rw [e3, e4]
        ring

/-! ### The candidate primes -/

/-- The candidate primes are primes between `exp(L^{.28})` and `exp(L^{.45})`
(`[P-07:0319–0323]`), once `L ≥ 1`. -/
theorem candidatePrimes_facts {x : ℝ} (hL : 1 ≤ Real.log x) {p : ℕ}
    (hp : p ∈ candidatePrimes x) :
    p.Prime ∧ Real.exp (Real.log x ^ (0.28 : ℝ)) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.45 : ℝ)) := by
  have hlow := candidatePrimes_ge hL hp
  obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hp
  rcases g with i | i
  · have hmem : p ∈ candidateBand 0.28 x i.val := hg
    have h1 := candidateBand_range (by norm_num : (0.28 : ℝ) ≤ 0.35) hL i.isLt hmem
    have h2 : Real.log x ^ (0.35 : ℝ) ≤ Real.log x ^ (0.45 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    exact ⟨(mem_candidateBand.mp hmem).1, hlow, h1.2.le.trans (Real.exp_le_exp.mpr h2)⟩
  · have hmem : p ∈ candidateBand 0.4 x i.val := hg
    have h1 := candidateBand_range (by norm_num : (0.4 : ℝ) ≤ 0.45) hL i.isLt hmem
    exact ⟨(mem_candidateBand.mp hmem).1, hlow, h1.2.le⟩

/-- The reciprocal mass of the candidate primes is `≤ log(L^{.45}) + 2C`, from Mertens' estimate
on the window `(e, exp(L^{.45})]`. -/
theorem reciprocalMass_candidatePrimes_le (hM : MertensReciprocal) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 < Real.log x →
      reciprocalMass (candidatePrimes x) ≤ Real.log (Real.log x ^ (0.45 : ℝ)) + 2 * C := by
  obtain ⟨C, hC, hwin⟩ := exists_reciprocal_window hM
  refine ⟨C, hC, fun x hL => ?_⟩
  have hL1 : 1 ≤ Real.log x := hL.le
  have ht : (1 : ℝ) ≤ Real.log x ^ (0.45 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have h28 : (1 : ℝ) < Real.log x ^ (0.28 : ℝ) := Real.one_lt_rpow hL (by norm_num)
  have hsub : candidatePrimes x ⊆
      (Finset.Icc 2 ⌊Real.exp (Real.log x ^ (0.45 : ℝ))⌋₊).filter Nat.Prime \
        (Finset.Icc 2 ⌊Real.exp 1⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hlo, hhi⟩ := candidatePrimes_facts hL1 hp
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpp.two_le, Nat.le_floor hhi⟩, hpp⟩, fun h => ?_⟩
    have h0 : p ≤ ⌊Real.exp 1⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).2
    have h1 : (p : ℝ) ≤ Real.exp 1 :=
      (Nat.cast_le.mpr h0).trans (Nat.floor_le (Real.exp_pos _).le)
    have h2 : Real.exp 1 < Real.exp (Real.log x ^ (0.28 : ℝ)) := Real.exp_lt_exp.mpr h28
    linarith
  have hle : reciprocalMass (candidatePrimes x) ≤
      ∑ p ∈ (Finset.Icc 2 ⌊Real.exp (Real.log x ^ (0.45 : ℝ))⌋₊).filter Nat.Prime \
        (Finset.Icc 2 ⌊Real.exp 1⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
    unfold reciprocalMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
  have hw := (abs_le.mp (hwin 1 (Real.log x ^ (0.45 : ℝ)) le_rfl ht)).2
  rw [Real.log_one, sub_zero, div_one] at hw
  linarith

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip
