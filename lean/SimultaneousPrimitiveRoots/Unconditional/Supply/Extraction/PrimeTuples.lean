module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.AllocationIdentityProof
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Ordered tuples of primes above the sieve level

The combinatorial part of `SiftedDecomposition` (`[P-07:0230–0240]`): "integers divisible by `p²`
for a prime `p > z` … we may discard these integers …, count the others with weight `1/j!`, and
restore repeated factors at the same cost".

For a level `z` and `v ≥ 1`, `convPow j (primeCoeff z) v` is the number of ordered `j`-tuples of
primes `> z` with product `v` (`convPow_primeCoeff`, `primeTuples`).

* A tuple of primes with product `v` is a permutation of `v.primeFactorsList`
  (`ofFn_perm_primeFactorsList`). So a tuple exists only if `v` is `z`-rough and `j = Ω(v)`
  (`primeTuples_rough`), and there are at most `j!` tuples (`card_primeTuples_le`).
* If `v` is squarefree and `z`-rough there are exactly `Ω(v)!` tuples
  (`card_primeTuples_squarefree`): the permutations of the list of prime factors.
* `tupleSum z J v = ∑_{2 ≤ j ≤ J} (1/j!) · #tuples` is `0` when `v` is not rough or `v` is prime,
  it lies in `[0, 1]`, and it is `1` when `v` is rough, squarefree and `2 ≤ Ω(v) ≤ J`.
* `sift_term_bound`: for `1 < z < v < z^{J+1}` the pointwise defect
  `1_{v rough} - 1_{v prime} - tupleSum z J v` vanishes unless `v` is rough and not squarefree,
  and it is at most `1` in absolute value. It is stated for arbitrary real numbers `P₁, P₂, P₃ j`
  with the values of the three terms, so that it applies to `if … then … else` expressions with
  any decidability instances.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

/-! ### The coefficient of the primes above `z` -/

theorem primeCoeff_eq_one {z : ℝ} {m : ℕ} (hm : m.Prime) (hz : z < (m : ℝ)) :
    primeCoeff z m = 1 := by
  unfold primeCoeff
  exact if_pos ⟨hm, hz⟩

theorem primeCoeff_eq_zero {z : ℝ} {m : ℕ} (h : ¬(m.Prime ∧ z < (m : ℝ))) :
    primeCoeff z m = 0 := by
  unfold primeCoeff
  exact if_neg h

/-! ### Tuples of primes -/

/-- The ordered `j`-tuples of primes `> z` with product `v`. -/
def primeTuples (z : ℝ) (j v : ℕ) : Finset (Fin j → ℕ) :=
  (orderedFactorizations j v).filter fun e => ∀ i, (e i).Prime ∧ z < (e i : ℝ)

theorem mem_primeTuples {z : ℝ} {j v : ℕ} (hv : v ≠ 0) {e : Fin j → ℕ} :
    e ∈ primeTuples z j v ↔ ∏ i, e i = v ∧ ∀ i, (e i).Prime ∧ z < (e i : ℝ) := by
  unfold primeTuples
  rw [Finset.mem_filter, mem_orderedFactorizations hv]

/-- `(1_{p > z})^{*j}(v)` is the number of ordered `j`-tuples of primes `> z` with product
`v`. -/
theorem convPow_primeCoeff (z : ℝ) (j v : ℕ) :
    convPow j (primeCoeff z) v = ((primeTuples z j v).card : ℝ) := by
  unfold convPow primeTuples
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with h
  · rw [Nat.cast_one]
    exact Finset.prod_eq_one fun i _ => primeCoeff_eq_one (h i).1 (h i).2
  · rw [Nat.cast_zero]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (primeCoeff_eq_zero hi)

/-- A tuple of primes with product `v` is a permutation of the list of the prime factors of
`v`. -/
theorem ofFn_perm_primeFactorsList {j v : ℕ} {e : Fin j → ℕ} (hprod : ∏ i, e i = v)
    (hprime : ∀ i, (e i).Prime) : (List.ofFn e).Perm v.primeFactorsList :=
  Nat.primeFactorsList_unique (by rw [List.prod_ofFn]; exact hprod)
    (List.forall_mem_ofFn_iff.mpr hprime)

/-- If there is a `j`-tuple of primes `> z` with product `v`, then `v` is `z`-rough and has `j`
prime factors counted with multiplicity. -/
theorem primeTuples_rough {z : ℝ} {j v : ℕ} (hv : v ≠ 0) {e : Fin j → ℕ}
    (he : e ∈ primeTuples z j v) : IsRough z v ∧ v.primeFactorsList.length = j := by
  obtain ⟨hprod, hgood⟩ := (mem_primeTuples hv).mp he
  have hperm := ofFn_perm_primeFactorsList hprod fun i => (hgood i).1
  refine ⟨fun p hp hdvd => ?_, ?_⟩
  · have hmem : p ∈ v.primeFactorsList := (Nat.mem_primeFactorsList hv).mpr ⟨hp, hdvd⟩
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hperm.mem_iff.mpr hmem)
    rw [← hi]
    exact (hgood i).2
  · rw [← hperm.length_eq, List.length_ofFn]

/-- There are at most `j!` ordered `j`-tuples of primes with a given product. -/
theorem card_primeTuples_le {z : ℝ} {j v : ℕ} (hv : v ≠ 0) :
    (primeTuples z j v).card ≤ j.factorial := by
  rcases (primeTuples z j v).eq_empty_or_nonempty with h0 | ⟨e₀, he₀⟩
  · rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  · have hlen : v.primeFactorsList.length = j := (primeTuples_rough hv he₀).2
    have hsub : (primeTuples z j v).image List.ofFn ⊆
        v.primeFactorsList.permutations.toFinset := by
      intro l hl
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨hprod, hgood⟩ := (mem_primeTuples hv).mp he
      exact List.mem_toFinset.mpr (List.mem_permutations.mpr
        (ofFn_perm_primeFactorsList hprod fun i => (hgood i).1))
    have hperm : v.primeFactorsList.permutations.toFinset.card ≤
        v.primeFactorsList.permutations.length := by
      apply List.toFinset_card_le
    calc (primeTuples z j v).card = ((primeTuples z j v).image List.ofFn).card :=
          (Finset.card_image_of_injective _ List.ofFn_injective).symm
      _ ≤ v.primeFactorsList.permutations.toFinset.card := Finset.card_le_card hsub
      _ ≤ v.primeFactorsList.permutations.length := hperm
      _ = j.factorial := by rw [List.length_permutations, hlen]

/-- A squarefree `z`-rough integer `v ≥ 1` with `k` prime factors is the product of exactly `k!`
ordered `k`-tuples of primes `> z`. -/
theorem card_primeTuples_squarefree {z : ℝ} {v : ℕ} (hv : v ≠ 0) (hsq : Squarefree v)
    (hrough : IsRough z v) :
    (primeTuples z v.primeFactorsList.length v).card = v.primeFactorsList.length.factorial := by
  refine le_antisymm (card_primeTuples_le hv) ?_
  have hnodup : v.primeFactorsList.Nodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList hv).mp hsq
  have hinj : Function.Injective v.primeFactorsList.get :=
    List.nodup_iff_injective_get.mp hnodup
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin v.primeFactorsList.length))).card =
      v.primeFactorsList.length.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hprod : ∏ i, v.primeFactorsList.get i = v := by
    have h := List.prod_ofFn (f := v.primeFactorsList.get)
    rw [List.ofFn_get] at h
    exact h.symm.trans (Nat.prod_primeFactorsList hv)
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun (σ : Equiv.Perm (Fin v.primeFactorsList.length)) (i : Fin v.primeFactorsList.length) =>
      v.primeFactorsList.get (σ i)) ?_ ?_
  · intro σ _
    refine Finset.mem_coe.mpr ((mem_primeTuples hv).mpr ⟨?_, fun i => ?_⟩)
    · show ∏ i, v.primeFactorsList.get (σ i) = v
      rw [Equiv.prod_comp σ v.primeFactorsList.get]
      exact hprod
    · have hmem : v.primeFactorsList.get (σ i) ∈ v.primeFactorsList := List.get_mem _ _
      have hp := Nat.prime_of_mem_primeFactorsList hmem
      exact ⟨hp, hrough _ hp (Nat.dvd_of_mem_primeFactorsList hmem)⟩
  · intro σ _ τ _ hστ
    exact Equiv.ext fun i => hinj (congrFun hστ i)

/-- The count vanishes unless `v` is rough with `j` prime factors. -/
theorem convPow_primeCoeff_eq_zero {z : ℝ} {j v : ℕ} (hv : v ≠ 0)
    (h : ¬(IsRough z v ∧ v.primeFactorsList.length = j)) : convPow j (primeCoeff z) v = 0 := by
  have hempty : primeTuples z j v = ∅ :=
    Finset.eq_empty_of_forall_notMem fun e he => h (primeTuples_rough hv he)
  rw [convPow_primeCoeff, hempty, Finset.card_empty, Nat.cast_zero]

/-! ### The weighted sum over the lengths -/

/-- `∑_{2 ≤ j ≤ J} (1/j!) · #{ordered j-tuples of primes > z with product v}`. -/
def tupleSum (z : ℝ) (J v : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 J, 1 / (j.factorial : ℝ) * convPow j (primeCoeff z) v

theorem tupleSum_nonneg (z : ℝ) (J v : ℕ) : 0 ≤ tupleSum z J v :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (by positivity) (convPow_nonneg (primeCoeff_nonneg z) j v)

theorem tupleSum_eq_zero_of_not_rough {z : ℝ} {J v : ℕ} (hv : v ≠ 0) (h : ¬IsRough z v) :
    tupleSum z J v = 0 :=
  Finset.sum_eq_zero fun j _ => by
    rw [convPow_primeCoeff_eq_zero hv fun h' => h h'.1, mul_zero]

theorem tupleSum_eq_zero_of_prime {z : ℝ} {J v : ℕ} (hp : v.Prime) : tupleSum z J v = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  have hne : ¬(IsRough z v ∧ v.primeFactorsList.length = j) := by
    rintro ⟨-, hlen⟩
    rw [Nat.primeFactorsList_prime hp, List.length_singleton] at hlen
    omega
  rw [convPow_primeCoeff_eq_zero hp.ne_zero hne, mul_zero]

/-- Only the length `Ω(v)` contributes. -/
theorem tupleSum_eq_single {z : ℝ} {J v : ℕ} (hv : v ≠ 0)
    (hk : v.primeFactorsList.length ∈ Finset.Icc 2 J) :
    tupleSum z J v = 1 / (v.primeFactorsList.length.factorial : ℝ) *
      ((primeTuples z v.primeFactorsList.length v).card : ℝ) := by
  unfold tupleSum
  rw [← convPow_primeCoeff]
  exact Finset.sum_eq_single_of_mem _ hk fun j _ hjk => by
    rw [convPow_primeCoeff_eq_zero hv fun h => hjk h.2.symm, mul_zero]

theorem tupleSum_le_one {z : ℝ} {J v : ℕ} (hv : v ≠ 0) : tupleSum z J v ≤ 1 := by
  by_cases hk : v.primeFactorsList.length ∈ Finset.Icc 2 J
  · have hfac : (0 : ℝ) < (v.primeFactorsList.length.factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hle : ((primeTuples z v.primeFactorsList.length v).card : ℝ) ≤
        (v.primeFactorsList.length.factorial : ℝ) := Nat.cast_le.mpr (card_primeTuples_le hv)
    rw [tupleSum_eq_single hv hk, one_div, inv_mul_le_iff₀ hfac, mul_one]
    exact hle
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun j hj => ?_)) zero_le_one
    have hne : ¬(IsRough z v ∧ v.primeFactorsList.length = j) := by
      rintro ⟨-, hlen⟩
      rw [hlen] at hk
      exact hk hj
    rw [convPow_primeCoeff_eq_zero hv hne, mul_zero]

theorem tupleSum_eq_one {z : ℝ} {J v : ℕ} (hv : v ≠ 0) (hsq : Squarefree v)
    (hrough : IsRough z v) (hk : v.primeFactorsList.length ∈ Finset.Icc 2 J) :
    tupleSum z J v = 1 := by
  have hfac : (v.primeFactorsList.length.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [tupleSum_eq_single hv hk, card_primeTuples_squarefree hv hsq hrough]
  exact one_div_mul_cancel hfac

/-! ### Rough integers below `z^{J+1}` -/

/-- A prime above `z` is `z`-rough. -/
theorem isRough_of_prime {z : ℝ} {v : ℕ} (hv : v.Prime) (hz : z < (v : ℝ)) : IsRough z v := by
  intro p hp hdvd
  rw [(Nat.prime_dvd_prime_iff_eq hp hv).mp hdvd]
  exact hz

/-- A `z`-rough integer `v ≥ 1` with `k` prime factors is at least `z^k`. -/
theorem pow_length_le_of_rough {z : ℝ} (hz : 0 ≤ z) {v : ℕ} (hv : v ≠ 0)
    (hrough : IsRough z v) : z ^ v.primeFactorsList.length ≤ (v : ℝ) := by
  have h1 : (⌊z⌋₊ + 1) ^ v.primeFactorsList.length ≤ v.primeFactorsList.prod :=
    List.pow_card_le_prod _ _ fun p hp => by
      have hp' := Nat.prime_of_mem_primeFactorsList hp
      have hlt : z < (p : ℝ) := hrough p hp' (Nat.dvd_of_mem_primeFactorsList hp)
      exact Nat.succ_le_of_lt ((Nat.floor_lt hz).mpr hlt)
  rw [Nat.prod_primeFactorsList hv] at h1
  have h2 : z ≤ ((⌊z⌋₊ + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact (Nat.lt_floor_add_one z).le
  calc z ^ v.primeFactorsList.length
      ≤ ((⌊z⌋₊ + 1 : ℕ) : ℝ) ^ v.primeFactorsList.length := pow_le_pow_left₀ hz h2 _
    _ = (((⌊z⌋₊ + 1) ^ v.primeFactorsList.length : ℕ) : ℝ) := (Nat.cast_pow _ _).symm
    _ ≤ (v : ℝ) := Nat.cast_le.mpr h1

/-- A `z`-rough composite `2 ≤ v < z^{J+1}` has between `2` and `J` prime factors. -/
theorem length_mem_Icc {z : ℝ} (hz : 1 < z) {J v : ℕ} (hv2 : 2 ≤ v) (hnp : ¬v.Prime)
    (hrough : IsRough z v) (hlt : (v : ℝ) < z ^ (J + 1)) :
    v.primeFactorsList.length ∈ Finset.Icc 2 J := by
  have hv0 : v ≠ 0 := by omega
  have h1 := pow_length_le_of_rough (by linarith) hv0 hrough
  have h2 : z ^ v.primeFactorsList.length < z ^ (J + 1) := lt_of_le_of_lt h1 hlt
  have h3 : v.primeFactorsList.length < J + 1 := (pow_lt_pow_iff_right₀ hz).mp h2
  have h4 : v.primeFactorsList.length ≠ 0 := by
    intro h0
    have hnil : v.primeFactorsList = [] := List.length_eq_zero_iff.mp h0
    rcases (Nat.primeFactorsList_eq_nil v).mp hnil with h | h
    · omega
    · omega
  have h5 : v.primeFactorsList.length ≠ 1 := by
    intro h1'
    obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp h1'
    have hmem : p ∈ v.primeFactorsList := by
      rw [hp]
      exact List.mem_singleton.mpr rfl
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hmem
    have hprod : v.primeFactorsList.prod = v := Nat.prod_primeFactorsList hv0
    rw [hp] at hprod
    have hpv : p = v := by simpa using hprod
    rw [hpv] at hpp
    exact hnp hpp
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-! ### The pointwise defect -/

/-- **The pointwise form of the sifted decomposition.** Let `1 < z < v < z^{J+1}`. Let
`P₁ = a · 1_{v rough ∧ cls}`, `P₂ = a · 1_{v prime ∧ cls}` and
`P₃ j = a · 1_{cls} · #{j-tuples of primes > z with product v}`. Then
`|P₁ - P₂ - ∑_{2 ≤ j ≤ J} P₃ j / j!| ≤ c` for every `c ≥ 0` that bounds `|a|` when `v` is rough
and not squarefree; in particular the difference vanishes for all other `v`. -/
theorem sift_term_bound {z : ℝ} (hz : 1 < z) {J v : ℕ} (hzv : z < (v : ℝ))
    (hlt : (v : ℝ) < z ^ (J + 1)) {cls : Prop} {a c P₁ P₂ : ℝ} {P₃ : ℕ → ℝ} (hc0 : 0 ≤ c)
    (hc : IsRough z v → ¬Squarefree v → |a| ≤ c)
    (h₁ : IsRough z v ∧ cls → P₁ = a) (h₁' : ¬(IsRough z v ∧ cls) → P₁ = 0)
    (h₂ : v.Prime ∧ cls → P₂ = a) (h₂' : ¬(v.Prime ∧ cls) → P₂ = 0)
    (h₃ : cls → ∀ j, P₃ j = a * convPow j (primeCoeff z) v) (h₃' : ¬cls → ∀ j, P₃ j = 0) :
    |P₁ - P₂ - ∑ j ∈ Finset.Icc 2 J, 1 / (j.factorial : ℝ) * P₃ j| ≤ c := by
  have h1v : (1 : ℝ) < (v : ℝ) := hz.trans hzv
  have h1v' : 1 < v := by exact_mod_cast h1v
  have hv2 : 2 ≤ v := h1v'
  have hv0 : v ≠ 0 := by omega
  have hzero : ∀ {D : ℝ}, D = 0 → |D| ≤ c := fun {D} hD => by
    rw [hD, abs_zero]
    exact hc0
  by_cases hcls : cls
  · have e₃ : ∑ j ∈ Finset.Icc 2 J, 1 / (j.factorial : ℝ) * P₃ j = a * tupleSum z J v := by
      unfold tupleSum
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [h₃ hcls j]
        ring
    rw [e₃]
    by_cases hr : IsRough z v
    · rw [h₁ ⟨hr, hcls⟩]
      by_cases hp : v.Prime
      · refine hzero ?_
        rw [h₂ ⟨hp, hcls⟩, tupleSum_eq_zero_of_prime hp]
        ring
      · rw [h₂' fun h => hp h.1]
        by_cases hsq : Squarefree v
        · refine hzero ?_
          rw [tupleSum_eq_one hv0 hsq hr (length_mem_Icc hz hv2 hp hr hlt)]
          ring
        · have h0 := tupleSum_nonneg z J v
          have h1 := tupleSum_le_one (z := z) (J := J) hv0
          have e : a - 0 - a * tupleSum z J v = a * (1 - tupleSum z J v) := by ring
          rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - tupleSum z J v)]
          calc |a| * (1 - tupleSum z J v) ≤ |a| * 1 :=
                mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg a)
            _ = |a| := mul_one _
            _ ≤ c := hc hr hsq
    · have hp : ¬v.Prime := fun hp => hr (isRough_of_prime hp hzv)
      refine hzero ?_
      rw [h₁' fun h => hr h.1, h₂' fun h => hp h.1, tupleSum_eq_zero_of_not_rough hv0 hr]
      ring
  · refine hzero ?_
    rw [h₁' fun h => hcls h.2, h₂' fun h => hcls h.2,
      Finset.sum_eq_zero fun j _ => by rw [h₃' hcls j, mul_zero]]
    ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
