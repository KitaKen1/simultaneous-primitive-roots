module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.CoreSanity

/-!
# The allocation identity (ext:allocation-identity)

`allocationIdentity : AllocationIdentity` (`[P-07:0576–0594]`): if the active primes are primes of
the candidate set that exceed `W`, in pairwise disjoint groups, and `v ≥ 1` is divisible by the
square of no active prime, then

`ã^{*j}(v) · ∏_g (q₀/j)^{ω_g(v)-1} ω_g(v)/V_g = j^{s_P} W_{1,q₀}(v) G_P(v)`.

Steps.

* `convPow_prime_mul`: for a prime `p ∤ u`, `u ≥ 1`, and a coefficient with `a(p m) = a(m)`,
  `a^{*j}(p u) = j · a^{*j}(u)`: "every active prime dividing `v` can be assigned independently to
  any of the `j` slots". The bijection is `(i, e) ↦ e` with the `i`-th coordinate multiplied by
  `p`; it is injective because `p` divides no coordinate of a factorization of `u`.
* `convPow_prod_primes_mul`: the same for a finite set `A` of primes, with the factor `j^{|A|}`.
* `strippedCoeff_prime_mul`: `ã(p m) = ã(m)` for an active prime `p` (`p ∈ candidates` is removed
  by the bar, `freePart_prime_mul`; `p > W` does not change roughness, `isRough_prime_mul`).
* `eq_prod_filter_mul_freePart`: `v = (∏_{p ∈ P, p ∣ v} p) · v_*` when no `p² ∣ v`, `p ∈ P`.
* `primeHits_allPrimes`: `ω_P(v) = ∑_g ω_g(v)` for disjoint groups.
* `markFactor_div`: `(q₀/j)^{ω-1} ω/V = (q₀^{ω-1} ω/V) / j^{ω-1}`.

Then `ã^{*j}(v) = j^{ω_P(v)} G_P(v)`, and `j^{ω_P(v)} / j^{ω_P(v) - s_P} = j^{s_P}` when every
group has a divisor of `v`; otherwise both sides vanish.

All four hypotheses are used: "no active square" and disjointness in the count `j^{ω_P(v)}`,
`p ∈ candidates` and `W < p` in `ã(p m) = ã(m)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

/-! ### Ordered factorizations -/

/-- For `n ≠ 0`, `e` is an ordered factorization of `n` iff `∏ e_i = n`. -/
theorem mem_orderedFactorizations {j n : ℕ} (hn : n ≠ 0) {e : Fin j → ℕ} :
    e ∈ orderedFactorizations j n ↔ ∏ i, e i = n := by
  unfold orderedFactorizations
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => Nat.mem_divisors.mpr ⟨?_, hn⟩, h⟩
    exact (Finset.dvd_prod_of_mem e (Finset.mem_univ i)).trans (dvd_of_eq h)

/-- Multiplying one coordinate by `c` multiplies the product by `c`. -/
theorem prod_update_mul {j : ℕ} (e : Fin j → ℕ) (i : Fin j) (c : ℕ) :
    ∏ k, Function.update e i (c * e i) k = c * ∏ k, e k := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i) e, mul_assoc]

/-! ### One prime, and a finite set of primes -/

/-- **One active prime**: if the prime `p` does not divide `u ≥ 1` and `a(p m) = a(m)` for all
`m`, then `a^{*j}(p u) = j · a^{*j}(u)`. -/
theorem convPow_prime_mul {j : ℕ} {a : ℕ → ℝ} {p u : ℕ} (hp : p.Prime) (hu : u ≠ 0)
    (hpu : ¬ p ∣ u) (ha : ∀ m : ℕ, a (p * m) = a m) :
    convPow j a (p * u) = (j : ℝ) * convPow j a u := by
  have hpu0 : p * u ≠ 0 := Nat.mul_ne_zero hp.ne_zero hu
  have hbij : ∑ x ∈ (Finset.univ : Finset (Fin j)) ×ˢ orderedFactorizations j u,
      ∏ k, a (x.2 k) = ∑ m ∈ orderedFactorizations j (p * u), ∏ k, a (m k) := by
    refine Finset.sum_bij (fun x _ => Function.update x.2 x.1 (p * x.2 x.1)) ?_ ?_ ?_ ?_
    · -- the image is a factorization of `p u`
      rintro ⟨i, e⟩ hx
      have he : ∏ k, e k = u :=
        (mem_orderedFactorizations hu).mp (Finset.mem_product.mp hx).2
      show Function.update e i (p * e i) ∈ orderedFactorizations j (p * u)
      rw [mem_orderedFactorizations hpu0, prod_update_mul, he]
    · -- injectivity: the slot of `p` is the only coordinate divisible by `p`
      rintro ⟨i₁, e₁⟩ hx₁ ⟨i₂, e₂⟩ hx₂ heq
      have heq' : Function.update e₁ i₁ (p * e₁ i₁) = Function.update e₂ i₂ (p * e₂ i₂) := heq
      have he₂ : ∏ k, e₂ k = u :=
        (mem_orderedFactorizations hu).mp (Finset.mem_product.mp hx₂).2
      have hidx : i₁ = i₂ := by
        by_contra hne
        have h1 := congrFun heq' i₁
        rw [Function.update_self, Function.update_of_ne hne] at h1
        have h2 : p ∣ e₂ i₁ := Dvd.intro _ h1
        have h3 : e₂ i₁ ∣ u :=
          (Finset.dvd_prod_of_mem e₂ (Finset.mem_univ i₁)).trans (dvd_of_eq he₂)
        exact hpu (h2.trans h3)
      have hfun : e₁ = e₂ := by
        funext k
        have h1 := congrFun heq' k
        rw [← hidx] at h1
        by_cases hk : k = i₁
        · rw [hk] at h1 ⊢
          rw [Function.update_self, Function.update_self] at h1
          exact Nat.eq_of_mul_eq_mul_left hp.pos h1
        · rw [Function.update_of_ne hk, Function.update_of_ne hk] at h1
          exact h1
      rw [hidx, hfun]
    · -- surjectivity: divide the coordinate that `p` divides
      intro m hm
      have hm' : ∏ k, m k = p * u := (mem_orderedFactorizations hpu0).mp hm
      have hdvd : p ∣ ∏ k, m k := Dvd.intro u hm'.symm
      obtain ⟨i, -, q, hq⟩ := hp.prime.exists_mem_finset_dvd hdvd
      have hupd : Function.update (Function.update m i q) i (p * Function.update m i q i) =
          m := by
        rw [Function.update_self, Function.update_idem, ← hq, Function.update_eq_self]
      have hprod : ∏ k, Function.update m i q k = u := by
        have h1 := prod_update_mul (Function.update m i q) i p
        rw [hupd, hm'] at h1
        exact (Nat.eq_of_mul_eq_mul_left hp.pos h1).symm
      exact ⟨(i, Function.update m i q),
        Finset.mem_product.mpr
          ⟨Finset.mem_univ i, (mem_orderedFactorizations hu).mpr hprod⟩, hupd⟩
    · -- the coefficient does not see the factor `p`
      rintro ⟨i, e⟩ hx
      show ∏ k, a (e k) = ∏ k, a (Function.update e i (p * e i) k)
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hk : k = i
      · rw [hk, Function.update_self, ha]
      · rw [Function.update_of_ne hk]
  calc convPow j a (p * u) = ∑ m ∈ orderedFactorizations j (p * u), ∏ k, a (m k) := rfl
    _ = ∑ x ∈ (Finset.univ : Finset (Fin j)) ×ˢ orderedFactorizations j u,
          ∏ k, a (x.2 k) := hbij.symm
    _ = ∑ _i : Fin j, ∑ e ∈ orderedFactorizations j u, ∏ k, a (e k) :=
        Finset.sum_product _ _ _
    _ = (j : ℝ) * ∑ e ∈ orderedFactorizations j u, ∏ k, a (e k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (j : ℝ) * convPow j a u := rfl

/-- **Several active primes**: `a^{*j}((∏_{p ∈ A} p) u) = j^{|A|} a^{*j}(u)` when the primes of
`A` do not divide `u ≥ 1` and `a(p m) = a(m)` for every `p ∈ A`. -/
theorem convPow_prod_primes_mul {j : ℕ} {a : ℕ → ℝ} {u : ℕ} (hu : u ≠ 0) (A : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hAu : ∀ p ∈ A, ¬ p ∣ u)
    (ha : ∀ p ∈ A, ∀ m : ℕ, a (p * m) = a m) :
    convPow j a ((∏ p ∈ A, p) * u) = (j : ℝ) ^ A.card * convPow j a u := by
  induction A using Finset.induction_on with
  | empty => rw [Finset.prod_empty, one_mul, Finset.card_empty, pow_zero, one_mul]
  | @insert p A hpA ih =>
    have hp : p.Prime := hA p (Finset.mem_insert_self p A)
    have hA' : ∀ q ∈ A, q.Prime := fun q hq => hA q (Finset.mem_insert_of_mem hq)
    have ih' := ih hA' (fun q hq => hAu q (Finset.mem_insert_of_mem hq))
      (fun q hq => ha q (Finset.mem_insert_of_mem hq))
    have hprod0 : (∏ q ∈ A, q) * u ≠ 0 :=
      Nat.mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun q hq => (hA' q hq).ne_zero) hu
    have hnd : ¬ p ∣ (∏ q ∈ A, q) * u := by
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
      · obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd h1
        have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp (hA' q hq)).mp hpq
        refine hpA ?_
        rw [hpq']
        exact hq
      · exact hAu p (Finset.mem_insert_self p A) h1
    rw [Finset.prod_insert hpA, Finset.card_insert_of_notMem hpA, mul_assoc,
      convPow_prime_mul hp hprod0 hnd (ha p (Finset.mem_insert_self p A)), ih']
    ring

/-! ### The stripped coefficient does not see the active primes -/

/-- A prime `p > W` does not change roughness. -/
theorem isRough_prime_mul {W : ℝ} {p : ℕ} (hp : p.Prime) (hpW : W < (p : ℝ)) (m : ℕ) :
    IsRough W (p * m) ↔ IsRough W m := by
  constructor
  · intro h q hq hdvd
    exact h q hq (Dvd.dvd.mul_left hdvd p)
  · intro h q hq hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h1 | h1
    · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp h1
      rw [hqp]
      exact hpW
    · exact h q hq h1

/-- The bar removes a prime of the set: `(p m)‾ = m̄` for a prime `p ∈ P`. -/
theorem freePart_prime_mul {P : Finset ℕ} {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) (m : ℕ) :
    freePart P (p * m) = freePart P m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm, mul_zero]
  · have hfac : (p * m).factorization.filter (fun q => q ∉ P) =
        m.factorization.filter (fun q => q ∉ P) := by
      rw [Nat.factorization_mul hp.ne_zero hm.ne', hp.factorization, Finsupp.filter_add,
        Finsupp.filter_single_of_neg, zero_add]
      exact fun h => h hpP
    rw [freePart_eq_prod, freePart_eq_prod, hfac]

/-- `ã(p m) = ã(m)` for a prime `p > W` of the candidate set. -/
theorem strippedCoeff_prime_mul {x γ : ℝ} {candidates : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hpc : p ∈ candidates) (hpW : roughCutoff x < (p : ℝ)) (m : ℕ) :
    strippedCoeff x γ candidates (p * m) = strippedCoeff x γ candidates m := by
  have hfree : freePart candidates (p * m) = freePart candidates m :=
    freePart_prime_mul hp hpc m
  have hrough : IsRough (roughCutoff x) (p * m) ↔ IsRough (roughCutoff x) m :=
    isRough_prime_mul hp hpW m
  unfold strippedCoeff
  rw [hfree]
  by_cases h : IsRough (roughCutoff x) m ∧ x ^ γ < (freePart candidates m : ℝ)
  · have h' : IsRough (roughCutoff x) (p * m) ∧ x ^ γ < (freePart candidates m : ℝ) :=
      ⟨hrough.mpr h.1, h.2⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬ (IsRough (roughCutoff x) (p * m) ∧ x ^ γ < (freePart candidates m : ℝ)) :=
      fun hc => h ⟨hrough.mp hc.1, hc.2⟩
    rw [if_neg h, if_neg h']

/-! ### The factorization `v = (∏_{p ∈ P, p ∣ v} p) · v_*` and the count of active primes -/

/-- If `v ≥ 1` is divisible by the square of no prime of `P`, then
`v = (∏_{p ∈ P, p ∣ v} p) · v_*`. -/
theorem eq_prod_filter_mul_freePart {P : Finset ℕ} {v : ℕ} (hv : v ≠ 0)
    (hP : ∀ p ∈ P, p.Prime) (hsq : ∀ p ∈ P, ¬ p ^ 2 ∣ v) :
    (∏ p ∈ P.filter (fun p => p ∣ v), p) * freePart P v = v := by
  have hset : v.primeFactors.filter (fun p => p ∈ P) = P.filter (fun p => p ∣ v) := by
    ext q
    rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hdvd, _⟩, hqP⟩
      exact ⟨hqP, hdvd⟩
    · rintro ⟨hqP, hdvd⟩
      exact ⟨⟨hP q hqP, hdvd, hv⟩, hqP⟩
  have hpow : ∏ q ∈ v.primeFactors.filter (fun p => p ∈ P), q ^ v.factorization q =
      ∏ q ∈ P.filter (fun p => p ∣ v), q := by
    rw [hset]
    refine Finset.prod_congr rfl fun q hq => ?_
    obtain ⟨hqP, hdvd⟩ := Finset.mem_filter.mp hq
    have hq' : q.Prime := hP q hqP
    have h1 : 0 < v.factorization q := hq'.factorization_pos_of_dvd hv hdvd
    have h2 : ¬ 2 ≤ v.factorization q := fun h =>
      hsq q hqP ((hq'.pow_dvd_iff_le_factorization hv).mpr h)
    have h3 : v.factorization q = 1 := by omega
    rw [h3, pow_one]
  have hsplit := Finset.prod_filter_mul_prod_filter_not v.primeFactors (fun p => p ∈ P)
    (fun q => q ^ v.factorization q)
  have hself : ∏ q ∈ v.primeFactors, q ^ v.factorization q = v :=
    Nat.prod_factorization_pow_eq_self hv
  unfold freePart
  rw [← hpow]
  exact hsplit.trans hself

/-- `ω_P(v) = ∑_g ω_g(v)` for pairwise disjoint groups. -/
theorem primeHits_allPrimes (𝔊 : ActiveGroups)
    (hdisj : ∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g')) (v : ℕ) :
    primeHits 𝔊.allPrimes v = ∑ g : 𝔊.Index, primeHits (𝔊.group g) v := by
  unfold primeHits ActiveGroups.allPrimes
  rw [Finset.filter_biUnion]
  exact Finset.card_biUnion fun g _ g' _ hne =>
    Finset.disjoint_filter_filter (hdisj g g' hne)

/-- `(q₀/j)^{ω-1} ω / V = (q₀^{ω-1} ω / V) / j^{ω-1}`. -/
theorem markFactor_div (q₀ j : ℝ) (S : Finset ℕ) (v : ℕ) :
    markFactor (q₀ / j) S v = markFactor q₀ S v / j ^ (primeHits S v - 1) := by
  unfold markFactor
  rw [div_pow]
  ring

/-! ### The identity -/

/-- **The allocation identity** (`[P-07:0576–0594]`, (ext:allocation-identity)). -/
theorem allocationIdentity : AllocationIdentity := by
  intro x γ q₀ j hj candidates 𝔊 hgrp hdisj v hv hsq
  have hv0 : v ≠ 0 := hv.ne'
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- the active primes are primes of the candidate set that exceed `W`
  have hP : ∀ p ∈ 𝔊.allPrimes, p.Prime ∧ p ∈ candidates ∧ roughCutoff x < (p : ℝ) := by
    intro p hp
    obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hp
    exact hgrp g p hg
  -- `v = (∏_{p ∈ A} p) v_*` with `A` the active primes dividing `v`
  obtain ⟨A, hAdef⟩ : ∃ A : Finset ℕ, A = 𝔊.allPrimes.filter (fun p => p ∣ v) := ⟨_, rfl⟩
  have hAP : ∀ p ∈ A, p ∈ 𝔊.allPrimes := by
    intro p hp
    rw [hAdef] at hp
    exact (Finset.mem_filter.mp hp).1
  have hdecomp : (∏ p ∈ A, p) * freePart 𝔊.allPrimes v = v := by
    rw [hAdef]
    exact eq_prod_filter_mul_freePart hv0 (fun p hp => (hP p hp).1) hsq
  have hu0 : freePart 𝔊.allPrimes v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdecomp
    exact hv0 hdecomp.symm
  have hAu : ∀ p ∈ A, ¬ p ∣ freePart 𝔊.allPrimes v := by
    intro p hp hdvd
    have hpA : p ∣ ∏ q ∈ A, q := Finset.dvd_prod_of_mem (fun q => q) hp
    have h2 : p * p ∣ (∏ q ∈ A, q) * freePart 𝔊.allPrimes v := mul_dvd_mul hpA hdvd
    rw [hdecomp, ← pow_two] at h2
    exact hsq p (hAP p hp) h2
  -- `ã^{*j}(v) = j^{ω_P(v)} G_P(v)`
  have hconv : convPow j (strippedCoeff x γ candidates) v =
      (j : ℝ) ^ A.card *
        convPow j (strippedCoeff x γ candidates) (freePart 𝔊.allPrimes v) := by
    have h := convPow_prod_primes_mul (j := j) (a := strippedCoeff x γ candidates) hu0 A
      (fun p hp => (hP p (hAP p hp)).1) hAu
      (fun p hp m => strippedCoeff_prime_mul (hP p (hAP p hp)).1 (hP p (hAP p hp)).2.1
        (hP p (hAP p hp)).2.2 m)
    rw [hdecomp] at h
    exact h
  have hcard : A.card = ∑ g : 𝔊.Index, primeHits (𝔊.group g) v := by
    rw [hAdef]
    exact primeHits_allPrimes 𝔊 hdisj v
  rw [allocationCore_eq_convPow, hconv, hcard]
  obtain ⟨G, hG⟩ : ∃ G : ℝ,
      G = convPow j (strippedCoeff x γ candidates) (freePart 𝔊.allPrimes v) := ⟨_, rfl⟩
  rw [← hG]
  by_cases hall : ∀ g : 𝔊.Index, 1 ≤ primeHits (𝔊.group g) v
  · -- every group has a divisor of `v`
    have hcardI : ∑ _g : 𝔊.Index, 1 = 𝔊.numGroups := by
      show ∑ _g : 𝔊.Index, 1 = 𝔊.numSmall + 𝔊.numBig
      rw [← Finset.card_eq_sum_ones, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
        Fintype.card_fin]
    have hsum : ∑ g : 𝔊.Index, (primeHits (𝔊.group g) v - 1) + 𝔊.numGroups =
        ∑ g : 𝔊.Index, primeHits (𝔊.group g) v := by
      rw [← hcardI, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ => Nat.sub_add_cancel (hall g)
    have hmf : ∏ g : 𝔊.Index, markFactor (q₀ / (j : ℝ)) (𝔊.group g) v =
        (∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) v) /
          (j : ℝ) ^ ∑ g : 𝔊.Index, (primeHits (𝔊.group g) v - 1) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun g _ => markFactor_div q₀ (j : ℝ) (𝔊.group g) v
    obtain ⟨E, hE⟩ : ∃ E : ℕ, E = ∑ g : 𝔊.Index, (primeHits (𝔊.group g) v - 1) := ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) v := ⟨_, rfl⟩
    have hne : (j : ℝ) ^ E ≠ 0 := pow_ne_zero E hjR
    rw [hmf, ← hsum, ← hE, ← hM, pow_add]
    calc (j : ℝ) ^ E * (j : ℝ) ^ 𝔊.numGroups * G * (M / (j : ℝ) ^ E)
        = (j : ℝ) ^ E / (j : ℝ) ^ E * ((j : ℝ) ^ 𝔊.numGroups * M * G) := by ring
      _ = (j : ℝ) ^ 𝔊.numGroups * M * G := by rw [div_self hne, one_mul]
  · -- some group has no divisor of `v`: both sides vanish
    obtain ⟨g, hg⟩ := not_forall.mp hall
    have hg0 : primeHits (𝔊.group g) v = 0 := by omega
    have h1 : ∏ g : 𝔊.Index, markFactor (q₀ / (j : ℝ)) (𝔊.group g) v = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ g) (markFactor_eq_zero hg0)
    have h2 : ∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) v = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ g) (markFactor_eq_zero hg0)
    rw [h1, h2, mul_zero, mul_zero, zero_mul]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
