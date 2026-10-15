module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.DyadicMass

/-!
# The block sieve for shifted sums

The block sieve (`BlockSieve`, [P] Lemma 2.6) is stated for a finite set of weighted objects and
abstract "bad" conditions. This file specializes it to the shifted sums of [P] §7
(`[P-07:0196–0211, 0653–0662]`): the objects are the integers `u`, the weight is
`Φ(u/x) 1_{u+1 ≡ b (H)} F(u)` with `F ≥ 0`, the bad condition at a prime `p ≤ z` is `p ∣ u + 1`,
and the density is `g(p) = 1/p` for `p ∤ H`, `g(p) = 0` for `p ∣ H` (`[PUB-tex:0523–0525]`).

* `sievePrimes z`: the primes `p ≤ z`; `sieveDensity H p`; `isRough_iff`: `P⁻(v) > z` iff no
  designated prime divides `v`.
* `prod_sieveDensity`: `∏_{p ∈ D} g(p) = 1_{(∏D, H) = 1} / ∏D`.
* `exists_block_density`: `∑_{w < p ≤ w²} g(p) ≤ C₀` for all `w > 1` ("its reciprocal mass in every
  block `(b, b²]` is bounded by an absolute constant by Lemma 2.1"), from Mertens' estimate
  (`exists_reciprocal_window`).
* `siftedWeight_eq_shiftSum`, `sieveWeight_eq_shiftSum`: the sifted weight is the shifted sum over
  `P⁻(u+1) > z`, and the weight on the conditions of `D` is the shifted sum over `∏D ∣ u + 1`.
* `sieveRemainderSum_le`: the sieve remainder up to `y` is at most the sum over all `1 ≤ r ≤ y` of
  `|∑_{r ∣ u+1, u+1 ≡ b (H)} Φ(u/x) F(u) - 1_{(r,H)=1} X/r|` ("the sieve remainder is bounded by
  the sum in Lemma 7.2"; `D ↦ ∏D` is injective on sets of primes).
* `shiftSum_sieve`: **the two conclusions of the block sieve for shifted sums**, with a constant
  `M_s ≥ 0` and a depth `h₀` that depend on nothing.
* `eventually_sieveProduct_le`: `∏_{p ≤ z} (1 - g(p)) · log z ≤ 2^{ω(H)} (e^{-γ} + 1)` for large
  `z`, from Mertens' product theorem.
* `sum_Icc_le_progressionRemainder`: the remainder sums up to `y ≤ x^{c₀}` are at most the left
  side of Lemma 7.2 (`progressionRemainder`); `shiftSum_le_shiftSum_of_imp`.

The declarations are in the namespace `Extraction.Presieve`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Presieve

open Filter
open scoped Topology

noncomputable section

/-! ### The designated primes and the density -/

/-- The designated primes of the presieve: the primes `p ≤ z`. -/
def sievePrimes (z : ℝ) : Finset ℕ := (Finset.Icc 2 ⌊z⌋₊).filter Nat.Prime

theorem mem_sievePrimes {z : ℝ} (hz : 0 ≤ z) {p : ℕ} :
    p ∈ sievePrimes z ↔ p.Prime ∧ (p : ℝ) ≤ z := by
  unfold sievePrimes
  rw [Finset.mem_filter, Finset.mem_Icc, Nat.le_floor_iff hz]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.two_le, h2⟩, h1⟩

/-- The sieve density with the class `u + 1 ≡ b (mod H)`: `g(p) = 1/p` for `p ∤ H` and `0` for
`p ∣ H` (`[PUB-tex:0523–0525]`). -/
def sieveDensity (H p : ℕ) : ℝ := if p ∣ H then 0 else 1 / (p : ℝ)

theorem sieveDensity_nonneg (H p : ℕ) : 0 ≤ sieveDensity H p := by
  unfold sieveDensity
  by_cases h : p ∣ H
  · rw [if_pos h]
  · rw [if_neg h]
    positivity

theorem sieveDensity_le (H p : ℕ) : sieveDensity H p ≤ 1 / (p : ℝ) := by
  unfold sieveDensity
  by_cases h : p ∣ H
  · rw [if_pos h]
    positivity
  · rw [if_neg h]

/-- "The density is at most `1/2`". -/
theorem sieveDensity_le_half (H : ℕ) {p : ℕ} (hp : p.Prime) : sieveDensity H p ≤ 1 - 1 / 2 := by
  have h1 := sieveDensity_le H p
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h3 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- `P⁻(v) > z` iff no prime `p ≤ z` divides `v`. -/
theorem isRough_iff {z : ℝ} (hz : 0 ≤ z) (v : ℕ) :
    IsRough z v ↔ ∀ p ∈ sievePrimes z, ¬ p ∣ v := by
  constructor
  · intro h p hp hdvd
    obtain ⟨hpp, hpz⟩ := (mem_sievePrimes hz).mp hp
    exact absurd (h p hpp hdvd) (not_lt.mpr hpz)
  · intro h p hpp hdvd
    by_contra hcon
    exact h p ((mem_sievePrimes hz).mpr ⟨hpp, not_lt.mp hcon⟩) hdvd

/-- The density is multiplicative on squarefree products: `∏_{p ∈ D} g(p) = 1/∏D` if `∏D` is
coprime to `H`, and `0` otherwise. -/
theorem prod_sieveDensity (H : ℕ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    ∏ p ∈ D, sieveDensity H p =
      if (∏ p ∈ D, p).Coprime H then 1 / ((∏ p ∈ D, p : ℕ) : ℝ) else 0 := by
  by_cases hall : ∀ p ∈ D, ¬ p ∣ H
  · have hco : (∏ p ∈ D, p).Coprime H :=
      Nat.Coprime.prod_left fun p hp => ((hD p hp).coprime_iff_not_dvd).mpr (hall p hp)
    have h1 : ∀ p ∈ D, sieveDensity H p = 1 / (p : ℝ) := fun p hp => by
      unfold sieveDensity
      exact if_neg (hall p hp)
    rw [if_pos hco, Nat.cast_prod, Finset.prod_congr rfl h1, Finset.prod_div_distrib,
      Finset.prod_const_one]
  · obtain ⟨p, hp'⟩ := not_forall.mp hall
    obtain ⟨hp, hpH⟩ := _root_.not_imp.mp hp'
    have hpH' : p ∣ H := not_not.mp hpH
    have hnc : ¬ (∏ p ∈ D, p).Coprime H := fun hco =>
      ((hD p hp).coprime_iff_not_dvd).mp
        (Nat.Coprime.coprime_dvd_left (Finset.dvd_prod_of_mem (fun p' : ℕ => p') hp) hco) hpH'
    rw [if_neg hnc]
    refine Finset.prod_eq_zero hp ?_
    unfold sieveDensity
    exact if_pos hpH'

/-! ### The density in the blocks `(w, w²]` -/

/-- **The reciprocal mass of the density in every block `(w, w²]` is bounded**
(`[P-07:0204–0206]`), from Mertens' estimate for `∑ 1/p`. The constant is absolute. -/
theorem exists_block_density (hM : MertensReciprocal) :
    ∃ C₀ : ℝ, ∀ (z : ℝ) (H : ℕ) (w : ℝ), 1 < w →
      ∑ p ∈ (sievePrimes z).filter (fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ 2),
        sieveDensity H p ≤ C₀ := by
  obtain ⟨C, hC, hwin⟩ := exists_reciprocal_window hM
  refine ⟨max (Real.log 2 + 2 * C) ((⌊Real.exp 2⌋₊ : ℝ) + 1), fun z H w hw => ?_⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ,
      S = (sievePrimes z).filter (fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ 2) := ⟨_, rfl⟩
  rw [← hS]
  have hSmem : ∀ p ∈ S, p.Prime ∧ w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ 2 := by
    intro p hp
    rw [hS] at hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    unfold sievePrimes at h1
    exact ⟨(Finset.mem_filter.mp h1).2, h2⟩
  have hle : ∑ p ∈ S, sieveDensity H p ≤ ∑ p ∈ S, 1 / (p : ℝ) :=
    Finset.sum_le_sum fun p _ => sieveDensity_le H p
  have hw0 : 0 < w := by linarith
  rcases le_or_gt (Real.exp 1) w with hbig | hsmall
  · -- `w ≥ e`: the window `(exp s, exp 2s]`, `s = log w ≥ 1`
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.log w := ⟨_, rfl⟩
    have hs1 : 1 ≤ s := by
      rw [hs]
      exact (Real.le_log_iff_exp_le hw0).mpr hbig
    have hes : Real.exp s = w := by
      rw [hs]
      exact Real.exp_log hw0
    have het : Real.exp (2 * s) = w ^ 2 := by
      have h := Real.exp_nat_mul s 2
      rw [Nat.cast_ofNat] at h
      rw [h, hes]
    have hsub : S ⊆ (Finset.Icc 2 ⌊Real.exp (2 * s)⌋₊).filter Nat.Prime \
        (Finset.Icc 2 ⌊Real.exp s⌋₊).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpp, hlo, hhi⟩ := hSmem p hp
      rw [het, hes]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpp.two_le, Nat.le_floor hhi⟩, hpp⟩, fun h => ?_⟩
      have h0 : p ≤ ⌊w⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).2
      have h1 : (p : ℝ) ≤ w := (Nat.cast_le.mpr h0).trans (Nat.floor_le hw0.le)
      linarith
    have hsum : ∑ p ∈ S, 1 / (p : ℝ) ≤
        ∑ p ∈ (Finset.Icc 2 ⌊Real.exp (2 * s)⌋₊).filter Nat.Prime \
          (Finset.Icc 2 ⌊Real.exp s⌋₊).filter Nat.Prime, 1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
    have hw' := (abs_le.mp (hwin s (2 * s) hs1 (by linarith))).2
    have hlog : Real.log (2 * s) = Real.log 2 + Real.log s :=
      Real.log_mul two_ne_zero (by linarith)
    have hCs : 2 * C / s ≤ 2 * C := div_le_self (by linarith) hs1
    have h3 : ∑ p ∈ S, 1 / (p : ℝ) ≤ Real.log 2 + 2 * C := by linarith
    exact (hle.trans h3).trans (le_max_left _ _)
  · -- `w < e`: all the primes are below `e²`
    have hsub : S ⊆ Finset.range (⌊Real.exp 2⌋₊ + 1) := by
      intro p hp
      obtain ⟨-, -, hhi⟩ := hSmem p hp
      have h2 : w ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ hw0.le hsmall.le 2
      have h3 : Real.exp 1 ^ 2 = Real.exp 2 := by
        rw [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one]
      rw [h3] at h2
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hhi.trans h2)))
    have hterm : ∀ p ∈ S, 1 / (p : ℝ) ≤ 1 := by
      intro p hp
      have h2 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hSmem p hp).1.one_lt.le
      exact (div_le_one (by linarith)).mpr h2
    have hcard : (S.card : ℝ) ≤ (⌊Real.exp 2⌋₊ : ℝ) + 1 := by
      have h := Finset.card_le_card hsub
      rw [Finset.card_range] at h
      exact_mod_cast h
    calc ∑ p ∈ S, sieveDensity H p ≤ ∑ p ∈ S, 1 / (p : ℝ) := hle
      _ ≤ ∑ _p ∈ S, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (⌊Real.exp 2⌋₊ : ℝ) + 1 := hcard
      _ ≤ max (Real.log 2 + 2 * C) ((⌊Real.exp 2⌋₊ : ℝ) + 1) := le_max_right _ _

/-! ### The sieve quantities as shifted sums -/

section Bridge

variable {Φ : ℝ → ℝ} {R x : ℝ}

/-- The sifted weight is the shifted sum over the `u` with `P⁻(u + 1) > z` in the class. -/
theorem siftedWeight_eq_shiftSum (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) {z : ℝ} (hz : 0 ≤ z)
    (H b : ℕ) (F : ℕ → ℝ) {wt : ℕ → ℝ}
    (hwt : ∀ u, wt u = if u + 1 ≡ b [MOD H] then Φ ((u : ℝ) / x) * F u else 0) :
    siftedWeight (Finset.range (⌊R * x⌋₊ + 1)) wt (fun p u => p ∣ u + 1) (sievePrimes z) =
      shiftSum Φ x (fun v => IsRough z v ∧ v ≡ b [MOD H]) F := by
  unfold siftedWeight
  rw [Finset.sum_filter, shiftSum_eq_sum hR hx]
  refine Finset.sum_congr rfl fun u _ => ?_
  beta_reduce
  rw [hwt u]
  by_cases h1 : IsRough z (u + 1)
  · have h1' : ∀ p ∈ sievePrimes z, ¬ p ∣ u + 1 := (isRough_iff hz (u + 1)).mp h1
    by_cases h2 : u + 1 ≡ b [MOD H]
    · have h3 : IsRough z (u + 1) ∧ u + 1 ≡ b [MOD H] := ⟨h1, h2⟩
      rw [if_pos h1', if_pos h2, if_pos h3]
    · have h3 : ¬ (IsRough z (u + 1) ∧ u + 1 ≡ b [MOD H]) := fun h => h2 h.2
      rw [if_pos h1', if_neg h2, if_neg h3]
  · have h1' : ¬ ∀ p ∈ sievePrimes z, ¬ p ∣ u + 1 := fun h =>
      h1 ((isRough_iff hz (u + 1)).mpr h)
    have h3 : ¬ (IsRough z (u + 1) ∧ u + 1 ≡ b [MOD H]) := fun h => h1 h.1
    rw [if_neg h1', if_neg h3]

/-- The weight on the bad conditions at the primes of `D` is the shifted sum over the `u` with
`∏D ∣ u + 1` in the class. -/
theorem sieveWeight_eq_shiftSum (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (H b : ℕ)
    (F : ℕ → ℝ) {wt : ℕ → ℝ}
    (hwt : ∀ u, wt u = if u + 1 ≡ b [MOD H] then Φ ((u : ℝ) / x) * F u else 0)
    {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    sieveWeight (Finset.range (⌊R * x⌋₊ + 1)) wt (fun p u => p ∣ u + 1) D =
      shiftSum Φ x (fun v => (∏ p ∈ D, p) ∣ v ∧ v ≡ b [MOD H]) F := by
  unfold sieveWeight
  rw [Finset.sum_filter, shiftSum_eq_sum hR hx]
  refine Finset.sum_congr rfl fun u _ => ?_
  beta_reduce
  rw [hwt u]
  have hiff : (∀ p ∈ D, p ∣ u + 1) ↔ (∏ p ∈ D, p) ∣ u + 1 :=
    ⟨fun h => Finset.prod_primes_dvd (u + 1) (fun p hp => (hD p hp).prime) h,
      fun h p hp => (Finset.dvd_prod_of_mem (fun p' : ℕ => p') hp).trans h⟩
  by_cases h1 : (∏ p ∈ D, p) ∣ u + 1
  · by_cases h2 : u + 1 ≡ b [MOD H]
    · have h3 : (∏ p ∈ D, p) ∣ u + 1 ∧ u + 1 ≡ b [MOD H] := ⟨h1, h2⟩
      rw [if_pos (hiff.mpr h1), if_pos h2, if_pos h3]
    · have h3 : ¬ ((∏ p ∈ D, p) ∣ u + 1 ∧ u + 1 ≡ b [MOD H]) := fun h => h2 h.2
      rw [if_pos (hiff.mpr h1), if_neg h2, if_neg h3]
  · have h1' : ¬ ∀ p ∈ D, p ∣ u + 1 := fun h => h1 (hiff.mp h)
    have h3 : ¬ ((∏ p ∈ D, p) ∣ u + 1 ∧ u + 1 ≡ b [MOD H]) := fun h => h1 h.1
    rw [if_neg h1', if_neg h3]

/-- **The sieve remainder is bounded by the sum over all moduli** (`[P-07:0206–0211]`): the
squarefree products `∏D ≤ y` of designated primes are distinct integers of `[1, y]`. -/
theorem sieveRemainderSum_le (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) {z : ℝ} (hz : 0 ≤ z)
    (H b : ℕ) (F : ℕ → ℝ) {wt : ℕ → ℝ}
    (hwt : ∀ u, wt u = if u + 1 ≡ b [MOD H] then Φ ((u : ℝ) / x) * F u else 0) (X y : ℝ) :
    sieveRemainderSum (Finset.range (⌊R * x⌋₊ + 1)) wt (fun p u => p ∣ u + 1) X
        (sieveDensity H) (sievePrimes z) y ≤
      ∑ r ∈ Finset.Icc 1 ⌊y⌋₊,
        |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) F -
          (if r.Coprime H then X / (r : ℝ) else 0)| := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, ∀ r, T r =
      |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) F -
        (if r.Coprime H then X / (r : ℝ) else 0)| := ⟨_, fun _ => rfl⟩
  have hprime : ∀ D ∈ (sievePrimes z).powerset, ∀ p ∈ D, p.Prime := fun D hD p hp =>
    ((mem_sievePrimes hz).mp (Finset.mem_powerset.mp hD hp)).1
  have hterm : ∀ D ∈ (sievePrimes z).powerset.filter
        (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ y),
      |sieveRemainder (Finset.range (⌊R * x⌋₊ + 1)) wt (fun p u => p ∣ u + 1) X
        (sieveDensity H) D| = T (∏ p ∈ D, p) := by
    intro D hD
    have hDp := hprime D (Finset.mem_filter.mp hD).1
    unfold sieveRemainder
    rw [hT, sieveWeight_eq_shiftSum hR hx H b F hwt hDp, prod_sieveDensity H hDp]
    by_cases hco : (∏ p ∈ D, p).Coprime H
    · rw [if_pos hco, if_pos hco, mul_one_div]
    · rw [if_neg hco, if_neg hco, mul_zero]
  have hinj : Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p)
      ↑((sievePrimes z).powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ y)) := by
    intro D hD D' hD' heq
    have heq' : ∏ p ∈ D, p = ∏ p ∈ D', p := heq
    calc D = (∏ p ∈ D, p).primeFactors :=
          (Nat.primeFactors_prod (hprime D (Finset.mem_filter.mp (Finset.mem_coe.mp hD)).1)).symm
      _ = (∏ p ∈ D', p).primeFactors := by rw [heq']
      _ = D' := Nat.primeFactors_prod
          (hprime D' (Finset.mem_filter.mp (Finset.mem_coe.mp hD')).1)
  have hsub : ((sievePrimes z).powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ y)).image
      (fun D : Finset ℕ => ∏ p ∈ D, p) ⊆ Finset.Icc 1 ⌊y⌋₊ := by
    intro r hr
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hD1, hD2⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_Icc.mpr
      ⟨Finset.prod_pos fun p hp => (hprime D hD1 p hp).pos, Nat.le_floor hD2⟩
  unfold sieveRemainderSum
  calc ∑ D ∈ (sievePrimes z).powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ y),
        |sieveRemainder (Finset.range (⌊R * x⌋₊ + 1)) wt (fun p u => p ∣ u + 1) X
          (sieveDensity H) D|
      = ∑ D ∈ (sievePrimes z).powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ y),
          T (∏ p ∈ D, p) := Finset.sum_congr rfl hterm
    _ = ∑ r ∈ ((sievePrimes z).powerset.filter
          (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ y)).image (fun D : Finset ℕ => ∏ p ∈ D, p), T r :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ r ∈ Finset.Icc 1 ⌊y⌋₊, T r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => by
          rw [hT r]
          exact abs_nonneg _
    _ = ∑ r ∈ Finset.Icc 1 ⌊y⌋₊,
          |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) F -
            (if r.Coprime H then X / (r : ℝ) else 0)| := Finset.sum_congr rfl fun r _ => hT r

/-- Monotonicity in the predicate on the support of the cutoff. -/
theorem shiftSum_le_shiftSum_of_imp (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x)
    (hΦ0 : ∀ t, 0 ≤ Φ t) {P Q : ℕ → Prop} {g : ℕ → ℝ} (hg : ∀ u, 0 ≤ g u)
    (h : ∀ u : ℕ, P (u + 1) → Φ ((u : ℝ) / x) ≠ 0 → Q (u + 1)) :
    shiftSum Φ x P g ≤ shiftSum Φ x Q g := by
  rw [shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx]
  refine Finset.sum_le_sum fun u _ => ?_
  have hnn : 0 ≤ Φ ((u : ℝ) / x) * g u := mul_nonneg (hΦ0 _) (hg u)
  by_cases hP : P (u + 1)
  · by_cases hΦu : Φ ((u : ℝ) / x) = 0
    · rw [if_pos hP, hΦu, zero_mul]
      by_cases hQ : Q (u + 1)
      · rw [if_pos hQ]
      · rw [if_neg hQ]
    · rw [if_pos hP, if_pos (h u hP hΦu)]
  · rw [if_neg hP]
    by_cases hQ : Q (u + 1)
    · rw [if_pos hQ]
      exact hnn
    · rw [if_neg hQ]

end Bridge

/-! ### The block sieve for shifted sums -/

/-- **The block sieve for shifted sums.** There are an absolute constant `M_s ≥ 0` and a depth
`h₀` such that for every nonnegative cutoff `Φ` vanishing beyond `R`, every `x > 0`, every class
`b (mod H)`, every `F ≥ 0`, every level `z ≥ 1` and every `X ≥ 0`, with
`V = ∏_{p ≤ z} (1 - g(p))`:

* for every even `h ≥ h₀`,
  `|∑_{P⁻(u+1) > z, u+1 ≡ b} Φ(u/x) F(u) - X V| ≤ M_s e^{-h} X V
      + M_s ∑_{r ≤ z^{4h+2}} |∑_{r ∣ u+1, u+1 ≡ b} Φ(u/x) F(u) - 1_{(r,H)=1} X/r|`;
* `∑_{P⁻(u+1) > z, u+1 ≡ b} Φ(u/x) F(u) ≤ M_s X V + M_s ∑_{r ≤ z^{10}} |…|`. -/
theorem shiftSum_sieve (hBS : BlockSieve) (hM : MertensReciprocal) :
    ∃ Ms : ℝ, 0 ≤ Ms ∧ ∃ h₀ : ℕ, ∀ (Φ : ℝ → ℝ) (R : ℝ), (∀ t, R < t → Φ t = 0) →
      (∀ t, 0 ≤ Φ t) → ∀ x : ℝ, 0 < x → ∀ (H b : ℕ) (F : ℕ → ℝ), (∀ u, 0 ≤ F u) →
      ∀ z : ℝ, 1 ≤ z → ∀ X : ℝ, 0 ≤ X →
        (∀ h : ℕ, h₀ ≤ h → Even h →
          |shiftSum Φ x (fun v => IsRough z v ∧ v ≡ b [MOD H]) F -
              X * ∏ p ∈ sievePrimes z, (1 - sieveDensity H p)| ≤
            Ms * Real.exp (-(h : ℝ)) * (X * ∏ p ∈ sievePrimes z, (1 - sieveDensity H p)) +
              Ms * ∑ r ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊,
                |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) F -
                  (if r.Coprime H then X / (r : ℝ) else 0)|) ∧
        shiftSum Φ x (fun v => IsRough z v ∧ v ≡ b [MOD H]) F ≤
          Ms * (X * ∏ p ∈ sievePrimes z, (1 - sieveDensity H p)) +
            Ms * ∑ r ∈ Finset.Icc 1 ⌊z ^ 10⌋₊,
              |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) F -
                (if r.Coprime H then X / (r : ℝ) else 0)| := by
  obtain ⟨C₀, hC₀⟩ := exists_block_density hM
  obtain ⟨M₀, h₀, hsieve⟩ := hBS (1 / 2) C₀ (by norm_num)
  refine ⟨|M₀|, abs_nonneg _, h₀, ?_⟩
  intro Φ R hR hΦ0 x hx H b F hF z hz X hX
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  obtain ⟨wt, hwt⟩ : ∃ wt : ℕ → ℝ,
      ∀ u, wt u = if u + 1 ≡ b [MOD H] then Φ ((u : ℝ) / x) * F u else 0 :=
    ⟨fun u => if u + 1 ≡ b [MOD H] then Φ ((u : ℝ) / x) * F u else 0, fun _ => rfl⟩
  have hwt0 : ∀ u, 0 ≤ wt u := fun u => by
    rw [hwt u]
    by_cases h : u + 1 ≡ b [MOD H]
    · rw [if_pos h]
      exact mul_nonneg (hΦ0 _) (hF u)
    · rw [if_neg h]
  have hprimes : ∀ p ∈ sievePrimes z, p.Prime ∧ (p : ℝ) ≤ z := fun p hp =>
    (mem_sievePrimes hz0).mp hp
  have hg : ∀ p ∈ sievePrimes z, 0 ≤ sieveDensity H p ∧ sieveDensity H p ≤ 1 - 1 / 2 :=
    fun p hp => ⟨sieveDensity_nonneg H p, sieveDensity_le_half H (hprimes p hp).1⟩
  obtain ⟨h1, h2⟩ := hsieve (Finset.range (⌊R * x⌋₊ + 1)) wt (fun u _ => hwt0 u) z
    (sievePrimes z) hz hprimes (fun p u => p ∣ u + 1) X hX (sieveDensity H) hg (hC₀ z H)
  rw [siftedWeight_eq_shiftSum hR hx hz0 H b F hwt] at h1 h2
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∏ p ∈ sievePrimes z, (1 - sieveDensity H p) := ⟨_, rfl⟩
  rw [← hV] at h1 h2 ⊢
  have hV0 : 0 ≤ V := by
    rw [hV]
    refine Finset.prod_nonneg fun p hp => ?_
    have h3 := (hg p hp).2
    linarith
  have hXV : 0 ≤ X * V := mul_nonneg hX hV0
  have hrem : ∀ y : ℝ,
      M₀ * sieveRemainderSum (Finset.range (⌊R * x⌋₊ + 1)) wt (fun p u => p ∣ u + 1) X
        (sieveDensity H) (sievePrimes z) y ≤
      |M₀| * ∑ r ∈ Finset.Icc 1 ⌊y⌋₊,
        |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) F -
          (if r.Coprime H then X / (r : ℝ) else 0)| := by
    intro y
    have h3 := sieveRemainderSum_le hR hx hz0 H b F hwt X y
    have h4 : 0 ≤ sieveRemainderSum (Finset.range (⌊R * x⌋₊ + 1)) wt (fun p u => p ∣ u + 1) X
        (sieveDensity H) (sievePrimes z) y := by
      unfold sieveRemainderSum
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact (mul_le_mul_of_nonneg_right (le_abs_self M₀) h4).trans
      (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
  constructor
  · intro h hh heven
    refine (h1 h hh heven).trans (add_le_add ?_ (hrem _))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self M₀) (Real.exp_pos _).le) hXV
  · refine h2.trans (add_le_add ?_ (hrem _))
    exact mul_le_mul_of_nonneg_right (le_abs_self M₀) hXV

/-! ### Mertens' product for the density -/

/-- `∏_{p ≤ z} (1 - g(p)) · log z ≤ 2^{ω(H)} (e^{-γ} + 1)` for large `z`, from Mertens' product
theorem (`∏_{r' ≤ z} (1 - 1/r') ≍ 1/(γ L)`, `[P-07:0216]`): the factors at the primes dividing `H`
are at least `1/2`. -/
theorem eventually_sieveProduct_le (hMP : MertensProduct) {H : ℕ} (hH : 0 < H) :
    ∀ᶠ z : ℝ in atTop, (∏ p ∈ sievePrimes z, (1 - sieveDensity H p)) * Real.log z ≤
      2 ^ H.primeFactors.card * (Real.exp (-Real.eulerMascheroniConstant) + 1) := by
  have hMP' : Tendsto (fun x : ℝ => Real.log x *
      ∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ)))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := hMP
  have hlt := hMP'.eventually
    (eventually_lt_nhds (lt_add_one (Real.exp (-Real.eulerMascheroniConstant))))
  filter_upwards [hlt, eventually_ge_atTop (1 : ℝ)] with z hz1 hz2
  have hz0 : 0 ≤ z := by linarith
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz2
  obtain ⟨Pg, hPg⟩ : ∃ Pg : ℝ, Pg = ∏ p ∈ sievePrimes z, (1 - sieveDensity H p) := ⟨_, rfl⟩
  obtain ⟨Pf, hPf⟩ : ∃ Pf : ℝ, Pf = ∏ p ∈ sievePrimes z, (1 - 1 / (p : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ,
      Q = ∏ p ∈ (sievePrimes z).filter (fun p => p ∣ H), (1 - 1 / (p : ℝ)) := ⟨_, rfl⟩
  have hfull : Real.log z * Pf < Real.exp (-Real.eulerMascheroniConstant) + 1 := by
    rw [hPf]
    exact hz1
  have hprime : ∀ p ∈ sievePrimes z, p.Prime := fun p hp => ((mem_sievePrimes hz0).mp hp).1
  have hhalf : ∀ p ∈ sievePrimes z, (1 / 2 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).two_le
    have h3 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hPg0 : 0 ≤ Pg := by
    rw [hPg]
    refine Finset.prod_nonneg fun p hp => ?_
    have h3 := sieveDensity_le_half H (hprime p hp)
    linarith
  have hsplit : Pf = Pg * Q := by
    rw [hPf, hPg, hQ, Finset.prod_filter, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    unfold sieveDensity
    by_cases h : p ∣ H
    · rw [if_pos h, if_pos h, sub_zero, one_mul]
    · rw [if_neg h, if_neg h, mul_one]
  have hQ1 : (1 / 2 : ℝ) ^ H.primeFactors.card ≤ Q := by
    have hsub : (sievePrimes z).filter (fun p => p ∣ H) ⊆ H.primeFactors := fun p hp => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hprime p h1, h2, hH.ne'⟩
    calc (1 / 2 : ℝ) ^ H.primeFactors.card
        ≤ (1 / 2 : ℝ) ^ ((sievePrimes z).filter (fun p => p ∣ H)).card :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.card_le_card hsub)
      _ = ∏ _p ∈ (sievePrimes z).filter (fun p => p ∣ H), (1 / 2 : ℝ) :=
          (Finset.prod_const _).symm
      _ ≤ Q := by
          rw [hQ]
          exact Finset.prod_le_prod (fun _ _ => by norm_num)
            (fun p hp => hhalf p (Finset.mem_filter.mp hp).1)
  have h2pos : (0 : ℝ) < 2 ^ H.primeFactors.card := pow_pos zero_lt_two _
  have hkey : Pg * (1 / 2) ^ H.primeFactors.card ≤ Pf := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hQ1 hPg0
  have hPgle : Pg ≤ 2 ^ H.primeFactors.card * Pf := by
    have e : 2 ^ H.primeFactors.card * (Pg * (1 / 2) ^ H.primeFactors.card) = Pg := by
      rw [one_div, inv_pow, mul_comm Pg, ← mul_assoc, mul_inv_cancel₀ h2pos.ne', one_mul]
    have h3 := mul_le_mul_of_nonneg_left hkey h2pos.le
    rw [e] at h3
    exact h3
  rw [← hPg]
  calc Pg * Real.log z ≤ 2 ^ H.primeFactors.card * Pf * Real.log z :=
        mul_le_mul_of_nonneg_right hPgle hlog
    _ = 2 ^ H.primeFactors.card * (Real.log z * Pf) := by ring
    _ ≤ 2 ^ H.primeFactors.card * (Real.exp (-Real.eulerMascheroniConstant) + 1) :=
        mul_le_mul_of_nonneg_left hfull.le h2pos.le

/-! ### The remainder sums and Lemma 7.2 -/

/-- The remainder sum of the sieve up to `y ≤ x^{c₀}` is at most the left side of Lemma 7.2. -/
theorem sum_Icc_le_progressionRemainder {H b : ℕ} {Φ : ℝ → ℝ} {x c₀ y : ℝ}
    (hy : y ≤ x ^ c₀) (f : ℕ → ℝ) (C : ℝ) (W : ℕ → ℝ) (mean : ℝ) {X : ℝ}
    (hX : X = x / (H : ℝ) * (∫ t, Φ t) * C * mean) {F : ℕ → ℝ} (hF : ∀ u, F u = f u * W u) :
    ∑ r ∈ Finset.Icc 1 ⌊y⌋₊,
        |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) F -
          (if r.Coprime H then X / (r : ℝ) else 0)| ≤
      progressionRemainder H b Φ x c₀ f C W mean := by
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.Icc 1 ⌊x ^ c₀⌋₊ :=
    Finset.Icc_subset_Icc_right (Nat.floor_le_floor hy)
  have hterm : ∀ r ∈ Finset.Icc 1 ⌊y⌋₊,
      |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) F -
        (if r.Coprime H then X / (r : ℝ) else 0)| =
      |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) (fun u => f u * W u) -
        (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * C * mean else 0)| := by
    intro r _
    have e : X / (r : ℝ) = x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * C * mean := by
      rw [hX]
      ring
    rw [shiftSum_congr Φ x _ hF, e]
  unfold progressionRemainder
  rw [Finset.sum_congr rfl hterm]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => abs_nonneg _

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Presieve
