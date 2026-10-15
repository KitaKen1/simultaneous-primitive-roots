module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Reduction

/-!
# Proof-internal objects of the prime extraction ([P] §7 with a fixed residue class)

This file defines the objects that occur *inside* the proof of [P] Theorem 7.1
(`verification/stage7-sources/P-07.tex`, lines 56–702) when it is re-run with the class
`p ≡ b (mod H)` as in the public paper (`[PUB-tex:0462–0535]`). The statements of the intermediate
results are in `Extraction/Statements.lean`, the proved chain in `Extraction/Assembly.lean`.

Conventions. `x` is the real parameter, `L = Real.log x`. Every sum over integers is written over
`u ≥ 0` with the *shifted* variable `v = u + 1` (the manuscript's `u = p - 1`, `v = m_1 ⋯ m_j`);
there is no natural subtraction anywhere in this directory.

* `IsCutoff Φ`: a nonnegative `Φ ∈ C_c^∞((0, ∞))` (`[P-07:0019–0023]`).
* `shiftSum Φ x P g = ∑_{u ≥ 0, P(u+1)} Φ(u/x) g(u)`: all the sums of the proof have this form
  (`classPrimeSum_eq_shiftSum` for the prime sum of Theorem 7.1). For `x > 0` it is a finite sum
  (`shiftSum_eq_sum`).
* `modelMean P F`: the independent divisor model `M_x` (`[P-07:0058–0062]`);
  `arrayMean = m_𝒲`, `normWeight = 𝒲 / m_𝒲`, `ArraysDisjoint`, `arrayDeviation = Z_b`
  (`[P-07:0631–0640]`), `pairWeight` (the monomials of Lemma 7.2).
* `progressionRemainder`: the left side of Lemma 7.2 (`[P-07:0082–0089]`) with the class.
* `convPow j a`: the `j`-fold Dirichlet convolution; `primeCoeff`, `proxyCoeff = a(m)`
  (`[P-07:0249–0253]`), `strippedCoeff = ã(m)` (`[P-07:0337–0341]`).
* `candidateGroups x`: the candidate groups of `[P-07:0319–0329]`; `restrictGroups`: an active
  subset as a system of active groups.
* `coinProb = s_g(u, v)` (`[P-07:0390–0396]`), `coinWeight`, `goodSets`, `retainedMass`,
  `failedMass`: the coin partition of `[P-07:0518–0525]`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ### Cutoffs -/

/-- A cutoff of [P] §7: a nonnegative `Φ ∈ C_c^∞((0, ∞))` (`[P-07:0019–0023]`). These are the
four hypotheses on `Φ` in `PrimeStatisticFixedClassAt`. -/
structure IsCutoff (Φ : ℝ → ℝ) : Prop where
  /-- `Φ` is smooth -/
  smooth : ContDiff ℝ ∞ Φ
  /-- `Φ` has compact support -/
  compact : HasCompactSupport Φ
  /-- the support is inside `(0, ∞)` -/
  support : tsupport Φ ⊆ Set.Ioi 0
  /-- `Φ ≥ 0` -/
  nonneg : ∀ t, 0 ≤ Φ t

namespace IsCutoff

variable {Φ : ℝ → ℝ}

/-- `Φ` vanishes beyond some `R > 0`. -/
theorem exists_upper (hΦ : IsCutoff Φ) : ∃ R : ℝ, 0 < R ∧ ∀ t, R < t → Φ t = 0 := by
  obtain ⟨R, hR⟩ := hΦ.compact.isCompact.bddAbove
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun t ht => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have h1 : t ≤ R := hR hmem
  exact absurd ((le_max_left R 1).trans_lt ht) (not_lt.mpr h1)

/-- `Φ` vanishes below some `r > 0`. -/
theorem exists_lower (hΦ : IsCutoff Φ) : ∃ r : ℝ, 0 < r ∧ ∀ t, t < r → Φ t = 0 := by
  have h0 : (0 : ℝ) ∉ tsupport Φ := fun h => lt_irrefl (0 : ℝ) (hΦ.support h)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isClosed_tsupport Φ).isOpen_compl 0 h0
  refine ⟨r, hr, fun t ht => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have htpos : 0 < t := hΦ.support hmem
  have hmem' : t ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact ht
  exact hball hmem' hmem

theorem apply_zero (hΦ : IsCutoff Φ) : Φ 0 = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => lt_irrefl (0 : ℝ) (hΦ.support h)

/-- `Φ` is bounded. -/
theorem exists_bound (hΦ : IsCutoff Φ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, Φ t ≤ B := by
  obtain ⟨B, hB⟩ := hΦ.smooth.continuous.bounded_above_of_compact_support hΦ.compact
  refine ⟨max B 0, le_max_right _ _, fun t => ?_⟩
  have h1 : Φ t ≤ |Φ t| := le_abs_self _
  have h2 : |Φ t| ≤ B := (Real.norm_eq_abs (Φ t)).symm.le.trans (hB t)
  exact h1.trans (h2.trans (le_max_left _ _))

/-- On the support of `u ↦ Φ(u/x)` one has `1 ≤ u ≤ R x`. -/
theorem range_of_ne_zero (hΦ : IsCutoff Φ) {R : ℝ} (hR : ∀ t, R < t → Φ t = 0) {x : ℝ}
    (hx : 0 < x) {u : ℕ} (hu : Φ ((u : ℝ) / x) ≠ 0) : 1 ≤ u ∧ (u : ℝ) ≤ R * x := by
  constructor
  · rcases Nat.eq_zero_or_pos u with h0 | h0
    · exfalso
      apply hu
      rw [h0, Nat.cast_zero, zero_div]
      exact hΦ.apply_zero
    · exact h0
  · by_contra hcon
    rw [not_le] at hcon
    exact hu (hR _ (by rwa [lt_div_iff₀ hx]))

end IsCutoff

/-! ### Shifted sums -/

open _root_.Classical in
/-- `∑_{u ≥ 0, P(u+1)} Φ(u/x) g(u)`: the sum over the integers `u` whose shift `v = u + 1`
satisfies `P`, with the cutoff `Φ(u/x)`. For a cutoff `Φ` the term `u = 0` vanishes (`Φ(0) = 0`),
so this is the manuscript's `∑_{u ≥ 1}`; for `x > 0` only finitely many terms are nonzero
(`shiftSum_eq_sum`). The instances used in the proof:

* `P v = v.Prime ∧ v ≡ b [MOD H]`: sums over primes `p = u + 1` of the class;
* `P v = IsRough z v ∧ v ≡ b [MOD H]`: the presifted sums (`[P-07:0217–0222]`);
* `P v = r ∣ v ∧ v ≡ b [MOD H]`: the progression sums of Lemma 7.2 (`[P-07:0083–0085]`);
* `P v = v ≡ b [MOD H]` and `g u = F u * convPow j a (u + 1)`: the tuple sums
  `∑_{m_1, …, m_j} Φ((m_1 ⋯ m_j - 1)/x) F(m_1 ⋯ m_j - 1) ∏ a(m_i)` (`[P-07:0242–0247]`). -/
def shiftSum (Φ : ℝ → ℝ) (x : ℝ) (P : ℕ → Prop) (g : ℕ → ℝ) : ℝ :=
  ∑ᶠ u : ℕ, if P (u + 1) then Φ ((u : ℝ) / x) * g u else 0

section ShiftSum

variable {Φ : ℝ → ℝ} {R x : ℝ}

open _root_.Classical in
/-- For `x > 0` and `Φ` vanishing beyond `R`, the shifted sum is a finite sum. -/
theorem shiftSum_eq_sum (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (P : ℕ → Prop) (g : ℕ → ℝ) :
    shiftSum Φ x P g =
      ∑ u ∈ Finset.range (⌊R * x⌋₊ + 1), if P (u + 1) then Φ ((u : ℝ) / x) * g u else 0 := by
  unfold shiftSum
  refine finsum_eq_sum_of_support_subset _ fun u hu =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : R * x < (u : ℝ) :=
    lt_of_lt_of_le (Nat.lt_floor_add_one (R * x)) (by exact_mod_cast hcon)
  have h2 : R < (u : ℝ) / x := by rwa [lt_div_iff₀ hx]
  have h3 : (if P (u + 1) then Φ ((u : ℝ) / x) * g u else 0) = 0 := by
    rw [hR _ h2, zero_mul]
    exact ite_self 0
  exact (Function.mem_support.mp hu) h3

theorem shiftSum_congr (Φ : ℝ → ℝ) (x : ℝ) (P : ℕ → Prop) {g g' : ℕ → ℝ}
    (h : ∀ u, g u = g' u) : shiftSum Φ x P g = shiftSum Φ x P g' := by
  have hgg : g = g' := funext h
  rw [hgg]

theorem shiftSum_nonneg (hΦ0 : ∀ t, 0 ≤ Φ t) (P : ℕ → Prop) {g : ℕ → ℝ} (hg : ∀ u, 0 ≤ g u) :
    0 ≤ shiftSum Φ x P g := by
  unfold shiftSum
  refine finsum_nonneg fun u => ?_
  split_ifs
  · exact mul_nonneg (hΦ0 _) (hg u)
  · exact le_rfl

theorem shiftSum_add (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (P : ℕ → Prop) (g₁ g₂ : ℕ → ℝ) :
    shiftSum Φ x P (fun u => g₁ u + g₂ u) = shiftSum Φ x P g₁ + shiftSum Φ x P g₂ := by
  rw [shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs
  · ring
  · ring

theorem shiftSum_sub (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (P : ℕ → Prop) (g₁ g₂ : ℕ → ℝ) :
    shiftSum Φ x P (fun u => g₁ u - g₂ u) = shiftSum Φ x P g₁ - shiftSum Φ x P g₂ := by
  rw [shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs
  · ring
  · ring

theorem shiftSum_const_mul (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (P : ℕ → Prop) (c : ℝ)
    (g : ℕ → ℝ) : shiftSum Φ x P (fun u => c * g u) = c * shiftSum Φ x P g := by
  rw [shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs
  · ring
  · ring

theorem shiftSum_finset_sum (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (P : ℕ → Prop)
    {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℝ) :
    shiftSum Φ x P (fun u => ∑ i ∈ s, g i u) = ∑ i ∈ s, shiftSum Φ x P (g i) := by
  classical
  have h : ∀ i ∈ s, shiftSum Φ x P (g i) =
      ∑ u ∈ Finset.range (⌊R * x⌋₊ + 1), if P (u + 1) then Φ ((u : ℝ) / x) * g i u else 0 :=
    fun i _ => shiftSum_eq_sum hR hx P (g i)
  rw [shiftSum_eq_sum hR hx, Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hP : P (u + 1)
  · rw [if_pos hP, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (if_pos hP).symm
  · rw [if_neg hP]
    exact (Finset.sum_eq_zero fun i _ => if_neg hP).symm

/-- Domination: if `P ⊆ Q`, `g' ≥ 0` and `|g| ≤ B g'` on the part of the support of the cutoff
where `P` holds, then `|∑_P Φ g| ≤ B ∑_Q Φ g'`. -/
theorem abs_shiftSum_le (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (hΦ0 : ∀ t, 0 ≤ Φ t)
    {P Q : ℕ → Prop} (hPQ : ∀ v, P v → Q v) {g g' : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hg' : ∀ u, 0 ≤ g' u)
    (h : ∀ u : ℕ, P (u + 1) → Φ ((u : ℝ) / x) ≠ 0 → |g u| ≤ B * g' u) :
    |shiftSum Φ x P g| ≤ B * shiftSum Φ x Q g' := by
  classical
  rw [shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  by_cases hP : P (u + 1)
  · rw [if_pos hP, if_pos (hPQ _ hP), abs_mul, abs_of_nonneg (hΦ0 _)]
    by_cases hΦu : Φ ((u : ℝ) / x) = 0
    · have e1 : Φ ((u : ℝ) / x) * |g u| = 0 := by rw [hΦu, zero_mul]
      have e2 : B * (Φ ((u : ℝ) / x) * g' u) = 0 := by rw [hΦu, zero_mul, mul_zero]
      exact le_of_eq (e1.trans e2.symm)
    · calc Φ ((u : ℝ) / x) * |g u| ≤ Φ ((u : ℝ) / x) * (B * g' u) :=
            mul_le_mul_of_nonneg_left (h u hP hΦu) (hΦ0 _)
        _ = B * (Φ ((u : ℝ) / x) * g' u) := by ring
  · rw [if_neg hP, abs_zero]
    refine mul_nonneg hB ?_
    split_ifs
    · exact mul_nonneg (hΦ0 _) (hg' u)
    · exact le_rfl

/-- Cauchy–Schwarz for shifted sums with the nonnegative weight `Φ(u/x)`. -/
theorem shiftSum_mul_sq_le (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (P : ℕ → Prop) (f g : ℕ → ℝ) :
    shiftSum Φ x P (fun u => f u * g u) ^ 2 ≤
      shiftSum Φ x P (fun u => f u ^ 2) * shiftSum Φ x P (fun u => g u ^ 2) := by
  classical
  rw [shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx]
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun u _ => ?_) (fun u _ => ?_)
    (fun u _ => ?_)
  · split_ifs
    · exact mul_nonneg (hΦ0 _) (sq_nonneg _)
    · exact le_rfl
  · split_ifs
    · exact mul_nonneg (hΦ0 _) (sq_nonneg _)
    · exact le_rfl
  · split_ifs
    · exact le_of_eq (by ring)
    · exact le_of_eq (by ring)

end ShiftSum

/-- Reindexing `p = u + 1` of a sum over the natural numbers whose term at `0` vanishes. No
finiteness is needed. -/
theorem finsum_nat_succ (F : ℕ → ℝ) (h0 : F 0 = 0) :
    ∑ᶠ p : ℕ, F p = ∑ᶠ u : ℕ, F (u + 1) := by
  have hinter : (Set.univ : Set ℕ) ∩ Function.support F =
      Set.range (fun u : ℕ => u + 1) ∩ Function.support F := by
    ext p
    constructor
    · rintro ⟨_, hp⟩
      refine ⟨?_, hp⟩
      rcases Nat.eq_zero_or_pos p with h | h
      · exfalso
        rw [h] at hp
        exact (Function.mem_support.mp hp) h0
      · exact ⟨p - 1, Nat.sub_add_cancel h⟩
    · rintro ⟨_, hp⟩
      exact ⟨Set.mem_univ p, hp⟩
  calc ∑ᶠ p : ℕ, F p = ∑ᶠ p ∈ (Set.univ : Set ℕ), F p := (finsum_mem_univ F).symm
    _ = ∑ᶠ p ∈ Set.range (fun u : ℕ => u + 1), F p :=
        finsum_mem_inter_support_eq F _ _ hinter
    _ = ∑ᶠ u : ℕ, F (u + 1) := finsum_mem_range (add_left_injective 1)

/-- The prime sum of Theorem 7.1^{H,b} (`classPrimeSum`, a sum over `p`) is the shifted sum over
`u = p - 1` with `P v = v.Prime ∧ v ≡ b [MOD H]`. No hypothesis is needed: the term `p = 0` of
`classPrimeSum` vanishes. -/
theorem classPrimeSum_eq_shiftSum {d : ℕ} (H b : ℕ) (Φ : ℝ → ℝ) (S : Fin d → Finset ℕ) (x : ℝ) :
    classPrimeSum H b Φ S x =
      shiftSum Φ x (fun v => v.Prime ∧ v ≡ b [MOD H])
        (fun u => (slotCount S u : ℝ) - slotMass S) := by
  unfold classPrimeSum shiftSum
  refine (finsum_nat_succ _ ?_).trans (finsum_congr fun u => ?_)
  · exact if_neg fun h => Nat.not_prime_zero h.1
  · have h1 : (((u + 1 : ℕ) : ℝ) - 1) = (u : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    have h2 : u + 1 - 1 = u := Nat.add_sub_cancel u 1
    rw [h1, h2]
    by_cases hc : (u + 1).Prime ∧ u + 1 ≡ b [MOD H]
    · exact (if_pos hc).trans (if_pos hc).symm
    · exact (if_neg hc).trans (if_neg hc).symm

/-! ### The independent divisor model and the marking arrays -/

/-- The primes of all the bands of a marking array. -/
def arrayPrimes {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) : Finset ℕ :=
  Finset.univ.biUnion fun i : Fin K => bandPrimes (𝔞.exponent i) x

/-- **The independent divisor model** (`[P-07:0058–0062]`): the expectation `M_x(F)` of a function
`F` of the divisibility indicators `1_{p ∣ u}`, `p ∈ P`, when these are replaced by independent
Bernoulli variables of mean `1/p`.

A configuration is the set `T ⊆ P` of the primes that "divide"; it has probability
`∏_{p ∈ T} 1/p · ∏_{p ∈ P ∖ T} (1 - 1/p)`, and the function is evaluated at the integer
`∏_{p ∈ T} p`, whose divisibility pattern on `P` is `T` when `P` consists of primes. The definition
is meant for functions with `F(u) = F(∏_{p ∈ P, p ∣ u} p)`, such as the marked weights of arrays
whose bands lie in `P`. The total mass is one (`modelMean_const`). -/
def modelMean (P : Finset ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ T ∈ P.powerset,
    (∏ p ∈ T, (1 / (p : ℝ))) * (∏ p ∈ P \ T, (1 - 1 / (p : ℝ))) * F (∏ p ∈ T, p)

/-- The model is a probability: `M_x(c) = c`. -/
theorem modelMean_const (P : Finset ℕ) (c : ℝ) : modelMean P (fun _ => c) = c := by
  unfold modelMean
  rw [← Finset.sum_mul, ← Finset.prod_add]
  have h : ∀ p ∈ P, (1 / (p : ℝ) + (1 - 1 / (p : ℝ))) = 1 := fun p _ => by ring
  rw [Finset.prod_congr rfl h, Finset.prod_const_one, one_mul]

/-- The model expectation is linear. -/
theorem modelMean_add (P : Finset ℕ) (F G : ℕ → ℝ) :
    modelMean P (fun n => F n + G n) = modelMean P F + modelMean P G := by
  unfold modelMean
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ => by ring

theorem modelMean_const_mul (P : Finset ℕ) (c : ℝ) (F : ℕ → ℝ) :
    modelMean P (fun n => c * F n) = c * modelMean P F := by
  unfold modelMean
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun T _ => by ring

/-- `m_𝒲 = M_x(𝒲)`, the model mean of the weight of an array (`[P-07:0062]`). -/
def arrayMean (q : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) : ℝ :=
  modelMean (arrayPrimes 𝔞 x) (markedWeight q 𝔞 x)

/-- The normalized weight `𝒲(u) / m_𝒲` of (ext:weighted-primes) `[P-07:0622–0628]`. It is `0` by
convention if `m_𝒲 = 0`; `ModelBounds` says `m_𝒲 ≥ c_K > 0` for large `x`. -/
def normWeight (q : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (u : ℕ) : ℝ :=
  markedWeight q 𝔞 x u / arrayMean q 𝔞 x

/-- **Disjoint arrays** (`[P-07:0631–0634]`): `n` arrays of `K` bands each, "using distinct
exponents across all arrays". For large `x` the bands of distinct exponents are pairwise disjoint.
A single array is a disjoint family (`arraysDisjoint_single` in `Assembly.lean`). -/
def ArraysDisjoint {n K : ℕ} (𝔄 : Fin n → MarkingArray K) : Prop :=
  Function.Injective fun p : Fin n × Fin K => (𝔄 p.1).exponent p.2

/-- The primes of all the bands of all the arrays of a family. -/
def familyPrimes {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ) : Finset ℕ :=
  Finset.univ.biUnion fun a : Fin n => arrayPrimes (𝔄 a) x

/-- `Z(u) = ((1/n) ∑_a 𝒲_a(u) / m_a - 1)²` (`[P-07:0637–0640]`, (ext:deweight-square); the
manuscript's number of arrays `b` is `n` here, `b` being the residue class). -/
def arrayDeviation (q : ℝ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ) (u : ℕ) : ℝ :=
  ((∑ a, normWeight q (𝔄 a) x u) / (n : ℝ) - 1) ^ 2

/-- The weight of the array `a` of a family, or the constant `1` for `a = none`. -/
def optWeight (q : ℝ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ) (a : Option (Fin n))
    (u : ℕ) : ℝ :=
  a.elim 1 fun a => markedWeight q (𝔄 a) x u

/-- The monomials of Lemma 7.2 (`[P-07:0078–0081]`): "a weight from a fixed finite collection of
disjoint arrays, a product of two such weights (allowing a repeated array), a constant".
`pairWeight q 𝔄 x none none = 1`, `pairWeight q 𝔄 x (some a) none = 𝒲_a`,
`pairWeight q 𝔄 x (some a) (some a') = 𝒲_a 𝒲_{a'}`. -/
def pairWeight (q : ℝ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ) (a a' : Option (Fin n))
    (u : ℕ) : ℝ :=
  optWeight q 𝔄 x a u * optWeight q 𝔄 x a' u

theorem markFactor_nonneg {q : ℝ} (hq : 0 ≤ q) (S : Finset ℕ) (n : ℕ) :
    0 ≤ markFactor q S n := by
  unfold markFactor
  have hV : 0 ≤ reciprocalMass S := by
    unfold reciprocalMass
    exact Finset.sum_nonneg fun p _ => by positivity
  exact div_nonneg (mul_nonneg (pow_nonneg hq _) (Nat.cast_nonneg _)) hV

theorem markedWeight_nonneg {q : ℝ} (hq : 0 ≤ q) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (n : ℕ) :
    0 ≤ markedWeight q 𝔞 x n := by
  unfold markedWeight
  exact Finset.prod_nonneg fun i _ => markFactor_nonneg hq _ n

/-! ### The progression sums of Lemma 7.2 -/

/-- The left side of (ext:progression) (`[P-07:0082–0089]`) with the class `u + 1 ≡ b (mod H)`
(`[PUB-tex:0518–0522]`):

`∑_{1 ≤ r ≤ x^{c₀}} | ∑_{u ≥ 1, r ∣ u+1, u+1 ≡ b (H)} Φ(u/x) f(u) W(u)
    - 1_{(r,H)=1} · x/(H r) · (∫ Φ) · C · mean |`.

Here `f`, `C` are the tuple statistic and its mean (`f_x`, `C_x`, or `1`, `1`), `W` is the array
function and `mean = M_x(W)`. For `(r, H) > 1` the two conditions are incompatible when
`(b, H) = 1`, and the main term is `0`; for `(r, H) = 1` they are one class modulo `H r`. -/
def progressionRemainder (H b : ℕ) (Φ : ℝ → ℝ) (x c₀ : ℝ) (f : ℕ → ℝ) (C : ℝ) (W : ℕ → ℝ)
    (mean : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊,
    |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) (fun u => f u * W u) -
      (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * C * mean else 0)|

/-! ### Tuple sums: convolution powers and the three coefficients -/

/-- The `j`-fold Dirichlet convolution `(a * ⋯ * a)(v) = ∑_{e_1 ⋯ e_j = v} ∏_i a(e_i)`. With it,
`∑_{m_1, …, m_j} Φ((m_1 ⋯ m_j - 1)/x) F(m_1 ⋯ m_j - 1) ∏_i a(m_i)` is
`shiftSum Φ x (fun _ => True) (fun u => F u * convPow j a (u + 1))`. -/
def convPow (j : ℕ) (a : ℕ → ℝ) (v : ℕ) : ℝ :=
  ∑ e ∈ orderedFactorizations j v, ∏ i, a (e i)

theorem convPow_nonneg {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m) (j v : ℕ) : 0 ≤ convPow j a v :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => ha _

open _root_.Classical in
/-- The indicator of the primes `> z`: the coefficient of the prime variables in
(ext:composite-vanishing) `[P-07:0242–0247]`. -/
def primeCoeff (z : ℝ) (m : ℕ) : ℝ := if m.Prime ∧ z < (m : ℝ) then 1 else 0

open _root_.Classical in
/-- The proxy coefficient `a(m) = 1_{m > z} 1_{P⁻(m) > W} κ(m)`, `z = x^γ`
(`[P-07:0249–0253]`, (ext:proxy-weight)). -/
def proxyCoeff (x γ : ℝ) (m : ℕ) : ℝ :=
  if x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m then proxyKappa x m else 0

open _root_.Classical in
/-- The stripped coefficient `ã(m) = 1_{P⁻(m) > W} 1_{m̄ > x^γ} κ(m̄)`, where `m̄` removes the
entire prime-power parts of `m` at the primes of `candidates`
(`[P-07:0335–0341]`, (ext:stripped-coefficient)). The allocation core of `Reduction.lean` is its
convolution power at `v_*` (`allocationCore_eq_convPow`). -/
def strippedCoeff (x γ : ℝ) (candidates : Finset ℕ) (m : ℕ) : ℝ :=
  if IsRough (roughCutoff x) m ∧ x ^ γ < (freePart candidates m : ℝ) then
    proxyKappa x (freePart candidates m) else 0

/-- `G_P(v) = (ã * ⋯ * ã)(v_*)`: the allocation core (`[P-07:0559–0565]`) is the `j`-fold
convolution of the stripped coefficient at the active-free part of `v`. -/
theorem allocationCore_eq_convPow (x γ : ℝ) (j : ℕ) (candidates active : Finset ℕ) (v : ℕ) :
    allocationCore x γ j candidates active v =
      convPow j (strippedCoeff x γ candidates) (freePart active v) :=
  rfl

theorem mertensProduct_pos (y : ℝ) : 0 < mertensProduct y := by
  unfold mertensProduct
  refine Finset.prod_pos fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
  have h : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  linarith

/-- `κ ≥ 0` (with no hypothesis on `x`: `V(W) > 0` always). -/
theorem proxyKappa_nonneg (x : ℝ) (m : ℕ) : 0 ≤ proxyKappa x m := by
  unfold proxyKappa
  split_ifs with h
  · have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    exact div_nonneg zero_le_one (mul_nonneg (mertensProduct_pos _).le (Real.log_nonneg hm))
  · exact le_rfl

theorem primeCoeff_nonneg (z : ℝ) (m : ℕ) : 0 ≤ primeCoeff z m := by
  unfold primeCoeff
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem proxyCoeff_nonneg (x γ : ℝ) (m : ℕ) : 0 ≤ proxyCoeff x γ m := by
  unfold proxyCoeff
  split_ifs
  · exact proxyKappa_nonneg _ _
  · exact le_rfl

theorem strippedCoeff_nonneg (x γ : ℝ) (candidates : Finset ℕ) (m : ℕ) :
    0 ≤ strippedCoeff x γ candidates m := by
  unfold strippedCoeff
  split_ifs
  · exact proxyKappa_nonneg _ _
  · exact le_rfl

/-! ### Candidate groups -/

/-- The number of consecutive bands `[exp(y), exp(2y))`, `y = 2^k L^{lo}`, `k = 0, 1, …`, with
`2y ≤ L^{hi}` (`[P-07:0319–0323]`: "starting at `y = L^{lo}` and doubling `y` while
`2y ≤ L^{hi}`"): `k` is allowed iff `2^{k+1} ≤ L^{hi - lo}`, i.e. `k + 1 ≤ (hi - lo) log L / log 2`.
The floor is the natural floor, so the count is `0` when `log L ≤ 0`. -/
def candidateCount (lo hi x : ℝ) : ℕ :=
  ⌊(hi - lo) * Real.log (Real.log x) / Real.log 2⌋₊

/-- The primes of the band `[exp(2^k L^{lo}), exp(2^{k+1} L^{lo}))` (`[P-07:0320–0321]`). -/
def candidateBand (lo x : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.range ⌈Real.exp (2 ^ (k + 1) * Real.log x ^ lo)⌉₊).filter fun p : ℕ =>
    p.Prime ∧ Real.exp (2 ^ k * Real.log x ^ lo) ≤ (p : ℝ)

theorem mem_candidateBand {lo x : ℝ} {k p : ℕ} :
    p ∈ candidateBand lo x k ↔
      p.Prime ∧ Real.exp (2 ^ k * Real.log x ^ lo) ≤ (p : ℝ) ∧
        (p : ℝ) < Real.exp (2 ^ (k + 1) * Real.log x ^ lo) := by
  unfold candidateBand
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
  tauto

/-- **The candidate groups** `𝒞` of `[P-07:0319–0329]`: the small groups are the bands starting at
`y = L^{0.28}` while `2y ≤ L^{0.35}`, the big groups the bands starting at `y = L^{0.40}` while
`2y ≤ L^{0.45}`. They are packaged as a system of active groups of [P] §6 (`ActiveGroups`). -/
def candidateGroups (x : ℝ) : ActiveGroups where
  numSmall := candidateCount 0.28 0.35 x
  numBig := candidateCount 0.4 0.45 x
  group := Sum.elim (fun i => candidateBand 0.28 x i.val) (fun i => candidateBand 0.4 x i.val)

/-- All candidate primes, active or not: the primes removed by the bar `m ↦ m̄`
(`[P-07:0335–0336]`). -/
def candidatePrimes (x : ℝ) : Finset ℕ := (candidateGroups x).allPrimes

/-- The sub-system of a system of groups given by a set `P` of indices: its small (big) groups are
the small (big) groups with index in `P`, listed in increasing order of the index. This is how an
active set `P = S ∪ T ⊆ 𝒞` of `[P-07:0527–0535]` is a system of active groups of Theorem 6.1. -/
def restrictGroups (𝔊 : ActiveGroups) (P : Finset 𝔊.Index) : ActiveGroups where
  numSmall := P.toLeft.card
  numBig := P.toRight.card
  group := Sum.elim (fun i => 𝔊.group (Sum.inl (P.toLeft.orderEmbOfFin rfl i)))
    (fun i => 𝔊.group (Sum.inr (P.toRight.orderEmbOfFin rfl i)))

/-! ### The success coins -/

/-- The success probability of the coin of the group `g` at the integer `u` (with `v = u + 1`):
`s_g(u, v) = c₁ q₀^{ω_g(u)-1} ω_g(u)/V_g · (q₀/j)^{ω_g(v)-1} ω_g(v)/V_g`
(`[P-07:0390–0396]`, (ext:success-probability)). "The factors with no hit are interpreted as
zero": this is the convention of `markFactor`. -/
def coinProb (𝔊 : ActiveGroups) (c₁ q₀ : ℝ) (j : ℕ) (u : ℕ) (g : 𝔊.Index) : ℝ :=
  c₁ * markFactor q₀ (𝔊.group g) u * markFactor (q₀ / (j : ℝ)) (𝔊.group g) (u + 1)

/-- The weight `∏_{g ∈ S} s_g ∏_{g ∉ S} (1 - s_g)` of the outcome "exactly the coins of `S`
succeed" (`[P-07:0519–0523]`). -/
def coinWeight (𝔊 : ActiveGroups) (s : 𝔊.Index → ℝ) (S : Finset 𝔊.Index) : ℝ :=
  (∏ g ∈ S, s g) * ∏ g ∈ Sᶜ, (1 - s g)

open _root_.Classical in
/-- The outcomes with at least `c₂ log L` successes of each kind (`[P-07:0404–0407, 0524]`). -/
def goodSets (𝔊 : ActiveGroups) (c₂ x : ℝ) : Finset (Finset 𝔊.Index) :=
  Finset.univ.filter fun S : Finset 𝔊.Index =>
    c₂ * Real.log (Real.log x) ≤ (S.toLeft.card : ℝ) ∧
      c₂ * Real.log (Real.log x) ≤ (S.toRight.card : ℝ)

/-- The total coin weight at `u` of the outcomes that are retained. -/
def retainedMass (𝔊 : ActiveGroups) (c₁ c₂ q₀ : ℝ) (j : ℕ) (x : ℝ) (u : ℕ) : ℝ :=
  ∑ S ∈ goodSets 𝔊 c₂ x, coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S

/-- The total coin weight at `u` of the failed outcomes: fewer than `c₂ log L` successes in
either family. -/
def failedMass (𝔊 : ActiveGroups) (c₁ c₂ q₀ : ℝ) (j : ℕ) (x : ℝ) (u : ℕ) : ℝ :=
  ∑ S ∈ (goodSets 𝔊 c₂ x)ᶜ, coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S

/-- The coin partition `1 = ∑_{S ⊆ 𝒞} ∏_{g ∈ S} s_g ∏_{g ∉ S} (1 - s_g)` (`[P-07:0519–0523]`),
for arbitrary real `s_g`. -/
theorem sum_coinWeight (𝔊 : ActiveGroups) (s : 𝔊.Index → ℝ) :
    ∑ S : Finset 𝔊.Index, coinWeight 𝔊 s S = 1 := by
  unfold coinWeight
  rw [← Fintype.prod_add]
  exact Finset.prod_eq_one fun g _ => by ring

/-- Retained and failed outcomes partition the coin measure. -/
theorem retainedMass_add_failedMass (𝔊 : ActiveGroups) (c₁ c₂ q₀ : ℝ) (j : ℕ) (x : ℝ) (u : ℕ) :
    retainedMass 𝔊 c₁ c₂ q₀ j x u + failedMass 𝔊 c₁ c₂ q₀ j x u = 1 := by
  unfold retainedMass failedMass
  rw [Finset.sum_add_sum_compl]
  exact sum_coinWeight 𝔊 _

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
