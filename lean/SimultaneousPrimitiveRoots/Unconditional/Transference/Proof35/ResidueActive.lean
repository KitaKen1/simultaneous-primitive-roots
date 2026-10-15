module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The proof of [S] Lemma 3.6, part 4: the path factor is a product of local factors

Source: `verification/stage7-sources/S-02.tex`, lines 226–231 and 244–262
(`[S-02:0226–0231, 0244–0262]`).

* `localFactor q n Λ h p u` — the factor of (eq:path-residue-factor) at the group prime `p`, as a
  function of the residue `u` modulo `p`:
  `∏_{i ≤ n} (1_{u + h_i = 0} if p ∈ Λ_i, q_i^{1_{u + h_i = 0}} otherwise)`.
* `pathFactor_resModel_eq`, `pathFactor_intPos_eq_prod` — (eq:path-residue-factor) is the product
  of the local factors over all group primes, at the residues `y_p`, respectively `n mod p`
  (`pathFactor_intPos_eq`: the integer position `n` and the residue position `(n mod p)_p` give the
  same factor).
* `resAvg_prod` — independence: the expectation of a product of functions of the single residues
  is the product of their means.
* `localFactor_nonneg`, `localFactor_le_one`, `sum_one_sub_localFactor_le` — `0 ≤ localFactor ≤ 1`,
  and for a prime which is active at no visit, `∑_u (1 - localFactor(u)) ≤ n + 1`: "its factor has
  the form `1 - X_p(n)`, `X_p(n) = ∑_r c_{p,r} 1_{n ≡ r (p)}`, `0 ≤ c_{p,r} ≤ 1`, with at most
  `N + 1` residues" [S-02:0255–0262]. Repeated offsets (and offsets which agree modulo `p`) are
  collected automatically: the bound is for the sum over the residues.
* `activeSet`, `card_activeSet_le` — the active primes: "there are at most `(N + 1) M s` of them"
  [S-02:0245–0246].
* `prime_of_mem_allPrimes`, `le_of_mem_allPrimes`, `mem_allPrimes_le`, `sum_inv_allPrimes_le` — the
  group primes are primes in `[exp(L^a), exp(L^d)]` with `∑ 1/p ≤ s v₊`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl

open scoped BigOperators

noncomputable section

/-! ### The local factors and the product formula -/

/-- The factor of (eq:path-residue-factor) [S-02:0226–0231] at the prime `p`, as a function of
the residue `u` of the position modulo `p`. -/
def localFactor (q : ℝ) (n : ℕ) (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ) (p : ℕ) (u : Res p) : ℝ :=
  ∏ i ∈ Finset.range (n + 1),
    if p ∈ Λ i then (if u + (h i : Res p) = 0 then 1 else 0)
    else (if u + (h i : Res p) = 0 then visitQ q n i else 1)

open _root_.Classical in
/-- `countHits` only depends on the predicate on the given set. -/
theorem countHits_congr {hit₁ hit₂ : ℕ → Prop} {s : Finset ℕ} (h : ∀ p ∈ s, hit₁ p ↔ hit₂ p) :
    countHits hit₁ s = countHits hit₂ s := by
  unfold countHits
  congr 1
  exact Finset.filter_congr h

open _root_.Classical in
/-- `countHits` on a subset of `Q`, counted in the subtype of `Q`. -/
theorem countHits_eq_card_subtype {Q s : Finset ℕ} (hit : ℕ → Prop)
    (P : {p : ℕ // p ∈ Q} → Prop) [DecidablePred P] (hs : s ⊆ Q)
    (h : ∀ p : {p : ℕ // p ∈ Q}, P p ↔ (p.1 ∈ s ∧ hit p.1)) :
    countHits hit s = (Finset.univ.filter P).card := by
  unfold countHits
  refine (Finset.card_bij (fun (p : {p : ℕ // p ∈ Q}) _ => p.1) ?_ ?_ ?_).symm
  · intro p hp
    have hp' := (h p).mp (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr hp'
  · intro p₁ _ p₂ _ h12
    exact Subtype.ext h12
  · intro p' hp'
    have hp'' := Finset.mem_filter.mp hp'
    exact ⟨⟨p', hs hp''.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h ⟨p', hs hp''.1⟩).mpr hp''⟩, rfl⟩

/-- One visit: the indicator of the active congruences times the damping factor is a product
over the primes of `Q`. The decidability instance of the condition is arbitrary. -/
theorem visit_factor_eq {Q L : Finset ℕ} (hL : L ⊆ Q) (w : ResVec Q) (c : ℝ)
    {inst : Decidable (∀ p ∈ L, ∃ hp : p ∈ Q, w ⟨p, hp⟩ = 0)} :
    (@ite ℝ (∀ p ∈ L, ∃ hp : p ∈ Q, w ⟨p, hp⟩ = 0) inst
        (c ^ countHits (fun p => ∃ hp : p ∈ Q, w ⟨p, hp⟩ = 0) (Q \ L)) 0) =
      ∏ p : {p : ℕ // p ∈ Q},
        if p.1 ∈ L then (if w p = 0 then (1 : ℝ) else 0) else (if w p = 0 then c else 1) := by
  by_cases hall : ∀ p ∈ L, ∃ hp : p ∈ Q, w ⟨p, hp⟩ = 0
  · rw [if_pos hall]
    have hfac : ∀ p : {p : ℕ // p ∈ Q},
        (if p.1 ∈ L then (if w p = 0 then (1 : ℝ) else 0) else (if w p = 0 then c else 1)) =
          if (p.1 ∉ L ∧ w p = 0) then c else 1 := by
      intro p
      by_cases hpL : p.1 ∈ L
      · obtain ⟨hp, h0⟩ := hall p.1 hpL
        have h0' : w p = 0 := h0
        simp [hpL, h0']
      · by_cases h0 : w p = 0
        · simp [hpL, h0]
        · simp [hpL, h0]
    rw [Finset.prod_congr rfl fun p _ => hfac p, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
    congr 1
    refine countHits_eq_card_subtype _ _ Finset.sdiff_subset fun p => ?_
    constructor
    · rintro ⟨hpL, h0⟩
      exact ⟨Finset.mem_sdiff.mpr ⟨p.2, hpL⟩, p.2, h0⟩
    · rintro ⟨hpQL, _, h0⟩
      exact ⟨(Finset.mem_sdiff.mp hpQL).2, h0⟩
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨p, hpL, hne⟩ := hall
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨p, hL hpL⟩ : {p : ℕ // p ∈ Q})) ?_
    have hne' := hne (hL hpL)
    simp [hpL, hne']

/-- **(eq:path-residue-factor) in the residue model is a product over the group primes**
[S-02:0226–0231]. -/
theorem pathFactor_resModel_eq (Q : Finset ℕ) (q : ℝ) (n : ℕ) (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ)
    (hΛ : ∀ i, Λ i ⊆ Q) (y : ResVec Q) :
    pathFactor (resModel Q) Q q n Λ h y =
      ∏ p : {p : ℕ // p ∈ Q}, localFactor q n Λ h p.1 (y p) := by
  unfold pathFactor localFactor
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact visit_factor_eq (hΛ i) (fun p => y p + (h i : Res p.1)) (visitQ q n i)

/-- The integer position `k` and the residue position `(k mod p)_{p ∈ Q}` have the same factor
(eq:path-residue-factor): it only reads the divisibility of `k + h_i` by the primes of `Q`. -/
theorem pathFactor_intPos_eq (Q : Finset ℕ) (q : ℝ) (n : ℕ) (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ)
    (hQ : ∀ p ∈ Q, 0 < p) (hΛ : ∀ i, Λ i ⊆ Q) (k : ℤ) :
    pathFactor intPos Q q n Λ h k =
      pathFactor (resModel Q) Q q n Λ h (fun p => (k : Res p.1)) := by
  unfold pathFactor
  refine Finset.prod_congr rfl fun i _ => ?_
  have key : ∀ p ∈ Q, (intPos.hit p (intPos.shift (h i) k) ↔
      (resModel Q).hit p ((resModel Q).shift (h i) (fun p => (k : Res p.1)))) := by
    intro p hp
    show ((p : ℤ) ∣ k + h i) ↔ ∃ _ : p ∈ Q, (k : Res p) + (h i : Res p) = 0
    rw [← Res.intCast_eq_zero_iff p (hQ p hp) (k + h i), Int.cast_add]
    exact ⟨fun h0 => ⟨hp, h0⟩, fun ⟨_, h0⟩ => h0⟩
  have hcount : countHits (fun p => intPos.hit p (intPos.shift (h i) k)) (Q \ Λ i) =
      countHits (fun p => (resModel Q).hit p
        ((resModel Q).shift (h i) (fun p => (k : Res p.1)))) (Q \ Λ i) :=
    countHits_congr fun p hp => key p (Finset.mem_sdiff.mp hp).1
  by_cases hc : ∀ p ∈ Λ i, intPos.hit p (intPos.shift (h i) k)
  · have hc' : ∀ p ∈ Λ i, (resModel Q).hit p
        ((resModel Q).shift (h i) (fun p => (k : Res p.1))) :=
      fun p hp => (key p (hΛ i hp)).mp (hc p hp)
    rw [if_pos hc, if_pos hc', hcount]
  · have hc' : ¬∀ p ∈ Λ i, (resModel Q).hit p
        ((resModel Q).shift (h i) (fun p => (k : Res p.1))) :=
      fun H => hc fun p hp => (key p (hΛ i hp)).mpr (H p hp)
    rw [if_neg hc, if_neg hc']

/-- **(eq:path-residue-factor) at an integer position is the product of the local factors at the
residues of the position.** -/
theorem pathFactor_intPos_eq_prod (Q : Finset ℕ) (q : ℝ) (n : ℕ) (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ)
    (hQ : ∀ p ∈ Q, 0 < p) (hΛ : ∀ i, Λ i ⊆ Q) (k : ℤ) :
    pathFactor intPos Q q n Λ h k =
      ∏ p : {p : ℕ // p ∈ Q}, localFactor q n Λ h p.1 (k : Res p.1) := by
  rw [pathFactor_intPos_eq Q q n Λ h hQ hΛ k, pathFactor_resModel_eq Q q n Λ h hΛ]

/-- **Independence**: the expectation of a product of functions of the single residues is the
product of their means [S-02:0238–0240]. -/
theorem resAvg_prod (Q : Finset ℕ) (φ : (p : {p : ℕ // p ∈ Q}) → Res p.1 → ℝ) :
    resAvg Q (fun y => ∏ p, φ p (y p)) =
      ∏ p : {p : ℕ // p ∈ Q}, ((∑ u : Res p.1, φ p u) / ((p.1 - 1 + 1 : ℕ) : ℝ)) := by
  have hcard : (Fintype.card (ResVec Q) : ℝ) =
      ∏ p : {p : ℕ // p ∈ Q}, ((p.1 - 1 + 1 : ℕ) : ℝ) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    exact Finset.prod_congr rfl fun p _ => by rw [ZMod.card]
  unfold resAvg
  rw [hcard, ← Fintype.prod_sum, Finset.prod_div_distrib, div_eq_inv_mul]

/-! ### Bounds for the local factors -/

theorem visitQ_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n i : ℕ) : 0 ≤ visitQ q n i :=
  (Graph.source_ghost_visit_range q (visitQ q n i) hq0 hq1 (visitQ_eq q n i)).1

theorem visitQ_le_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n i : ℕ) : visitQ q n i ≤ 1 :=
  (Graph.source_ghost_visit_range q (visitQ q n i) hq0 hq1 (visitQ_eq q n i)).2.1

theorem localFactor_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) (Λ : ℕ → Finset ℕ)
    (h : ℕ → ℤ) (p : ℕ) (u : Res p) : 0 ≤ localFactor q n Λ h p u := by
  unfold localFactor
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact visitQ_nonneg hq0 hq1 n i
  · exact zero_le_one

theorem localFactor_le_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) (Λ : ℕ → Finset ℕ)
    (h : ℕ → ℤ) (p : ℕ) (u : Res p) : localFactor q n Λ h p u ≤ 1 := by
  unfold localFactor
  refine Finset.prod_le_one (fun i _ => ?_) fun i _ => ?_
  · split_ifs
    · exact zero_le_one
    · exact le_rfl
    · exact visitQ_nonneg hq0 hq1 n i
    · exact zero_le_one
  · split_ifs
    · exact le_rfl
    · exact zero_le_one
    · exact visitQ_le_one hq0 hq1 n i
    · exact le_rfl

/-- `1 - ∏ a_i ≤ ∑ (1 - a_i)` for numbers in `[0,1]`. -/
theorem one_sub_prod_le {α : Type*} [DecidableEq α] (s : Finset α) (a : α → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have h0' : ∀ i ∈ s, 0 ≤ a i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ s, a i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih h0' h1'
    have hP1 : ∏ i ∈ s, a i ≤ 1 := Finset.prod_le_one h0' h1'
    have hj1 := h1 j (Finset.mem_insert_self j s)
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    nlinarith [mul_nonneg (sub_nonneg.mpr hj1) (sub_nonneg.mpr hP1)]

/-- **A prime which is active at no visit** [S-02:0255–0262]: its factor is `1 - X_p` with
`∑_u X_p(u) ≤ n + 1` (the number of visits; at each visit at most one residue is damped). -/
theorem sum_one_sub_localFactor_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ)
    (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ) (p : ℕ) (hp : ∀ i ∈ Finset.range (n + 1), p ∉ Λ i) :
    ∑ u : Res p, (1 - localFactor q n Λ h p u) ≤ (n : ℝ) + 1 := by
  have hterm : ∀ u : Res p, 1 - localFactor q n Λ h p u ≤
      ∑ i ∈ Finset.range (n + 1), if u + (h i : Res p) = 0 then (1 : ℝ) else 0 := by
    intro u
    have heq : localFactor q n Λ h p u =
        ∏ i ∈ Finset.range (n + 1), if u + (h i : Res p) = 0 then visitQ q n i else 1 := by
      unfold localFactor
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [if_neg (hp i hi)]
    rw [heq]
    refine (one_sub_prod_le _ _ ?_ ?_).trans (Finset.sum_le_sum fun i _ => ?_)
    · intro i _
      split_ifs
      · exact visitQ_nonneg hq0 hq1 n i
      · exact zero_le_one
    · intro i _
      split_ifs
      · exact visitQ_le_one hq0 hq1 n i
      · exact le_rfl
    · split_ifs
      · linarith [visitQ_nonneg hq0 hq1 n i]
      · linarith
  calc ∑ u : Res p, (1 - localFactor q n Λ h p u)
      ≤ ∑ u : Res p, ∑ i ∈ Finset.range (n + 1),
          if u + (h i : Res p) = 0 then (1 : ℝ) else 0 :=
        Finset.sum_le_sum fun u _ => hterm u
    _ = ∑ i ∈ Finset.range (n + 1), ∑ u : Res p,
          if u + (h i : Res p) = 0 then (1 : ℝ) else 0 := Finset.sum_comm
    _ = ∑ _i ∈ Finset.range (n + 1), (1 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single (-(h i : Res p))]
        · rw [if_pos (neg_add_cancel _)]
        · intro u _ hu
          rw [if_neg fun h0 => hu (eq_neg_of_add_eq_zero_left h0)]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
    _ = (n : ℝ) + 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        push_cast
        ring

/-! ### The active primes -/

/-- The primes of `Q` which are active at some visit `0, …, n`, as elements of the index type. -/
def activeSet (Q : Finset ℕ) (n : ℕ) (Λ : ℕ → Finset ℕ) : Finset {p : ℕ // p ∈ Q} :=
  Finset.univ.filter fun p => p.1 ∈ (Finset.range (n + 1)).biUnion Λ

theorem notMem_of_notMem_activeSet {Q : Finset ℕ} {n : ℕ} {Λ : ℕ → Finset ℕ}
    {p : {p : ℕ // p ∈ Q}} (hp : p ∉ activeSet Q n Λ) :
    ∀ i ∈ Finset.range (n + 1), p.1 ∉ Λ i := fun i hi hpi =>
  hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨i, hi, hpi⟩⟩)

/-- "There are at most `(N + 1) M s` of them" [S-02:0245–0246]. -/
theorem card_activeSet_le (Q : Finset ℕ) (n : ℕ) (Λ : ℕ → Finset ℕ) (c : ℕ)
    (hc : ∀ i, (Λ i).card ≤ c) : (activeSet Q n Λ).card ≤ (n + 1) * c := by
  have h1 : (activeSet Q n Λ).card ≤ ((Finset.range (n + 1)).biUnion Λ).card := by
    refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ Subtype.val_injective.injOn
    intro p hp
    exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
  calc (activeSet Q n Λ).card ≤ ((Finset.range (n + 1)).biUnion Λ).card := h1
    _ ≤ ∑ i ∈ Finset.range (n + 1), (Λ i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (n + 1), c := Finset.sum_le_sum fun i _ => hc i
    _ = (n + 1) * c := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ### The group primes -/

section Groups

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B]

theorem mem_allPrimes_iff (𝒢 : GroupFamily S B) (p : ℕ) :
    p ∈ 𝒢.allPrimes ↔ (∃ g, p ∈ 𝒢.small g) ∨ ∃ g, p ∈ 𝒢.big g := by
  unfold GroupFamily.allPrimes
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]

theorem prime_of_mem_allPrimes (𝔊 : PrimeGroups P x S B) {p : ℕ} (hp : p ∈ 𝔊.allPrimes) :
    p.Prime := by
  rcases (mem_allPrimes_iff 𝔊.toGroupFamily p).mp hp with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact 𝔊.prime_small g p hg
  · exact 𝔊.prime_big g p hg

/-- Every group prime is at least `exp(L^a)` (for `L ≥ 1`). -/
theorem le_of_mem_allPrimes (𝔊 : PrimeGroups P x S B) (hL : 1 ≤ Real.log x) {p : ℕ}
    (hp : p ∈ 𝔊.allPrimes) : Real.exp (Real.log x ^ P.a) ≤ (p : ℝ) := by
  rcases (mem_allPrimes_iff 𝔊.toGroupFamily p).mp hp with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact 𝔊.small_ge g p hg
  · have hac : P.a ≤ P.c := (P.a_lt_b.trans P.b_lt_c).le
    exact (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL hac)).trans
      (𝔊.big_ge g p hg)

/-- Every group prime is at most `exp(L^d)` (for `L ≥ 1`). -/
theorem mem_allPrimes_le (𝔊 : PrimeGroups P x S B) (hL : 1 ≤ Real.log x) {p : ℕ}
    (hp : p ∈ 𝔊.allPrimes) : (p : ℝ) ≤ Real.exp (Real.log x ^ P.d) := by
  rcases (mem_allPrimes_iff 𝔊.toGroupFamily p).mp hp with ⟨g, hg⟩ | ⟨g, hg⟩
  · have hbd : P.b ≤ P.d := (P.b_lt_c.trans P.c_lt_d).le
    exact (𝔊.small_le g p hg).trans
      (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL hbd))
  · exact 𝔊.big_le g p hg

/-- `∑_p 1/p ≤ s v₊` over all group primes [S-02:0264–0265]. -/
theorem sum_inv_allPrimes_le (𝔊 : PrimeGroups P x S B) :
    ∑ p ∈ 𝔊.allPrimes, 1 / (p : ℝ) ≤ (groupCount S B : ℝ) * P.vPlus := by
  unfold GroupFamily.allPrimes
  have hunion : (∑ p ∈ Finset.univ.biUnion 𝔊.small ∪ Finset.univ.biUnion 𝔊.big, 1 / (p : ℝ)) +
      ∑ p ∈ Finset.univ.biUnion 𝔊.small ∩ Finset.univ.biUnion 𝔊.big, 1 / (p : ℝ) =
      ∑ p ∈ Finset.univ.biUnion 𝔊.small, 1 / (p : ℝ) +
        ∑ p ∈ Finset.univ.biUnion 𝔊.big, 1 / (p : ℝ) := Finset.sum_union_inter
  have hinter : 0 ≤ ∑ p ∈ Finset.univ.biUnion 𝔊.small ∩ Finset.univ.biUnion 𝔊.big,
      1 / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
  have hsmall : ∑ p ∈ Finset.univ.biUnion 𝔊.small, 1 / (p : ℝ) ≤
      (Fintype.card S : ℝ) * P.vPlus := by
    rw [Finset.sum_biUnion fun g _ g' _ hne => 𝔊.disjoint_small g g' hne]
    calc ∑ g, ∑ p ∈ 𝔊.small g, 1 / (p : ℝ) ≤ ∑ _g : S, P.vPlus :=
          Finset.sum_le_sum fun g _ => 𝔊.mass_small_le g
      _ = (Fintype.card S : ℝ) * P.vPlus := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hbig : ∑ p ∈ Finset.univ.biUnion 𝔊.big, 1 / (p : ℝ) ≤
      (Fintype.card B : ℝ) * P.vPlus := by
    rw [Finset.sum_biUnion fun g _ g' _ hne => 𝔊.disjoint_big g g' hne]
    calc ∑ g, ∑ p ∈ 𝔊.big g, 1 / (p : ℝ) ≤ ∑ _g : B, P.vPlus :=
          Finset.sum_le_sum fun g _ => 𝔊.mass_big_le g
      _ = (Fintype.card B : ℝ) * P.vPlus := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcount : (groupCount S B : ℝ) = (Fintype.card S : ℝ) + (Fintype.card B : ℝ) := by
    unfold groupCount
    push_cast
    ring
  rw [hcount]
  linarith

end Groups

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl
