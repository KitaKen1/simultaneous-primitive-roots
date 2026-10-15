module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ModelVarianceProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SlotBound
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.DivisorModelTruncation

/-!
# The array monomials and the model with forced absences

Facts about the monomials `W ∈ {1, 𝒲_a, 𝒲_a 𝒲_{a'}}` of [P] Lemma 7.2 and about the independent
divisor model that are used in its proof (`[P-07:0095–0192]`).

* `abs_modelMean_le`: `|M_P(G)| ≤ sup |G|`.
* `abs_modelMean_union_sub_le`: **forced absence** (`[P-07:0182–0188]`: "coupling the
  forced-absence model to the unconditional one and using the boundedness of `H` bounds their mean
  difference by `O(∑_{p ∣ r} 1/p)`"): `|M_{P ∪ B}(G) - M_P(G)| ≤ 2 sup|G| ∑_{p ∈ B} 1/p`, one
  prime at a time (`modelMean_insert`).
* `pairWeight_congr`: a monomial depends on `u` only through the set of the primes of the family
  that divide `u`; `abs_pairWeight_le`: it is bounded by `max(1, C_𝒲)²`.
* The primes of the family: `mem_familyPrimes`, `familyPrimes_facts`
  (`exp(L^{.1}) ≤ p ≤ exp(2 L^{.2})`), `reciprocalMass_familyPrimes_le`.
* `sum_inv_le_of_primes_dvd`: the primes `p ≥ y` of a set `B` that divide `r` satisfy
  `∑ 1/p ≤ |B|/y` and `y^{|B|} ≤ r`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression

noncomputable section

/-! ### The model -/

/-- `|M_P(G)| ≤ H_b` when `|G| ≤ H_b`. -/
theorem abs_modelMean_le {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) {G : ℕ → ℝ} {Hb : ℝ}
    (hG : ∀ n, |G n| ≤ Hb) : |modelMean P G| ≤ Hb := by
  have h1 := modelMean_le_of_le hP (F := G) (G := fun _ => Hb)
    fun n => (le_abs_self _).trans (hG n)
  have h2 := modelMean_le_of_le hP (F := fun _ => -Hb) (G := G) fun n => by
    have h3 := neg_abs_le (G n)
    have h4 := hG n
    linarith
  rw [modelMean_const] at h1 h2
  exact abs_le.mpr ⟨h2, h1⟩

/-- Adding one prime `p` to the model changes the mean of a bounded function by at most
`2 H_b / p`. -/
theorem abs_modelMean_insert_sub_le {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) {p : ℕ} (hp : p ∉ P)
    {G : ℕ → ℝ} {Hb : ℝ} (hG : ∀ n, |G n| ≤ Hb) :
    |modelMean (insert p P) G - modelMean P G| ≤ 2 * Hb * (1 / (p : ℝ)) := by
  have h1 : |modelMean P G| ≤ Hb := abs_modelMean_le hP hG
  have h2 : |modelMean P fun n => G (p * n)| ≤ Hb :=
    abs_modelMean_le hP (G := fun n => G (p * n)) fun n => hG (p * n)
  have e : (1 - 1 / (p : ℝ)) * modelMean P G +
      1 / (p : ℝ) * modelMean P (fun n => G (p * n)) - modelMean P G =
      1 / (p : ℝ) * (modelMean P (fun n => G (p * n)) - modelMean P G) := by ring
  have h0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have h3 := abs_sub (modelMean P fun n => G (p * n)) (modelMean P G)
  rw [modelMean_insert hp G, e, abs_mul, abs_of_nonneg h0]
  calc 1 / (p : ℝ) * |modelMean P (fun n => G (p * n)) - modelMean P G|
      ≤ 1 / (p : ℝ) * (2 * Hb) := mul_le_mul_of_nonneg_left (by linarith) h0
    _ = 2 * Hb * (1 / (p : ℝ)) := by ring

/-- **Forced absence** (`[P-07:0182–0188]`): the model on `P ∪ B` and the model on `P` (the primes
of `B` are absent) differ on a function bounded by `H_b` by at most `2 H_b ∑_{p ∈ B} 1/p`. -/
theorem abs_modelMean_union_sub_le {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) {G : ℕ → ℝ} {Hb : ℝ}
    (hG : ∀ n, |G n| ≤ Hb) (B : Finset ℕ) :
    Disjoint P B → (∀ p ∈ B, 1 ≤ p) →
      |modelMean (P ∪ B) G - modelMean P G| ≤ 2 * Hb * ∑ p ∈ B, 1 / (p : ℝ) := by
  induction B using Finset.induction_on with
  | empty =>
    intro _ _
    rw [Finset.union_empty, sub_self, abs_zero, Finset.sum_empty, mul_zero]
  | @insert p B' hp ih =>
    intro hdisj hB
    have hdisj' : Disjoint P B' :=
      Finset.disjoint_of_subset_right (Finset.subset_insert p B') hdisj
    have hB' : ∀ p' ∈ B', 1 ≤ p' := fun p' hp' => hB p' (Finset.mem_insert_of_mem hp')
    have hpP : p ∉ P := Finset.disjoint_right.mp hdisj (Finset.mem_insert_self p B')
    have hpU : p ∉ P ∪ B' := fun h => (Finset.mem_union.mp h).elim hpP hp
    have hU1 : ∀ p' ∈ P ∪ B', 1 ≤ p' := fun p' hp' =>
      (Finset.mem_union.mp hp').elim (hP p') (hB' p')
    have h1 := abs_modelMean_insert_sub_le hU1 hpU hG
    have h2 := ih hdisj' hB'
    have h3 : modelMean (insert p (P ∪ B')) G - modelMean P G =
        (modelMean (insert p (P ∪ B')) G - modelMean (P ∪ B') G) +
          (modelMean (P ∪ B') G - modelMean P G) := by ring
    rw [Finset.union_insert, Finset.sum_insert hp, mul_add, h3]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-! ### The monomials -/

/-- The weight of an array depends on `u` only through the primes of its bands that divide
`u`. -/
theorem markedWeight_congr (q : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) {u u' : ℕ}
    (h : ∀ p ∈ arrayPrimes 𝔞 x, (p ∣ u ↔ p ∣ u')) :
    markedWeight q 𝔞 x u = markedWeight q 𝔞 x u' := by
  have hband : ∀ i : Fin K, (bandPrimes (𝔞.exponent i) x).filter (fun p => p ∣ u) =
      (bandPrimes (𝔞.exponent i) x).filter (fun p => p ∣ u') := fun i =>
    Finset.filter_congr fun p hp => h p (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩)
  unfold markedWeight markFactor primeHits
  exact Finset.prod_congr rfl fun i _ => by rw [hband i]

/-- A monomial of Lemma 7.2 depends on `u` only through the primes of the family that divide
`u`. -/
theorem pairWeight_congr (q : ℝ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ)
    (a a' : Option (Fin n)) {u u' : ℕ} (h : ∀ p ∈ familyPrimes 𝔄 x, (p ∣ u ↔ p ∣ u')) :
    pairWeight q 𝔄 x a a' u = pairWeight q 𝔄 x a a' u' := by
  have hopt : ∀ c : Option (Fin n), optWeight q 𝔄 x c u = optWeight q 𝔄 x c u' := by
    intro c
    cases c with
    | none => rfl
    | some c =>
      exact markedWeight_congr q (𝔄 c) x fun p hp =>
        h p (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hp⟩)
  unfold pairWeight
  rw [hopt a, hopt a']

/-- A monomial is bounded by `max(1, C_𝒲)²` when the array weights are bounded by `C_𝒲`. -/
theorem abs_pairWeight_le {q : ℝ} {n K : ℕ} {𝔄 : Fin n → MarkingArray K} {x CW : ℝ}
    (hW : ∀ c : Fin n, ∀ u : ℕ, |markedWeight q (𝔄 c) x u| ≤ CW) (a a' : Option (Fin n))
    (u : ℕ) : |pairWeight q 𝔄 x a a' u| ≤ max 1 CW * max 1 CW := by
  have hopt : ∀ c : Option (Fin n), |optWeight q 𝔄 x c u| ≤ max 1 CW := by
    intro c
    cases c with
    | none =>
      show |(1 : ℝ)| ≤ max 1 CW
      rw [abs_one]
      exact le_max_left _ _
    | some c => exact (hW c u).trans (le_max_right _ _)
  unfold pairWeight
  rw [abs_mul]
  exact mul_le_mul (hopt a) (hopt a') (abs_nonneg _) (zero_le_one.trans (le_max_left _ _))

/-! ### The primes of the family -/

theorem mem_familyPrimes {n K : ℕ} {𝔄 : Fin n → MarkingArray K} {x : ℝ} {p : ℕ} :
    p ∈ familyPrimes 𝔄 x ↔
      ∃ a : Fin n, ∃ i : Fin K, p ∈ bandPrimes ((𝔄 a).exponent i) x := by
  unfold familyPrimes arrayPrimes
  constructor
  · intro h
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp ha
    exact ⟨a, i, hi⟩
  · rintro ⟨a, i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a,
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩⟩

/-- The primes of the family are primes between `exp(L^{.1})` and `exp(2 L^{.2})`
(`[P-07:0041–0042]`), once `L ≥ 1`. -/
theorem familyPrimes_facts {n K : ℕ} (𝔄 : Fin n → MarkingArray K) {x : ℝ}
    (hL1 : 1 ≤ Real.log x) {p : ℕ} (hp : p ∈ familyPrimes 𝔄 x) :
    p.Prime ∧ Real.exp (Real.log x ^ (1 / 10 : ℝ)) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) := by
  obtain ⟨a, i, hpi⟩ := mem_familyPrimes.mp hp
  obtain ⟨hpp, hlo, hhi⟩ := mem_bandPrimes.mp hpi
  have h1 : Real.log x ^ (1 / 10 : ℝ) ≤ Real.log x ^ (𝔄 a).exponent i :=
    Real.rpow_le_rpow_of_exponent_le hL1 ((𝔄 a).gt_tenth i).le
  have h2 : Real.log x ^ (𝔄 a).exponent i ≤ Real.log x ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 ((𝔄 a).lt_fifth i).le
  exact ⟨hpp, (Real.exp_le_exp.mpr h1).trans hlo,
    hhi.trans (Real.exp_le_exp.mpr (by linarith))⟩

/-- The reciprocal mass of the primes of the family is at most `n K V` when every band has
reciprocal mass at most `V`. -/
theorem reciprocalMass_familyPrimes_le {n K : ℕ} (𝔄 : Fin n → MarkingArray K) {x V : ℝ}
    (hV : ∀ a : Fin n, ∀ i : Fin K, reciprocalMass (bandPrimes ((𝔄 a).exponent i) x) ≤ V) :
    reciprocalMass (familyPrimes 𝔄 x) ≤ (n : ℝ) * ((K : ℝ) * V) := by
  have harr : ∀ a : Fin n, reciprocalMass (arrayPrimes (𝔄 a) x) ≤ (K : ℝ) * V := by
    intro a
    unfold arrayPrimes
    calc reciprocalMass (Finset.univ.biUnion fun i : Fin K => bandPrimes ((𝔄 a).exponent i) x)
        ≤ ∑ i : Fin K, reciprocalMass (bandPrimes ((𝔄 a).exponent i) x) :=
          EndpointProof.reciprocalMass_biUnion_le _ _
      _ ≤ ∑ _i : Fin K, V := Finset.sum_le_sum fun i _ => hV a i
      _ = (K : ℝ) * V := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold familyPrimes
  calc reciprocalMass (Finset.univ.biUnion fun a : Fin n => arrayPrimes (𝔄 a) x)
      ≤ ∑ a : Fin n, reciprocalMass (arrayPrimes (𝔄 a) x) :=
        EndpointProof.reciprocalMass_biUnion_le _ _
    _ ≤ ∑ _a : Fin n, (K : ℝ) * V := Finset.sum_le_sum fun a _ => harr a
    _ = (n : ℝ) * ((K : ℝ) * V) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The reciprocal mass is monotone. -/
theorem reciprocalMass_mono {A B : Finset ℕ} (h : A ⊆ B) :
    reciprocalMass A ≤ reciprocalMass B := by
  unfold reciprocalMass
  exact Finset.sum_le_sum_of_subset_of_nonneg h fun p _ _ =>
    div_nonneg zero_le_one (Nat.cast_nonneg p)

/-- Primes `p ≥ y > 0` of a set `B` that all divide `r ≥ 1`: `∑_{p ∈ B} 1/p ≤ |B|/y` and
`y^{|B|} ≤ r`. -/
theorem sum_inv_le_of_primes_dvd {B : Finset ℕ} {y : ℝ} {r : ℕ} (hy : 0 < y) (hr : 1 ≤ r)
    (hprime : ∀ p ∈ B, p.Prime) (hdvd : ∀ p ∈ B, p ∣ r) (hlow : ∀ p ∈ B, y ≤ (p : ℝ)) :
    ∑ p ∈ B, 1 / (p : ℝ) ≤ (B.card : ℝ) / y ∧ y ^ B.card ≤ (r : ℝ) := by
  refine ⟨?_, pow_card_le_of_primes_dvd hy.le hr hprime hdvd hlow⟩
  calc ∑ p ∈ B, 1 / (p : ℝ) ≤ ∑ _p ∈ B, 1 / y :=
        Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le hy (hlow p hp)
    _ = (B.card : ℝ) / y := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression
