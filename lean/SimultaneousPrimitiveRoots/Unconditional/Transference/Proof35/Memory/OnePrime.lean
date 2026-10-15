module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.Statements
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The exact expansion for one big prime: `OnePrimeLifespan`

Source: `verification/stage7-sources/S-02.tex`, lines 327–373 (`[S-02:0327–0373]`),
(eq:prefix-ghost) and (eq:orphan-expansion).

`onePrimeLifespan : OnePrimeLifespan` is proved here: for every skeleton and every `p ≥ 1` with
`b_p ≠ 0`, `onePrimeExp p = b_p · lifeSum p`.

The residue expectation `onePrimeExp p` is the uniform expectation over the residue `t ∈ ℤ/pℤ` of
`(∏_{i active} 1_{-h_i = t}) · ∏_{i inactive} (1 - η_i 1_{-h_i = t})` (`Skel.onePrimeExp_eq_expect`);
the three cases of `Skel.lifeSum` are the three identities of `Graph/`:

* `Graph.primewise_active_lifespan_expectation` — active, compatible offsets (eq:prefix-ghost);
* `Graph.primewise_active_expectation_eq_zero` — "incompatible active offsets give zero";
* `Graph.primewise_orphan_expectation` — never active (eq:orphan-expansion).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- `b · (X / (p b)) = X / p`: the baseline cancels. -/
theorem memId_baseline_cancel {p b : ℝ} (hp : p ≠ 0) (hb : b ≠ 0) (X : ℝ) :
    b * (X / (p * b)) = X / p := by
  rw [mul_div_assoc', div_eq_div_iff (mul_ne_zero hp hb) hp]
  ring

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {D : MemData 𝒢 J ℓ N}

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The product over the visits of the factors of one prime, for the residue `t`: the indicators
of the active visits times the damping of the inactive ones, in the form of `Graph/`. -/
theorem Skel.onePrime_prod (sk : Skel D) (p : ℕ) (t : Res p) :
    (∏ i ∈ Finset.range (D.n + 1),
        if i ∈ sk.activeVisits p then
          (if t + ((sk.off i : ℤ) : Res p) = 0 then (1 : ℝ) else 0)
        else (if t + ((sk.off i : ℤ) : Res p) = 0 then visitQ D.q D.n i else 1)) =
      (∏ i ∈ sk.activeVisits p, if sk.color p i = t then (1 : ℝ) else 0) *
        ∏ i ∈ Finset.range (D.n + 1) \ sk.activeVisits p,
          (1 - Graph.hitWeight (sk.color p) (visitEta D.q D.n) i t) := by
  have hiff : ∀ i : ℕ, (t + ((sk.off i : ℤ) : Res p) = 0) ↔ sk.color p i = t := fun i =>
    eq_neg_iff_add_eq_zero.symm.trans eq_comm
  have hsub : sk.activeVisits p ⊆ Finset.range (D.n + 1) := Finset.filter_subset _ _
  refine (Finset.prod_sdiff hsub).symm.trans (Eq.trans (mul_comm _ _) ?_)
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [if_pos hi]
    by_cases h : sk.color p i = t
    · rw [if_pos ((hiff i).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hiff i).mp h')), if_neg h]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [if_neg (Finset.mem_sdiff.mp hi).2]
    unfold Graph.hitWeight
    by_cases h : sk.color p i = t
    · rw [if_pos ((hiff i).mpr h), if_pos h]
      unfold visitEta
      ring
    · rw [if_neg (fun h' => h ((hiff i).mp h')), if_neg h, sub_zero]

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **The residue expectation of one prime is a uniform expectation over its residue**
[S-02:0327–0334]: "its residue expectation is `p⁻¹ ∏_{i : p ∉ Λ_i} (1 - η_i H_i)`". -/
theorem Skel.onePrimeExp_eq_expect (sk : Skel D) (p : ℕ) (hp : 0 < p) :
    sk.onePrimeExp p =
      𝔼 t : Res p, (∏ i ∈ sk.activeVisits p, if sk.color p i = t then (1 : ℝ) else 0) *
        ∏ i ∈ Finset.range (D.n + 1) \ sk.activeVisits p,
          (1 - Graph.hitWeight (sk.color p) (visitEta D.q D.n) i t) := by
  have hcard : (Fintype.card (Res p) : ℝ) = (p : ℝ) := by rw [Res.card p hp]
  rw [Fintype.expect_eq_sum_div_card, hcard]
  unfold Skel.onePrimeExp
  rw [Finset.sum_congr rfl fun t _ => sk.onePrime_prod p t, inv_mul_eq_div]

/-- **(C2) The exact expansion for one big prime** (eq:prefix-ghost), (eq:orphan-expansion)
[S-02:0327–0373]: `onePrimeExp p = b_p · lifeSum p` for every skeleton and every `p ≥ 1` with
`b_p ≠ 0`. -/
theorem onePrimeLifespan : OnePrimeLifespan := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D sk p hp hb
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hcard : (Fintype.card (Res p) : ℝ) = (p : ℝ) := by rw [Res.card p hp]
  rw [sk.onePrimeExp_eq_expect p hp]
  unfold Skel.lifeSum
  by_cases hne : (sk.activeVisits p).Nonempty
  · rw [dif_pos hne]
    by_cases hcol : ∀ i ∈ sk.activeVisits p,
        sk.color p i = sk.color p ((sk.activeVisits p).min' hne)
    · rw [if_pos hcol]
      -- active, compatible offsets
      have hG := Graph.primewise_active_lifespan_expectation (Finset.range (D.n + 1))
        (sk.activeVisits p) (sk.color p) (visitEta D.q D.n)
        (sk.color p ((sk.activeVisits p).min' hne)) (Finset.min'_mem _ hne)
        (Finset.max'_mem _ hne)
        (fun i hi => ⟨Finset.min'_le _ i hi, Finset.le_max' _ i hi⟩) hcol
      have hG' : (𝔼 t : Res p,
            (∏ i ∈ sk.activeVisits p, if sk.color p i = t then (1 : ℝ) else 0) *
              ∏ i ∈ Finset.range (D.n + 1) \ sk.activeVisits p,
                (1 - Graph.hitWeight (sk.color p) (visitEta D.q D.n) i t)) =
          activeBracket (Finset.range (D.n + 1)) (sk.activeVisits p) (sk.color p)
              (visitEta D.q D.n) (sk.color p ((sk.activeVisits p).min' hne))
              ((sk.activeVisits p).min' hne) ((sk.activeVisits p).max' hne) / (p : ℝ) := by
        rw [← hcard]
        exact hG
      rw [hG']
      exact (memId_baseline_cancel hp' hb _).symm
    · rw [if_neg hcol]
      -- active, incompatible offsets
      obtain ⟨i, hi, hci⟩ : ∃ i ∈ sk.activeVisits p,
          sk.color p i ≠ sk.color p ((sk.activeVisits p).min' hne) := by
        by_contra hcon
        exact hcol fun i hi => not_not.mp fun h => hcon ⟨i, hi, h⟩
      have hG := Graph.primewise_active_expectation_eq_zero (sk.activeVisits p)
        (Finset.range (D.n + 1) \ sk.activeVisits p) (sk.color p) (visitEta D.q D.n) hi
        (Finset.min'_mem _ hne) hci
      rw [mul_zero]
      exact hG
  · rw [dif_neg hne]
    -- never active
    have hA : sk.activeVisits p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hA, Finset.sdiff_empty]
    simp only [Finset.prod_empty, one_mul]
    refine (Graph.primewise_orphan_expectation (Finset.range (D.n + 1)) (sk.color p)
      (visitEta D.q D.n)).trans ?_
    rw [hcard]
    have key : ∀ (b Sη X : ℝ), b = 1 - Sη / (p : ℝ) → b ≠ 0 →
        1 - Sη / (p : ℝ) + X / (p : ℝ) = b * (1 + X / ((p : ℝ) * b)) := by
      intro b Sη X hbe hb0
      rw [mul_add, mul_one, memId_baseline_cancel hp' hb0, hbe]
    exact key (lifeBaseline D.q D.n p) (∑ i ∈ Finset.range (D.n + 1), visitEta D.q D.n i)
      (orphanSum (Finset.range (D.n + 1)) (sk.color p) (visitEta D.q D.n)) rfl hb

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
