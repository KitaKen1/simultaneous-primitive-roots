module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.ShRow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 3.10: the two changes are negligible in operator norm

Source: `verification/stage7-sources/S-02.tex`, lines 981–1012 (`[S-02:0981–1012]`).

"… with two changes only: the measures of active labels and fresh target integrations are `μ̃_g`
in place of `μ_g`, and the free/active collision ban remains in force. Both changes are negligible
in operator norm. … For the ban, in either row direction condition on the fixed active state. Each
free auxiliary draw has maximal atom `O(1/P_*)`; its chance to match a fixed active label is
bounded by that quantity. … There are `O_{J,m}(s)` possible comparisons. Reversal has the same
estimate."

* `cleanBan`, `cleanBanInd` — no auxiliary free label occurs in a big list, and its indicator.
* `clean_sum_aux_banInd` — the probability that the ban holds for a fixed list is a product over
  the auxiliary labels; `clean_ban_prob_ge` — it is at least `1 - m|ℬ| · |ℬ| M μ_*`, where `μ_*`
  bounds the atoms of the laws `μ_g`.
* `cleanShRow_perturb` — **the perturbation estimate**: if the multiplier `Φ` of a row operation
  with the ideal transition law is bounded by `c₀`, then multiplying it by the indicators of the
  ban for the source and for the target list and by a function `ρ(target)` with `|ρ - 1| ≤ ε₁`
  changes the operator by at most `c₀ (ε₁ + 2 √ε₂)` in `ℋ_id`, `ε₂ = m|ℬ| · |ℬ| M μ_*`.

The estimate for the ban differs from the text in one point: the banned transitions are split
into those in which an auxiliary label meets the *source* list and the remaining ones, in which it
meets the *target* list. For the first operator the row sums are small and the column sums are at
most one; for the second the converse holds. Schur's test gives `√ε₂` for each (instead of `ε₂`
for the sum), which is still `o(L^{-A})`; no joint law of an auxiliary label and a fresh target
label is needed.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

section Ban

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- **The ban of the auxiliary free labels from a big list** [S-02:0109–0111, 0983–0985]: no
auxiliary label of `D` occurs in the list. -/
def cleanBan (C : B → Finset (Fin J)) (r : AuxList big C) (x : LabelList big J ℓ) : Prop :=
  ∀ (g : B) (i : {i : Fin J // i ∈ C g}) (g' : B) (s : Slot J ℓ), (x g' s : ℕ) ≠ (r g i : ℕ)

open _root_.Classical in
/-- The indicator of the ban. -/
def cleanBanInd (C : B → Finset (Fin J)) (r : AuxList big C) (x : LabelList big J ℓ) : ℝ :=
  if cleanBan C r x then 1 else 0

open _root_.Classical in
/-- The indicator that the number `v` is none of the labels of the list. -/
def cleanHitInd (x : LabelList big J ℓ) (v : ℕ) : ℝ :=
  if ∀ (g' : B) (s : Slot J ℓ), (x g' s : ℕ) ≠ v then 1 else 0

omit [Fintype B] [DecidableEq B] in
theorem cleanBanInd_nonneg (C : B → Finset (Fin J)) (r : AuxList big C)
    (x : LabelList big J ℓ) : 0 ≤ cleanBanInd C r x := by
  unfold cleanBanInd
  split_ifs
  · exact zero_le_one
  · exact le_rfl

omit [Fintype B] [DecidableEq B] in
theorem cleanBanInd_le_one (C : B → Finset (Fin J)) (r : AuxList big C)
    (x : LabelList big J ℓ) : cleanBanInd C r x ≤ 1 := by
  unfold cleanBanInd
  split_ifs
  · exact le_rfl
  · exact zero_le_one

omit [DecidableEq B] in
/-- The indicator of the ban is the product of the indicators of the single auxiliary labels. -/
theorem cleanBanInd_eq_prod (C : B → Finset (Fin J)) (r : AuxList big C)
    (x : LabelList big J ℓ) :
    cleanBanInd C r x = ∏ g, ∏ i : {i : Fin J // i ∈ C g}, cleanHitInd x (r g i : ℕ) := by
  by_cases h : cleanBan C r x
  · have e : cleanBanInd C r x = 1 := if_pos h
    rw [e]
    symm
    refine Finset.prod_eq_one fun g _ => Finset.prod_eq_one fun i _ => ?_
    exact if_pos (h g i)
  · have e : cleanBanInd C r x = 0 := if_neg h
    rw [e]
    symm
    obtain ⟨g, hg⟩ := not_forall.mp h
    obtain ⟨i, hi⟩ := not_forall.mp hg
    exact Finset.prod_eq_zero (Finset.mem_univ g)
      (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi))

/-- **The probability of the ban for a fixed list is a product over the auxiliary labels**: the
auxiliary labels are independent. -/
theorem clean_sum_aux_banInd (C : B → Finset (Fin J)) (x : LabelList big J ℓ) :
    ∑ r : AuxList big C, auxWeight big C r * cleanBanInd C r x =
      ∏ g, ∏ _i : {i : Fin J // i ∈ C g}, ∑ p : {p : ℕ // p ∈ big g},
        Graph.primeGroupLaw (big g) p * cleanHitInd x (p : ℕ) := by
  have hterm : ∀ r : AuxList big C, auxWeight big C r * cleanBanInd C r x =
      ∏ g, ∏ i : {i : Fin J // i ∈ C g},
        (Graph.primeGroupLaw (big g) (r g i) * cleanHitInd x (r g i : ℕ)) := by
    intro r
    rw [cleanBanInd_eq_prod]
    unfold auxWeight
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => Finset.prod_mul_distrib.symm
  rw [Finset.sum_congr rfl fun r _ => hterm r,
    ← Fintype.prod_sum (fun (g : B) (φ : {i : Fin J // i ∈ C g} → {q : ℕ // q ∈ big g}) =>
      ∏ i, (Graph.primeGroupLaw (big g) (φ i) * cleanHitInd x (φ i : ℕ)))]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [← Fintype.prod_sum (fun (_ : {i : Fin J // i ∈ C g}) (q : {q : ℕ // q ∈ big g}) =>
    Graph.primeGroupLaw (big g) q * cleanHitInd x (q : ℕ))]

/-- The mass of one value under a law with atoms at most `μ_*`. -/
theorem clean_sum_law_eq_le {s : Finset ℕ} {μs : ℝ} (hμ0 : 0 ≤ μs)
    (hμ : ∀ p ∈ s, Graph.primeGroupLaw s p ≤ μs) (v : ℕ) :
    ∑ p : {p : ℕ // p ∈ s},
        Graph.primeGroupLaw s p * (if v = (p : ℕ) then (1 : ℝ) else 0) ≤ μs := by
  by_cases hv : v ∈ s
  · have h1 : ∑ p : {p : ℕ // p ∈ s},
          Graph.primeGroupLaw s p * (if v = (p : ℕ) then (1 : ℝ) else 0) =
        Graph.primeGroupLaw s v :=
      (Finset.sum_eq_single_of_mem
        (f := fun p : {p : ℕ // p ∈ s} =>
          Graph.primeGroupLaw s p * (if v = (p : ℕ) then (1 : ℝ) else 0))
        (⟨v, hv⟩ : {p : ℕ // p ∈ s}) (Finset.mem_univ _)
        (fun p _ hne => by
          show Graph.primeGroupLaw s p * (if v = (p : ℕ) then (1 : ℝ) else 0) = 0
          rw [if_neg (fun h => hne (Subtype.ext h.symm)), mul_zero])).trans
        ((congrArg (fun z => Graph.primeGroupLaw s v * z) (if_pos rfl)).trans (mul_one _))
    rw [h1]
    exact hμ v hv
  · have h1 : ∑ p : {p : ℕ // p ∈ s},
          Graph.primeGroupLaw s p * (if v = (p : ℕ) then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun p _ => by
        have hne : ¬(v = (p : ℕ)) := fun h => hv (h ▸ p.2)
        rw [if_neg hne, mul_zero]
    rw [h1]
    exact hμ0

omit [DecidableEq B] in
/-- **One auxiliary label avoids a fixed list with probability at least `1 - |ℬ| M μ_*`**: "its
chance to match a fixed active label is bounded by [the maximal atom]" [S-02:1003–1005]. -/
theorem clean_hit_factor_ge (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {μs : ℝ} (hμ0 : 0 ≤ μs) (hμ : ∀ g, ∀ p ∈ big g, Graph.primeGroupLaw (big g) p ≤ μs)
    (x : LabelList big J ℓ) (g : B) :
    1 - (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) ≤
      ∑ p : {p : ℕ // p ∈ big g}, Graph.primeGroupLaw (big g) p * cleanHitInd x (p : ℕ) := by
  have h1 : ∑ p : {p : ℕ // p ∈ big g}, Graph.primeGroupLaw (big g) p = 1 := by
    rw [Finset.sum_coe_sort (big g) (fun q => Graph.primeGroupLaw (big g) q)]
    exact hlaw g
  have hind0 : ∀ (g' : B) (s : Slot J ℓ) (p : {p : ℕ // p ∈ big g}),
      (0 : ℝ) ≤ (if (x g' s : ℕ) = (p : ℕ) then (1 : ℝ) else 0) := by
    intro g' s p
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have hpt : ∀ p : {p : ℕ // p ∈ big g}, 1 - cleanHitInd x (p : ℕ) ≤
      ∑ g' : B, ∑ s : Slot J ℓ, (if (x g' s : ℕ) = (p : ℕ) then (1 : ℝ) else 0) := by
    intro p
    by_cases h : ∀ (g' : B) (s : Slot J ℓ), (x g' s : ℕ) ≠ (p : ℕ)
    · have e : cleanHitInd x (p : ℕ) = 1 := if_pos h
      rw [e, sub_self]
      exact Finset.sum_nonneg fun g' _ => Finset.sum_nonneg fun s _ => hind0 g' s p
    · have e : cleanHitInd x (p : ℕ) = 0 := if_neg h
      rw [e, sub_zero]
      obtain ⟨g', hg'⟩ := not_forall.mp h
      obtain ⟨s, hs⟩ := not_forall.mp hg'
      have hs' : (x g' s : ℕ) = (p : ℕ) := not_not.mp hs
      have h2 : (1 : ℝ) ≤ ∑ s : Slot J ℓ, (if (x g' s : ℕ) = (p : ℕ) then (1 : ℝ) else 0) :=
        le_trans (le_of_eq (if_pos hs').symm)
          (Finset.single_le_sum
            (f := fun s : Slot J ℓ => (if (x g' s : ℕ) = (p : ℕ) then (1 : ℝ) else 0))
            (fun s _ => hind0 g' s p) (Finset.mem_univ s))
      exact h2.trans (Finset.single_le_sum
        (f := fun g' : B => ∑ s : Slot J ℓ, (if (x g' s : ℕ) = (p : ℕ) then (1 : ℝ) else 0))
        (fun g' _ => Finset.sum_nonneg fun s _ => hind0 g' s p) (Finset.mem_univ g'))
  have hbad : ∑ p : {p : ℕ // p ∈ big g},
        Graph.primeGroupLaw (big g) p * (1 - cleanHitInd x (p : ℕ)) ≤
      (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) := by
    calc ∑ p : {p : ℕ // p ∈ big g},
          Graph.primeGroupLaw (big g) p * (1 - cleanHitInd x (p : ℕ))
        ≤ ∑ p : {p : ℕ // p ∈ big g}, ∑ g' : B, ∑ s : Slot J ℓ,
            Graph.primeGroupLaw (big g) p * (if (x g' s : ℕ) = (p : ℕ) then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun p _ => ?_
          calc Graph.primeGroupLaw (big g) p * (1 - cleanHitInd x (p : ℕ))
              ≤ Graph.primeGroupLaw (big g) p *
                  ∑ g' : B, ∑ s : Slot J ℓ, (if (x g' s : ℕ) = (p : ℕ) then (1 : ℝ) else 0) :=
                mul_le_mul_of_nonneg_left (hpt p) (Schur.primeGroupLaw_nonneg _ _)
            _ = ∑ g' : B, ∑ s : Slot J ℓ,
                  Graph.primeGroupLaw (big g) p *
                    (if (x g' s : ℕ) = (p : ℕ) then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun g' _ => Finset.mul_sum _ _ _
      _ = ∑ g' : B, ∑ s : Slot J ℓ, ∑ p : {p : ℕ // p ∈ big g},
            Graph.primeGroupLaw (big g) p * (if (x g' s : ℕ) = (p : ℕ) then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun g' _ => Finset.sum_comm
      _ ≤ ∑ _g' : B, ∑ _s : Slot J ℓ, μs :=
          Finset.sum_le_sum fun g' _ => Finset.sum_le_sum fun s _ =>
            clean_sum_law_eq_le hμ0 (hμ g) (x g' s : ℕ)
      _ = (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_slot]
  have hsplit : ∑ p : {p : ℕ // p ∈ big g},
        Graph.primeGroupLaw (big g) p * cleanHitInd x (p : ℕ) =
      (∑ p : {p : ℕ // p ∈ big g}, Graph.primeGroupLaw (big g) p) -
        ∑ p : {p : ℕ // p ∈ big g},
          Graph.primeGroupLaw (big g) p * (1 - cleanHitInd x (p : ℕ)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit, h1]
  linarith

/-- **The ban holds for a fixed list with probability at least `1 - m|ℬ| · |ℬ| M μ_*`**
[S-02:1000–1008]: "there are `O_{J,m}(s)` possible comparisons". -/
theorem clean_ban_prob_ge (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {μs : ℝ} (hμ0 : 0 ≤ μs) (hμ : ∀ g, ∀ p ∈ big g, Graph.primeGroupLaw (big g) p ≤ μs)
    {m : ℕ} (C : B → Finset (Fin J)) (hCm : ∀ g, (C g).card ≤ m)
    (hδ : (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) ≤ 1) (x : LabelList big J ℓ) :
    1 - ((m * Fintype.card B : ℕ) : ℝ) * ((Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs)) ≤
      ∑ r : AuxList big C, auxWeight big C r * cleanBanInd C r x := by
  have hfacg := fun g : B => clean_hit_factor_ge hlaw hμ0 hμ x g
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) :=
    ⟨_, rfl⟩
  rw [← hδ'] at hδ hfacg ⊢
  have hδ0 : 0 ≤ δ' := by
    rw [hδ']
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hμ0)
  have h1δ : 0 ≤ 1 - δ' := by linarith
  rw [clean_sum_aux_banInd]
  have hfac : ∀ g : B, (1 - δ') ^ m ≤
      ∏ _i : {i : Fin J // i ∈ C g}, ∑ p : {p : ℕ // p ∈ big g},
        Graph.primeGroupLaw (big g) p * cleanHitInd x (p : ℕ) := by
    intro g
    calc (1 - δ') ^ m ≤ (1 - δ') ^ (C g).card :=
          pow_le_pow_of_le_one h1δ (by linarith) (hCm g)
      _ = ∏ _i : {i : Fin J // i ∈ C g}, (1 - δ') := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
      _ ≤ ∏ _i : {i : Fin J // i ∈ C g}, ∑ p : {p : ℕ // p ∈ big g},
            Graph.primeGroupLaw (big g) p * cleanHitInd x (p : ℕ) :=
          Finset.prod_le_prod (fun _ _ => h1δ) (fun _ _ => hfacg g)
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ' by linarith) (m * Fintype.card B)
  have e1 : (1 : ℝ) + ((m * Fintype.card B : ℕ) : ℝ) * -δ' =
      1 - ((m * Fintype.card B : ℕ) : ℝ) * δ' := by ring
  have e2 : (1 : ℝ) + -δ' = 1 - δ' := by ring
  rw [e1, e2] at hb
  calc 1 - ((m * Fintype.card B : ℕ) : ℝ) * δ' ≤ (1 - δ') ^ (m * Fintype.card B) := hb
    _ = ∏ _g : B, (1 - δ') ^ m := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
    _ ≤ ∏ g, ∏ _i : {i : Fin J // i ∈ C g}, ∑ p : {p : ℕ // p ∈ big g},
          Graph.primeGroupLaw (big g) p * cleanHitInd x (p : ℕ) :=
        Finset.prod_le_prod (fun g _ => pow_nonneg h1δ m) (fun g _ => hfac g)

/-- The probability that the ban fails for a fixed list. -/
theorem clean_ban_fail_le (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {μs : ℝ} (hμ0 : 0 ≤ μs) (hμ : ∀ g, ∀ p ∈ big g, Graph.primeGroupLaw (big g) p ≤ μs)
    {m : ℕ} (C : B → Finset (Fin J)) (hCm : ∀ g, (C g).card ≤ m)
    (hδ : (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) ≤ 1) (x : LabelList big J ℓ) :
    ∑ r : AuxList big C, auxWeight big C r * (1 - cleanBanInd C r x) ≤
      ((m * Fintype.card B : ℕ) : ℝ) * ((Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs)) := by
  have h := clean_ban_prob_ge hlaw hμ0 hμ C hCm hδ x
  have hsplit : ∑ r : AuxList big C, auxWeight big C r * (1 - cleanBanInd C r x) =
      (∑ r : AuxList big C, auxWeight big C r) -
        ∑ r : AuxList big C, auxWeight big C r * cleanBanInd C r x := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [hsplit, sum_auxWeight hlaw C]
  linarith

open _root_.Classical in
/-- **The perturbation estimate** [S-02:0986–1012]: the ban of the auxiliary labels from the
source and from the target list, and a density `ρ(target)` with `|ρ - 1| ≤ ε₁`, change a row
operation with the ideal transition law and a multiplier bounded by `c₀` by at most
`c₀ (ε₁ + 2 √ε₂)` in the norm of `ℋ_id`, where `ε₂ = m|ℬ| · |ℬ| M μ_*`. -/
theorem cleanShRow_perturb (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {μs : ℝ} (hμ0 : 0 ≤ μs) (hμ : ∀ g, ∀ p ∈ big g, Graph.primeGroupLaw (big g) p ≤ μs)
    {m : ℕ} (C : B → Finset (Fin J)) (hCm : ∀ g, (C g).card ≤ m)
    (hδ : (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) ≤ 1)
    (Φ : LabelList big J ℓ → AuxList big C → LabelList big J ℓ → ℂ) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hΦ : ∀ x r x', ‖Φ x r x'‖ ≤ c₀) (ρ : LabelList big J ℓ → ℝ) {ε₁ : ℝ} (hε₁0 : 0 ≤ ε₁)
    (hρ : ∀ x', |ρ x' - 1| ≤ ε₁) (g : LabelList big J ℓ → ℂ) :
    wNorm (idealWeight big J ℓ)
        (cleanShRow C (fun x r x' =>
          ((cleanBanInd C r x * cleanBanInd C r x' * ρ x' : ℝ) : ℂ) * Φ x r x') g -
          cleanShRow C Φ g) ≤
      c₀ * (ε₁ + 2 * Real.sqrt (((m * Fintype.card B : ℕ) : ℝ) *
        ((Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs)))) *
        wNorm (idealWeight big J ℓ) g := by
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℝ, ε₂ = ((m * Fintype.card B : ℕ) : ℝ) *
      ((Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs)) := ⟨_, rfl⟩
  rw [← hε₂]
  have hε₂0 : 0 ≤ ε₂ := by
    rw [hε₂]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hμ0))
  have hfail : ∀ x : LabelList big J ℓ,
      ∑ r : AuxList big C, auxWeight big C r * (1 - cleanBanInd C r x) ≤ ε₂ := by
    intro x
    rw [hε₂]
    exact clean_ban_fail_le hlaw hμ0 hμ C hCm hδ x
  have hone : ∀ _x : LabelList big J ℓ,
      ∑ r : AuxList big C, auxWeight big C r * (1 : ℝ) ≤ 1 := by
    intro _
    simp only [mul_one]
    exact le_of_eq (sum_auxWeight hlaw C)
  have hm0 : ∀ x : LabelList big J ℓ, 0 ≤ idealWeight big J ℓ x := fun x =>
    clean_idealWeight_nonneg x
  -- the three parts of the difference
  have hdecomp : cleanShRow C (fun x r x' =>
        ((cleanBanInd C r x * cleanBanInd C r x' * ρ x' : ℝ) : ℂ) * Φ x r x') =
      cleanShRow C Φ +
        (cleanShRow C (fun x r x' =>
            ((cleanBanInd C r x * cleanBanInd C r x' * (ρ x' - 1) : ℝ) : ℂ) * Φ x r x') +
          (cleanShRow C (fun x r x' => ((-(1 - cleanBanInd C r x) : ℝ) : ℂ) * Φ x r x') +
            cleanShRow C (fun x r x' =>
              ((-(cleanBanInd C r x * (1 - cleanBanInd C r x')) : ℝ) : ℂ) * Φ x r x'))) := by
    rw [← cleanShRow_add, ← cleanShRow_add, ← cleanShRow_add]
    refine congrArg (cleanShRow C) (funext fun x => funext fun r => funext fun x' => ?_)
    push_cast
    ring
  have hA : wNorm (idealWeight big J ℓ) (cleanShRow C (fun x r x' =>
        ((cleanBanInd C r x * cleanBanInd C r x' * (ρ x' - 1) : ℝ) : ℂ) * Φ x r x') g) ≤
      c₀ * ε₁ * wNorm (idealWeight big J ℓ) g := by
    have h := cleanShRow_opBound hlaw C (fun x r x' =>
        ((cleanBanInd C r x * cleanBanInd C r x' * (ρ x' - 1) : ℝ) : ℂ) * Φ x r x')
      (fun _ _ => 1) (fun _ _ => 1) (c₀ := ε₁ * c₀) (R := 1) (R' := 1) (mul_nonneg hε₁0 hc₀)
      (fun _ _ => zero_le_one) (fun _ _ => le_rfl) (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
      (fun x r x' => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (cleanBanInd_nonneg C r x), abs_of_nonneg (cleanBanInd_nonneg C r x'),
          mul_one, mul_one]
        have h1 : cleanBanInd C r x * cleanBanInd C r x' ≤ 1 :=
          (mul_le_mul (cleanBanInd_le_one C r x) (cleanBanInd_le_one C r x')
            (cleanBanInd_nonneg C r x') zero_le_one).trans (le_of_eq (one_mul 1))
        have h2 : cleanBanInd C r x * cleanBanInd C r x' * |ρ x' - 1| ≤ 1 * ε₁ :=
          mul_le_mul h1 (hρ x') (abs_nonneg _) zero_le_one
        rw [one_mul] at h2
        exact mul_le_mul h2 (hΦ x r x') (norm_nonneg _) hε₁0)
      zero_le_one hone zero_le_one hone g
    rw [mul_one, Real.sqrt_one, mul_one] at h
    rw [mul_comm c₀ ε₁]
    exact h
  have hB : wNorm (idealWeight big J ℓ) (cleanShRow C (fun x r x' =>
        ((-(1 - cleanBanInd C r x) : ℝ) : ℂ) * Φ x r x') g) ≤
      c₀ * Real.sqrt ε₂ * wNorm (idealWeight big J ℓ) g := by
    have h := cleanShRow_opBound hlaw C (fun x r x' =>
        ((-(1 - cleanBanInd C r x) : ℝ) : ℂ) * Φ x r x')
      (fun x r => 1 - cleanBanInd C r x) (fun _ _ => 1) (c₀ := c₀) (R := ε₂) (R' := 1) hc₀
      (fun x r => sub_nonneg.mpr (cleanBanInd_le_one C r x))
      (fun x r => sub_le_self _ (cleanBanInd_nonneg C r x))
      (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
      (fun x r x' => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
          abs_of_nonneg (sub_nonneg.mpr (cleanBanInd_le_one C r x)), mul_one, mul_comm]
        exact mul_le_mul_of_nonneg_right (hΦ x r x')
          (sub_nonneg.mpr (cleanBanInd_le_one C r x)))
      hε₂0 hfail zero_le_one hone g
    rw [mul_one] at h
    exact h
  have hCc : wNorm (idealWeight big J ℓ) (cleanShRow C (fun x r x' =>
        ((-(cleanBanInd C r x * (1 - cleanBanInd C r x')) : ℝ) : ℂ) * Φ x r x') g) ≤
      c₀ * Real.sqrt ε₂ * wNorm (idealWeight big J ℓ) g := by
    have h := cleanShRow_opBound hlaw C (fun x r x' =>
        ((-(cleanBanInd C r x * (1 - cleanBanInd C r x')) : ℝ) : ℂ) * Φ x r x')
      (fun _ _ => 1) (fun r x' => 1 - cleanBanInd C r x') (c₀ := c₀) (R := 1) (R' := ε₂) hc₀
      (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
      (fun r x' => sub_nonneg.mpr (cleanBanInd_le_one C r x'))
      (fun r x' => sub_le_self _ (cleanBanInd_nonneg C r x'))
      (fun x r x' => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
          abs_of_nonneg (cleanBanInd_nonneg C r x),
          abs_of_nonneg (sub_nonneg.mpr (cleanBanInd_le_one C r x')), one_mul]
        have h1 : cleanBanInd C r x * (1 - cleanBanInd C r x') ≤ 1 - cleanBanInd C r x' :=
          mul_le_of_le_one_left (sub_nonneg.mpr (cleanBanInd_le_one C r x'))
            (cleanBanInd_le_one C r x)
        calc cleanBanInd C r x * (1 - cleanBanInd C r x') * ‖Φ x r x'‖
            ≤ (1 - cleanBanInd C r x') * c₀ :=
              mul_le_mul h1 (hΦ x r x') (norm_nonneg _)
                (sub_nonneg.mpr (cleanBanInd_le_one C r x'))
          _ = c₀ * (1 - cleanBanInd C r x') := mul_comm _ _)
      zero_le_one hone hε₂0 hfail g
    rw [one_mul] at h
    exact h
  have hdiff : cleanShRow C (fun x r x' =>
        ((cleanBanInd C r x * cleanBanInd C r x' * ρ x' : ℝ) : ℂ) * Φ x r x') g -
        cleanShRow C Φ g =
      cleanShRow C (fun x r x' =>
          ((cleanBanInd C r x * cleanBanInd C r x' * (ρ x' - 1) : ℝ) : ℂ) * Φ x r x') g +
        (cleanShRow C (fun x r x' => ((-(1 - cleanBanInd C r x) : ℝ) : ℂ) * Φ x r x') g +
          cleanShRow C (fun x r x' =>
            ((-(cleanBanInd C r x * (1 - cleanBanInd C r x')) : ℝ) : ℂ) * Φ x r x') g) := by
    rw [hdecomp, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply,
      add_sub_cancel_left]
  rw [hdiff]
  refine (wNorm_add_le hm0 _ _).trans ?_
  have h2 := wNorm_add_le hm0
    (cleanShRow C (fun x r x' => ((-(1 - cleanBanInd C r x) : ℝ) : ℂ) * Φ x r x') g)
    (cleanShRow C (fun x r x' =>
      ((-(cleanBanInd C r x * (1 - cleanBanInd C r x')) : ℝ) : ℂ) * Φ x r x') g)
  linarith

end Ban

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
