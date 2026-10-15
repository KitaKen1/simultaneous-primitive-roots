module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueSumCoef
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The summation over paths, part 3: one visit of a path

Source: `verification/stage7-sources/S-02.tex`, lines 222–231 (`[S-02:0222–0231]`): "Let `Λ_i` be
the set of active labels at visit `i`. Put `q_0 = q_N = √q` and `q_i = q` for `0 < i < N`. The
dependence on the initial integer `n` is precisely the nonnegative factor
(eq:path-residue-factor)."

For a family of pairwise disjoint groups (`GroupsDisjoint`) and lists `x`:

* `labOf`, `labelSet`, `ListInj` — the labels of the lists, the set `Λ` of these labels, and the
  condition that the labels of every group are distinct. `IsPhys 𝔭 n x` means `ListInj x` and that
  every label of `Λ` divides the position (`isPhys_iff`); `Λ` consists of group primes and has at
  most `M s` elements (`labelSet_subset`, `card_labelSet_le`), exactly `M s` if `ListInj x`
  (`card_labelSet`).
* `omegaOf_eq_add` — at a physical state, `ω(n) - M s` is the number of the group primes outside
  `Λ` which divide the position.
* `posWeight_visit` — the weight `posWeight` of `ResidueSumCoef.lean`, to the power `1` at the end
  visits and `2` at the interior visits, is `1_{ListInj x}` times the factor of the visit in
  (eq:path-residue-factor).
* `prod_visit_eq` — hence the product over the visits is `∏_i 1_{ListInj x_i}` times
  (eq:path-residue-factor).
* `pathFactor_hit_of_ne_zero`, `pathFactor_nonneg`, `pathFactor_tag_eq` — where
  (eq:path-residue-factor) does not vanish, all active congruences hold; it is nonnegative; and
  for the residue model with offsets, started at `(0, y)`, it is the factor of the residue
  model at `y`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum

open scoped BigOperators

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-- The groups of the family are pairwise disjoint (Definition 3.1, [S-02:0020–0021]). -/
structure GroupsDisjoint (𝒢 : GroupFamily S B) : Prop where
  small : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g')
  big : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')
  small_big : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g')

omit [DecidableEq S] [DecidableEq B] in
theorem groupsDisjoint_of {P : GroupParams} {x : ℝ} (𝔊 : PrimeGroups P x S B) :
    GroupsDisjoint 𝔊.toGroupFamily :=
  ⟨𝔊.disjoint_small, 𝔊.disjoint_big, 𝔊.disjoint_small_big⟩

section Labels

variable {𝒢 : GroupFamily S B} {J ℓ : ℕ}

/-- The label of a slot of a small group or of a big group. -/
def labOf (x : Lists 𝒢 J ℓ) : (S × Slot J ℓ) ⊕ (B × Slot J ℓ) → ℕ :=
  Sum.elim (fun a => (x.1 a.1 a.2 : ℕ)) (fun a => (x.2 a.1 a.2 : ℕ))

/-- **The set `Λ` of the labels of the lists** [S-02:0222]. -/
def labelSet (x : Lists 𝒢 J ℓ) : Finset ℕ := Finset.univ.image (labOf x)

/-- The labels of every group are distinct. -/
def ListInj (x : Lists 𝒢 J ℓ) : Prop :=
  (∀ g, Function.Injective (x.1 g)) ∧ ∀ g, Function.Injective (x.2 g)

omit [DecidableEq S] [DecidableEq B] in
/-- A state is physical if and only if the labels of every group are distinct and every label
divides the position. -/
theorem isPhys_iff (𝔭 : PosModel) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) :
    IsPhys 𝔭 n x ↔ ListInj x ∧ ∀ p ∈ labelSet x, 𝔭.hit p n := by
  have hmem : (∀ p ∈ labelSet x, 𝔭.hit p n) ↔
      (∀ g i, 𝔭.hit (x.1 g i) n) ∧ ∀ g i, 𝔭.hit (x.2 g i) n := by
    unfold labelSet
    rw [Finset.forall_mem_image]
    constructor
    · intro h
      exact ⟨fun g i => h (Finset.mem_univ (Sum.inl (g, i))),
        fun g i => h (Finset.mem_univ (Sum.inr (g, i)))⟩
    · rintro ⟨h1, h2⟩ a _
      rcases a with ⟨g, i⟩ | ⟨g, i⟩
      · exact h1 g i
      · exact h2 g i
  unfold IsPhys ListInj
  rw [hmem]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

omit [DecidableEq S] [DecidableEq B] in
/-- The labels are group primes. -/
theorem labelSet_subset (x : Lists 𝒢 J ℓ) : labelSet x ⊆ 𝒢.allPrimes := by
  intro p hp
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
  unfold GroupFamily.allPrimes
  rcases a with ⟨g, i⟩ | ⟨g, i⟩
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (x.1 g i).2⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (x.2 g i).2⟩)

omit [DecidableEq S] [DecidableEq B] in
theorem card_slots (S B : Type) [Fintype S] [Fintype B] (J ℓ : ℕ) :
    Fintype.card ((S × Slot J ℓ) ⊕ (B × Slot J ℓ)) = (J + ℓ) * groupCount S B := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, card_slot]
  unfold groupCount
  ring

omit [DecidableEq S] [DecidableEq B] in
/-- There are at most `M s` labels. -/
theorem card_labelSet_le (x : Lists 𝒢 J ℓ) : (labelSet x).card ≤ (J + ℓ) * groupCount S B := by
  unfold labelSet
  calc (Finset.univ.image (labOf x)).card
      ≤ (Finset.univ : Finset ((S × Slot J ℓ) ⊕ (B × Slot J ℓ))).card := Finset.card_image_le
    _ = (J + ℓ) * groupCount S B := by rw [Finset.card_univ, card_slots]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- For disjoint groups and distinct labels in every group, all labels are distinct. -/
theorem labOf_injective (hd : GroupsDisjoint 𝒢) {x : Lists 𝒢 J ℓ} (hx : ListInj x) :
    Function.Injective (labOf x) := by
  rintro (⟨g, i⟩ | ⟨g, i⟩) (⟨g', i'⟩ | ⟨g', i'⟩) h
  · have h' : (x.1 g i : ℕ) = (x.1 g' i' : ℕ) := h
    have hg : g = g' := by
      by_contra hne
      have hmem : (x.1 g i : ℕ) ∈ 𝒢.small g' := by
        rw [h']
        exact (x.1 g' i').2
      exact Finset.disjoint_left.mp (hd.small g g' hne) (x.1 g i).2 hmem
    subst hg
    have hi : i = i' := hx.1 g (Subtype.ext h')
    rw [hi]
  · have h' : (x.1 g i : ℕ) = (x.2 g' i' : ℕ) := h
    have hmem : (x.1 g i : ℕ) ∈ 𝒢.big g' := by
      rw [h']
      exact (x.2 g' i').2
    exact absurd hmem (Finset.disjoint_left.mp (hd.small_big g g') (x.1 g i).2)
  · have h' : (x.2 g i : ℕ) = (x.1 g' i' : ℕ) := h
    have hmem : (x.1 g' i' : ℕ) ∈ 𝒢.big g := by
      rw [← h']
      exact (x.2 g i).2
    exact absurd hmem (Finset.disjoint_left.mp (hd.small_big g' g) (x.1 g' i').2)
  · have h' : (x.2 g i : ℕ) = (x.2 g' i' : ℕ) := h
    have hg : g = g' := by
      by_contra hne
      have hmem : (x.2 g i : ℕ) ∈ 𝒢.big g' := by
        rw [h']
        exact (x.2 g' i').2
      exact Finset.disjoint_left.mp (hd.big g g' hne) (x.2 g i).2 hmem
    subst hg
    have hi : i = i' := hx.2 g (Subtype.ext h')
    rw [hi]

omit [DecidableEq S] [DecidableEq B] in
/-- For disjoint groups and distinct labels in every group there are exactly `M s` labels. -/
theorem card_labelSet (hd : GroupsDisjoint 𝒢) {x : Lists 𝒢 J ℓ} (hx : ListInj x) :
    (labelSet x).card = (J + ℓ) * groupCount S B := by
  unfold labelSet
  rw [Finset.card_image_of_injective _ (labOf_injective hd hx), Finset.card_univ, card_slots]

end Labels

/-! ### Counting the hits -/

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- For disjoint groups, `ω` counts the group primes which hit. -/
theorem omegaOf_eq_countHits {𝒢 : GroupFamily S B} (hd : GroupsDisjoint 𝒢) (hit : ℕ → Prop) :
    𝒢.omegaOf hit = countHits hit 𝒢.allPrimes := by
  have h1 : Disjoint (Finset.univ.biUnion 𝒢.small) (Finset.univ.biUnion 𝒢.big) :=
    (Finset.disjoint_biUnion_left _ _ _).mpr fun g _ =>
      (Finset.disjoint_biUnion_right _ _ _).mpr fun g' _ => hd.small_big g g'
  have h2 : ((Finset.univ.biUnion 𝒢.small ∪ Finset.univ.biUnion 𝒢.big).filter hit).card =
      ((Finset.univ.biUnion 𝒢.small).filter hit).card +
        ((Finset.univ.biUnion 𝒢.big).filter hit).card := by
    rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h1)]
  have h3 : ((Finset.univ.biUnion 𝒢.small).filter hit).card =
      ∑ g, ((𝒢.small g).filter hit).card := by
    rw [Finset.filter_biUnion, Finset.card_biUnion fun g _ g' _ hne =>
      Finset.disjoint_filter_filter (hd.small g g' hne)]
  have h4 : ((Finset.univ.biUnion 𝒢.big).filter hit).card =
      ∑ g, ((𝒢.big g).filter hit).card := by
    rw [Finset.filter_biUnion, Finset.card_biUnion fun g _ g' _ hne =>
      Finset.disjoint_filter_filter (hd.big g g' hne)]
  unfold GroupFamily.omegaOf countHits GroupFamily.allPrimes
  rw [h2, h3, h4]

open _root_.Classical in
/-- The hits of `Q` are the hits of `Q ∖ Λ` and the elements of `Λ`, if all of `Λ ⊆ Q` hits. -/
theorem countHits_eq_sdiff_add {Q Λ : Finset ℕ} {hit : ℕ → Prop} (hΛ : Λ ⊆ Q)
    (hhit : ∀ p ∈ Λ, hit p) : countHits hit Q = countHits hit (Q \ Λ) + Λ.card := by
  unfold countHits
  have hsub : Λ ⊆ Q.filter hit := fun p hp => Finset.mem_filter.mpr ⟨hΛ hp, hhit p hp⟩
  have e : (Q \ Λ).filter hit = Q.filter hit \ Λ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [e, Finset.card_sdiff_add_card_eq_card hsub]

omit [DecidableEq S] [DecidableEq B] in
/-- **At a physical state, `ω - M s` is the number of group primes outside `Λ` which hit.** -/
theorem omegaOf_eq_add {𝒢 : GroupFamily S B} (hd : GroupsDisjoint 𝒢) {J ℓ : ℕ}
    {x : Lists 𝒢 J ℓ} (hx : ListInj x) {hit : ℕ → Prop} (hhit : ∀ p ∈ labelSet x, hit p) :
    𝒢.omegaOf hit = countHits hit (𝒢.allPrimes \ labelSet x) + (J + ℓ) * groupCount S B := by
  rw [omegaOf_eq_countHits hd, countHits_eq_sdiff_add (labelSet_subset x) hhit,
    card_labelSet hd hx]

/-! ### The weight of a visit -/

section Visit

variable {𝒢 : GroupFamily S B} {J ℓ : ℕ}

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- **The weight of a visit is its factor in (eq:path-residue-factor)** [S-02:0223–0231]: for
disjoint groups, `posWeight` to the power one (at the end visits `i = 0`, `i = m`) or two (at the
interior visits) is `1_{ListInj x}` times `1_{Λ ⊆ hits} · q_i^{#hits(Q ∖ Λ)}`. The decidability
instance of the condition is arbitrary. -/
theorem posWeight_visit (hd : GroupsDisjoint 𝒢) {q : ℝ} (hq : 0 < q) (𝔭 : PosModel)
    (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) {inst : Decidable (∀ p ∈ labelSet x, 𝔭.hit p n)}
    (i m : ℕ) :
    (if i = 0 ∨ i = m then posWeight 𝔭 𝒢 q n x else posWeight 𝔭 𝒢 q n x ^ 2) =
      (if ListInj x then (1 : ℝ) else 0) *
        @ite ℝ (∀ p ∈ labelSet x, 𝔭.hit p n) inst
          (visitQ q m i ^ countHits (fun p => 𝔭.hit p n) (𝒢.allPrimes \ labelSet x)) 0 := by
  by_cases hI : ListInj x
  · by_cases hH : ∀ p ∈ labelSet x, 𝔭.hit p n
    · have hphys : IsPhys 𝔭 n x := (isPhys_iff 𝔭 n x).mpr ⟨hI, hH⟩
      have hcnt := omegaOf_eq_add hd hI (hit := fun p => 𝔭.hit p n) hH
      have hdamp : damping 𝔭 𝒢 J ℓ q n =
          q ^ (((countHits (fun p => 𝔭.hit p n) (𝒢.allPrimes \ labelSet x) : ℕ) : ℝ) / 2) := by
        unfold damping
        rw [hcnt]
        congr 1
        push_cast
        ring
      have hW : posWeight 𝔭 𝒢 q n x =
          q ^ (((countHits (fun p => 𝔭.hit p n) (𝒢.allPrimes \ labelSet x) : ℕ) : ℝ) / 2) := by
        unfold posWeight
        rw [if_pos hphys, hdamp]
      rw [if_pos hI, if_pos hH, one_mul, hW]
      unfold visitQ
      by_cases hi : i = 0 ∨ i = m
      · rw [if_pos hi, if_pos hi, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_mul hq.le]
        congr 1
        ring
      · rw [if_neg hi, if_neg hi,
          ← Real.rpow_natCast (q ^ (((countHits (fun p => 𝔭.hit p n)
            (𝒢.allPrimes \ labelSet x) : ℕ) : ℝ) / 2)) 2, ← Real.rpow_mul hq.le,
          ← Real.rpow_natCast q]
        congr 1
        push_cast
        ring
    · have hphys : ¬IsPhys 𝔭 n x := fun h => hH ((isPhys_iff 𝔭 n x).mp h).2
      have hW : posWeight 𝔭 𝒢 q n x = 0 := by
        unfold posWeight
        exact if_neg hphys
      rw [if_neg hH, mul_zero, hW]
      split_ifs <;> simp
  · have hphys : ¬IsPhys 𝔭 n x := fun h => hI ((isPhys_iff 𝔭 n x).mp h).1
    have hW : posWeight 𝔭 𝒢 q n x = 0 := by
      unfold posWeight
      exact if_neg hphys
    rw [if_neg hI, zero_mul, hW]
    split_ifs <;> simp

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- **The product of the weights over the visits is (eq:path-residue-factor)**, times the
indicator that the labels of every group are distinct at every visit. -/
theorem prod_visit_eq (hd : GroupsDisjoint 𝒢) {q : ℝ} (hq : 0 < q) (𝔭 : PosModel)
    (pos : 𝔭.Pos) (m : ℕ) (off : ℕ → ℤ) (lst : ℕ → Lists 𝒢 J ℓ) :
    ∏ i ∈ Finset.range (m + 1),
        (if i = 0 ∨ i = m then posWeight 𝔭 𝒢 q (𝔭.shift (off i) pos) (lst i)
          else posWeight 𝔭 𝒢 q (𝔭.shift (off i) pos) (lst i) ^ 2) =
      (∏ i ∈ Finset.range (m + 1), if ListInj (lst i) then (1 : ℝ) else 0) *
        pathFactor 𝔭 𝒢.allPrimes q m (fun i => labelSet (lst i)) off pos := by
  unfold pathFactor
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ =>
    posWeight_visit hd hq 𝔭 (𝔭.shift (off i) pos) (lst i) i m

end Visit

/-! ### (eq:path-residue-factor) -/

/-- Where (eq:path-residue-factor) does not vanish, the active congruences hold at every
visit. -/
theorem pathFactor_hit_of_ne_zero {𝔭 : PosModel} {Q : Finset ℕ} {q : ℝ} {m : ℕ}
    {Λ : ℕ → Finset ℕ} {h : ℕ → ℤ} {pos : 𝔭.Pos} (hne : pathFactor 𝔭 Q q m Λ h pos ≠ 0)
    {i : ℕ} (hi : i ≤ m) : ∀ p ∈ Λ i, 𝔭.hit p (𝔭.shift (h i) pos) := by
  unfold pathFactor at hne
  have hfac := Finset.prod_ne_zero_iff.mp hne i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  by_contra hc
  exact hfac (if_neg hc)

/-- (eq:path-residue-factor) is nonnegative. -/
theorem pathFactor_nonneg (𝔭 : PosModel) (Q : Finset ℕ) {q : ℝ} (hq : 0 ≤ q) (m : ℕ)
    (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ) (pos : 𝔭.Pos) : 0 ≤ pathFactor 𝔭 Q q m Λ h pos := by
  unfold pathFactor
  refine Finset.prod_nonneg fun i _ => ?_
  have hv : 0 ≤ visitQ q m i := by
    unfold visitQ
    split_ifs
    · exact Real.sqrt_nonneg q
    · exact hq
  split_ifs
  · exact pow_nonneg hv _
  · exact le_rfl

/-- For the residue model with offsets, started at `(0, y)`, (eq:path-residue-factor) is the
factor of the residue model at `y`. -/
theorem pathFactor_tag_eq (Q : Finset ℕ) (q : ℝ) (m : ℕ) (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ)
    (y : ResVec Q) :
    pathFactor (tagModel Q) Q q m Λ h (tagStart y) = pathFactor (resModel Q) Q q m Λ h y :=
  rfl

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum
