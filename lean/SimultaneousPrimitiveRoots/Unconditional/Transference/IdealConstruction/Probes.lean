module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Mixing
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealFamily
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The probes: the components which are mean zero in every probe are small

Source: `verification/stage7-sources/S-03.tex`, lines 491–540 (`[S-03:0491–0540]`).

For a symmetric `F ∈ ℋ_id` and a set `G` of big groups, (eq:ideal-full-component) bounds the
component of `F` which is mean zero in all `m` probes of every group of `G`, after "averaging out
the last `ℓ` slots": `‖∏_{probes of G} (1 - E_i) ∏_{last slots} E_j F‖² ≤ θ^{|G|} ‖F‖²`
(`probe_bound`).

Here `θ = 1/(m + 1)`: in one group, the `m + 1` operators
`E_k ∏_{i ∈ T, i ≠ k} (1 - E_i)`, `k ∈ T`, where `T` consists of the `m` probes and one of the
last `ℓ ≥ 1` slots, are mutually orthogonal projections, and for a symmetric vector their images
have the same norm (`single_group_bound`, from `AvgSystem.card_mul_le`). This is the case of the
Hoeffding count (eq:ideal-hoeffding-fraction) in which one excluded slot is kept; it needs
`J ≥ m` only, and "this bound tensorizes" [S-03:0519–0529] by induction on the groups, since the
projections of the other groups commute with the permutations of the slots of one group.

* `slotSet`, `lastSet`, `probeSet`, `lastOne` — sets of coordinates.
* `IsSym`, `IsSymAt` — invariance under slot permutations (of all groups, of one group).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Two facts about images of finite sets -/

theorem image_eq_self_of_fix {α : Type*} [DecidableEq α] (π : α → α) (V : Finset α)
    (h : ∀ x ∈ V, π x = x) : V.image π = V := by
  ext x
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [h y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, h x hx⟩

theorem image_eq_self_of_swap {α : Type*} [DecidableEq α] (π : α → α) (T : Finset α)
    (k k₀ : α) (hk : k ∈ T) (hk₀ : k₀ ∈ T) (h1 : π k = k₀) (h2 : π k₀ = k)
    (h3 : ∀ x, x ≠ k → x ≠ k₀ → π x = x) : T.image π = T := by
  have hmaps : ∀ y ∈ T, π y ∈ T := by
    intro y hy
    by_cases e1 : y = k
    · rw [e1, h1]
      exact hk₀
    · by_cases e2 : y = k₀
      · rw [e2, h2]
        exact hk
      · rw [h3 y e1 e2]
        exact hy
  have hinv : ∀ y, π (π y) = y := by
    intro y
    by_cases e1 : y = k
    · rw [e1, h1, h2]
    · by_cases e2 : y = k₀
      · rw [e2, h2, h1]
      · rw [h3 y e1 e2, h3 y e1 e2]
  ext x
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hmaps y hy
  · intro hx
    exact ⟨π x, hmaps x hx, hinv x⟩

/-! ### Sets of coordinates -/

section Sets

variable {B : Type} [Fintype B] {J ℓ : ℕ}

/-- The coordinates `(g, i)`, `i ∈ Λ g`, of a family of slot sets. -/
def slotSet (ℓ : ℕ) (Λ : B → Finset (Fin J)) : Finset (B × Slot J ℓ) :=
  (Finset.univ.sigma Λ).map
    ⟨fun x : (Σ _ : B, Fin J) => (x.1, Sum.inl x.2), fun x y h => by
      obtain ⟨g, i⟩ := x
      obtain ⟨g', i'⟩ := y
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      have h1' : g = g' := h1
      have h2' : (Sum.inl i : Slot J ℓ) = Sum.inl i' := h2
      subst h1'
      rw [Sum.inl.inj h2']⟩

theorem mem_slotSet {Λ : B → Finset (Fin J)} {g : B} {s : Slot J ℓ} :
    (g, s) ∈ slotSet ℓ Λ ↔ ∃ i, i ∈ Λ g ∧ s = Sum.inl i := by
  unfold slotSet
  rw [Finset.mem_map]
  constructor
  · rintro ⟨⟨g', i⟩, hmem, heq⟩
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    have h1' : g' = g := h1
    have h2' : (Sum.inl i : Slot J ℓ) = s := h2
    subst h1'
    exact ⟨i, (Finset.mem_sigma.mp hmem).2, h2'.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨g, i⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ g, hi⟩, rfl⟩

theorem inl_mem_slotSet {Λ : B → Finset (Fin J)} {g : B} {i : Fin J} :
    (g, (Sum.inl i : Slot J ℓ)) ∈ slotSet ℓ Λ ↔ i ∈ Λ g := by
  rw [mem_slotSet]
  constructor
  · rintro ⟨i', hi', heq⟩
    rw [Sum.inl.inj heq]
    exact hi'
  · intro h
    exact ⟨i, h, rfl⟩

theorem inr_notMem_slotSet {Λ : B → Finset (Fin J)} {g : B} {j : Fin ℓ} :
    (g, (Sum.inr j : Slot J ℓ)) ∉ slotSet ℓ Λ := by
  rw [mem_slotSet]
  rintro ⟨i, _, heq⟩
  cases heq

theorem card_slotSet (ℓ : ℕ) (Λ : B → Finset (Fin J)) :
    (slotSet ℓ Λ).card = ∑ g, (Λ g).card := by
  unfold slotSet
  rw [Finset.card_map, Finset.card_sigma]

/-- The coordinates of the last `ℓ` slots of all groups. -/
def lastSet (B : Type) [Fintype B] (J ℓ : ℕ) : Finset (B × Slot J ℓ) :=
  Finset.univ.filter fun k => k.2.isRight = true

theorem inr_mem_lastSet (g : B) (j : Fin ℓ) :
    (g, (Sum.inr j : Slot J ℓ)) ∈ lastSet B J ℓ := by
  simp [lastSet]

theorem inl_notMem_lastSet (g : B) (i : Fin J) :
    (g, (Sum.inl i : Slot J ℓ)) ∉ lastSet B J ℓ := by
  simp [lastSet]

theorem disjoint_slotSet_lastSet (Λ : B → Finset (Fin J)) :
    Disjoint (slotSet ℓ Λ) (lastSet B J ℓ) := by
  refine Finset.disjoint_left.mpr ?_
  rintro ⟨g, s⟩ hk hk'
  obtain ⟨i, _, rfl⟩ := mem_slotSet.mp hk
  exact inl_notMem_lastSet g i hk'

/-- The slot sets of two families which are disjoint in every group are disjoint. -/
theorem disjoint_slotSet {Λ Λ' : B → Finset (Fin J)} (h : ∀ g, Disjoint (Λ g) (Λ' g)) :
    Disjoint (slotSet ℓ Λ) (slotSet ℓ Λ') := by
  refine Finset.disjoint_left.mpr ?_
  rintro ⟨g, s⟩ hk hk'
  obtain ⟨i, hi, rfl⟩ := mem_slotSet.mp hk
  exact Finset.disjoint_left.mp (h g) hi (inl_mem_slotSet.mp hk')

variable [DecidableEq B]

/-- The probes of the groups of `G`: the coordinates `(g, i)` with `g ∈ G` and `i < m`
[S-03:0444–0446]. -/
def probeSet (J ℓ m : ℕ) (G : Finset B) : Finset (B × Slot J ℓ) :=
  slotSet ℓ fun g => if g ∈ G then probeSlots J m else ∅

/-- One of the last `ℓ` slots in every group of `G`. -/
def lastOne (J : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) (G : Finset B) : Finset (B × Slot J ℓ) :=
  G.image fun g => (g, Sum.inr ⟨0, hℓ⟩)

theorem mem_probeSet_fst {m : ℕ} {G : Finset B} {k : B × Slot J ℓ}
    (h : k ∈ probeSet J ℓ m G) : k.1 ∈ G := by
  obtain ⟨g, s⟩ := k
  obtain ⟨i, hi, _⟩ := mem_slotSet.mp h
  by_contra hg
  have hg' : g ∉ G := hg
  rw [if_neg hg'] at hi
  exact Finset.notMem_empty i hi

omit [Fintype B] in
theorem mem_lastOne_fst (hℓ : 0 < ℓ) {G : Finset B} {k : B × Slot J ℓ}
    (h : k ∈ lastOne J hℓ G) : k.1 ∈ G := by
  obtain ⟨g', hg', heq⟩ := Finset.mem_image.mp h
  rw [← heq]
  exact hg'

theorem lastOne_subset_lastSet (hℓ : 0 < ℓ) (G : Finset B) :
    lastOne J hℓ G ⊆ lastSet B J ℓ := by
  intro k hk
  obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hk
  exact inr_mem_lastSet g _

theorem card_probeSlots_ge {m : ℕ} (hJ : m ≤ J) : m ≤ (probeSlots J m).card := by
  have h : (Finset.univ : Finset (Fin m)).card ≤ (probeSlots J m).card := by
    refine Finset.card_le_card_of_injOn
      (fun i : Fin m => (⟨i.val, lt_of_lt_of_le i.isLt hJ⟩ : Fin J)) ?_ ?_
    · intro i _
      rw [Finset.mem_coe, probeSlots, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, i.isLt⟩
    · intro i _ j _ hij
      have h := congrArg Fin.val hij
      exact Fin.ext h
  rwa [Finset.card_univ, Fintype.card_fin] at h

theorem card_probeSet_singleton_ge {m : ℕ} (hJ : m ≤ J) (g₀ : B) :
    m ≤ (probeSet J ℓ m {g₀}).card := by
  unfold probeSet
  rw [card_slotSet]
  have h2 : (if g₀ ∈ ({g₀} : Finset B) then probeSlots J m else ∅).card ≤
      ∑ g : B, (if g ∈ ({g₀} : Finset B) then probeSlots J m else ∅).card :=
    Finset.single_le_sum
      (f := fun g : B => (if g ∈ ({g₀} : Finset B) then probeSlots J m else ∅).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ g₀)
  rw [if_pos (Finset.mem_singleton_self g₀)] at h2
  exact (card_probeSlots_ge hJ).trans h2

theorem probeSet_insert {m : ℕ} {g₀ : B} {G : Finset B} (hg : g₀ ∉ G) :
    probeSet J ℓ m (insert g₀ G) = probeSet J ℓ m {g₀} ∪ probeSet J ℓ m G := by
  ext ⟨g, s⟩
  cases s with
  | inl i =>
    simp only [probeSet, Finset.mem_union, inl_mem_slotSet]
    by_cases h1 : g = g₀
    · subst h1
      simp [hg]
    · simp [h1]
  | inr j => simp [probeSet, inr_notMem_slotSet]

theorem disjoint_probeSet {m : ℕ} {g₀ : B} {G : Finset B} (hg : g₀ ∉ G) :
    Disjoint (probeSet J ℓ m {g₀}) (probeSet J ℓ m G) := by
  refine Finset.disjoint_left.mpr fun k hkU hkV => hg ?_
  have a := mem_probeSet_fst hkU
  have b := mem_probeSet_fst hkV
  rw [Finset.mem_singleton] at a
  rw [← a]
  exact b

end Sets

/-! ### Symmetric vectors -/

section Sym

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- Invariance under the slot permutations of all big groups. -/
def IsSym (F : LabelList big J ℓ → ℂ) : Prop :=
  ∀ (σ : SlotPerms B J ℓ) (p : LabelList big J ℓ), F (permuteSlots σ p) = F p

/-- Invariance under the permutations of the slots of the group `g₀`. -/
def IsSymAt (g₀ : B) (F : LabelList big J ℓ → ℂ) : Prop :=
  ∀ σ : SlotPerms B J ℓ, (∀ g, g ≠ g₀ → σ g = 1) →
    ∀ p : LabelList big J ℓ, F (permuteSlots σ p) = F p

theorem isSym_bigSym (F : LabelList big J ℓ → ℂ) : IsSym (bigSym big J ℓ F) :=
  fun σ p => bigSym_permute F σ p

/-- **One group** [S-03:0491–0517]: for a vector which is symmetric in the slots of the group
`g₀`, the component which is mean zero in the `m` probes of `g₀` and averaged in one of its last
slots has at most the fraction `1/(m + 1)` of the squared norm. -/
theorem single_group_bound (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (hnn : ∀ p : LabelList big J ℓ, 0 ≤ idealWeight big J ℓ p) {m : ℕ} (hJ : m ≤ J)
    (hℓ : 0 < ℓ) (g₀ : B) (F : LabelList big J ℓ → ℂ) (hF : IsSymAt g₀ F) :
    ((m : ℝ) + 1) * wNormSq (idealWeight big J ℓ)
        ((labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)}
          ((labelAvg hlaw).D (probeSet J ℓ m {g₀}) F)) ≤
      wNormSq (idealWeight big J ℓ) F := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : B × Slot J ℓ, k₀ = (g₀, Sum.inr ⟨0, hℓ⟩) := ⟨_, rfl⟩
  rw [← hk₀]
  have hk₀T : k₀ ∉ probeSet J ℓ m {g₀} := by
    rw [hk₀]
    exact inr_notMem_slotSet
  obtain ⟨T, hT⟩ : ∃ T : Finset (B × Slot J ℓ), T = insert k₀ (probeSet J ℓ m {g₀}) :=
    ⟨_, rfl⟩
  have herase : T.erase k₀ = probeSet J ℓ m {g₀} := by
    rw [hT, Finset.erase_insert hk₀T]
  have hk₀mem : k₀ ∈ T := by
    rw [hT]
    exact Finset.mem_insert_self _ _
  have hc : ∀ k ∈ T, wNormSq (idealWeight big J ℓ)
      ((labelAvg hlaw).E {k} ((labelAvg hlaw).D (T.erase k) F)) =
      wNormSq (idealWeight big J ℓ)
        ((labelAvg hlaw).E {k₀} ((labelAvg hlaw).D (probeSet J ℓ m {g₀}) F)) := by
    intro k hk
    have hk' : k = k₀ ∨ k ∈ probeSet J ℓ m {g₀} := by
      rw [hT] at hk
      exact Finset.mem_insert.mp hk
    rcases hk' with hk0 | hkp
    · rw [hk0, herase]
    · obtain ⟨g, s⟩ := k
      have hgg : g = g₀ := Finset.mem_singleton.mp (mem_probeSet_fst hkp)
      subst hgg
      obtain ⟨σ, hσdef⟩ : ∃ σ : SlotPerms B J ℓ,
          σ = fun g' => if g' = g then Equiv.swap s (Sum.inr ⟨0, hℓ⟩) else 1 := ⟨_, rfl⟩
      have hσ0 : σ g = Equiv.swap s (Sum.inr ⟨0, hℓ⟩) := by
        rw [hσdef]
        exact if_pos rfl
      have hσ1 : ∀ g', g' ≠ g → σ g' = 1 := fun g' hg' => by
        rw [hσdef]
        exact if_neg hg'
      have h1 : coordPerm σ (g, s) = k₀ := by
        rw [hk₀]
        show (g, σ g s) = (g, Sum.inr ⟨0, hℓ⟩)
        rw [hσ0, Equiv.swap_apply_left]
      have h2 : coordPerm σ k₀ = (g, s) := by
        rw [hk₀]
        show (g, σ g (Sum.inr ⟨0, hℓ⟩)) = (g, s)
        rw [hσ0, Equiv.swap_apply_right]
      have h3 : ∀ x : B × Slot J ℓ, x ≠ (g, s) → x ≠ k₀ → coordPerm σ x = x := by
        rintro ⟨g', t⟩ hx1 hx2
        show (g', σ g' t) = (g', t)
        by_cases hg' : g' = g
        · rw [hg'] at hx1 hx2 ⊢
          have ht1 : t ≠ s := fun h => hx1 (by rw [h])
          have ht2 : t ≠ Sum.inr ⟨0, hℓ⟩ := fun h => hx2 (by rw [h, hk₀])
          rw [hσ0, Equiv.swap_apply_of_ne_of_ne ht1 ht2]
        · rw [hσ1 g' hg', Equiv.Perm.one_apply]
      have hπT : T.image (coordPerm σ) = T :=
        image_eq_self_of_swap (coordPerm σ) T (g, s) k₀ hk hk₀mem h1 h2 h3
      have e1 : permOp σ ((labelAvg hlaw).E {k₀} ((labelAvg hlaw).D (T.erase k₀) F)) =
          (labelAvg hlaw).E {(g, s)} ((labelAvg hlaw).D (T.erase (g, s)) F) := by
        have a1 : permOp σ ((labelAvg hlaw).E {k₀} ((labelAvg hlaw).D (T.erase k₀) F)) =
            (labelAvg hlaw).E (({k₀} : Finset (B × Slot J ℓ)).image (coordPerm σ))
              (permOp σ ((labelAvg hlaw).D (T.erase k₀) F)) :=
          funext fun p => avg_permute σ {k₀} _ p
        have a2 := permOp_D hlaw σ (T.erase k₀) F
        have a3 : permOp σ F = F := funext fun p => hF σ hσ1 p
        rw [a1, a2, a3, Finset.image_singleton, Finset.image_erase (coordPerm_injective σ), hπT,
          h2]
      calc wNormSq (idealWeight big J ℓ)
            ((labelAvg hlaw).E {(g, s)} ((labelAvg hlaw).D (T.erase (g, s)) F))
          = wNormSq (idealWeight big J ℓ)
              (permOp σ ((labelAvg hlaw).E {k₀} ((labelAvg hlaw).D (T.erase k₀) F))) := by
            rw [e1]
        _ = wNormSq (idealWeight big J ℓ)
              ((labelAvg hlaw).E {k₀} ((labelAvg hlaw).D (T.erase k₀) F)) :=
            wNormSq_permOp σ _
        _ = wNormSq (idealWeight big J ℓ)
              ((labelAvg hlaw).E {k₀} ((labelAvg hlaw).D (probeSet J ℓ m {g}) F)) := by
            rw [herase]
  have hcard := (labelAvg hlaw).card_mul_le hnn T F _ hc
  have hge : m ≤ (probeSet J ℓ m {g₀}).card := card_probeSet_singleton_ge hJ g₀
  have hTcard : (m : ℝ) + 1 ≤ (T.card : ℝ) := by
    rw [hT, Finset.card_insert_of_notMem hk₀T]
    have h' : (m : ℝ) ≤ ((probeSet J ℓ m {g₀}).card : ℝ) := by exact_mod_cast hge
    push_cast
    linarith
  exact (mul_le_mul_of_nonneg_right hTcard (wNormSq_nonneg hnn _)).trans hcard

/-- **The bound tensorizes** [S-03:0519–0529]: for a symmetric vector, the component which is mean
zero in all probes of the groups of `G`, after averaging one of the last slots in each of these
groups, has at most the fraction `(m + 1)^{-|G|}` of the squared norm. -/
theorem probe_bound_lastOne (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (hnn : ∀ p : LabelList big J ℓ, 0 ≤ idealWeight big J ℓ p) {m : ℕ} (hJ : m ≤ J)
    (hℓ : 0 < ℓ) (F : LabelList big J ℓ → ℂ) (hF : IsSym F) (G : Finset B) :
    wNormSq (idealWeight big J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F)) ≤
      (1 / ((m : ℝ) + 1)) ^ G.card * wNormSq (idealWeight big J ℓ) F := by
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  induction G using Finset.induction_on with
  | empty =>
    have h1 : probeSet J ℓ m (∅ : Finset B) = ∅ :=
      Finset.subset_empty.mp fun k hk => absurd (mem_probeSet_fst hk) (Finset.notMem_empty _)
    have h2 : lastOne J hℓ (∅ : Finset B) = ∅ := Finset.image_empty _
    rw [h1, h2, (labelAvg hlaw).D_empty, (labelAvg hlaw).E_empty, Finset.card_empty, pow_zero,
      one_mul]
    exact le_refl _
  | @insert g₀ G hg ih =>
    have hset2 : lastOne J hℓ (insert g₀ G) =
        {(g₀, Sum.inr ⟨0, hℓ⟩)} ∪ lastOne J hℓ G := by
      unfold lastOne
      rw [Finset.image_insert, Finset.insert_eq]
    have hop : (labelAvg hlaw).D (probeSet J ℓ m {g₀}) * (labelAvg hlaw).D (probeSet J ℓ m G) *
        ((labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} * (labelAvg hlaw).E (lastOne J hℓ G)) =
        (labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} * ((labelAvg hlaw).D (probeSet J ℓ m {g₀}) *
          ((labelAvg hlaw).D (probeSet J ℓ m G) * (labelAvg hlaw).E (lastOne J hℓ G))) := by
      calc (labelAvg hlaw).D (probeSet J ℓ m {g₀}) * (labelAvg hlaw).D (probeSet J ℓ m G) *
            ((labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} * (labelAvg hlaw).E (lastOne J hℓ G))
          = (labelAvg hlaw).D (probeSet J ℓ m {g₀}) * (((labelAvg hlaw).D (probeSet J ℓ m G) *
              (labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)}) *
                (labelAvg hlaw).E (lastOne J hℓ G)) := by
            simp only [mul_assoc]
        _ = (labelAvg hlaw).D (probeSet J ℓ m {g₀}) * (((labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} *
              (labelAvg hlaw).D (probeSet J ℓ m G)) * (labelAvg hlaw).E (lastOne J hℓ G)) := by
            rw [(labelAvg hlaw).E_D_comm]
        _ = ((labelAvg hlaw).D (probeSet J ℓ m {g₀}) * (labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)}) *
              ((labelAvg hlaw).D (probeSet J ℓ m G) * (labelAvg hlaw).E (lastOne J hℓ G)) := by
            simp only [mul_assoc]
        _ = ((labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} * (labelAvg hlaw).D (probeSet J ℓ m {g₀})) *
              ((labelAvg hlaw).D (probeSet J ℓ m G) * (labelAvg hlaw).E (lastOne J hℓ G)) := by
            rw [(labelAvg hlaw).E_D_comm]
        _ = (labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} * ((labelAvg hlaw).D (probeSet J ℓ m {g₀}) *
              ((labelAvg hlaw).D (probeSet J ℓ m G) * (labelAvg hlaw).E (lastOne J hℓ G))) := by
            simp only [mul_assoc]
    have hmain : (labelAvg hlaw).D (probeSet J ℓ m (insert g₀ G))
          ((labelAvg hlaw).E (lastOne J hℓ (insert g₀ G)) F) =
        (labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} ((labelAvg hlaw).D (probeSet J ℓ m {g₀})
          ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F))) := by
      rw [probeSet_insert hg, hset2, (labelAvg hlaw).D_union (disjoint_probeSet hg),
        ← (labelAvg hlaw).E_mul]
      exact LinearMap.congr_fun hop F
    have hsymAt : IsSymAt g₀
        ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F)) := by
      intro σ hσ p
      have hV : (probeSet J ℓ m G).image (coordPerm σ) = probeSet J ℓ m G :=
        image_eq_self_of_fix _ _ fun x hx => by
          have hx1 : x.1 ≠ g₀ := fun h => hg (h ▸ mem_probeSet_fst hx)
          show (x.1, σ x.1 x.2) = x
          rw [hσ x.1 hx1, Equiv.Perm.one_apply]
      have hL : (lastOne J hℓ G).image (coordPerm σ) = lastOne J hℓ G :=
        image_eq_self_of_fix _ _ fun x hx => by
          have hx1 : x.1 ≠ g₀ := fun h => hg (h ▸ mem_lastOne_fst hℓ hx)
          show (x.1, σ x.1 x.2) = x
          rw [hσ x.1 hx1, Equiv.Perm.one_apply]
      have e : permOp σ ((labelAvg hlaw).D (probeSet J ℓ m G)
            ((labelAvg hlaw).E (lastOne J hℓ G) F)) =
          (labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F) := by
        have a1 := permOp_D hlaw σ (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F)
        have a2 : permOp σ ((labelAvg hlaw).E (lastOne J hℓ G) F) =
            (labelAvg hlaw).E ((lastOne J hℓ G).image (coordPerm σ)) (permOp σ F) :=
          funext fun p => avg_permute σ (lastOne J hℓ G) F p
        have a3 : permOp σ F = F := funext fun p => hF σ p
        rw [a1, a2, a3, hV, hL]
      exact congrFun e p
    have hs := single_group_bound hlaw hnn hJ hℓ g₀ _ hsymAt
    have hinv : (1 / ((m : ℝ) + 1)) * (((m : ℝ) + 1) * wNormSq (idealWeight big J ℓ)
        ((labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} ((labelAvg hlaw).D (probeSet J ℓ m {g₀})
          ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F))))) =
        wNormSq (idealWeight big J ℓ)
          ((labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} ((labelAvg hlaw).D (probeSet J ℓ m {g₀})
            ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F)))) := by
      rw [← mul_assoc, one_div, inv_mul_cancel₀ hpos.ne', one_mul]
    have hθ : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := (div_pos one_pos hpos).le
    rw [hmain, Finset.card_insert_of_notMem hg, pow_succ]
    calc wNormSq (idealWeight big J ℓ)
          ((labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} ((labelAvg hlaw).D (probeSet J ℓ m {g₀})
            ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F))))
        = (1 / ((m : ℝ) + 1)) * (((m : ℝ) + 1) * wNormSq (idealWeight big J ℓ)
            ((labelAvg hlaw).E {(g₀, Sum.inr ⟨0, hℓ⟩)} ((labelAvg hlaw).D (probeSet J ℓ m {g₀})
              ((labelAvg hlaw).D (probeSet J ℓ m G)
                ((labelAvg hlaw).E (lastOne J hℓ G) F))))) := hinv.symm
      _ ≤ (1 / ((m : ℝ) + 1)) * wNormSq (idealWeight big J ℓ)
            ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F)) :=
          mul_le_mul_of_nonneg_left hs hθ
      _ ≤ (1 / ((m : ℝ) + 1)) *
            ((1 / ((m : ℝ) + 1)) ^ G.card * wNormSq (idealWeight big J ℓ) F) :=
          mul_le_mul_of_nonneg_left ih hθ
      _ = (1 / ((m : ℝ) + 1)) ^ G.card * (1 / ((m : ℝ) + 1)) *
            wNormSq (idealWeight big J ℓ) F := by ring

/-- **(eq:ideal-full-component)** [S-03:0530–0534]: for a symmetric `F`,
`‖∏_{probes of G} (1 - E_i) E_{last slots} F‖² ≤ (m + 1)^{-|G|} ‖F‖²`. -/
theorem probe_bound (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (hnn : ∀ p : LabelList big J ℓ, 0 ≤ idealWeight big J ℓ p) {m : ℕ} (hJ : m ≤ J)
    (hℓ : 0 < ℓ) (F : LabelList big J ℓ → ℂ) (hF : IsSym F) (G : Finset B) :
    wNormSq (idealWeight big J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m G) (avg big J ℓ (lastSet B J ℓ) F)) ≤
      (1 / ((m : ℝ) + 1)) ^ G.card * wNormSq (idealWeight big J ℓ) F := by
  have hsub : lastSet B J ℓ ∪ lastOne J hℓ G = lastSet B J ℓ :=
    Finset.union_eq_left.mpr (lastOne_subset_lastSet hℓ G)
  have e1 : avg big J ℓ (lastSet B J ℓ) F =
      (labelAvg hlaw).E (lastSet B J ℓ) ((labelAvg hlaw).E (lastOne J hℓ G) F) := by
    rw [(labelAvg hlaw).E_apply_apply, hsub]
    rfl
  have e2 : (labelAvg hlaw).D (probeSet J ℓ m G)
        ((labelAvg hlaw).E (lastSet B J ℓ) ((labelAvg hlaw).E (lastOne J hℓ G) F)) =
      (labelAvg hlaw).E (lastSet B J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F)) :=
    (LinearMap.congr_fun ((labelAvg hlaw).E_D_comm (lastSet B J ℓ) (probeSet J ℓ m G))
      ((labelAvg hlaw).E (lastOne J hℓ G) F)).symm
  rw [e1, e2]
  have h1 := (labelAvg hlaw).wNorm_E_le hnn (lastSet B J ℓ)
    ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F))
  have h2 : wNormSq (idealWeight big J ℓ) ((labelAvg hlaw).E (lastSet B J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F))) ≤
      wNormSq (idealWeight big J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m G) ((labelAvg hlaw).E (lastOne J hℓ G) F)) := by
    rw [← wNorm_sq hnn, ← wNorm_sq hnn]
    exact pow_le_pow_left₀ (wNorm_nonneg _ _) h1 2
  exact h2.trans (probe_bound_lastOne hlaw hnn hJ hℓ F hF G)

end Sym

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction
