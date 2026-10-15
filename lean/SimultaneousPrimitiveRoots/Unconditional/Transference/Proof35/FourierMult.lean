module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.BirthFourier
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Fourier multipliers of the operations

Source: `verification/stage7-sources/S-02.tex`, lines 1172–1196 (`[S-02:1172–1196]`).

"For fixed Fourier parameters, collect the factors by their birth operation. Each affected
operation is multiplied, on its individual local choices, by
`1_{designated local births are performed} e(∑_{β local} c_β p_β)`, of modulus at most one.
Initial-slot factors merely modify the initial boundary vector by such a multiplier. … Unaffected
edges retain their complete signed pattern sum and both symmetrizations."

For a collection `π` of blocks of birth addresses and Fourier parameters `t` (one residue modulo
`Q` for every ordered pair of addresses), `fourierMult D Bc π Q t` is the family of multipliers
on the births of the operations (`BirthMult`): every operation is multiplied by the product of the
multipliers `addrMult π Q t β` (`BirthFourier.lean`) of its own addresses `β`. Then

* the value of the family on a history is the product over all addresses
  (`History.mult_fourierMult`);
* all multipliers have modulus at most one (`norm_fourierMult_init_le`,
  `norm_fourierMult_ghost_le`, `norm_fourierMult_edge_le`);
* the multiplier of an edge none of whose addresses is in a block is `1`
  (`fourierMult_edge_of_not_affected`), and at most `2 r(π)` edges have an address in a block
  (`card_affectedEdges_le`);
* with `Q = primeBound 𝒢`, larger than all big primes, the sum over the parameters `t` of the
  path integrals with the multipliers is the number of parameters times the path integral with
  the indicator of `𝒞_π` (`card_mul_rankPart`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Generic lemmas -/

/-- If `if P then some x else none` is `some p`, then `x = p`. -/
theorem ite_some_none_eq_some {α : Type*} {P : Prop} {hP : Decidable P} {x p : α}
    (h : @ite (Option α) P hP (some x) none = some p) : x = p := by
  by_cases hc : P
  · rw [if_pos hc] at h
    exact Option.some.inj h
  · rw [if_neg hc] at h
    exact (Option.some_ne_none p h.symm).elim

/-- If `if hc : P then some (x hc) else none` is `some p`, then `P` holds and `x hc = p`. -/
theorem dite_some_none_eq_some {α : Type*} {P : Prop} {hP : Decidable P} {x : P → α} {p : α}
    (h : @dite (Option α) P hP (fun hc => some (x hc)) (fun _ => none) = some p) :
    ∃ hc : P, x hc = p := by
  by_cases hc : P
  · rw [dif_pos hc] at h
    exact ⟨hc, Option.some.inj h⟩
  · rw [dif_neg hc] at h
    exact (Option.some_ne_none p h.symm).elim

/-- A product of complex numbers of modulus at most one has modulus at most one. -/
theorem norm_prod_le_one {ι : Type*} [Fintype ι] (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖∏ i, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hf i)

/-! ### The edges of the addresses of a collection -/

/-- Equality of birth addresses is decidable. The instance is assembled in steps: the direct
synthesis for the nested sum of products exceeds the size limit of the instance synthesis (as for
`History.instFintype`). -/
instance BirthAddr.instDecidableEq (B : Type) [DecidableEq B] (J ℓ Bc n : ℕ) :
    DecidableEq (BirthAddr B J ℓ Bc n) := by
  haveI h1 : DecidableEq (B × Slot J ℓ) := inferInstance
  haveI h2 : DecidableEq (Fin n × B × Slot J ℓ) := inferInstance
  haveI h3 : DecidableEq (Fin (n + 1) × B × Fin Bc) := inferInstance
  haveI h4 : DecidableEq ((Fin n × B × Slot J ℓ) ⊕ (Fin (n + 1) × B × Fin Bc)) := inferInstance
  exact inferInstanceAs
    (DecidableEq ((B × Slot J ℓ) ⊕ ((Fin n × B × Slot J ℓ) ⊕ (Fin (n + 1) × B × Fin Bc))))

/-- The edge of a birth address: the index of the edge for a target slot of an edge, and `n`
(which is not the index of an edge) for an initial slot and for a ghost address. -/
def edgeIndex (B : Type) (J ℓ Bc n : ℕ) : BirthAddr B J ℓ Bc n → ℕ
  | Sum.inl _ => n
  | Sum.inr (Sum.inl a) => a.1.val
  | Sum.inr (Sum.inr _) => n

/-- **The affected edges** [S-02:1192–1196]: the edges which have a target slot in a block of the
collection `π` (together, possibly, with the number `n`, which is not an edge). -/
def affectedEdges {B : Type} [DecidableEq B] {J ℓ Bc n : ℕ}
    (π : Finset (Finset (BirthAddr B J ℓ Bc n))) : Finset ℕ :=
  (π.biUnion id).image (edgeIndex B J ℓ Bc n)

/-- "At most `2r` edges are affected by a rank-`r` collection" [S-02:1218]. -/
theorem card_affectedEdges_le {B : Type} [Fintype B] [DecidableEq B] {J ℓ Bc n : ℕ}
    {π : Finset (Finset (BirthAddr B J ℓ Bc n))}
    (hπ : π ∈ blockCollections (BirthAddr B J ℓ Bc n)) :
    (affectedEdges π).card ≤ 2 * blockRank π := by
  show ((π.biUnion id).image (edgeIndex B J ℓ Bc n)).card ≤ 2 * blockRank π
  exact Finset.card_image_le.trans (card_biUnion_le_two_mul_blockRank hπ)

/-- The edge of a target slot which is in a block is affected. -/
theorem mem_affectedEdges {B : Type} [DecidableEq B] {J ℓ Bc n : ℕ}
    {π : Finset (Finset (BirthAddr B J ℓ Bc n))} (a : Fin n × B × Slot J ℓ)
    (ha : Sum.inr (Sum.inl a) ∈ π.biUnion id) : a.1.val ∈ affectedEdges π := by
  show a.1.val ∈ (π.biUnion id).image (edgeIndex B J ℓ Bc n)
  exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inl a), ha, rfl⟩

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

/-! ### A bound for the prime values -/

/-- A number larger than all big primes: the modulus of the Fourier parameters. -/
def primeBound (𝒢 : GroupFamily S B) : ℕ := (bigPrimes 𝒢).sup id + 1

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
theorem primeBound_pos (𝒢 : GroupFamily S B) : 0 < primeBound 𝒢 := by
  unfold primeBound
  omega

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
theorem lt_primeBound {g : B} {p : ℕ} (hp : p ∈ 𝒢.big g) : p < primeBound 𝒢 := by
  have h : id p ≤ (bigPrimes 𝒢).sup id := Finset.le_sup (mem_bigPrimes.mpr ⟨g, hp⟩)
  have h' : p ≤ (bigPrimes 𝒢).sup id := h
  unfold primeBound
  omega

/-! ### The births of a history -/

omit [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem History.birth_inl {D : MemData 𝒢 J ℓ N} {Bc : ℕ} (h : History D Bc)
    (a : B × Slot J ℓ) : h.birth (Sum.inl a) = some (h.xb₀ a.1 a.2 : ℕ) := rfl

omit [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem History.birth_edge {D : MemData 𝒢 J ℓ N} {Bc : ℕ} (h : History D Bc)
    (a : Fin D.n × B × Slot J ℓ) :
    h.birth (Sum.inr (Sum.inl a)) = edgeBirths (h.edge a.1).2.1 a.2.1 a.2.2 := rfl

omit [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem History.birth_ghost {D : MemData 𝒢 J ℓ N} {Bc : ℕ} (h : History D Bc)
    (a : Fin (D.n + 1) × B × Fin Bc) :
    h.birth (Sum.inr (Sum.inr a)) =
      if hj : a.2.2.val < (h.ghost a.1 a.2.1).2.1.val then
        some ((h.ghost a.1 a.2.1).2.2 ⟨a.2.2.val, hj⟩ : ℕ)
      else none := rfl

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- Every prime born at an address of a history is a big prime, hence smaller than
`primeBound 𝒢`. -/
theorem History.birth_lt {D : MemData 𝒢 J ℓ N} {Bc : ℕ} (h : History D Bc)
    (β : BirthAddr B J ℓ Bc D.n) (p : ℕ) (hp : h.birth β = some p) : p < primeBound 𝒢 := by
  rcases β with a | a | a
  · rw [h.birth_inl] at hp
    have h1 := Option.some.inj hp
    rw [← h1]
    exact lt_primeBound (h.xb₀ a.1 a.2).2
  · rw [h.birth_edge] at hp
    unfold edgeBirths at hp
    have h1 := ite_some_none_eq_some hp
    rw [← h1]
    exact lt_primeBound ((h.edge a.1).2.1.xbT a.2.1 a.2.2).2
  · rw [h.birth_ghost] at hp
    obtain ⟨hj, h1⟩ := dite_some_none_eq_some hp
    rw [← h1]
    exact lt_primeBound ((h.ghost a.1 a.2.1).2.2 ⟨a.2.2.val, hj⟩).2

/-! ### The multipliers -/

/-- **The Fourier multipliers of the operations** [S-02:1183–1191], for the collection `π` and the
Fourier parameters `t`: the initial boundary vector, the visit operation `G_i` and the edge
operation `ℰ_i` are multiplied by the product of the multipliers `addrMult` of their own
addresses, which are functions of the births of that operation. -/
def fourierMult (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) : BirthMult 𝒢 J ℓ Bc where
  init := fun xb => ∏ a : B × Slot J ℓ, addrMult π Q t (Sum.inl a) (some (xb a.1 a.2 : ℕ))
  ghost := fun i b =>
    if hi : i < D.n + 1 then
      ∏ a : B × Fin Bc, addrMult π Q t (Sum.inr (Sum.inr (⟨i, hi⟩, a.1, a.2)))
        (if hj : a.2.val < (b a.1).1.val then some ((b a.1).2 ⟨a.2.val, hj⟩ : ℕ) else none)
    else 1
  edge := fun i births =>
    if hi : i < D.n then
      ∏ a : B × Slot J ℓ,
        addrMult π Q t (Sum.inr (Sum.inl (⟨i, hi⟩, a.1, a.2))) (births a.1 a.2)
    else 1

omit [Fintype S] [DecidableEq S] [Fintype N] in
theorem fourierMult_init (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q)
    (xb : LabelList 𝒢.big J ℓ) :
    (fourierMult D Bc π Q t).init xb =
      ∏ a : B × Slot J ℓ, addrMult π Q t (Sum.inl a) (some (xb a.1 a.2 : ℕ)) := rfl

omit [Fintype S] [DecidableEq S] [Fintype N] in
theorem fourierMult_ghost_of_lt (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) {i : ℕ}
    (hi : i < D.n + 1) (b : (g : B) → Batch 𝒢 Bc g) :
    (fourierMult D Bc π Q t).ghost i b =
      ∏ a : B × Fin Bc, addrMult π Q t (Sum.inr (Sum.inr (⟨i, hi⟩, a.1, a.2)))
        (if hj : a.2.val < (b a.1).1.val then some ((b a.1).2 ⟨a.2.val, hj⟩ : ℕ) else none) :=
  dif_pos hi

omit [Fintype S] [DecidableEq S] [Fintype N] in
theorem fourierMult_ghost_of_not_lt (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) {i : ℕ}
    (hi : ¬i < D.n + 1) (b : (g : B) → Batch 𝒢 Bc g) :
    (fourierMult D Bc π Q t).ghost i b = 1 :=
  dif_neg hi

omit [Fintype S] [DecidableEq S] [Fintype N] in
theorem fourierMult_edge_of_lt (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) {i : ℕ}
    (hi : i < D.n) (births : (g : B) → Slot J ℓ → Option ℕ) :
    (fourierMult D Bc π Q t).edge i births =
      ∏ a : B × Slot J ℓ,
        addrMult π Q t (Sum.inr (Sum.inl (⟨i, hi⟩, a.1, a.2))) (births a.1 a.2) :=
  dif_pos hi

omit [Fintype S] [DecidableEq S] [Fintype N] in
theorem fourierMult_edge_of_not_lt (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) {i : ℕ}
    (hi : ¬i < D.n) (births : (g : B) → Slot J ℓ → Option ℕ) :
    (fourierMult D Bc π Q t).edge i births = 1 :=
  dif_neg hi

omit [Fintype S] [DecidableEq S] [Fintype N] in
/-- The multiplier of the initial boundary vector has modulus at most one. -/
theorem norm_fourierMult_init_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q)
    (xb : LabelList 𝒢.big J ℓ) : ‖(fourierMult D Bc π Q t).init xb‖ ≤ 1 := by
  rw [fourierMult_init D Bc π Q t xb]
  refine norm_prod_le_one _ fun a => ?_
  exact norm_addrMult_le π Q t _ _

omit [Fintype S] [DecidableEq S] [Fintype N] in
/-- The multipliers of the visit operations have modulus at most one. -/
theorem norm_fourierMult_ghost_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) (i : ℕ)
    (b : (g : B) → Batch 𝒢 Bc g) : ‖(fourierMult D Bc π Q t).ghost i b‖ ≤ 1 := by
  by_cases hi : i < D.n + 1
  · rw [fourierMult_ghost_of_lt D Bc π Q t hi b]
    refine norm_prod_le_one _ fun a => ?_
    exact norm_addrMult_le π Q t _ _
  · rw [fourierMult_ghost_of_not_lt D Bc π Q t hi b]
    exact le_of_eq norm_one

omit [Fintype S] [DecidableEq S] [Fintype N] in
/-- The multipliers of the edge operations have modulus at most one. -/
theorem norm_fourierMult_edge_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) (i : ℕ)
    (births : (g : B) → Slot J ℓ → Option ℕ) :
    ‖(fourierMult D Bc π Q t).edge i births‖ ≤ 1 := by
  by_cases hi : i < D.n
  · rw [fourierMult_edge_of_lt D Bc π Q t hi births]
    refine norm_prod_le_one _ fun a => ?_
    exact norm_addrMult_le π Q t _ _
  · rw [fourierMult_edge_of_not_lt D Bc π Q t hi births]
    exact le_of_eq norm_one

omit [Fintype S] [DecidableEq S] [Fintype N] in
/-- **Unaffected edges keep their operation** [S-02:1194–1196]: the multiplier of an edge none of
whose target slots is in a block is `1`. -/
theorem fourierMult_edge_of_not_affected (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) {i : ℕ}
    (hi : i < D.n) (hia : i ∉ affectedEdges π) :
    (fourierMult D Bc π Q t).edge i = fun _ => 1 := by
  funext births
  rw [fourierMult_edge_of_lt D Bc π Q t hi births]
  refine Finset.prod_eq_one fun a _ => addrMult_of_notMem π Q t ?_ _
  intro hmem
  exact hia (mem_affectedEdges (⟨i, hi⟩, a.1, a.2) hmem)

/-! ### The value of the multipliers on a history -/

omit [DecidableEq S] [Fintype N] in
theorem History.fourierMult_ghost {D : MemData 𝒢 J ℓ N} {Bc : ℕ} (h : History D Bc)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) (i : Fin (D.n + 1)) :
    (fourierMult D Bc π Q t).ghost i.val (ghostBirths (h.ghost i)) =
      ∏ a : B × Fin Bc,
        addrMult π Q t (Sum.inr (Sum.inr (i, a))) (h.birth (Sum.inr (Sum.inr (i, a)))) :=
  fourierMult_ghost_of_lt D Bc π Q t i.isLt (ghostBirths (h.ghost i))

omit [DecidableEq S] [Fintype N] in
theorem History.fourierMult_edge {D : MemData 𝒢 J ℓ N} {Bc : ℕ} (h : History D Bc)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) (i : Fin D.n) :
    (fourierMult D Bc π Q t).edge i.val (edgeBirths (h.edge i).2.1) =
      ∏ a : B × Slot J ℓ,
        addrMult π Q t (Sum.inr (Sum.inl (i, a))) (h.birth (Sum.inr (Sum.inl (i, a)))) :=
  fourierMult_edge_of_lt D Bc π Q t i.isLt (edgeBirths (h.edge i).2.1)

omit [DecidableEq S] [Fintype N] in
/-- **The value of the Fourier multipliers on a history is the product over all addresses** of
the multipliers of the births of the history: "collect the factors by their birth operation"
[S-02:1183–1184]. -/
theorem History.mult_fourierMult {D : MemData 𝒢 J ℓ N} {Bc : ℕ} (h : History D Bc)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) :
    h.mult (fourierMult D Bc π Q t) =
      ∏ β : BirthAddr B J ℓ Bc D.n, addrMult π Q t β (h.birth β) := by
  have hI : (fourierMult D Bc π Q t).init h.xb₀ =
      ∏ a : B × Slot J ℓ, addrMult π Q t (Sum.inl a) (h.birth (Sum.inl a)) := rfl
  have hG : ∏ i : Fin (D.n + 1), (fourierMult D Bc π Q t).ghost i.val (ghostBirths (h.ghost i)) =
      ∏ a : Fin (D.n + 1) × B × Fin Bc,
        addrMult π Q t (Sum.inr (Sum.inr a)) (h.birth (Sum.inr (Sum.inr a))) := by
    rw [Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ => h.fourierMult_ghost π Q t i
  have hE : ∏ i : Fin D.n, (fourierMult D Bc π Q t).edge i.val (edgeBirths (h.edge i).2.1) =
      ∏ a : Fin D.n × B × Slot J ℓ,
        addrMult π Q t (Sum.inr (Sum.inl a)) (h.birth (Sum.inr (Sum.inl a))) := by
    rw [Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ => h.fourierMult_edge π Q t i
  have hsplit : ∏ β : BirthAddr B J ℓ Bc D.n, addrMult π Q t β (h.birth β) =
      (∏ a : B × Slot J ℓ, addrMult π Q t (Sum.inl a) (h.birth (Sum.inl a))) *
        ((∏ a : Fin D.n × B × Slot J ℓ,
            addrMult π Q t (Sum.inr (Sum.inl a)) (h.birth (Sum.inr (Sum.inl a)))) *
          ∏ a : Fin (D.n + 1) × B × Fin Bc,
            addrMult π Q t (Sum.inr (Sum.inr a)) (h.birth (Sum.inr (Sum.inr a)))) := by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  show (fourierMult D Bc π Q t).init h.xb₀ *
      (∏ i : Fin (D.n + 1), (fourierMult D Bc π Q t).ghost i.val (ghostBirths (h.ghost i))) *
      ∏ i : Fin D.n, (fourierMult D Bc π Q t).edge i.val (edgeBirths (h.edge i).2.1) = _
  rw [hI, hG, hE, hsplit]
  ring

/-! ### The Fourier representation of the path integral with the indicator of `𝒞_π` -/

open _root_.Classical in
/-- **The path integral with the indicator of `𝒞_π` is the average over the Fourier parameters of
the path integrals with the Fourier multipliers** (eq:birth-equality-fourier) [S-02:1172–1184]:
`#{t} · rankPart(π) = ∑_t ∑_h Φ_t(h) weight(h)`. The modulus `primeBound 𝒢` is larger than all
big primes, so that two primes which are congruent are equal. -/
theorem card_mul_rankPart (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n)))
    (hπ : π ∈ blockCollections (BirthAddr B J ℓ Bc D.n)) :
    (Fintype.card (BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin (primeBound 𝒢)) : ℂ) *
        rankPart D Bc θ π =
      ∑ t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin (primeBound 𝒢),
        ∑ h : History D Bc, h.mult (fourierMult D Bc π (primeBound 𝒢) t) * h.weight θ := by
  have key : ∀ h : History D Bc,
      (Fintype.card
            (BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin (primeBound 𝒢)) : ℂ) *
          (if BlockConstraint h.birth π then h.weight θ else 0) =
        ∑ t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin (primeBound 𝒢),
          h.mult (fourierMult D Bc π (primeBound 𝒢) t) * h.weight θ := by
    intro h
    rw [← Finset.sum_mul,
      Finset.sum_congr rfl fun t _ => h.mult_fourierMult π (primeBound 𝒢) t,
      sum_prod_addrMult π hπ (primeBound 𝒢) (primeBound_pos 𝒢) h.birth h.birth_lt]
    by_cases hC : BlockConstraint h.birth π
    · rw [if_pos hC, if_pos hC]
      ring
    · rw [if_neg hC, if_neg hC]
      ring
  unfold rankPart
  rw [Finset.mul_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun h _ => key h

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
