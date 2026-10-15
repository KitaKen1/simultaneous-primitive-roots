module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Operators
public import SimultaneousPrimitiveRoots.Unconditional.Graph.BirthDistinctness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The expanded path integral of the memory evolution: histories, births, equality rank

Source: `verification/stage7-sources/S-02.tex`, lines 516–535 and 1043–1105
(`[S-02:0516–0535, 1043–1105]`).

The memory identity is about `⟨𝟏_∅, G_0 ℰ_0 G_1 ⋯ ℰ_{N-1} G_N 𝟏_∅⟩_distinct`, where "the
subscript means that the indicator is inserted in the expanded path integral, not that each local
operator separately enforces it" [S-02:0532–0534]. This file defines the expanded path integral.

* `History` — a term of the expanded path integral: the initial small residues and active lists
  (the memory starts empty) and one local transition choice for each of the operations
  `G_0, ℰ_0, G_1, …, ℰ_{N-1}, G_N`. `History.visitState` is the state before `G_i`;
  `History.weight` is the product of the measure of the initial state, of all coefficients, and
  of `𝟏_∅` at the final state.
* `BirthAddr`, `History.birth` — the potential birth addresses of [S-02:1053–1062]: "initial big
  slots; every possible big target slot at every edge, in its canonical order before final
  symmetrization; and indices `1, …, B` in each group's ordered ghost batch at each visit", and
  the prime born at an address if the address is performed.
* `distinctSum` — the path integral with the distinct-birth rule: "all prime values assigned at
  different births are distinct" [S-02:0516–0521] (`Graph.PerformedBirthsDistinct`).
* `blockCollections`, `blockMu`, `blockRank`, `BlockConstraint`, `rankPart`, `absRankPart` — the
  collections `π` of disjoint blocks of addresses of size at least two, `μ(π)`, `r(π)`, the
  constraint `𝒞_π` of (eq:distinct-birth-expansion) [S-02:1070–1079], and the path integral with
  the indicator of `𝒞_π`, with signed and with absolute weights.
* `memTailWith`, `History.mult`, `HistoryExpansion` — the operator product with multipliers on
  the births, and the statement that the path integral with these multipliers is its matrix
  element between boundary vectors.

Proved here: `birthAddr_card` (the number of addresses is the left side of
(eq:birth-address-count)), `distinctSum_eq_sum_rankPart` (the expansion of the path integral by
(eq:distinct-indicator)), `norm_rankPart_le` and `blockRank_le_card`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Collections of blocks -/

section Blocks

variable {I : Type}

open _root_.Classical in
/-- **The collections `π` of disjoint blocks of addresses, every block having size at least two**
[S-02:1071–1073]. -/
def blockCollections (I : Type) [Fintype I] : Finset (Finset (Finset I)) :=
  Finset.univ.filter fun π =>
    (∀ b ∈ π, 2 ≤ b.card) ∧ ∀ b ∈ π, ∀ b' ∈ π, b ≠ b' → Disjoint b b'

/-- `μ(π) = ∏_{B' ∈ π} (-1)^{|B'| - 1} (|B'| - 1)!` of (eq:distinct-birth-expansion)
[S-02:1076–1079]. -/
def blockMu (π : Finset (Finset I)) : ℤ :=
  ∏ b ∈ π, (-1) ^ (b.card - 1) * ((b.card - 1).factorial : ℤ)

/-- `r(π) = ∑_{B' ∈ π} (|B'| - 1)`, the rank of (eq:distinct-birth-expansion) [S-02:1076–1079]:
the number of independent equalities. -/
def blockRank (π : Finset (Finset I)) : ℕ := ∑ b ∈ π, (b.card - 1)

/-- **The constraint `𝒞_π`** [S-02:1073–1075]: "all addresses in those blocks [are] performed and
… the prime values within each block [are] equal". -/
def BlockConstraint {Z : Type} (birth : I → Option Z) (π : Finset (Finset I)) : Prop :=
  ∀ b ∈ π, ∃ z : Z, ∀ i ∈ b, birth i = some z

theorem mem_blockCollections [Fintype I] {π : Finset (Finset I)} :
    π ∈ blockCollections I ↔
      (∀ b ∈ π, 2 ≤ b.card) ∧ ∀ b ∈ π, ∀ b' ∈ π, b ≠ b' → Disjoint b b' := by
  classical
  unfold blockCollections
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

/-- "A rank-`r` collection involves at most `2r` addresses" [S-02:1095]; in particular its rank is
at most the number of addresses. -/
theorem blockRank_le_card [Fintype I] [DecidableEq I] {π : Finset (Finset I)}
    (hπ : π ∈ blockCollections I) : blockRank π ≤ Fintype.card I := by
  have hdisj := (mem_blockCollections.mp hπ).2
  have h1 : blockRank π ≤ ∑ b ∈ π, b.card := Finset.sum_le_sum fun b _ => Nat.sub_le _ _
  have h2 : (π.biUnion id).card = ∑ b ∈ π, b.card :=
    Finset.card_biUnion fun b hb b' hb' hne => hdisj b hb b' hb' hne
  calc blockRank π ≤ ∑ b ∈ π, b.card := h1
    _ = (π.biUnion id).card := h2.symm
    _ ≤ Fintype.card I := Finset.card_le_univ _

open _root_.Classical in
/-- **(eq:distinct-indicator)** [S-02:1080–1093]: "for a fixed realized path,
`1_{distinct performed birth values} = ∑_π μ(π) 1_{𝒞_π}`."

A statement about an arbitrary assignment `birth : I → Option ℕ` on a finite set of addresses;
no path is involved. `Graph.performed_birth_permutation_expansion` proves the intermediate form of
the paper's argument (the signed sum over the permutations of the addresses which preserve the
birth values); what remains is the passage from permutations to collections of cycles ("there are
`(h - 1)!` such cycles, each with sign `(-1)^{h-1}`"). -/
def DistinctIndicatorExpansion : Prop :=
  ∀ (I : Type) [Fintype I] (birth : I → Option ℕ),
    (∑ π ∈ blockCollections I, blockMu π * (if BlockConstraint birth π then (1 : ℤ) else 0)) =
      if Graph.PerformedBirthsDistinct birth then 1 else 0

open _root_.Classical in
/-- **(eq:rank-coefficient-count)** [S-02:1095–1105]: "its total absolute coefficient, summed over
all collections of rank `r`, obeys `∑_{r(π) = r} |μ(π)| ≤ A_*^{2r}`", `A_*` the number of
addresses. A statement about a finite set of addresses. -/
def RankCoefficientCount : Prop :=
  ∀ (I : Type) [Fintype I] (r : ℕ),
    (∑ π ∈ (blockCollections I).filter (fun π => blockRank π = r), |blockMu π|) ≤
      (Fintype.card I : ℤ) ^ (2 * r)

end Blocks

/-! ### Histories -/

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

/-- **A term of the expanded path integral** of `⟨𝟏_∅, G_0 ℰ_0 G_1 ⋯ ℰ_{N-1} G_N 𝟏_∅⟩`
[S-02:0523–0534]: the initial small residues `y₀`, the initial small and big active lists, a
local choice of the visit operation at each visit `0, …, N` and a local choice of the edge
operation (source permutation, row choice, target permutation) at each edge `0, …, N - 1`. The
memory starts empty. -/
structure History (D : MemData 𝒢 J ℓ N) (Bc : ℕ) where
  /-- the initial small residues -/
  y₀ : ResVec (smallPrimes 𝒢)
  /-- the initial small list -/
  xs₀ : LabelList 𝒢.small J ℓ
  /-- the initial big active list; its `M |ℬ|` slots are births -/
  xb₀ : LabelList 𝒢.big J ℓ
  /-- the choices of the visit operations `G_0, …, G_N` -/
  ghost : Fin (D.n + 1) → GhostChoice 𝒢 Bc
  /-- the choices of the edge operations `ℰ_0, …, ℰ_{N-1}` -/
  edge : Fin D.n → EdgeFullChoice D Bc

variable {D : MemData 𝒢 J ℓ N} {Bc : ℕ}

/-- A history is the tuple of its components. -/
def History.equivProd : History D Bc ≃
    ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ ×
      (Fin (D.n + 1) → GhostChoice 𝒢 Bc) × (Fin D.n → EdgeFullChoice D Bc) where
  toFun h := (h.y₀, h.xs₀, h.xb₀, h.ghost, h.edge)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv h := by
    cases h
    rfl
  right_inv t := by
    rcases t with ⟨a, b, c, d, e⟩
    rfl

instance History.instFintype : Fintype (History D Bc) := by
  haveI h1 : Fintype (LabelList 𝒢.small J ℓ) := inferInstance
  haveI h2 : Fintype (LabelList 𝒢.big J ℓ) := inferInstance
  haveI h3 : Fintype (GhostChoice 𝒢 Bc) := inferInstance
  haveI h4 : Fintype (ListPerms S B J ℓ) := inferInstance
  haveI h5 : Fintype (EdgeFullChoice D Bc) := inferInstance
  exact Fintype.ofEquiv _ History.equivProd.symm

/-- The initial state: the initial lists and empty memories. -/
def History.init (h : History D Bc) : MState 𝒢 J ℓ Bc :=
  ⟨h.y₀, h.xs₀, h.xb₀, fun g => emptyMem 𝒢 Bc g⟩

/-- The state at the visit `i`, before the visit operation `G_i` ("`G_i` acts after arrival and
promotion at visit `i`, and before storage and departure", [S-02:0439–0440]). -/
def History.visitState (h : History D Bc) : ℕ → MState 𝒢 J ℓ Bc
  | 0 => h.init
  | i + 1 =>
    if hi : i < D.n then
      edgeFullTgt D i (ghostTgt (h.visitState i) (h.ghost (Fin.castSucc ⟨i, hi⟩)))
        (h.edge ⟨i, hi⟩)
    else h.visitState i

/-- The state at the visit `i` after the visit operation `G_i`. -/
def History.afterGhost (h : History D Bc) (i : Fin (D.n + 1)) : MState 𝒢 J ℓ Bc :=
  ghostTgt (h.visitState i.val) (h.ghost i)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem History.visitState_succ (h : History D Bc) (i : Fin D.n) :
    h.visitState (i.val + 1) = edgeFullTgt D i.val (h.afterGhost i.castSucc) (h.edge i) := by
  show (if hi : i.val < D.n then _ else _) = _
  rw [dif_pos i.isLt]
  rfl

/-- **The weight of a history**: the measure of the initial state, times the coefficients of
`G_0, ℰ_0, …, ℰ_{N-1}, G_N` along the history, times `𝟏_∅` at the final state ("at visit `N`
[the memory] must end empty", [S-02:0553–0554]). The phase `e(θ h_N)` of (eq:return-fourier) is
the product of the phases of the edges. -/
def History.weight (θ : ℝ) (h : History D Bc) : ℂ :=
  ((memWeight 𝒢 D.q D.n h.init : ℝ) : ℂ) *
    (∏ i : Fin D.n,
      ((ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) : ℝ) : ℂ) *
        edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)) *
    (((ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n)) : ℝ) : ℂ) *
      emptyVec 𝒢 J ℓ Bc (h.afterGhost (Fin.last D.n)))

/-! ### Births -/

/-- **The potential birth addresses** [S-02:1053–1057]: "initial big slots; every possible big
target slot at every edge, in its canonical order before final symmetrization; and indices
`1, …, B` in each group's ordered ghost batch at each visit". -/
abbrev BirthAddr (B : Type) (J ℓ Bc n : ℕ) : Type :=
  (B × Slot J ℓ) ⊕ (Fin n × B × Slot J ℓ) ⊕ (Fin (n + 1) × B × Fin Bc)

/-- **The number `A_*` of potential addresses** is the left side of (eq:birth-address-count)
[S-02:1063–1066]: `M |ℬ| + N M |ℬ| + (N + 1) |ℬ| B = M |ℬ| (N + 1) + (N + 1) |ℬ| B`. -/
theorem birthAddr_card (B : Type) [Fintype B] (J ℓ Bc n : ℕ) :
    Fintype.card (BirthAddr B J ℓ Bc n) =
      (J + ℓ) * Fintype.card B * (n + 1) + (n + 1) * Fintype.card B * Bc := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- **The prime born at an address, if the address is performed** [S-02:1058–1062]. Every initial
big slot is performed. "A target slot is performed as an address precisely when it is a fresh
birth rather than shared or promoted. A ghost address is performed precisely when its batch is at
least that large. These are conditions on the choices made in their single local operation." -/
def History.birth (h : History D Bc) : BirthAddr B J ℓ Bc D.n → Option ℕ
  | Sum.inl a => some (h.xb₀ a.1 a.2 : ℕ)
  | Sum.inr (Sum.inl a) => edgeBirths (h.edge a.1).2.1 a.2.1 a.2.2
  | Sum.inr (Sum.inr a) =>
    if hj : a.2.2.val < (h.ghost a.1 a.2.1).2.1.val then
      some ((h.ghost a.1 a.2.1).2.2 ⟨a.2.2.val, hj⟩ : ℕ)
    else none

open _root_.Classical in
/-- **The path integral with the distinct-birth rule**,
`⟨𝟏_∅, G_0 ℰ_0 G_1 ⋯ ℰ_{N-1} G_N 𝟏_∅⟩_distinct` of (eq:memory-product) [S-02:0526–0534], with the
memory truncated to total size at most `Bc`: the sum of the weights of the histories in which
"all prime values assigned at different births are distinct. Births comprise initial active slots,
fresh active target slots, and ghost births. This is a global rule" [S-02:0516–0520]. -/
def distinctSum (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) : ℂ :=
  ∑ h : History D Bc, if Graph.PerformedBirthsDistinct h.birth then h.weight θ else 0

open _root_.Classical in
/-- The path integral with the indicator of the constraint `𝒞_π` inserted [S-02:1080–1084]. -/
def rankPart (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) : ℂ :=
  ∑ h : History D Bc, if BlockConstraint h.birth π then h.weight θ else 0

open _root_.Classical in
/-- "The total absolute contribution for this fixed collection" [S-02:1150–1151]: the sum of the
moduli of the weights of the histories which satisfy `𝒞_π`. -/
def absRankPart (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) : ℝ :=
  ∑ h : History D Bc, if BlockConstraint h.birth π then ‖h.weight θ‖ else 0

theorem norm_rankPart_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n))) :
    ‖rankPart D Bc θ π‖ ≤ absRankPart D Bc θ π := by
  unfold rankPart absRankPart
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun h _ => ?_))
  split_ifs
  · rfl
  · exact norm_zero

open _root_.Classical in
/-- **The expansion of the path integral by (eq:distinct-indicator)** [S-02:1243]: "apply
(eq:distinct-indicator) in the truncated memory identity":
`⟨…⟩_distinct = ∑_π μ(π) · (path integral with the indicator of 𝒞_π)`. -/
theorem distinctSum_eq_sum_rankPart (hexp : DistinctIndicatorExpansion) (D : MemData 𝒢 J ℓ N)
    (Bc : ℕ) (θ : ℝ) :
    distinctSum D Bc θ =
      ∑ π ∈ blockCollections (BirthAddr B J ℓ Bc D.n),
        ((blockMu π : ℤ) : ℂ) * rankPart D Bc θ π := by
  have key : ∀ h : History D Bc,
      (if Graph.PerformedBirthsDistinct h.birth then h.weight θ else 0) =
        ∑ π ∈ blockCollections (BirthAddr B J ℓ Bc D.n),
          ((blockMu π : ℤ) : ℂ) * (if BlockConstraint h.birth π then h.weight θ else 0) := by
    intro h
    calc (if Graph.PerformedBirthsDistinct h.birth then h.weight θ else 0)
        = (((if Graph.PerformedBirthsDistinct h.birth then (1 : ℤ) else 0 : ℤ)) : ℂ) *
            h.weight θ := by
          split_ifs <;> simp
      _ = ((∑ π ∈ blockCollections (BirthAddr B J ℓ Bc D.n),
              blockMu π * (if BlockConstraint h.birth π then (1 : ℤ) else 0) : ℤ) : ℂ) *
            h.weight θ := by
          rw [hexp]
      _ = ∑ π ∈ blockCollections (BirthAddr B J ℓ Bc D.n),
            ((blockMu π : ℤ) : ℂ) * (if BlockConstraint h.birth π then h.weight θ else 0) := by
          rw [Int.cast_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun π _ => ?_
          split_ifs <;> simp
  unfold distinctSum rankPart
  rw [Finset.sum_congr rfl fun h _ => key h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun π _ => (Finset.mul_sum _ _ _).symm

/-! ### The operator product -/

/-- **Multipliers on the births**, one for every operation [S-02:1183–1191]: on the initial big
list, on the batches of each visit operation, and on the fresh births of each edge. -/
structure BirthMult (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) where
  /-- the multiplier of the initial boundary vector, a function of the initial big list -/
  init : LabelList 𝒢.big J ℓ → ℂ
  /-- the multiplier of the visit operation `G_i`, a function of its batches -/
  ghost : ℕ → ((g : B) → Batch 𝒢 Bc g) → ℂ
  /-- the multiplier of the edge operation `ℰ_i`, a function of its fresh births -/
  edge : ℕ → ((g : B) → Slot J ℓ → Option ℕ) → ℂ

/-- The trivial multipliers. -/
def BirthMult.one (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) : BirthMult 𝒢 J ℓ Bc :=
  ⟨fun _ => 1, fun _ _ => 1, fun _ _ => 1⟩

/-- The value of a family of multipliers on a history: the product over all operations. -/
def History.mult (Φ : BirthMult 𝒢 J ℓ Bc) (h : History D Bc) : ℂ :=
  Φ.init h.xb₀ * (∏ i : Fin (D.n + 1), Φ.ghost i.val (ghostBirths (h.ghost i))) *
    ∏ i : Fin D.n, Φ.edge i.val (edgeBirths (h.edge i).2.1)

/-- `G_j ℰ_j G_{j+1} ⋯ ℰ_{N-1} G_N 𝟏_∅` for `j = N - m`, with the multipliers `Φ` on the births of
the operations (`m = 0` is `G_N 𝟏_∅`). -/
def memTailWith (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc) (θ : ℝ) :
    ℕ → MState 𝒢 J ℓ Bc → ℂ
  | 0 => ghostOpWith D Bc (Φ.ghost D.n) D.n (emptyVec 𝒢 J ℓ Bc)
  | m + 1 =>
    ghostOpWith D Bc (Φ.ghost (D.n - (m + 1))) (D.n - (m + 1))
      (edgeOpWith D Bc (Φ.edge (D.n - (m + 1))) θ (D.n - (m + 1)) (memTailWith D Bc Φ θ m))

/-- **The path integral is the matrix element of the operator product**: for every family `Φ` of
multipliers on the births,
`∑_h Φ(h) weight(h) = ∫ Φ_init · 𝟏_∅ · (G_0^Φ ℰ_0^Φ G_1^Φ ⋯ ℰ_{N-1}^Φ G_N^Φ 𝟏_∅) dm`,
the integral being over the states with the measure `memWeight`. For `Φ = 1` the right side is
`⟨𝟏_∅, G_0 ℰ_0 ⋯ G_N 𝟏_∅⟩`. This is what "the expanded path integral" [S-02:0532–0534] means, and
it is how "each affected operation is multiplied, on its individual local choices" [S-02:1184–1189]
in the small-rank argument. An exact statement for every family of groups. -/
def HistoryExpansion : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc)
    (θ : ℝ),
    (∑ h : History D Bc, h.mult Φ * h.weight θ) =
      ∑ s : MState 𝒢 J ℓ Bc, ((memWeight 𝒢 D.q D.n s : ℝ) : ℂ) *
        (Φ.init s.xb * emptyVec 𝒢 J ℓ Bc s * memTailWith D Bc Φ θ D.n s)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
