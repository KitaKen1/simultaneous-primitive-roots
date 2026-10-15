module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.BirthStages
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The distinct-birth rule as a running set of born primes: `BornSetRecursion`

Source: `verification/stage7-sources/S-02.tex`, lines 516–521 (`[S-02:0516–0521]`).

`bornSetRecursion : BornSetRecursion` is proved here: the memory sum of a skeleton (the sum over
the decorations with pairwise distinct births of the memory part of the weight) is the measure of
the initial big list times the recursively defined `Skel.fut N`, started with empty memories and
the set of the initial labels; zero if two initial slots have the same label.

## The proof

* The sums of one operation with new births (`Skel.ghostSum`, `Skel.edgeSum`) are row sums on the
  states `(memories, set of born primes)` (`BornState`) with the coefficients `Skel.gCoef`,
  `Skel.eCoef` (the memory coefficients times the indicator `NewBirths`) and the targets `bornGhostTgt`,
  `Skel.eTgt` (`Skel.ghostSum_eq`, `Skel.edgeSum_eq`).
* So `Skel.fut m` is the alternating product `altTail` of `HistoryExpansionProof.lean`
  (`Skel.futC`), hence the sum over the words of the product of the coefficients along the walk
  (`altTail_eq_sum`).
* A decoration is a word of `N` double choices and a last choice (`decoWordEquiv`); the states of
  its walk are `(Skel.memAt d i, Skel.bornAt d i)` (`walk_ofFn`). This gives
  `fut N = ∑_d stepW d` (`Skel.fut_eq_sum_stepW`).
* `stepW d` is the memory weight `Skel.memW d` if the births of every operation are new, and zero
  otherwise (`Skel.stepW_eq`); the births of all operations are new and the initial labels are
  distinct if and only if the births of the history are pairwise distinct
  (`Skel.distinct_iff_newBirths`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Two lemmas on `if` -/

theorem memId_ite_mul_right_zero {P : Prop} {hP : Decidable P} (a b : ℝ) :
    (@ite ℝ P hP (a * b) 0) = (@ite ℝ P hP a 0) * b := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]

theorem memId_of_ite_ne_zero {P : Prop} {hP : Decidable P} {a : ℝ} (h : (@ite ℝ P hP a 0) ≠ 0) : P := by
  by_contra hn
  exact h (if_neg hn)

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {D : MemData 𝒢 J ℓ N} {Bc : ℕ}

/-! ### States with the set of born primes -/

/-- The memories together with the set of the primes born so far. -/
abbrev BornState (𝒢 : GroupFamily S B) (Bc : ℕ) : Type := ((g : B) → Mem 𝒢 Bc g) × Finset ℕ

/-- The stores and the promotions of one edge. -/
abbrev EdgeDeco (B : Type) (J ℓ Bc : ℕ) : Type :=
  ((g : B) → Finset (Slot J ℓ)) × ((g : B) → Slot J ℓ → Option (Fin Bc))

/-- The words of double choices with a last choice form a finite type (a named instance: the
instance found by unfolding the nested products is larger than the default
`synthInstance.maxSize`). -/
instance wordDecoFintype (𝒢 : GroupFamily S B) (J ℓ Bc n : ℕ) :
    Fintype ((Fin n → GhostChoice 𝒢 Bc × EdgeDeco B J ℓ Bc) × GhostChoice 𝒢 Bc) :=
  instFintypeProd _ _

open _root_.Classical in
/-- The coefficient of the visit operation `G_j` with the indicator of new births. -/
def Skel.gCoef (sk : Skel D) (Bc : ℕ) (j : ℕ) (x : BornState 𝒢 Bc) (c : GhostChoice 𝒢 Bc) : ℝ :=
  if NewBirths (ghostAddrBirth c) x.2 then ghostCoef D j (sk.mstate j x.1) c else 0

/-- The state after a visit operation. -/
def bornGhostTgt (x : BornState 𝒢 Bc) (c : GhostChoice 𝒢 Bc) : BornState 𝒢 Bc :=
  (fun g => ghostNewMem (x.1 g) (c g), x.2 ∪ birthSet (ghostAddrBirth c))

open _root_.Classical in
/-- The memory part of the coefficient of the edge `j` with the indicator of new fresh births
(zero for `j ≥ N`). -/
def Skel.eCoef (sk : Skel D) (Bc : ℕ) (j : ℕ) (x : BornState 𝒢 Bc) (ξ : EdgeDeco B J ℓ Bc) : ℝ :=
  if h : j < D.n then
    (if NewBirths (edgeAddrBirth (sk.edgeChoice ⟨j, h⟩ ξ.1 ξ.2)) x.2 then
      edgeMemCoef D j ((sk.mstate j x.1).permLists (sk.edge ⟨j, h⟩).1)
        (sk.edgeChoice ⟨j, h⟩ ξ.1 ξ.2)
    else 0)
  else 0

/-- The state after the edge `j` (the same state for `j ≥ N`). -/
def Skel.eTgt (sk : Skel D) (j : ℕ) (x : BornState 𝒢 Bc) (ξ : EdgeDeco B J ℓ Bc) : BornState 𝒢 Bc :=
  if h : j < D.n then
    (fun g => memOfList (edgeNewList D j ((sk.mstate j x.1).permLists (sk.edge ⟨j, h⟩).1)
        (sk.edgeChoice ⟨j, h⟩ ξ.1 ξ.2) g),
      x.2 ∪ birthSet (edgeAddrBirth (sk.edgeChoice ⟨j, h⟩ ξ.1 ξ.2)))
  else x

/-- `𝟏_∅` on the states with the set of born primes. -/
def bornFinalVal (x : BornState 𝒢 Bc) : ℝ := if (∑ g, (x.1 g).1.val) = 0 then 1 else 0

omit [DecidableEq S] [Fintype N] in
/-- The sum of a visit operation is a row sum. -/
theorem Skel.ghostSum_eq (sk : Skel D) (i : ℕ)
    (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (x : BornState 𝒢 Bc) :
    sk.ghostSum Bc i Ψ x.1 x.2 =
      ∑ c : GhostChoice 𝒢 Bc, sk.gCoef Bc i x c * Ψ (bornGhostTgt x c).1 (bornGhostTgt x c).2 := by
  unfold Skel.ghostSum Skel.gCoef
  exact Finset.sum_congr rfl fun c _ => memId_ite_mul_right_zero _ _

omit [DecidableEq S] [Fintype N] in
open _root_.Classical in
/-- The sum of an edge is a row sum. -/
theorem Skel.edgeSum_eq (sk : Skel D) (i : Fin D.n)
    (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (x : BornState 𝒢 Bc) :
    sk.edgeSum Bc i Ψ x.1 x.2 =
      ∑ ξ : EdgeDeco B J ℓ Bc,
        sk.eCoef Bc i.val x ξ * Ψ (sk.eTgt i.val x ξ).1 (sk.eTgt i.val x ξ).2 := by
  have hc : ∀ ξ : EdgeDeco B J ℓ Bc, sk.eCoef Bc i.val x ξ =
      (if NewBirths (edgeAddrBirth (sk.edgeChoice i ξ.1 ξ.2)) x.2 then
        edgeMemCoef D i.val ((sk.mstate i.val x.1).permLists (sk.edge i).1)
          (sk.edgeChoice i ξ.1 ξ.2)
      else 0) := fun ξ => dif_pos i.isLt
  have ht : ∀ ξ : EdgeDeco B J ℓ Bc, sk.eTgt i.val x ξ =
      (fun g => memOfList (edgeNewList D i.val ((sk.mstate i.val x.1).permLists (sk.edge i).1)
          (sk.edgeChoice i ξ.1 ξ.2) g),
        x.2 ∪ birthSet (edgeAddrBirth (sk.edgeChoice i ξ.1 ξ.2))) := fun ξ => dif_pos i.isLt
  unfold Skel.edgeSum
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun st _ => Finset.sum_congr rfl fun pr _ => ?_
  rw [hc (st, pr), ht (st, pr)]
  exact memId_ite_mul_right_zero _ _

/-! ### `fut` as an alternating product -/

omit [DecidableEq S] [Fintype N] in
/-- **`Skel.fut m` is the alternating product of the row sums of the visit and edge operations**,
started at the visit `N - m`. -/
theorem Skel.futC (sk : Skel D) : ∀ m : ℕ, m ≤ D.n → ∀ x : BornState 𝒢 Bc,
    ((sk.fut Bc m x.1 x.2 : ℝ) : ℂ) =
      altTail (fun j (x : BornState 𝒢 Bc) c => ((sk.gCoef Bc j x c : ℝ) : ℂ)) bornGhostTgt
        (fun j (x : BornState 𝒢 Bc) (ξ : EdgeDeco B J ℓ Bc) => ((sk.eCoef Bc j x ξ : ℝ) : ℂ))
        sk.eTgt (fun x : BornState 𝒢 Bc => ((bornFinalVal x : ℝ) : ℂ)) m (D.n - m) x := by
  intro m
  induction m with
  | zero =>
    intro _ x
    rw [Nat.sub_zero, Skel.fut, sk.ghostSum_eq, altTail, rowOp_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.ofReal_mul]
    rfl
  | succ m ih =>
    intro hm x
    have hlt : m < D.n := hm
    have hidx : D.n - (m + 1) + 1 = D.n - m := by omega
    rw [Skel.fut, dif_pos hlt, sk.ghostSum_eq, altTail, rowOp_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.ofReal_mul, rowOp_apply, sk.edgeSum_eq, Complex.ofReal_sum]
    refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun ξ _ => ?_)
    rw [Complex.ofReal_mul, hidx]
    exact congrArg₂ (· * ·) rfl
      (ih (Nat.le_of_succ_le hm) (sk.eTgt (D.n - (m + 1)) (bornGhostTgt x c) ξ))

/-! ### Decorations and words -/

/-- **A decoration is the word of its `n` double choices and its last choice.** -/
def decoWordEquiv (𝒢 : GroupFamily S B) (J ℓ Bc n : ℕ) :
    Deco 𝒢 J ℓ Bc n ≃ (Fin n → GhostChoice 𝒢 Bc × EdgeDeco B J ℓ Bc) × GhostChoice 𝒢 Bc where
  toFun d := (fun i => (d.ghost i.castSucc, (d.store i, d.promo i)), d.ghost (Fin.last n))
  invFun t :=
    ⟨Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i : Fin n => (t.1 i).1) t.2,
      fun i => (t.1 i).2.1, fun i => (t.1 i).2.2⟩
  left_inv d := by
    obtain ⟨ghost, store, promo⟩ := d
    have e : Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i : Fin n => ghost i.castSucc)
        (ghost (Fin.last n)) = ghost := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Fin.snoc_last _ _
      · exact Fin.snoc_castSucc _ _ j
    exact congrArg (fun g => (⟨g, store, promo⟩ : Deco 𝒢 J ℓ Bc n)) e
  right_inv t := by
    obtain ⟨w, c⟩ := t
    have e1 : (fun i : Fin n =>
        ((Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i => (w i).1) c :
          Fin (n + 1) → GhostChoice 𝒢 Bc) i.castSucc, ((w i).2.1, (w i).2.2))) = w := by
      funext i
      refine Prod.ext ?_ rfl
      show Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i : Fin n => (w i).1) c
        i.castSucc = (w i).1
      exact Fin.snoc_castSucc (α := fun _ => GhostChoice 𝒢 Bc) c (fun i : Fin n => (w i).1) i
    have e2 : (Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i => (w i).1) c :
        Fin (n + 1) → GhostChoice 𝒢 Bc) (Fin.last n) = c := Fin.snoc_last _ _
    exact Prod.ext e1 e2

/-- **The weight of a decoration with the indicators of new births**: the product along the
operations of the coefficients `gCoef`, `eCoef` at the states `(memAt d i, bornAt d i)`, and
`𝟏_∅` at the end. -/
def Skel.stepW (sk : Skel D) (d : Deco 𝒢 J ℓ Bc D.n) : ℝ :=
  (∏ i : Fin D.n,
      sk.gCoef Bc i.val (sk.memAt d i.val, sk.bornAt d i.val) (d.ghost i.castSucc) *
        sk.eCoef Bc i.val (bornGhostTgt (sk.memAt d i.val, sk.bornAt d i.val) (d.ghost i.castSucc))
          (d.store i, d.promo i)) *
    (sk.gCoef Bc D.n (sk.memAt d D.n, sk.bornAt d D.n) (d.ghost (Fin.last D.n)) *
      bornFinalVal (bornGhostTgt (sk.memAt d D.n, sk.bornAt d D.n) (d.ghost (Fin.last D.n))))

omit [DecidableEq S] [Fintype N] in
/-- **`fut N`, started with empty memories and the initial labels, is the sum over the decorations
of `stepW`.** -/
theorem Skel.fut_eq_sum_stepW (sk : Skel D) :
    sk.fut Bc D.n (fun g => emptyMem 𝒢 Bc g)
        (Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) =
      ∑ d : Deco 𝒢 J ℓ Bc D.n, sk.stepW d := by
  apply Complex.ofReal_injective
  have h1 := sk.futC D.n le_rfl
    ((fun g => emptyMem 𝒢 Bc g, Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) :
      BornState 𝒢 Bc)
  rw [Nat.sub_self, altTail_eq_sum] at h1
  refine h1.trans ?_
  rw [Complex.ofReal_sum]
  -- the term of a decoration
  have key : ∀ d : Deco 𝒢 J ℓ Bc D.n,
      walkCoef
          (altCoef (fun j (x : BornState 𝒢 Bc) c => ((sk.gCoef Bc j x c : ℝ) : ℂ)) bornGhostTgt
            (fun j (x : BornState 𝒢 Bc) (ξ : EdgeDeco B J ℓ Bc) => ((sk.eCoef Bc j x ξ : ℝ) : ℂ)))
          (altTgt bornGhostTgt sk.eTgt)
          ((0 : ℕ), ((fun g => emptyMem 𝒢 Bc g,
            Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) : BornState 𝒢 Bc))
          (List.ofFn (decoWordEquiv 𝒢 J ℓ Bc D.n d).1) *
        altLast (fun j (x : BornState 𝒢 Bc) c => ((sk.gCoef Bc j x c : ℝ) : ℂ)) bornGhostTgt
          (fun x : BornState 𝒢 Bc => ((bornFinalVal x : ℝ) : ℂ)) (decoWordEquiv 𝒢 J ℓ Bc D.n d).2
          (walkEnd (altTgt bornGhostTgt sk.eTgt)
            ((0 : ℕ), ((fun g => emptyMem 𝒢 Bc g,
              Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) : BornState 𝒢 Bc))
            (List.ofFn (decoWordEquiv 𝒢 J ℓ Bc D.n d).1)) =
        ((sk.stepW d : ℝ) : ℂ) := by
    intro d
    have hrec : ∀ i : Fin D.n,
        ((i.val + 1, (sk.memAt d (i.val + 1), sk.bornAt d (i.val + 1))) : ℕ × BornState 𝒢 Bc) =
          altTgt bornGhostTgt sk.eTgt ((i.val, (sk.memAt d i.val, sk.bornAt d i.val)) : ℕ × BornState 𝒢 Bc)
            ((decoWordEquiv 𝒢 J ℓ Bc D.n d).1 i) := by
      intro i
      show ((i.val + 1, (sk.memAt d (i.val + 1), sk.bornAt d (i.val + 1))) : ℕ × BornState 𝒢 Bc) =
        (i.val + 1, sk.eTgt i.val (bornGhostTgt (sk.memAt d i.val, sk.bornAt d i.val)
          (d.ghost i.castSucc)) (d.store i, d.promo i))
      rw [sk.memAt_succ d i.val i.isLt, sk.bornAt_succ d i.val i.isLt]
      unfold Skel.eTgt
      rw [dif_pos i.isLt]
      rfl
    obtain ⟨hend, hcoef⟩ := walk_ofFn
      (altCoef (fun j (x : BornState 𝒢 Bc) c => ((sk.gCoef Bc j x c : ℝ) : ℂ)) bornGhostTgt
        (fun j (x : BornState 𝒢 Bc) (ξ : EdgeDeco B J ℓ Bc) => ((sk.eCoef Bc j x ξ : ℝ) : ℂ)))
      (altTgt bornGhostTgt sk.eTgt)
      (fun i => ((i, (sk.memAt d i, sk.bornAt d i)) : ℕ × BornState 𝒢 Bc)) D.n
      (decoWordEquiv 𝒢 J ℓ Bc D.n d).1 hrec
    have hend' : walkEnd (altTgt bornGhostTgt sk.eTgt)
        ((0 : ℕ), ((fun g => emptyMem 𝒢 Bc g,
          Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) : BornState 𝒢 Bc))
        (List.ofFn (decoWordEquiv 𝒢 J ℓ Bc D.n d).1) =
        (D.n, (sk.memAt d D.n, sk.bornAt d D.n)) := hend
    have hcoef' : walkCoef
        (altCoef (fun j (x : BornState 𝒢 Bc) c => ((sk.gCoef Bc j x c : ℝ) : ℂ)) bornGhostTgt
          (fun j (x : BornState 𝒢 Bc) (ξ : EdgeDeco B J ℓ Bc) => ((sk.eCoef Bc j x ξ : ℝ) : ℂ)))
        (altTgt bornGhostTgt sk.eTgt)
        ((0 : ℕ), ((fun g => emptyMem 𝒢 Bc g,
          Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) : BornState 𝒢 Bc))
        (List.ofFn (decoWordEquiv 𝒢 J ℓ Bc D.n d).1) =
        ∏ i : Fin D.n,
          altCoef (fun j (x : BornState 𝒢 Bc) c => ((sk.gCoef Bc j x c : ℝ) : ℂ)) bornGhostTgt
            (fun j (x : BornState 𝒢 Bc) (ξ : EdgeDeco B J ℓ Bc) => ((sk.eCoef Bc j x ξ : ℝ) : ℂ))
            ((i.val, (sk.memAt d i.val, sk.bornAt d i.val)) : ℕ × BornState 𝒢 Bc)
            ((decoWordEquiv 𝒢 J ℓ Bc D.n d).1 i) := hcoef
    rw [hend', hcoef']
    unfold Skel.stepW
    simp only [Complex.ofReal_mul, Complex.ofReal_prod]
    rfl
  -- the sum over the words and the last choices is the sum over the decorations
  calc (∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeDeco B J ℓ Bc,
        altWalk (fun j (x : BornState 𝒢 Bc) c => ((sk.gCoef Bc j x c : ℝ) : ℂ)) bornGhostTgt
          (fun j (x : BornState 𝒢 Bc) (ξ : EdgeDeco B J ℓ Bc) => ((sk.eCoef Bc j x ξ : ℝ) : ℂ))
          sk.eTgt (fun x : BornState 𝒢 Bc => ((bornFinalVal x : ℝ) : ℂ))
          ((0 : ℕ), ((fun g => emptyMem 𝒢 Bc g,
            Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) : BornState 𝒢 Bc)) w)
      = ∑ t : (Fin D.n → GhostChoice 𝒢 Bc × EdgeDeco B J ℓ Bc) × GhostChoice 𝒢 Bc,
          walkCoef
              (altCoef (fun j (x : BornState 𝒢 Bc) c => ((sk.gCoef Bc j x c : ℝ) : ℂ)) bornGhostTgt
                (fun j (x : BornState 𝒢 Bc) (ξ : EdgeDeco B J ℓ Bc) =>
                  ((sk.eCoef Bc j x ξ : ℝ) : ℂ)))
              (altTgt bornGhostTgt sk.eTgt)
              ((0 : ℕ), ((fun g => emptyMem 𝒢 Bc g,
                Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) : BornState 𝒢 Bc))
              (List.ofFn t.1) *
            altLast (fun j (x : BornState 𝒢 Bc) c => ((sk.gCoef Bc j x c : ℝ) : ℂ)) bornGhostTgt
              (fun x : BornState 𝒢 Bc => ((bornFinalVal x : ℝ) : ℂ)) t.2
              (walkEnd (altTgt bornGhostTgt sk.eTgt)
                ((0 : ℕ), ((fun g => emptyMem 𝒢 Bc g,
                  Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) :
                    BornState 𝒢 Bc))
                (List.ofFn t.1)) := by
        rw [Fintype.sum_prod_type]
        rfl
    _ = ∑ d : Deco 𝒢 J ℓ Bc D.n, ((sk.stepW d : ℝ) : ℂ) := by
        rw [← Equiv.sum_comp (decoWordEquiv 𝒢 J ℓ Bc D.n)]
        exact Finset.sum_congr rfl fun d _ => key d

/-! ### The weight with indicators and the memory weight -/

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
open _root_.Classical in
/-- **`stepW d` is the memory weight of the decoration if the births of every operation are new,
and zero otherwise** (up to the measure of the initial big list). -/
theorem Skel.stepW_eq (sk : Skel D) (d : Deco 𝒢 J ℓ Bc D.n) :
    bigListMass 𝒢 D.q D.n sk.xb₀ * sk.stepW d =
      if (∀ i : Fin (D.n + 1), NewBirths (ghostAddrBirth (d.ghost i)) (sk.bornAt d i.val)) ∧
          ∀ i : Fin D.n, NewBirths (edgeAddrBirth (sk.edgeChoice i (d.store i) (d.promo i)))
            (sk.bornAt d i.val ∪ birthSet (ghostAddrBirth (d.ghost i.castSucc)))
      then sk.memW d else 0 := by
  have hgi : ∀ i : Fin D.n,
      sk.gCoef Bc i.val (sk.memAt d i.val, sk.bornAt d i.val) (d.ghost i.castSucc) =
        if NewBirths (ghostAddrBirth (d.ghost i.castSucc)) (sk.bornAt d i.val) then
          ghostCoef D i.val (sk.mstate i.val (sk.memAt d i.val)) (d.ghost i.castSucc)
        else 0 := fun i => rfl
  have he : ∀ i : Fin D.n,
      sk.eCoef Bc i.val (bornGhostTgt (sk.memAt d i.val, sk.bornAt d i.val) (d.ghost i.castSucc))
          (d.store i, d.promo i) =
        if NewBirths (edgeAddrBirth (sk.edgeChoice i (d.store i) (d.promo i)))
            (sk.bornAt d i.val ∪ birthSet (ghostAddrBirth (d.ghost i.castSucc))) then
          edgeMemCoef D i.val
            ((sk.mstate i.val fun g =>
              ghostNewMem (sk.memAt d i.val g) (d.ghost i.castSucc g)).permLists (sk.edge i).1)
            (sk.edgeChoice i (d.store i) (d.promo i))
        else 0 := fun i => dif_pos i.isLt
  have hgn : sk.gCoef Bc D.n (sk.memAt d D.n, sk.bornAt d D.n) (d.ghost (Fin.last D.n)) =
      if NewBirths (ghostAddrBirth (d.ghost (Fin.last D.n))) (sk.bornAt d D.n) then
        ghostCoef D D.n (sk.mstate D.n (sk.memAt d D.n)) (d.ghost (Fin.last D.n))
      else 0 := rfl
  have hfin : bornFinalVal (bornGhostTgt (sk.memAt d D.n, sk.bornAt d D.n) (d.ghost (Fin.last D.n))) =
      if (∑ g, (ghostNewMem (sk.memAt d D.n g) (d.ghost (Fin.last D.n) g)).1.val) = 0 then 1
      else 0 := rfl
  by_cases hall : (∀ i : Fin (D.n + 1),
      NewBirths (ghostAddrBirth (d.ghost i)) (sk.bornAt d i.val)) ∧
      ∀ i : Fin D.n, NewBirths (edgeAddrBirth (sk.edgeChoice i (d.store i) (d.promo i)))
        (sk.bornAt d i.val ∪ birthSet (ghostAddrBirth (d.ghost i.castSucc)))
  · rw [if_pos hall]
    have hP : (∏ i : Fin D.n,
          sk.gCoef Bc i.val (sk.memAt d i.val, sk.bornAt d i.val) (d.ghost i.castSucc) *
            sk.eCoef Bc i.val (bornGhostTgt (sk.memAt d i.val, sk.bornAt d i.val) (d.ghost i.castSucc))
              (d.store i, d.promo i)) =
        ∏ i : Fin D.n,
          ghostCoef D i.val (sk.mstate i.val (sk.memAt d i.val)) (d.ghost i.castSucc) *
            edgeMemCoef D i.val
              ((sk.mstate i.val fun g =>
                ghostNewMem (sk.memAt d i.val g) (d.ghost i.castSucc g)).permLists (sk.edge i).1)
              (sk.edgeChoice i (d.store i) (d.promo i)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      have h1 : NewBirths (ghostAddrBirth (d.ghost i.castSucc)) (sk.bornAt d i.val) :=
        hall.1 i.castSucc
      rw [hgi i, he i, if_pos h1, if_pos (hall.2 i)]
    have hlast : NewBirths (ghostAddrBirth (d.ghost (Fin.last D.n))) (sk.bornAt d D.n) :=
      hall.1 (Fin.last D.n)
    unfold Skel.stepW Skel.memW
    rw [hP, hgn, hfin, if_pos hlast]
    exact (mul_assoc _ _ _).symm
  · rw [if_neg hall]
    have hz : sk.stepW d = 0 := by
      by_contra hne
      unfold Skel.stepW at hne
      have hprod := (mul_ne_zero_iff.mp hne).1
      have hgl := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).2).1
      have hfac := Finset.prod_ne_zero_iff.mp hprod
      have hGi : ∀ i : Fin D.n,
          NewBirths (ghostAddrBirth (d.ghost i.castSucc)) (sk.bornAt d i.val) := by
        intro i
        have h1 := (mul_ne_zero_iff.mp (hfac i (Finset.mem_univ i))).1
        rw [hgi i] at h1
        exact memId_of_ite_ne_zero h1
      have hE : ∀ i : Fin D.n, NewBirths (edgeAddrBirth (sk.edgeChoice i (d.store i) (d.promo i)))
          (sk.bornAt d i.val ∪ birthSet (ghostAddrBirth (d.ghost i.castSucc))) := by
        intro i
        have h1 := (mul_ne_zero_iff.mp (hfac i (Finset.mem_univ i))).2
        rw [he i] at h1
        exact memId_of_ite_ne_zero h1
      have hGn : NewBirths (ghostAddrBirth (d.ghost (Fin.last D.n))) (sk.bornAt d D.n) := by
        rw [hgn] at hgl
        exact memId_of_ite_ne_zero hgl
      refine hall ⟨fun i => ?_, hE⟩
      refine Fin.lastCases ?_ (fun k => ?_) i
      · exact hGn
      · exact hGi k
    rw [hz, mul_zero]

/-! ### The statement -/

/-- **(M1) The distinct-birth rule as a running set of born primes** [S-02:0516–0521]: the memory
sum of a skeleton is `⊗ μ̃_g^{⊗M}(initial big list) · fut N (empty memories) (initial labels)`,
and zero if two initial slots have the same label. -/
theorem bornSetRecursion : BornSetRecursion := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D Bc sk
  classical
  have hms : sk.memSum Bc =
      ∑ d : Deco 𝒢 J ℓ Bc D.n,
        if Graph.PerformedBirthsDistinct (sk.hist (fun _ => 0) d).birth then sk.memW d
        else 0 := by
    unfold Skel.memSum
    exact Finset.sum_congr rfl fun d _ => by rw [sk.memPart_hist]
  rw [hms]
  by_cases hinj : Function.Injective fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)
  · rw [if_pos hinj, sk.fut_eq_sum_stepW, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [sk.stepW_eq d]
    exact ite_congr_of_iff
      ((sk.distinct_iff_newBirths (fun _ => 0) d).trans ⟨fun h => h.2, fun h => ⟨hinj, h⟩⟩)
      rfl rfl
  · rw [if_neg hinj]
    refine Finset.sum_eq_zero fun d _ => ?_
    exact if_neg fun h => hinj ((sk.distinct_iff_newBirths (fun _ => 0) d).mp h).1

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
