module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HistoryExpansionProof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A history is a skeleton, its small residues and a decoration

Source: `verification/stage7-sources/S-02.tex`, lines 477–534 (`[S-02:0477–0534]`).

Tools for the memory side of the proof of Lemma 3.7, used by `DistinctSkeletonProof.lean`.

* `edgeCommonCoef`, `edgeCoef_eq_common_mul_mem` — the coefficient `edgeCoef` of an edge is the
  product of a part which does not involve the memories (the small states, the shared labels, the
  bans, the free-label probabilities, the small endpoint factors, the oriented coefficient and the
  phase) and the memory part `edgeMemCoef`.
* `History.commonPart`, `History.weight_eq` — the weight of a history is the Haar mass of its
  small residues, its common part and its memory part `History.memPart`.
* `histSkelEquiv` — a history is its initial small residues, its skeleton and its decoration.
* `Skel.memAt`, `Skel.visitState_hist` — the state at the visit `i` of the history with skeleton
  `sk`, small residues `y` and decoration `d`: the residues `y + h_i`, the lists of the skeleton
  and memories which do not depend on `y`.
* `Skel.commonPart_hist`, `Skel.memW`, `Skel.memPart_hist`, `Skel.birth_hist` — the common part of
  that history is `Skel.common`; its memory part and its births do not depend on `y`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Translations of residue vectors -/

theorem memId_shift_zero {Q : Finset ℕ} (y : ResVec Q) :
    ((resModel Q).shift 0 y : ResVec Q) = y := by
  funext p
  show y p + ((0 : ℤ) : Res p.1) = y p
  rw [Int.cast_zero, add_zero]

theorem memId_shift_shift {Q : Finset ℕ} (a b : ℤ) (y : ResVec Q) :
    ((resModel Q).shift a ((resModel Q).shift b y) : ResVec Q) = (resModel Q).shift (b + a) y := by
  funext p
  show y p + (b : Res p.1) + (a : Res p.1) = y p + ((b + a : ℤ) : Res p.1)
  push_cast
  ring

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {D : MemData 𝒢 J ℓ N} {Bc : ℕ}

/-! ### The two parts of the coefficient of an edge -/

open _root_.Classical in
/-- **The part of the coefficient `edgeCoef` which does not involve the memories**: zero unless
the small lists are small states at `y` and `y + Δ` with the same shared labels, the big target
list has the shared labels of the source and no auxiliary label occurs in the lists; otherwise the
probability of the auxiliary labels, the small normalization, the two small endpoint factors, the
oriented coefficient and the phase. -/
def edgeCommonCoef (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) : ℂ :=
  if IsSmallState 𝒢 s.y s.xs ∧
      IsSmallState 𝒢 ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y) c.xsT ∧
      SharedSmall s.xs c.xsT ∧ SharedBig (D.fam c.ν).C s.xb c.xbT ∧
      AuxAvoids (D.fam c.ν).C c.r ((s.xs, s.xb) : Lists 𝒢 J ℓ) ∧
      AuxAvoids (D.fam c.ν).C c.r ((c.xsT, c.xbT) : Lists 𝒢 J ℓ) then
    ((auxWeight 𝒢.big (D.fam c.ν).C c.r *
        ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          (smallDamping 𝒢 J ℓ D.q s.y *
            smallDamping 𝒢 J ℓ D.q
              ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y))) : ℝ) : ℂ) *
      (edgeMultiplier D i s c * expUnit (θ * (edgeStep D i s c : ℝ)))
  else 0

/-- An `if` over an interleaved conjunction is the product of the `if`s of its two halves. -/
theorem memId_ite_split_mul {P₀ Q P : Prop} {h₀ : Decidable P₀} {hQ : Decidable Q}
    {hP : Decidable P} (X Y : ℂ) (Z : ℝ) (hiff : P₀ ↔ Q ∧ P) (hXY : X = Y * (Z : ℂ)) :
    (@ite ℂ P₀ h₀ X 0) = (@ite ℂ Q hQ Y 0) * (((@ite ℝ P hP Z 0 : ℝ)) : ℂ) := by
  by_cases hq : Q
  · by_cases hp : P
    · rw [if_pos (hiff.mpr ⟨hq, hp⟩), if_pos hq, if_pos hp]
      exact hXY
    · rw [if_neg (fun h => hp (hiff.mp h).2), if_neg hp, Complex.ofReal_zero,
        mul_zero]
  · rw [if_neg (fun h => hq (hiff.mp h).1), if_neg hq, zero_mul]

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **The coefficient of an edge is its common part times its memory part.** -/
theorem edgeCoef_eq_common_mul_mem (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) :
    edgeCoef D θ i s c = edgeCommonCoef D θ i s c * ((edgeMemCoef D i s c : ℝ) : ℂ) := by
  have alg : ∀ (a r1 v f r2 sn : ℝ) (m : ℂ),
      ((a * r1 * v * f * r2 * sn : ℝ) : ℂ) * m =
        ((a * sn : ℝ) : ℂ) * m * ((r1 * v * f * r2 : ℝ) : ℂ) := by
    intro a r1 v f r2 sn m
    push_cast
    ring
  unfold edgeCoef edgeCommonCoef edgeMemCoef
  refine memId_ite_split_mul _ _ _ ⟨fun h => ⟨⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩, ⟨h.1, h.2.1, h.2.2.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.2⟩⟩,
    fun h => ⟨h.2.1, h.2.2.1, h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
      h.1.2.2.2.2.2, h.2.2.2.1, h.2.2.2.2⟩⟩ ?_
  exact alg _ _ _ _ _ _ _

/-! ### The two parts of the weight of a history -/

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- The measure of empty memories is one. -/
theorem memId_memMass_empty (𝒢 : GroupFamily S B) (q : ℝ) (n Bc : ℕ) :
    memMass 𝒢 q n (fun g => emptyMem 𝒢 Bc g) = 1 := by
  unfold memMass
  refine Finset.prod_eq_one fun g _ => ?_
  show (∏ i : Fin 0, _) / ((Nat.factorial 0 : ℕ) : ℝ) = 1
  rw [Finset.univ_eq_empty, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, div_one]

open _root_.Classical in
/-- **The common part of the weight of a history**: the mass of the initial small state and, for
every edge, the two symmetrization averages and the common part of the coefficient. -/
def History.commonPart (θ : ℝ) (h : History D Bc) : ℂ :=
  (if IsSmallState 𝒢 h.y₀ h.xs₀ then ((smallListMass 𝒢 J ℓ : ℝ) : ℂ) else 0) *
    ∏ i : Fin D.n, ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
      edgeCommonCoef D θ i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1) (h.edge i).2.1 *
      (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹)

omit [Fintype N] in
open _root_.Classical in
/-- **The weight of a history is the Haar mass of its small residues, its common part and its
memory part.** -/
theorem History.weight_eq (θ : ℝ) (h : History D Bc) :
    h.weight θ =
      ((haarMass (smallPrimes 𝒢) : ℝ) : ℂ) * h.commonPart θ * ((h.memPart : ℝ) : ℂ) := by
  have hinit : ((memWeight 𝒢 D.q D.n h.init : ℝ) : ℂ) =
      ((haarMass (smallPrimes 𝒢) : ℝ) : ℂ) *
        (if IsSmallState 𝒢 h.y₀ h.xs₀ then ((smallListMass 𝒢 J ℓ : ℝ) : ℂ) else 0) *
        ((bigListMass 𝒢 D.q D.n h.xb₀ : ℝ) : ℂ) := by
    have hm : memMass 𝒢 D.q D.n h.init.mem = 1 := memId_memMass_empty 𝒢 D.q D.n Bc
    unfold memWeight
    by_cases hs : IsSmallState 𝒢 h.init.y h.init.xs
    · have hs' : IsSmallState 𝒢 h.y₀ h.xs₀ := hs
      rw [if_pos hs, if_pos hs', hm, mul_one, Complex.ofReal_mul, Complex.ofReal_mul]
      rfl
    · have hs' : ¬IsSmallState 𝒢 h.y₀ h.xs₀ := hs
      rw [if_neg hs, if_neg hs', Complex.ofReal_zero, mul_zero, zero_mul]
  have hprod : (∏ i : Fin D.n,
        ((ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) : ℝ) : ℂ) *
          edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)) =
      (∏ i : Fin D.n, ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
        edgeCommonCoef D θ i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1)
          (h.edge i).2.1 * (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹)) *
        ((∏ i : Fin D.n, ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) *
          edgeMemCoef D i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1)
            (h.edge i).2.1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold edgeFullCoef
    simp only [one_mul]
    rw [edgeCoef_eq_common_mul_mem, Complex.ofReal_mul]
    ring
  have hlast : ((ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n)) : ℝ) : ℂ) *
        emptyVec 𝒢 J ℓ Bc (h.afterGhost (Fin.last D.n)) =
      ((ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n)) *
        (if memTotal (h.afterGhost (Fin.last D.n)) = 0 then 1 else 0) : ℝ) : ℂ) := by
    unfold emptyVec
    by_cases hz : memTotal (h.afterGhost (Fin.last D.n)) = 0
    · rw [if_pos hz, if_pos hz, mul_one, mul_one]
    · rw [if_neg hz, if_neg hz, mul_zero, mul_zero, Complex.ofReal_zero]
  have hmem : ((h.memPart : ℝ) : ℂ) =
      ((bigListMass 𝒢 D.q D.n h.xb₀ : ℝ) : ℂ) *
        ((∏ i : Fin D.n, ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) *
          edgeMemCoef D i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1)
            (h.edge i).2.1 : ℝ) : ℂ) *
        ((ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n)) *
          (if memTotal (h.afterGhost (Fin.last D.n)) = 0 then 1 else 0) : ℝ) : ℂ) := by
    unfold History.memPart
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
  unfold History.weight
  rw [hinit, hprod, hlast, hmem]
  unfold History.commonPart
  ring

/-! ### Histories, skeletons and decorations -/

/-- **A history is its initial small residues, its skeleton and its decoration.** -/
def histSkelEquiv (D : MemData 𝒢 J ℓ N) (Bc : ℕ) :
    History D Bc ≃ ResVec (smallPrimes 𝒢) × Skel D × Deco 𝒢 J ℓ Bc D.n where
  toFun h := (h.y₀,
    ⟨h.xs₀, h.xb₀, fun i => ((h.edge i).1,
      ⟨(h.edge i).2.1.ν, (h.edge i).2.1.r, ((h.edge i).2.1.xsT, (h.edge i).2.1.xbT)⟩,
      (h.edge i).2.2)⟩,
    ⟨h.ghost, fun i => (h.edge i).2.1.store, fun i => (h.edge i).2.1.promo⟩)
  invFun t := t.2.1.hist t.1 t.2.2
  left_inv h := by
    obtain ⟨y₀, xs₀, xb₀, ghost, edge⟩ := h
    rfl
  right_inv t := by
    obtain ⟨y, ⟨xs₀, xb₀, edge⟩, ⟨ghost, store, promo⟩⟩ := t
    rfl

/-! ### The offsets and the lists of a skeleton -/

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.off_zero (sk : Skel D) : sk.off 0 = 0 := by
  unfold Skel.off
  exact Finset.sum_eq_zero fun j _ => if_neg (Nat.not_lt_zero _)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.off_succ (sk : Skel D) (i : ℕ) (hi : i < D.n) :
    sk.off (i + 1) = sk.off i + sk.step ⟨i, hi⟩ := by
  have h : ∀ j : Fin D.n, (if j.val < i + 1 then sk.step j else 0) =
      (if j.val < i then sk.step j else 0) + (if j = ⟨i, hi⟩ then sk.step j else 0) := by
    intro j
    by_cases h1 : j.val < i
    · have h2 : j.val < i + 1 := Nat.lt_succ_of_lt h1
      have h3 : j ≠ ⟨i, hi⟩ := fun h => absurd h1 (by rw [h]; exact Nat.lt_irrefl i)
      rw [if_pos h1, if_pos h2, if_neg h3, add_zero]
    · by_cases h3 : j = ⟨i, hi⟩
      · have h2 : j.val < i + 1 := by
          rw [h3]
          exact Nat.lt_succ_self i
        rw [if_pos h2, if_neg h1, if_pos h3, zero_add]
      · have h2 : ¬j.val < i + 1 := fun h => h3 (Fin.ext (show j.val = i by omega))
        rw [if_neg h1, if_neg h2, if_neg h3, add_zero]
  have h5 : ∑ j : Fin D.n, (if j = ⟨i, hi⟩ then sk.step j else 0) = sk.step ⟨i, hi⟩ := by
    exact (Fintype.sum_eq_single (⟨i, hi⟩ : Fin D.n) fun j hj => if_neg hj).trans
      (if_pos rfl)
  unfold Skel.off
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, h5]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.lists_succ (sk : Skel D) (i : ℕ) (hi : i < D.n) :
    sk.lists (i + 1) = permuteLists (sk.edge ⟨i, hi⟩).2.2 (sk.tgt ⟨i, hi⟩) := by
  rw [Skel.lists]
  exact dif_pos hi

/-! ### The states of the history of a skeleton and a decoration -/

/-- **The memories at the visit `i`** (before the visit operation `G_i`) of the histories with
skeleton `sk` and decoration `d`; they do not depend on the small residues. -/
def Skel.memAt (sk : Skel D) (d : Deco 𝒢 J ℓ Bc D.n) : ℕ → (g : B) → Mem 𝒢 Bc g
  | 0 => fun g => emptyMem 𝒢 Bc g
  | i + 1 =>
    if hi : i < D.n then
      fun g => memOfList (edgeNewList D i
        ((sk.mstate i fun g' =>
          ghostNewMem (sk.memAt d i g') (d.ghost (Fin.castSucc ⟨i, hi⟩) g')).permLists
            (sk.edge ⟨i, hi⟩).1)
        (sk.edgeChoice ⟨i, hi⟩ (d.store ⟨i, hi⟩) (d.promo ⟨i, hi⟩)) g)
    else sk.memAt d i

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.memAt_succ (sk : Skel D) (d : Deco 𝒢 J ℓ Bc D.n) (i : ℕ) (hi : i < D.n) :
    sk.memAt d (i + 1) =
      fun g => memOfList (edgeNewList D i
        ((sk.mstate i fun g' =>
          ghostNewMem (sk.memAt d i g') (d.ghost (Fin.castSucc ⟨i, hi⟩) g')).permLists
            (sk.edge ⟨i, hi⟩).1)
        (sk.edgeChoice ⟨i, hi⟩ (d.store ⟨i, hi⟩) (d.promo ⟨i, hi⟩)) g) := by
  rw [Skel.memAt]
  exact dif_pos hi

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **The state at the visit `i` of the history with skeleton `sk`, small residues `y` and
decoration `d`**: the residues `y + h_i`, the lists of the skeleton and the memories `memAt`. -/
theorem Skel.visitState_hist (sk : Skel D) (y : ResVec (smallPrimes 𝒢))
    (d : Deco 𝒢 J ℓ Bc D.n) :
    ∀ i : ℕ, i ≤ D.n → (sk.hist y d).visitState i =
      ⟨(resModel (smallPrimes 𝒢)).shift (sk.off i) y, (sk.lists i).1, (sk.lists i).2,
        sk.memAt d i⟩ := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [sk.off_zero, memId_shift_zero]
    rfl
  | succ i ih =>
    intro hi
    have hi' : i < D.n := hi
    have e1 : (sk.hist y d).visitState (i + 1) =
        edgeFullTgt D i
          (ghostTgt ((sk.hist y d).visitState i) ((sk.hist y d).ghost (Fin.castSucc ⟨i, hi'⟩)))
          ((sk.hist y d).edge ⟨i, hi'⟩) :=
      History.visitState_succ (sk.hist y d) ⟨i, hi'⟩
    rw [e1, ih (Nat.le_of_lt hi'), sk.off_succ i hi', ← memId_shift_shift,
      sk.lists_succ i hi', sk.memAt_succ d i hi']
    rfl

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The state after the visit operation `G_i` and the source permutation of the edge `i`. -/
theorem Skel.afterGhost_hist (sk : Skel D) (y : ResVec (smallPrimes 𝒢))
    (d : Deco 𝒢 J ℓ Bc D.n) (i : Fin D.n) :
    ((sk.hist y d).afterGhost i.castSucc).permLists ((sk.hist y d).edge i).1 =
      (⟨(resModel (smallPrimes 𝒢)).shift (sk.off i.val) y, (sk.src i).1, (sk.src i).2,
        fun g => ghostNewMem (sk.memAt d i.val g) (d.ghost i.castSucc g)⟩ : MState 𝒢 J ℓ Bc) := by
  show (ghostTgt ((sk.hist y d).visitState i.val) ((sk.hist y d).ghost i.castSucc)).permLists
    ((sk.hist y d).edge i).1 = _
  rw [sk.visitState_hist y d i.val (Nat.le_of_lt i.isLt)]
  rfl

/-! ### The common part -/

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The common part of the coefficient of the edge `i` at a state with the residues `y + h_i` and
the source lists of the skeleton is `Skel.edgeCommon`. -/
theorem Skel.edgeCommonCoef_hist (sk : Skel D) (θ : ℝ) (y : ResVec (smallPrimes 𝒢))
    (i : Fin D.n) (mem : (g : B) → Mem 𝒢 Bc g) (st : (g : B) → Finset (Slot J ℓ))
    (pr : (g : B) → Slot J ℓ → Option (Fin Bc)) :
    edgeCommonCoef D θ i.val
        (⟨(resModel (smallPrimes 𝒢)).shift (sk.off i.val) y, (sk.src i).1, (sk.src i).2, mem⟩ :
          MState 𝒢 J ℓ Bc) (sk.edgeChoice i st pr) = sk.edgeCommon θ y i := by
  have hshift : ((resModel (smallPrimes 𝒢)).shift (sk.step i)
      ((resModel (smallPrimes 𝒢)).shift (sk.off i.val) y) : ResVec (smallPrimes 𝒢)) =
      (resModel (smallPrimes 𝒢)).shift (sk.off (i.val + 1)) y := by
    rw [memId_shift_shift]
    exact congrArg (fun t => (resModel (smallPrimes 𝒢)).shift t y)
      (sk.off_succ i.val i.isLt).symm
  unfold Skel.edgeCommon
  rw [← hshift]
  rfl

omit [Fintype N] in
/-- **The common part of the history of a skeleton is the common part of the skeleton.** -/
theorem Skel.commonPart_hist (sk : Skel D) (θ : ℝ) (y : ResVec (smallPrimes 𝒢))
    (d : Deco 𝒢 J ℓ Bc D.n) : (sk.hist y d).commonPart θ = sk.common θ y := by
  unfold History.commonPart Skel.common
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun i _ => ?_)
  have e : edgeCommonCoef D θ i.val
      (((sk.hist y d).afterGhost i.castSucc).permLists ((sk.hist y d).edge i).1)
      ((sk.hist y d).edge i).2.1 = sk.edgeCommon θ y i := by
    rw [sk.afterGhost_hist y d i]
    exact sk.edgeCommonCoef_hist θ y i _ (d.store i) (d.promo i)
  rw [e]

/-! ### The memory part and the births -/

/-- **The memory weight of a decoration of a skeleton**: the memory part of the weight of its
histories, written with the states `Skel.mstate` (no small residues). -/
def Skel.memW (sk : Skel D) (d : Deco 𝒢 J ℓ Bc D.n) : ℝ :=
  bigListMass 𝒢 D.q D.n sk.xb₀ *
    (∏ i : Fin D.n, ghostCoef D i.val (sk.mstate i.val (sk.memAt d i.val)) (d.ghost i.castSucc) *
      edgeMemCoef D i.val
        ((sk.mstate i.val fun g =>
          ghostNewMem (sk.memAt d i.val g) (d.ghost i.castSucc g)).permLists (sk.edge i).1)
        (sk.edgeChoice i (d.store i) (d.promo i))) *
    (ghostCoef D D.n (sk.mstate D.n (sk.memAt d D.n)) (d.ghost (Fin.last D.n)) *
      (if (∑ g, (ghostNewMem (sk.memAt d D.n g) (d.ghost (Fin.last D.n) g)).1.val) = 0 then 1
        else 0))

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **The memory part of the history of a skeleton and a decoration does not depend on the small
residues.** -/
theorem Skel.memPart_hist (sk : Skel D) (y : ResVec (smallPrimes 𝒢)) (d : Deco 𝒢 J ℓ Bc D.n) :
    (sk.hist y d).memPart = sk.memW d := by
  have h0 : (sk.hist y d).xb₀ = sk.xb₀ := rfl
  have h1 : ∀ i : Fin D.n,
      ghostCoef D i.val ((sk.hist y d).visitState i.val) ((sk.hist y d).ghost i.castSucc) =
        ghostCoef D i.val (sk.mstate i.val (sk.memAt d i.val)) (d.ghost i.castSucc) := by
    intro i
    rw [sk.visitState_hist y d i.val (Nat.le_of_lt i.isLt)]
    rfl
  have h2 : ∀ i : Fin D.n,
      edgeMemCoef D i.val
          (((sk.hist y d).afterGhost i.castSucc).permLists ((sk.hist y d).edge i).1)
          ((sk.hist y d).edge i).2.1 =
        edgeMemCoef D i.val
          ((sk.mstate i.val fun g =>
            ghostNewMem (sk.memAt d i.val g) (d.ghost i.castSucc g)).permLists (sk.edge i).1)
          (sk.edgeChoice i (d.store i) (d.promo i)) := by
    intro i
    rw [sk.afterGhost_hist y d i]
    rfl
  have h3 : ghostCoef D D.n ((sk.hist y d).visitState D.n)
        ((sk.hist y d).ghost (Fin.last D.n)) =
      ghostCoef D D.n (sk.mstate D.n (sk.memAt d D.n)) (d.ghost (Fin.last D.n)) := by
    rw [sk.visitState_hist y d D.n le_rfl]
    rfl
  have h4 : memTotal ((sk.hist y d).afterGhost (Fin.last D.n)) =
      ∑ g, (ghostNewMem (sk.memAt d D.n g) (d.ghost (Fin.last D.n) g)).1.val := by
    show memTotal (ghostTgt ((sk.hist y d).visitState D.n)
      ((sk.hist y d).ghost (Fin.last D.n))) = _
    rw [sk.visitState_hist y d D.n le_rfl]
    rfl
  have hP : (∏ i : Fin D.n,
        ghostCoef D i.val ((sk.hist y d).visitState i.val) ((sk.hist y d).ghost i.castSucc) *
          edgeMemCoef D i.val
            (((sk.hist y d).afterGhost i.castSucc).permLists ((sk.hist y d).edge i).1)
            ((sk.hist y d).edge i).2.1) =
      ∏ i : Fin D.n,
        ghostCoef D i.val (sk.mstate i.val (sk.memAt d i.val)) (d.ghost i.castSucc) *
          edgeMemCoef D i.val
            ((sk.mstate i.val fun g =>
              ghostNewMem (sk.memAt d i.val g) (d.ghost i.castSucc g)).permLists (sk.edge i).1)
            (sk.edgeChoice i (d.store i) (d.promo i)) :=
    Finset.prod_congr rfl fun i _ => by rw [h1 i, h2 i]
  unfold History.memPart Skel.memW
  rw [h0, hP, h3, h4]

omit [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The births of the history of a skeleton and a decoration do not depend on the small
residues. -/
theorem Skel.birth_hist (sk : Skel D) (y y' : ResVec (smallPrimes 𝒢)) (d : Deco 𝒢 J ℓ Bc D.n) :
    (sk.hist y d).birth = (sk.hist y' d).birth := by
  funext a
  rcases a with a | a | a <;> rfl

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
