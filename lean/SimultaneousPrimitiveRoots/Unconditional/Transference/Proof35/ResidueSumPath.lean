module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueSumVisit
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The summation over paths, part 4: the dependence of a path on the position

Source: `verification/stage7-sources/S-02.tex`, lines 212–234 (`[S-02:0212–0234]`).

"Fix the patterns, all endpoint permutations, the auxiliary labels, and the active lists at
visits `0, …, N`. These choices fix offsets `h_0 = 0, h_1, …, h_N` … Let `Λ_i` be the set of
active labels at visit `i`. … The dependence on the initial integer `n` is precisely the
nonnegative factor (eq:path-residue-factor). … All remaining factors are independent of `n`."

A path is a pair of initial lists `x` and a word of edges `fw` (the choices of one edge are
`PhysChoice`). Its *skeleton* is the walk of the same edges in `intPos`, started at the offset `0`:

* `skel`, `skelOff`, `skelLst`, `skelLab` — the state, the offset `h_i`, the lists and the set
  `Λ_i` of their labels after `i` edges;
* `skelInj` — the indicator that the labels of every group are distinct at every visit;
* `skelKappa` — the product of the position-independent parts of the coefficients;
* `pathAmp` — the real amplitude of the path: the real part of `mass · skelKappa · 1_{h_N = 0}`
  times `skelInj`.

For a position model with additive translations (`shift a (shift b n) = shift (b + a) n`,
`shift 0 n = n`):

* `edge_walkCoef` — the coefficient of the walk from the position `pos` is
  `skelKappa · skelInj · (eq:path-residue-factor)(pos)`;
* `round_term_of_isPhys`, `skelInj_mul_pathFactor_eq_zero` — the term of the path in the expansion
  of the moment (`PathExpansion.lean`), including the return condition `u_n(end)`, if
  `shift d pos = pos ↔ d = 0`;
* `physMoment_eq_sum_paths` — **the moment is `∑_paths pathAmp · (eq:path-residue-factor)`**, with
  amplitudes, offsets and label sets which do not depend on the position or on the model.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum

open scoped BigOperators

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  (𝒢 : GroupFamily S B) {J ℓ : ℕ} {N : Type} [Fintype N]

/-! ### The skeleton of a path -/

/-- The skeleton after `i` edges: the direction flag, the integer offset and the lists. -/
def skel (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (x : Lists 𝒢 J ℓ) (fw : List (PhysChoice 𝒢 𝔉))
    (i : ℕ) : EState intPos 𝒢 J ℓ :=
  walkEnd (edgeTgt intPos 𝒢 𝔉 k) (false, ((0 : ℤ), x)) (fw.take i)

/-- The offset `h_i` of the path after `i` edges [S-02:0214–0217]. -/
def skelOff (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (x : Lists 𝒢 J ℓ) (fw : List (PhysChoice 𝒢 𝔉))
    (i : ℕ) : ℤ := (skel 𝒢 𝔉 k x fw i).2.1

/-- The lists of the path at visit `i`. -/
def skelLst (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (x : Lists 𝒢 J ℓ) (fw : List (PhysChoice 𝒢 𝔉))
    (i : ℕ) : Lists 𝒢 J ℓ := (skel 𝒢 𝔉 k x fw i).2.2

/-- The set `Λ_i` of the active labels at visit `i` [S-02:0222]. -/
def skelLab (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (x : Lists 𝒢 J ℓ) (fw : List (PhysChoice 𝒢 𝔉))
    (i : ℕ) : Finset ℕ := labelSet (skelLst 𝒢 𝔉 k x fw i)

open _root_.Classical in
/-- The indicator that at every visit the labels of every group are distinct. -/
def skelInj (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) : ℝ :=
  ∏ i ∈ Finset.range (fw.length + 1), if ListInj (skelLst 𝒢 𝔉 k x fw i) then (1 : ℝ) else 0

/-- The product along the path of the position-independent parts of the coefficients. -/
def skelKappa (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) : ℂ :=
  walkCoef (edgeK intPos 𝒢 𝔉 ζ) (edgeTgt intPos 𝒢 𝔉 k) (false, ((0 : ℤ), x)) fw

open _root_.Classical in
/-- **The amplitude of a path**: the real part of `mass · skelKappa · 1_{h_N = 0}`, times the
indicator `skelInj`. It does not depend on the position, on the position model or on `q`. -/
def pathAmp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) : ℝ :=
  ((stateMass 𝒢 J ℓ : ℂ) * skelKappa 𝒢 𝔉 k ζ x fw *
      (if skelOff 𝒢 𝔉 k x fw fw.length = 0 then 1 else 0)).re * skelInj 𝒢 𝔉 k x fw

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- `h_0 = 0`. -/
theorem skelOff_zero (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) : skelOff 𝒢 𝔉 k x fw 0 = 0 := rfl

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem skelLst_zero (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) : skelLst 𝒢 𝔉 k x fw 0 = x := rfl

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- `Λ_i` consists of group primes. -/
theorem skelLab_subset (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) (i : ℕ) : skelLab 𝒢 𝔉 k x fw i ⊆ 𝒢.allPrimes :=
  labelSet_subset _

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- `|Λ_i| ≤ M s`. -/
theorem card_skelLab_le (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) (i : ℕ) :
    (skelLab 𝒢 𝔉 k x fw i).card ≤ (J + ℓ) * groupCount S B :=
  card_labelSet_le _

/-! ### The walk from a position -/

section Model

variable (𝔭 : PosModel)
  (hadd : ∀ (a b : ℤ) (n : 𝔭.Pos), 𝔭.shift a (𝔭.shift b n) = 𝔭.shift (b + a) n)
  (hzero : ∀ n : 𝔭.Pos, 𝔭.shift 0 n = n)

include hzero in
omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem liftSt_start (pos : 𝔭.Pos) (x : Lists 𝒢 J ℓ) :
    ((false, (pos, x)) : EState 𝔭 𝒢 J ℓ) = liftSt 𝔭 𝒢 pos (false, ((0 : ℤ), x)) := by
  show ((false, (pos, x)) : EState 𝔭 𝒢 J ℓ) = (false, (𝔭.shift 0 pos, x))
  rw [hzero]

include hadd hzero in
omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The walk from the position `pos` visits the positions `pos + h_i` with the lists of the
skeleton. -/
theorem walkEnd_edge_take (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (pos : 𝔭.Pos) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) (i : ℕ) :
    walkEnd (edgeTgt 𝔭 𝒢 𝔉 k) (false, (pos, x)) (fw.take i) =
      liftSt 𝔭 𝒢 pos (skel 𝒢 𝔉 k x fw i) := by
  rw [liftSt_start 𝒢 𝔭 hzero pos x]
  exact walkEnd_map (liftSt 𝔭 𝒢 pos) (edgeTgt intPos 𝒢 𝔉 k) (edgeTgt 𝔭 𝒢 𝔉 k)
    (edgeTgt_liftSt 𝔭 𝒢 hadd 𝔉 k pos) _ _

include hadd hzero in
omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem walkEnd_edge (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (pos : 𝔭.Pos) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) :
    walkEnd (edgeTgt 𝔭 𝒢 𝔉 k) (false, (pos, x)) fw =
      liftSt 𝔭 𝒢 pos (skel 𝒢 𝔉 k x fw fw.length) := by
  have h := walkEnd_edge_take 𝒢 𝔭 hadd hzero 𝔉 k pos x fw fw.length
  rwa [List.take_length] at h

open _root_.Classical in
include hadd hzero in
omit [Fintype N] in
/-- **The coefficient of the walk of a path from the position `pos`** [S-02:0222–0234]: the
position-independent product `skelKappa`, times `skelInj`, times (eq:path-residue-factor). -/
theorem edge_walkCoef (hd : GroupsDisjoint 𝒢) {q : ℝ} (hq : 0 < q)
    (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (pos : 𝔭.Pos) (x : Lists 𝒢 J ℓ)
    (fw : List (PhysChoice 𝒢 𝔉)) (hfw : fw ≠ []) :
    walkCoef (edgeCoef 𝔭 𝒢 q 𝔉 k ζ) (edgeTgt 𝔭 𝒢 𝔉 k) (false, (pos, x)) fw =
      skelKappa 𝒢 𝔉 k ζ x fw *
        ((skelInj 𝒢 𝔉 k x fw * pathFactor 𝔭 𝒢.allPrimes q fw.length (skelLab 𝒢 𝔉 k x fw)
          (skelOff 𝒢 𝔉 k x fw) pos : ℝ) : ℂ) := by
  have hκ : walkCoef (edgeK 𝔭 𝒢 𝔉 ζ) (edgeTgt 𝔭 𝒢 𝔉 k) (false, (pos, x)) fw =
      skelKappa 𝒢 𝔉 k ζ x fw := by
    rw [liftSt_start 𝒢 𝔭 hzero pos x]
    exact walkCoef_map (liftSt 𝔭 𝒢 pos) (edgeTgt intPos 𝒢 𝔉 k) (edgeTgt 𝔭 𝒢 𝔉 k)
      (edgeK intPos 𝒢 𝔉 ζ) (edgeK 𝔭 𝒢 𝔉 ζ) (edgeTgt_liftSt 𝔭 𝒢 hadd 𝔉 k pos)
      (edgeK_liftSt 𝔭 𝒢 𝔉 ζ pos) _ fw
  have hW : ∀ i : ℕ, edgeW 𝔭 𝒢 q (walkEnd (edgeTgt 𝔭 𝒢 𝔉 k) (false, (pos, x)) (fw.take i)) =
      posWeight 𝔭 𝒢 q (𝔭.shift (skelOff 𝒢 𝔉 k x fw i) pos) (skelLst 𝒢 𝔉 k x fw i) := by
    intro i
    rw [walkEnd_edge_take 𝒢 𝔭 hadd hzero 𝔉 k pos x fw i]
    rfl
  obtain ⟨m, hm⟩ : ∃ m, fw.length = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun h0 => hfw (List.length_eq_zero_iff.mp h0)
  have hprod : ∏ e ∈ Finset.range (m + 1),
        posWeight 𝔭 𝒢 q (𝔭.shift (skelOff 𝒢 𝔉 k x fw e) pos) (skelLst 𝒢 𝔉 k x fw e) *
          posWeight 𝔭 𝒢 q (𝔭.shift (skelOff 𝒢 𝔉 k x fw (e + 1)) pos)
            (skelLst 𝒢 𝔉 k x fw (e + 1)) =
      (∏ i ∈ Finset.range (m + 1 + 1),
          if ListInj (skelLst 𝒢 𝔉 k x fw i) then (1 : ℝ) else 0) *
        pathFactor 𝔭 𝒢.allPrimes q (m + 1) (skelLab 𝒢 𝔉 k x fw) (skelOff 𝒢 𝔉 k x fw) pos := by
    rw [prod_adjacent
      (fun i => posWeight 𝔭 𝒢 q (𝔭.shift (skelOff 𝒢 𝔉 k x fw i) pos) (skelLst 𝒢 𝔉 k x fw i)) m]
    exact prod_visit_eq hd hq 𝔭 pos (m + 1) (skelOff 𝒢 𝔉 k x fw) (skelLst 𝒢 𝔉 k x fw)
  have hreal : ∏ e ∈ Finset.range fw.length,
        edgeW 𝔭 𝒢 q (walkEnd (edgeTgt 𝔭 𝒢 𝔉 k) (false, (pos, x)) (fw.take e)) *
          edgeW 𝔭 𝒢 q (walkEnd (edgeTgt 𝔭 𝒢 𝔉 k) (false, (pos, x)) (fw.take (e + 1))) =
      skelInj 𝒢 𝔉 k x fw * pathFactor 𝔭 𝒢.allPrimes q fw.length (skelLab 𝒢 𝔉 k x fw)
        (skelOff 𝒢 𝔉 k x fw) pos := by
    rw [Finset.prod_congr rfl fun e _ => by rw [hW e, hW (e + 1)]]
    unfold skelInj
    rw [hm]
    exact hprod
  rw [walkCoef_eq_weights (edgeCoef 𝔭 𝒢 q 𝔉 k ζ) (edgeTgt 𝔭 𝒢 𝔉 k) (edgeW 𝔭 𝒢 q)
    (edgeK 𝔭 𝒢 𝔉 ζ) (edgeCoef_eq 𝔭 𝒢 q 𝔉 k ζ), hκ, hreal]

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- Where `skelInj · (eq:path-residue-factor)` does not vanish, the state of the path is
physical at every visit. -/
theorem isPhys_of_ne_zero {q : ℝ} (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (pos : 𝔭.Pos)
    (x : Lists 𝒢 J ℓ) (fw : List (PhysChoice 𝒢 𝔉))
    (hne : skelInj 𝒢 𝔉 k x fw * pathFactor 𝔭 𝒢.allPrimes q fw.length (skelLab 𝒢 𝔉 k x fw)
      (skelOff 𝒢 𝔉 k x fw) pos ≠ 0) {i : ℕ} (hi : i ≤ fw.length) :
    IsPhys 𝔭 (𝔭.shift (skelOff 𝒢 𝔉 k x fw i) pos) (skelLst 𝒢 𝔉 k x fw i) := by
  have hInj : skelInj 𝒢 𝔉 k x fw ≠ 0 := left_ne_zero_of_mul hne
  have hpf := right_ne_zero_of_mul hne
  refine (isPhys_iff 𝔭 _ _).mpr ⟨?_, pathFactor_hit_of_ne_zero hpf hi⟩
  unfold skelInj at hInj
  have hfac := Finset.prod_ne_zero_iff.mp hInj i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  by_contra hc
  exact hfac (if_neg hc)

end Model

/-! ### The term of a path in the expansion of the moment -/

section Term

variable (𝔭 : PosModel)
  (hadd : ∀ (a b : ℤ) (n : 𝔭.Pos), 𝔭.shift a (𝔭.shift b n) = 𝔭.shift (b + a) n)
  (hzero : ∀ n : 𝔭.Pos, 𝔭.shift 0 n = n)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem flatWord_ne_nil {Ξ : Type*} {w : List (Ξ × Ξ)} (hw : w ≠ []) : flatWord w ≠ [] := by
  cases w with
  | nil => exact absurd rfl hw
  | cons ξ w => exact List.cons_ne_nil _ _

include hzero in
omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- If the start is not physical, `skelInj · (eq:path-residue-factor)` vanishes. -/
theorem skelInj_mul_pathFactor_eq_zero {q : ℝ} (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ)
    (pos : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (fw : List (PhysChoice 𝒢 𝔉)) (h0 : ¬IsPhys 𝔭 pos x) :
    skelInj 𝒢 𝔉 k x fw * pathFactor 𝔭 𝒢.allPrimes q fw.length (skelLab 𝒢 𝔉 k x fw)
      (skelOff 𝒢 𝔉 k x fw) pos = 0 := by
  by_contra hne
  have h := isPhys_of_ne_zero 𝒢 𝔭 𝔉 k pos x fw hne (Nat.zero_le _)
  rw [skelOff_zero, hzero, skelLst_zero] at h
  exact h0 h

include hadd hzero in
omit [Fintype N] in
/-- **The term of a path in the expansion of the moment** [S-02:0212–0234]: for a physical start,
`mass · (coefficient of the walk) · u_n(end)` is
`mass · skelKappa · 1_{h_N = 0} · skelInj · (eq:path-residue-factor)`. -/
theorem round_term_of_isPhys (hd : GroupsDisjoint 𝒢) {q : ℝ} (hq : 0 < q)
    (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (pos : 𝔭.Pos)
    (hfree : ∀ d : ℤ, 𝔭.shift d pos = pos ↔ d = 0) (x : Lists 𝒢 J ℓ)
    (w : List (PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉)) (hw : w ≠ []) :
    (stateMass 𝒢 J ℓ : ℂ) *
        walkCoef (physRoundCoef 𝔭 𝒢 q 𝔉 k ζ) (physRoundTgt 𝔭 𝒢 𝔉 k) (pos, x) w *
        physUnit 𝔭 𝒢 J ℓ pos (walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (pos, x) w) =
      ((stateMass 𝒢 J ℓ : ℂ) * skelKappa 𝒢 𝔉 k ζ x (flatWord w) *
          (if skelOff 𝒢 𝔉 k x (flatWord w) (flatWord w).length = 0 then 1 else 0)) *
        ((skelInj 𝒢 𝔉 k x (flatWord w) *
          pathFactor 𝔭 𝒢.allPrimes q (flatWord w).length (skelLab 𝒢 𝔉 k x (flatWord w))
            (skelOff 𝒢 𝔉 k x (flatWord w)) pos : ℝ) : ℂ) := by
  have hcoef : walkCoef (physRoundCoef 𝔭 𝒢 q 𝔉 k ζ) (physRoundTgt 𝔭 𝒢 𝔉 k) (pos, x) w =
      skelKappa 𝒢 𝔉 k ζ x (flatWord w) *
        ((skelInj 𝒢 𝔉 k x (flatWord w) *
          pathFactor 𝔭 𝒢.allPrimes q (flatWord w).length (skelLab 𝒢 𝔉 k x (flatWord w))
            (skelOff 𝒢 𝔉 k x (flatWord w)) pos : ℝ) : ℂ) :=
    (walkCoef_round_eq (physFwdCoef 𝔭 𝒢 q 𝔉 k ζ) (physBwdCoef 𝔭 𝒢 q 𝔉 k ζ)
      (physFwdTgt 𝔭 𝒢 𝔉 k) (physBwdTgt 𝔭 𝒢 𝔉 k) (pos, x) w).trans
      (edge_walkCoef 𝒢 𝔭 hadd hzero hd hq 𝔉 k ζ pos x (flatWord w) (flatWord_ne_nil hw))
  have hend : walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (pos, x) w =
      (𝔭.shift (skelOff 𝒢 𝔉 k x (flatWord w) (flatWord w).length) pos,
        skelLst 𝒢 𝔉 k x (flatWord w) (flatWord w).length) := by
    have h1 := walkEnd_round_eq (physFwdTgt 𝔭 𝒢 𝔉 k) (physBwdTgt 𝔭 𝒢 𝔉 k) (pos, x) w
    have h2 := walkEnd_edge 𝒢 𝔭 hadd hzero 𝔉 k pos x (flatWord w)
    exact congrArg Prod.snd (h1.symm.trans h2)
  by_cases hPF : skelInj 𝒢 𝔉 k x (flatWord w) *
      pathFactor 𝔭 𝒢.allPrimes q (flatWord w).length (skelLab 𝒢 𝔉 k x (flatWord w))
        (skelOff 𝒢 𝔉 k x (flatWord w)) pos = 0
  · rw [hcoef, hPF]
    simp
  · have hN := isPhys_of_ne_zero 𝒢 𝔭 𝔉 k pos x (flatWord w) hPF le_rfl
    have hunit : physUnit 𝔭 𝒢 J ℓ pos (walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (pos, x) w) =
        if skelOff 𝒢 𝔉 k x (flatWord w) (flatWord w).length = 0 then 1 else 0 := by
      rw [hend]
      unfold physUnit
      dsimp only
      by_cases hd0 : skelOff 𝒢 𝔉 k x (flatWord w) (flatWord w).length = 0
      · rw [if_pos hd0, if_pos (And.intro ((hfree _).mpr hd0) hN)]
      · rw [if_neg hd0, if_neg fun h => hd0 ((hfree _).mp h.1)]
    rw [hcoef, hunit]
    ring

include hadd hzero in
omit [Fintype N] in
/-- The real part of the term of a path, for a physical start. -/
theorem re_round_term (hd : GroupsDisjoint 𝒢) {q : ℝ} (hq : 0 < q)
    (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (pos : 𝔭.Pos)
    (hfree : ∀ d : ℤ, 𝔭.shift d pos = pos ↔ d = 0) (x : Lists 𝒢 J ℓ)
    (w : List (PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉)) (hw : w ≠ []) :
    ((stateMass 𝒢 J ℓ : ℂ) *
        walkCoef (physRoundCoef 𝔭 𝒢 q 𝔉 k ζ) (physRoundTgt 𝔭 𝒢 𝔉 k) (pos, x) w *
        physUnit 𝔭 𝒢 J ℓ pos (walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (pos, x) w)).re =
      pathAmp 𝒢 𝔉 k ζ x (flatWord w) *
        pathFactor 𝔭 𝒢.allPrimes q (flatWord w).length (skelLab 𝒢 𝔉 k x (flatWord w))
          (skelOff 𝒢 𝔉 k x (flatWord w)) pos := by
  rw [round_term_of_isPhys 𝒢 𝔭 hadd hzero hd hq 𝔉 k ζ pos hfree x w hw, Complex.re_mul_ofReal]
  unfold pathAmp
  ring

include hzero in
omit [Fintype N] in
/-- If the start is not physical, the amplitude times (eq:path-residue-factor) vanishes. -/
theorem pathAmp_mul_pathFactor_eq_zero {q : ℝ} (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (pos : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (fw : List (PhysChoice 𝒢 𝔉)) (h0 : ¬IsPhys 𝔭 pos x) :
    pathAmp 𝒢 𝔉 k ζ x fw *
      pathFactor 𝔭 𝒢.allPrimes q fw.length (skelLab 𝒢 𝔉 k x fw) (skelOff 𝒢 𝔉 k x fw) pos =
        0 := by
  unfold pathAmp
  rw [mul_assoc, skelInj_mul_pathFactor_eq_zero 𝒢 𝔭 hzero 𝔉 k pos x fw h0, mul_zero]

include hadd hzero in
/-- **The moment is a sum over paths of amplitudes times (eq:path-residue-factor)**
[S-02:0212–0234]. The amplitudes `pathAmp`, the offsets `skelOff` and the label sets `skelLab`
do not depend on the position `pos` or on the position model. -/
theorem physMoment_eq_sum_paths (hd : GroupsDisjoint 𝒢) {q : ℝ} (hq : 0 < q)
    (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (pos : 𝔭.Pos)
    (hfree : ∀ d : ℤ, 𝔭.shift d pos = pos ↔ d = 0) {R : ℕ} (hR : 0 < R) :
    physMoment 𝔭 𝒢 q 𝔉 k ζ R pos =
      ∑ x : Lists 𝒢 J ℓ, ∑ w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉,
        pathAmp 𝒢 𝔉 k ζ x (flatWord (List.ofFn w)) *
          pathFactor 𝔭 𝒢.allPrimes q (2 * R) (skelLab 𝒢 𝔉 k x (flatWord (List.ofFn w)))
            (skelOff 𝒢 𝔉 k x (flatWord (List.ofFn w))) pos := by
  have hlen : ∀ w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉,
      (flatWord (List.ofFn w)).length = 2 * R := fun w => by
    rw [length_flatWord, List.length_ofFn]
  have hne : ∀ w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉, List.ofFn w ≠ [] := fun w h => by
    have h1 := congrArg List.length h
    rw [List.length_ofFn, List.length_nil] at h1
    omega
  rw [physMoment_eq_sum_walks, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h0 : IsPhys 𝔭 pos x
  · rw [if_pos h0, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h := re_round_term 𝒢 𝔭 hadd hzero hd hq 𝔉 k ζ pos hfree x (List.ofFn w) (hne w)
    rw [hlen w] at h
    rw [← mul_assoc]
    exact h
  · rw [if_neg h0, Complex.zero_re]
    symm
    refine Finset.sum_eq_zero fun w _ => ?_
    have h := pathAmp_mul_pathFactor_eq_zero 𝒢 𝔭 hzero (q := q) 𝔉 k ζ pos x
      (flatWord (List.ofFn w)) h0
    rw [hlen w] at h
    exact h

end Term

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum
