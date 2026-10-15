module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.PhaseEdge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The physical walk of a skeleton

Source: `verification/stage7-sources/S-02.tex`, lines 212–222 (`[S-02:0212–0222]`): "expand the
left side of (eq:transference-moment) into paths with `N` alternating forward and backward edges.
Fix the patterns, all endpoint permutations, the auxiliary labels, and the active lists at visits
`0, …, N`. These choices fix offsets `h_0 = 0, h_1, …, h_N`."

Tools for `PhaseSkeletonProof.lean` (part (A) of the proof of [S] Lemma 3.7): the physical side of
what `HistorySkeleton.lean` does for the memory side.

* `Skel.ppos`, `Skel.pstate` — the position `(h_i, y + h_i)` and the state at the visit `i` of the
  walk with skeleton `sk` which starts at the residues `y`.
* `Skel.fwdTgt_pstate`, `Skel.bwdTgt_pstate` — an even edge is a forward edge and an odd edge a
  backward edge from the state at the visit `i` to the state at the visit `i + 1`.
* `Skel.physCore`, `Skel.fwdCoef_pstate`, `Skel.bwdCoef_pstate` — in both orientations the
  coefficient of the edge `i` is the two symmetrization averages times the symmetric coefficient
  `Skel.physCore` between the visits `i` and `i + 1`, with the oriented multiplier `Skel.mult`.
* `Skel.rounds`, `Skel.sum_rounds` — a skeleton with `N = 2R` edges is its initial lists and a
  word of `R` rounds.
* `Skel.walk_rounds` — the walk of the rounds of a skeleton ends at the state of the visit `N`,
  and its coefficient is the product over the edges.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {D : MemData 𝒢 J ℓ N}

/-! ### Positions and states -/

/-- **The position at the visit `i`** of the walk with skeleton `sk` which starts at the offset
`0` and the residues `y`: the offset `h_i` and the residues `y + h_i`. -/
def Skel.ppos (sk : Skel D) (y : ResVec 𝒢.allPrimes) (i : ℕ) : (tagModel 𝒢.allPrimes).Pos :=
  tagPos (Q := 𝒢.allPrimes) (sk.off i) ((resModel 𝒢.allPrimes).shift (sk.off i) y)

/-- **The state at the visit `i`**: the position `Skel.ppos` and the lists of the skeleton. -/
def Skel.pstate (sk : Skel D) (y : ResVec 𝒢.allPrimes) (i : ℕ) :
    PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ :=
  (sk.ppos y i, sk.lists i)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The step of a forward edge is `k D_i`. -/
theorem Skel.step_even (sk : Skel D) (i : Fin D.n) (hi : i.val % 2 = 0) :
    sk.step i = D.k * (sk.dilAt i : ℤ) := by
  unfold Skel.step edgeSign
  rw [if_pos hi, one_mul]

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The step of a backward edge is `-k D_i`. -/
theorem Skel.step_odd (sk : Skel D) (i : Fin D.n) (hi : ¬i.val % 2 = 0) :
    sk.step i = -(D.k * (sk.dilAt i : ℤ)) := by
  unfold Skel.step edgeSign
  rw [if_neg hi]
  ring

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The position at the visit `i + 1` is the position at the visit `i`, translated by the step of
the edge `i`. -/
theorem Skel.ppos_succ (sk : Skel D) (y : ResVec 𝒢.allPrimes) (i : Fin D.n) :
    (tagModel 𝒢.allPrimes).shift (sk.step i) (sk.ppos y i.val) = sk.ppos y (i.val + 1) := by
  have hoff : sk.off (i.val + 1) = sk.off i.val + sk.step i := sk.off_succ i.val i.isLt
  unfold Skel.ppos
  rw [hoff, ← memId_shift_shift]
  rfl

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The initial state. -/
theorem Skel.pstate_zero (sk : Skel D) (y : ResVec 𝒢.allPrimes) :
    sk.pstate y 0 =
      ((tagStart y, ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ)) : PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ) := by
  have h0 := sk.off_zero
  have h1 : ((resModel 𝒢.allPrimes).shift (sk.off 0) y : ResVec 𝒢.allPrimes) = y := by
    rw [h0]
    exact memId_shift_zero y
  refine Prod.ext ?_ rfl
  exact congrArg₂ (fun (a : ℤ) (z : ResVec 𝒢.allPrimes) => tagPos a z) h0 h1

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **A forward edge**: the forward transition of the edge `i` (for even `i`) maps the state at
the visit `i` to the state at the visit `i + 1`. -/
theorem Skel.fwdTgt_pstate (sk : Skel D) (y : ResVec 𝒢.allPrimes) (i : Fin D.n)
    (hi : i.val % 2 = 0) :
    physFwdTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k (sk.pstate y i.val) (sk.edge i) =
      sk.pstate y (i.val + 1) := by
  refine Prod.ext ?_ (sk.lists_succ i.val i.isLt).symm
  have h := sk.ppos_succ y i
  rw [sk.step_even i hi] at h
  exact h

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **A backward edge**: the backward transition of the edge `i` (for odd `i`) maps the state at
the visit `i` to the state at the visit `i + 1`. -/
theorem Skel.bwdTgt_pstate (sk : Skel D) (y : ResVec 𝒢.allPrimes) (i : Fin D.n)
    (hi : ¬i.val % 2 = 0) :
    physBwdTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k (sk.pstate y i.val) (sk.edge i) =
      sk.pstate y (i.val + 1) := by
  refine Prod.ext ?_ (sk.lists_succ i.val i.isLt).symm
  have h := sk.ppos_succ y i
  rw [sk.step_odd i hi] at h
  exact h

/-! ### The coefficient of an edge -/

/-- **The coefficient of the edge `i` between the two symmetrizations**, in symmetric form: the
symmetric coefficient between the positions and the canonical lists at the visits `i` and `i + 1`,
with the oriented multiplier `Skel.mult` (`K_ν D^{iζ}` or its conjugate with roles
interchanged). -/
def Skel.physCore (sk : Skel D) (y : ResVec 𝒢.allPrimes) (i : Fin D.n) : ℂ :=
  symCoef (tagModel 𝒢.allPrimes) 𝒢 D.q (D.fam (sk.pat i)) (sk.ppos y i.val)
    (sk.ppos y (i.val + 1)) (sk.src i) (sk.tgt i) (sk.aux i) (sk.mult i)

omit [Fintype N] in
/-- The coefficient of a forward edge. -/
theorem Skel.fwdCoef_pstate (sk : Skel D) (y : ResVec 𝒢.allPrimes) (i : Fin D.n)
    (hi : i.val % 2 = 0) :
    physFwdCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ (sk.pstate y i.val) (sk.edge i) =
      (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * sk.physCore y i *
        (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ := by
  have hpos : (tagModel 𝒢.allPrimes).shift
      (D.k * (dil (D.fam (sk.pat i)).C (sk.src i) (sk.aux i) : ℤ)) (sk.ppos y i.val) =
      sk.ppos y (i.val + 1) := by
    have h := sk.ppos_succ y i
    rw [sk.step_even i hi] at h
    exact h
  have hmult : (D.fam (sk.pat i)).K (sk.src i).2 (sk.tgt i).2 (sk.aux i) *
      ((dil (D.fam (sk.pat i)).C (sk.src i) (sk.aux i) : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I) =
      sk.mult i := by
    unfold Skel.mult
    exact (if_pos hi).symm
  have hcore : physCoef (tagModel 𝒢.allPrimes) 𝒢 D.q (D.fam (sk.pat i)) D.k D.ζ
      (sk.ppos y i.val) (sk.src i) (sk.aux i) (sk.tgt i) = sk.physCore y i :=
    (physCoef_eq_symCoef (tagModel 𝒢.allPrimes) 𝒢 D.q (D.fam (sk.pat i)) D.k D.ζ
      (sk.ppos y i.val) (sk.src i) (sk.aux i) (sk.tgt i)).trans
      (congrArg₂ (fun (m' : (tagModel 𝒢.allPrimes).Pos) (μ : ℂ) =>
        symCoef (tagModel 𝒢.allPrimes) 𝒢 D.q (D.fam (sk.pat i)) (sk.ppos y i.val) m'
          (sk.src i) (sk.tgt i) (sk.aux i) μ) hpos hmult)
  exact congrArg (fun t => (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * t *
    (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹) hcore

omit [Fintype N] in
/-- The coefficient of a backward edge [S-02:0120–0130]. -/
theorem Skel.bwdCoef_pstate (sk : Skel D) (y : ResVec 𝒢.allPrimes) (i : Fin D.n)
    (hi : ¬i.val % 2 = 0) :
    physBwdCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ (sk.pstate y i.val) (sk.edge i) =
      (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * sk.physCore y i *
        (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ := by
  have hpos : (tagModel 𝒢.allPrimes).shift
      (-(D.k * (dil (D.fam (sk.pat i)).C (sk.src i) (sk.aux i) : ℤ))) (sk.ppos y i.val) =
      sk.ppos y (i.val + 1) := by
    have h := sk.ppos_succ y i
    rw [sk.step_odd i hi] at h
    exact h
  have hmult : conj ((D.fam (sk.pat i)).K (sk.tgt i).2 (sk.src i).2 (sk.aux i) *
      ((dil (D.fam (sk.pat i)).C (sk.src i) (sk.aux i) : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I)) =
      sk.mult i := by
    unfold Skel.mult
    exact (if_neg hi).symm
  have hcore : conj (physCoef (tagModel 𝒢.allPrimes) 𝒢 D.q (D.fam (sk.pat i)) D.k D.ζ
      ((tagModel 𝒢.allPrimes).shift
        (-(D.k * (dil (D.fam (sk.pat i)).C (sk.src i) (sk.aux i) : ℤ))) (sk.ppos y i.val))
      (sk.tgt i) (sk.aux i) (sk.src i)) = sk.physCore y i :=
    (phSkel_conj_physCoef_rev (tagModel 𝒢.allPrimes) 𝒢 D.q (D.fam (sk.pat i)) D.k D.ζ
      (sk.ppos y i.val) (sk.src i) (sk.tgt i) (sk.aux i)).trans
      (congrArg₂ (fun (m' : (tagModel 𝒢.allPrimes).Pos) (μ : ℂ) =>
        symCoef (tagModel 𝒢.allPrimes) 𝒢 D.q (D.fam (sk.pat i)) (sk.ppos y i.val) m'
          (sk.src i) (sk.tgt i) (sk.aux i) μ) hpos hmult)
  exact congrArg (fun t => (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * t *
    (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹) hcore

/-! ### Rounds -/

/-- **The rounds of a skeleton with `N = 2R` edges**: the round `r` is the pair of the edges
`2r` (forward) and `2r + 1` (backward). -/
def Skel.rounds (sk : Skel D) {R : ℕ} (hN : D.n = 2 * R) :
    Fin R → PhysChoice 𝒢 D.fam × PhysChoice 𝒢 D.fam :=
  fun r => (sk.edge ⟨2 * r.val, by have := r.isLt; omega⟩,
    sk.edge ⟨2 * r.val + 1, by have := r.isLt; omega⟩)

/-- **A skeleton with `N = 2R` edges is its initial lists and a word of `R` rounds**: a sum over
the initial lists and over the words of rounds is a sum over the skeletons. -/
theorem Skel.sum_rounds (D : MemData 𝒢 J ℓ N) {R : ℕ} (hN : D.n = 2 * R)
    (F : Lists 𝒢 J ℓ → (Fin R → PhysChoice 𝒢 D.fam × PhysChoice 𝒢 D.fam) → ℂ) :
    ∑ x : Lists 𝒢 J ℓ, ∑ w : Fin R → PhysChoice 𝒢 D.fam × PhysChoice 𝒢 D.fam, F x w =
      ∑ sk : Skel D, F (sk.xs₀, sk.xb₀) (sk.rounds hN) := by
  have h1 : ∑ sk : Skel D, F (sk.xs₀, sk.xb₀) (sk.rounds hN) =
      ∑ xs : LabelList 𝒢.small J ℓ, ∑ xb : LabelList 𝒢.big J ℓ,
        ∑ e : Fin D.n → PhysChoice 𝒢 D.fam,
          F (xs, xb) (phSkel_pairWordEquiv (PhysChoice 𝒢 D.fam) hN e) :=
    sum_equiv_triple (Skel.equivProd D)
      (fun xs xb e => F (xs, xb) (phSkel_pairWordEquiv (PhysChoice 𝒢 D.fam) hN e))
  have h2 : ∑ x : Lists 𝒢 J ℓ, ∑ w : Fin R → PhysChoice 𝒢 D.fam × PhysChoice 𝒢 D.fam, F x w =
      ∑ xs : LabelList 𝒢.small J ℓ, ∑ xb : LabelList 𝒢.big J ℓ,
        ∑ w : Fin R → PhysChoice 𝒢 D.fam × PhysChoice 𝒢 D.fam, F (xs, xb) w :=
    Fintype.sum_prod_type (fun x : LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ =>
      ∑ w : Fin R → PhysChoice 𝒢 D.fam × PhysChoice 𝒢 D.fam, F x w)
  refine h2.trans (Eq.trans ?_ h1.symm)
  exact Finset.sum_congr rfl fun xs _ => Finset.sum_congr rfl fun xb _ =>
    (Equiv.sum_comp (phSkel_pairWordEquiv (PhysChoice 𝒢 D.fam) hN)
      (fun w => F (xs, xb) w)).symm

omit [Fintype N] in
/-- **The walk of a skeleton**: the walk of the `R` rounds of a skeleton with `N = 2R` edges,
from the offset `0`, the residues `y` and the initial lists, ends at the state of the visit `N`;
its coefficient is the product over the edges of the two symmetrization averages and the symmetric
coefficient `Skel.physCore`. -/
theorem Skel.walk_rounds (sk : Skel D) {R : ℕ} (hN : D.n = 2 * R) (y : ResVec 𝒢.allPrimes) :
    walkEnd (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k)
        ((tagStart y, ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ)) : PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ)
        (List.ofFn (sk.rounds hN)) = sk.pstate y D.n ∧
      walkCoef (physRoundCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ)
        (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k)
        ((tagStart y, ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ)) : PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ)
        (List.ofFn (sk.rounds hN)) =
        ∏ i : Fin D.n, ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * sk.physCore y i *
          (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹) := by
  -- one round: a forward edge and a backward edge
  have hround : ∀ r : Fin R,
      physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k (sk.pstate y (2 * r.val))
          (sk.rounds hN r) = sk.pstate y (2 * r.val + 1 + 1) ∧
        physRoundCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ (sk.pstate y (2 * r.val))
          (sk.rounds hN r) =
          ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
              sk.physCore y ⟨2 * r.val, by have := r.isLt; omega⟩ *
              (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹) *
            ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
              sk.physCore y ⟨2 * r.val + 1, by have := r.isLt; omega⟩ *
              (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹) := by
    intro r
    have hr := r.isLt
    have h0 : 2 * r.val < D.n := by omega
    have h1 : 2 * r.val + 1 < D.n := by omega
    have p0 : (2 * r.val) % 2 = 0 := by omega
    have p1 : ¬(2 * r.val + 1) % 2 = 0 := by omega
    have e0 : physFwdTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k (sk.pstate y (2 * r.val))
        (sk.edge ⟨2 * r.val, h0⟩) = sk.pstate y (2 * r.val + 1) :=
      sk.fwdTgt_pstate y ⟨2 * r.val, h0⟩ p0
    have e1 : physBwdTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k (sk.pstate y (2 * r.val + 1))
        (sk.edge ⟨2 * r.val + 1, h1⟩) = sk.pstate y (2 * r.val + 1 + 1) :=
      sk.bwdTgt_pstate y ⟨2 * r.val + 1, h1⟩ p1
    have c0 : physFwdCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ (sk.pstate y (2 * r.val))
        (sk.edge ⟨2 * r.val, h0⟩) =
        (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * sk.physCore y ⟨2 * r.val, h0⟩ *
          (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ :=
      sk.fwdCoef_pstate y ⟨2 * r.val, h0⟩ p0
    have c1 : physBwdCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ
        (sk.pstate y (2 * r.val + 1)) (sk.edge ⟨2 * r.val + 1, h1⟩) =
        (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * sk.physCore y ⟨2 * r.val + 1, h1⟩ *
          (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ :=
      sk.bwdCoef_pstate y ⟨2 * r.val + 1, h1⟩ p1
    refine ⟨?_, ?_⟩
    · exact (congrArg (fun s => physBwdTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k s
        (sk.edge ⟨2 * r.val + 1, h1⟩)) e0).trans e1
    · exact congrArg₂ (· * ·) c0
        ((congrArg (fun s => physBwdCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ s
          (sk.edge ⟨2 * r.val + 1, h1⟩)) e0).trans c1)
  -- the walk
  obtain ⟨hend, hcoef⟩ := walk_ofFn (physRoundCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ)
    (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k) (fun r => sk.pstate y (2 * r)) R
    (sk.rounds hN)
    (fun r => (congrArg (sk.pstate y) (show 2 * (r.val + 1) = 2 * r.val + 1 + 1 by omega)).trans
      (hround r).1.symm)
  have hs : sk.pstate y (2 * 0) =
      ((tagStart y, ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ)) : PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ) :=
    sk.pstate_zero y
  refine ⟨((congrArg (fun s => walkEnd (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k) s
      (List.ofFn (sk.rounds hN))) hs).symm.trans hend).trans
      (congrArg (sk.pstate y) hN.symm), ?_⟩
  refine ((congrArg (fun s => walkCoef (physRoundCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ)
      (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k) s (List.ofFn (sk.rounds hN)))
      hs).symm.trans hcoef).trans ?_
  exact (Finset.prod_congr rfl fun r _ => (hround r).2).trans
    (phSkel_prod_fin_pairs hN (fun i => (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
      sk.physCore y i * (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹)).symm

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
