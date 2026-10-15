module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.PhaseWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The physical path expansion by skeletons: `PhaseSkeleton`

Source: `verification/stage7-sources/S-02.tex`, lines 212–234 and 293–314
(`[S-02:0212–0234, 0293–0314]`).

`phaseSkeleton : PhaseSkeleton` (part (A) of the proof of [S] Lemma 3.7) is proved here: for
`N = 2R`, `q > 0` and disjoint sets of small and big primes,

`phaseSum θ = E_y Σ_sk common(θ, y, sk) · bigPhys(sk)`,

the mean over the small residues `y` of the sum over the skeletons of the common part times the
expectation of the big part of the physical weight.

## The proof

* **Paths.** `pairUnit_pow_eq_sum_walks` expands `⟨u_{(0,y)}, (𝒜 𝒜*)^R φ_θ⟩` into the initial
  lists and the words of `R` rounds; these are the skeletons (`Skel.sum_rounds`).
* **One path.** The walk of a skeleton visits the states `((h_i, y + h_i), lists i)` and its
  coefficient is the product over the edges of the symmetric coefficients `Skel.physCore`
  (`Skel.walk_rounds`). The phase `e(θ h_N)` is the product of the phases of the edges
  (`Skel.expUnit_off`); the coefficient of an edge times its phase is the common factor
  `Skel.edgeCommon` at the small residues times the factor `Skel.bigEdge` at the big residues
  (`Skel.physCore_split`); the mass of the initial state splits in the same way
  (`Skel.start_split`); the indicator of the vector `φ_θ` at the end of the walk is implied by
  the conditions of the last edge (`Skel.start_mul_walkW_eq_zero`). Hence the term of a skeleton
  is `common(θ, y_𝒮) · bigPhysAt(y_ℬ)` (`Skel.phaseTerm_eq`).
* **Residues.** The residue vector at all group primes is the pair of its small and its big part
  (`resSplit_sum`, `resSplit_card`); the mean over the big part of `bigPhysAt` is `bigPhys`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {D : MemData 𝒢 J ℓ N}

/-! ### The two halves of an edge -/

open _root_.Classical in
/-- **The factor of the edge `i` in the big part of the physical weight** (`Skel.bigPhysAt`), for
the big residues `yB` at the visit `0`. -/
def Skel.bigEdge (sk : Skel D) (yB : ResVec (bigPrimes 𝒢)) (i : Fin D.n) : ℝ :=
  if IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) yB) (sk.src i).2 ∧
      IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) yB) (sk.tgt i).2 then
    bigTargetNorm 𝒢 ℓ (sk.Cset i) *
      (bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) yB) *
        bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) yB))
  else 0

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
open _root_.Classical in
/-- The big part of the physical weight is the mass of the initial big state times the product of
the factors of the edges. -/
theorem Skel.bigPhysAt_eq_bigEdge (sk : Skel D) (yB : ResVec (bigPrimes 𝒢)) :
    sk.bigPhysAt yB =
      (if IsBigState 𝒢 yB sk.xb₀ then bigListNorm 𝒢 J ℓ else 0) *
        ∏ i : Fin D.n, sk.bigEdge yB i :=
  rfl

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **The coefficient of an edge, with its phase, is the common factor times the big factor**
[S-02:0226–0234]: for `q > 0`,
`physCore(y) · e(θ σ_i k D_i) = edgeCommon(θ, y_𝒮) · bigEdge(y_ℬ)`. -/
theorem Skel.physCore_split (sk : Skel D) (hq : 0 < D.q) (θ : ℝ) (y : ResVec 𝒢.allPrimes)
    (i : Fin D.n) :
    sk.physCore y i * expUnit (θ * (sk.step i : ℝ)) =
      sk.edgeCommon θ (resS 𝒢 y) i * ((sk.bigEdge (resB 𝒢 y) i : ℝ) : ℂ) :=
  symCoef_tag_split hq (D.fam (sk.pat i)) (sk.off i.val) (sk.off (i.val + 1))
    ((resModel 𝒢.allPrimes).shift (sk.off i.val) y)
    ((resModel 𝒢.allPrimes).shift (sk.off (i.val + 1)) y)
    ((resModel (smallPrimes 𝒢)).shift (sk.off i.val) (resS 𝒢 y))
    ((resModel (smallPrimes 𝒢)).shift (sk.off (i.val + 1)) (resS 𝒢 y))
    ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) (resB 𝒢 y))
    ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) (resB 𝒢 y))
    rfl rfl rfl rfl (sk.src i) (sk.tgt i) (sk.aux i) (sk.mult i)
    (expUnit (θ * (sk.step i : ℝ)))

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **The phase `e(θ h_N)` is the product of the phases of the edges** [S-02:0308–0313]. -/
theorem Skel.expUnit_off (sk : Skel D) (θ : ℝ) :
    expUnit (θ * (sk.off D.n : ℝ)) = ∏ i : Fin D.n, expUnit (θ * (sk.step i : ℝ)) := by
  have hoff : ((sk.off D.n : ℤ) : ℝ) = ∑ i : Fin D.n, (sk.step i : ℝ) := by
    unfold Skel.off
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [if_pos j.isLt]
  rw [hoff, Finset.mul_sum]
  exact phSkel_expUnit_sum Finset.univ fun i => θ * (sk.step i : ℝ)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- If the state at the visit `i + 1` is not physical, the coefficient of the edge `i`
vanishes: the target lists of an edge are a physical state at the next position, and physical
states are stable under the target permutation. -/
theorem Skel.physCore_eq_zero (sk : Skel D) (y : ResVec 𝒢.allPrimes) (i : Fin D.n) (j : ℕ)
    (hj : j = i.val + 1)
    (hn : ¬IsPhys (tagModel 𝒢.allPrimes) (sk.ppos y j) (sk.lists j)) : sk.physCore y i = 0 := by
  subst hj
  rw [sk.lists_succ i.val i.isLt] at hn
  unfold Skel.physCore symCoef
  exact if_neg fun h => hn (isPhys_permuteLists_of _ _ h.2.1)

/-! ### The term of a skeleton -/

/-- **The coefficient of the walk of a skeleton**: the product over the edges of the two
symmetrization averages and the symmetric coefficient. -/
def Skel.walkW (sk : Skel D) (y : ResVec 𝒢.allPrimes) : ℂ :=
  ∏ i : Fin D.n, ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * sk.physCore y i *
    (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹)

omit [Fintype N] in
/-- **The coefficient of the walk, with the phase `e(θ h_N)`, is the product of the common
factors of the edges times the product of their big factors.** -/
theorem Skel.walkW_mul_phase (sk : Skel D) (hq : 0 < D.q) (θ : ℝ) (y : ResVec 𝒢.allPrimes) :
    sk.walkW y * expUnit (θ * (sk.off D.n : ℝ)) =
      (∏ i : Fin D.n, ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
          sk.edgeCommon θ (resS 𝒢 y) i * (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹)) *
        ((∏ i : Fin D.n, sk.bigEdge (resB 𝒢 y) i : ℝ) : ℂ) := by
  have alg : ∀ (c pc e ec be : ℂ), pc * e = ec * be → c * pc * c * e = c * ec * c * be := by
    intro c pc e ec be h
    calc c * pc * c * e = c * (pc * e) * c := by ring
      _ = c * (ec * be) * c := by rw [h]
      _ = c * ec * c * be := by ring
  unfold Skel.walkW
  rw [sk.expUnit_off θ, ← Finset.prod_mul_distrib, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => alg _ _ _ _ _ (sk.physCore_split hq θ y i)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
open _root_.Classical in
/-- **The mass of the initial state is the product of its small and its big half.** -/
theorem Skel.start_split (sk : Skel D) (y : ResVec 𝒢.allPrimes) :
    (if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ) then
        (stateMass 𝒢 J ℓ : ℂ) else 0) =
      (if IsSmallState 𝒢 (resS 𝒢 y) sk.xs₀ then ((smallListMass 𝒢 J ℓ : ℝ) : ℂ) else 0) *
        (((if IsBigState 𝒢 (resB 𝒢 y) sk.xb₀ then bigListNorm 𝒢 J ℓ else 0 : ℝ)) : ℂ) :=
  memId_ite_split_mul _ _ _ (isPhys_tagPos_iff 0 y (sk.xs₀, sk.xb₀)) (Complex.ofReal_mul _ _)

omit [Fintype N] in
open _root_.Classical in
/-- **The end of the walk is physical**: if the state at the visit `N` is not physical, then the
initial state is not physical (`N = 0`) or the coefficient of the last edge vanishes. -/
theorem Skel.start_mul_walkW_eq_zero (sk : Skel D) (y : ResVec 𝒢.allPrimes)
    (hE : ¬IsPhys (tagModel 𝒢.allPrimes) (sk.ppos y D.n) (sk.lists D.n)) :
    (if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ) then
        (stateMass 𝒢 J ℓ : ℂ) else 0) * sk.walkW y = 0 := by
  rcases Nat.eq_zero_or_pos D.n with h0 | hpos
  · have hE' : ¬IsPhys (tagModel 𝒢.allPrimes) (tagStart y)
        ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ) := by
      intro hst
      apply hE
      rw [h0]
      have e1 : sk.ppos y 0 = tagStart y := congrArg Prod.fst (sk.pstate_zero y)
      rw [e1]
      exact hst
    rw [if_neg hE', zero_mul]
  · have hlt : D.n - 1 < D.n := by omega
    have hc : sk.physCore y ⟨D.n - 1, hlt⟩ = 0 :=
      sk.physCore_eq_zero y ⟨D.n - 1, hlt⟩ D.n (show D.n = D.n - 1 + 1 by omega) hE
    have hW : sk.walkW y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (⟨D.n - 1, hlt⟩ : Fin D.n)) (by
        show (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * sk.physCore y ⟨D.n - 1, hlt⟩ *
          (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ = 0
        rw [hc, mul_zero, zero_mul])
    rw [hW, mul_zero]

omit [Fintype N] in
open _root_.Classical in
/-- **The term of a skeleton in the path expansion** [S-02:0212–0234]: for `N = 2R` and `q > 0`,
the mass of the initial state, times the coefficient of the walk of the rounds of the skeleton
from `(0, y)`, times the value of the phase vector at its end, is the common part at the small
residues times the big part of the physical weight at the big residues. -/
theorem Skel.phaseTerm_eq (sk : Skel D) {R : ℕ} (hN : D.n = 2 * R) (hq : 0 < D.q) (θ : ℝ)
    (y : ResVec 𝒢.allPrimes) :
    (if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ) then
        (stateMass 𝒢 J ℓ : ℂ) *
          (walkCoef (physRoundCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ)
              (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k)
              ((tagStart y, ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ)) :
                PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ)
              (List.ofFn (sk.rounds hN)) *
            phaseVec 𝒢 θ (walkEnd (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k)
              ((tagStart y, ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ)) :
                PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ)
              (List.ofFn (sk.rounds hN))))
      else 0) =
      sk.common θ (resS 𝒢 y) * ((sk.bigPhysAt (resB 𝒢 y) : ℝ) : ℂ) := by
  obtain ⟨hend, hcoef⟩ := sk.walk_rounds hN y
  have hcoef' : walkCoef (physRoundCoef (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ)
      (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 D.fam D.k)
      ((tagStart y, ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ)) : PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ)
      (List.ofFn (sk.rounds hN)) = sk.walkW y := hcoef
  rw [hend, hcoef', phSkel_ite_mul]
  -- the term with the phase, without the indicator at the end
  have hB' : ((sk.bigPhysAt (resB 𝒢 y) : ℝ) : ℂ) =
      (((if IsBigState 𝒢 (resB 𝒢 y) sk.xb₀ then bigListNorm 𝒢 J ℓ else 0 : ℝ)) : ℂ) *
        ((∏ i : Fin D.n, sk.bigEdge (resB 𝒢 y) i : ℝ) : ℂ) := by
    rw [sk.bigPhysAt_eq_bigEdge]
    exact Complex.ofReal_mul _ _
  have hmain : (if IsPhys (tagModel 𝒢.allPrimes) (tagStart y)
          ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ) then (stateMass 𝒢 J ℓ : ℂ) else 0) *
        (sk.walkW y * expUnit (θ * (sk.off D.n : ℝ))) =
      sk.common θ (resS 𝒢 y) * ((sk.bigPhysAt (resB 𝒢 y) : ℝ) : ℂ) := by
    rw [sk.walkW_mul_phase hq θ y, sk.start_split y, hB']
    unfold Skel.common
    exact mul_mul_mul_comm _ _ _ _
  by_cases hE : IsPhys (tagModel 𝒢.allPrimes) (sk.ppos y D.n) (sk.lists D.n)
  · have hpv : phaseVec 𝒢 θ (sk.pstate y D.n) = expUnit (θ * (sk.off D.n : ℝ)) :=
      if_pos hE
    rw [hpv]
    exact hmain
  · have hpv : phaseVec 𝒢 θ (sk.pstate y D.n) = 0 := if_neg hE
    have h0 : (if IsPhys (tagModel 𝒢.allPrimes) (tagStart y)
          ((sk.xs₀, sk.xb₀) : Lists 𝒢 J ℓ) then (stateMass 𝒢 J ℓ : ℂ) else 0) *
        (sk.walkW y * expUnit (θ * (sk.off D.n : ℝ))) = 0 := by
      rw [← mul_assoc, sk.start_mul_walkW_eq_zero y hE, zero_mul]
    rw [hpv, mul_zero, mul_zero]
    exact (hmain.symm.trans h0).symm

open _root_.Classical in
/-- **The path expansion at one residue vector** [S-02:0212–0234]: for `N = 2R` and `q > 0`,
`⟨u_{(0,y)}, (𝒜 𝒜*)^R φ_θ⟩ = Σ_sk common(θ, y_𝒮, sk) · bigPhysAt(sk, y_ℬ)`. -/
theorem phSkel_pairUnit_eq (D : MemData 𝒢 J ℓ N) {R : ℕ} (hN : D.n = 2 * R) (hq : 0 < D.q)
    (θ : ℝ) (y : ResVec 𝒢.allPrimes) :
    pairUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y)
        (((physOp (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ *
          physAdj (tagModel 𝒢.allPrimes) 𝒢 D.q D.fam D.k D.ζ) ^ R) (phaseVec 𝒢 θ)) =
      ∑ sk : Skel D, sk.common θ (resS 𝒢 y) * ((sk.bigPhysAt (resB 𝒢 y) : ℝ) : ℂ) := by
  rw [pairUnit_pow_eq_sum_walks]
  refine (Finset.sum_congr rfl fun x _ => phSkel_ite_mul_sum _ _).trans ?_
  refine (Skel.sum_rounds D hN _).trans ?_
  exact Finset.sum_congr rfl fun sk _ => sk.phaseTerm_eq hN hq θ y

/-! ### The statement -/

/-- **(A) The physical path expansion by skeletons** [S-02:0212–0234, 0293–0314]: for `N = 2R`,
`q > 0` and disjoint sets of small and big primes,
`phaseSum θ = E_y Σ_sk common(θ, y, sk) · bigPhys(sk)`. -/
theorem phaseSkeleton : PhaseSkeleton := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D R θ hN hq hdisj
  have hS := smallPrimes_subset_all 𝒢
  have hB := bigPrimes_subset_all 𝒢
  have hcov := allPrimes_cover 𝒢
  have hfin : ∀ (cS cB T : ℂ), cB ≠ 0 → (cS * cB)⁻¹ * (cB * T) = cS⁻¹ * T := by
    intro cS cB T h
    rw [mul_inv, mul_assoc, inv_mul_cancel_left₀ h]
  -- the number of residue vectors
  have hcardB : ((Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ) : ℂ) ≠ 0 := by
    have h : (Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact Complex.ofReal_ne_zero.mpr h
  have hcard : ((Fintype.card (ResVec 𝒢.allPrimes) : ℝ) : ℂ) =
      ((Fintype.card (ResVec (smallPrimes 𝒢)) : ℝ) : ℂ) *
        ((Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ) : ℂ) := by
    rw [resSplit_card hS hB hcov hdisj, Nat.cast_mul, Complex.ofReal_mul]
  -- the residue vector is the pair of its small and its big part
  have hsum : ∑ y : ResVec 𝒢.allPrimes, ∑ sk : Skel D,
        sk.common θ (resS 𝒢 y) * ((sk.bigPhysAt (resB 𝒢 y) : ℝ) : ℂ) =
      ∑ a : ResVec (smallPrimes 𝒢), ∑ b : ResVec (bigPrimes 𝒢), ∑ sk : Skel D,
        sk.common θ a * ((sk.bigPhysAt b : ℝ) : ℂ) :=
    resSplit_sum hS hB hcov hdisj
      (fun a b => ∑ sk : Skel D, sk.common θ a * ((sk.bigPhysAt b : ℝ) : ℂ))
  -- the mean over the big residues
  have hinner : ∀ a : ResVec (smallPrimes 𝒢),
      ∑ b : ResVec (bigPrimes 𝒢), ∑ sk : Skel D,
          sk.common θ a * ((sk.bigPhysAt b : ℝ) : ℂ) =
        ((Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ) : ℂ) *
          ∑ sk : Skel D, sk.common θ a * ((sk.bigPhys : ℝ) : ℂ) := by
    intro a
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun sk _ => ?_
    have hb : ((sk.bigPhys : ℝ) : ℂ) =
        ((Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ) : ℂ)⁻¹ *
          ∑ b : ResVec (bigPrimes 𝒢), ((sk.bigPhysAt b : ℝ) : ℂ) := by
      unfold Skel.bigPhys
      rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum]
    rw [hb, ← Finset.mul_sum, mul_left_comm, mul_inv_cancel_left₀ hcardB]
  calc phaseSum 𝒢 D.q D.fam D.k D.ζ R θ
      = ((Fintype.card (ResVec 𝒢.allPrimes) : ℝ) : ℂ)⁻¹ *
          ∑ y : ResVec 𝒢.allPrimes, ∑ sk : Skel D,
            sk.common θ (resS 𝒢 y) * ((sk.bigPhysAt (resB 𝒢 y) : ℝ) : ℂ) :=
        congrArg (fun t => ((Fintype.card (ResVec 𝒢.allPrimes) : ℝ) : ℂ)⁻¹ * t)
          (Finset.sum_congr rfl fun y _ => phSkel_pairUnit_eq D hN hq θ y)
    _ = (((Fintype.card (ResVec (smallPrimes 𝒢)) : ℝ) : ℂ) *
            ((Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ) : ℂ))⁻¹ *
          (((Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ) : ℂ) *
            ∑ a : ResVec (smallPrimes 𝒢), ∑ sk : Skel D,
              sk.common θ a * ((sk.bigPhys : ℝ) : ℂ)) := by
        rw [hsum, Finset.sum_congr rfl fun a _ => hinner a, ← Finset.mul_sum, hcard]
    _ = ((Fintype.card (ResVec (smallPrimes 𝒢)) : ℝ) : ℂ)⁻¹ *
          ∑ y : ResVec (smallPrimes 𝒢), ∑ sk : Skel D,
            sk.common θ y * ((sk.bigPhys : ℝ) : ℂ) := hfin _ _ _ hcardB

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
