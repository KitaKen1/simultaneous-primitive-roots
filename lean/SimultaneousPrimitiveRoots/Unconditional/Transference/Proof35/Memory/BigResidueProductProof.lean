module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.BigDampingFactor
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.HistorySkeleton
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The big residue expectation is a product over the big primes: `BigResidueProduct`

Source: `verification/stage7-sources/S-02.tex`, lines 226–234 and 327–334
(`[S-02:0226–0234, 0327–0334]`), (eq:path-residue-factor).

`bigResidueProduct : BigResidueProduct` (part (C1) of the proof of [S] Lemma 3.7) is proved here:
for `N ≥ 1`, `q > 0`, pairwise disjoint big groups of positive integers and every skeleton,

`bigPhys = (label normalization) · 1_{big lists injective at all visits} · ∏_{p big} onePrimeExp p`.

## The proof

* **Visits.** `Skel.visitA y i` is the factor of the visit `i`: the indicator that the big list of
  the skeleton at the visit `i` is a big state at `y + h_i`, times the big endpoint damping there.
  The factor of an edge in `Skel.bigPhysAt` is `∏_g V_g^{-t_g} · A_i · A_{i+1}`
  (`IsBigState` is invariant under the slot permutations, `isBigState_permuteSlots`), and the
  initial indicator is absorbed by `A_0` because `N ≥ 1` (`Skel.bigPhysAt_eq_visitA`). So every
  visit `0 < i < N` contributes `A_i²` and the visits `0`, `N` contribute `A_0`, `A_N`
  (`bigRes_prod_adjacent`): this is "`q_0 = q_N = √q` and `q_i = q` for `0 < i < N`".
* **Primes.** For pairwise disjoint big groups, `A_i` is the indicator that the lists at the visit
  `i` are injective times the product over the big primes `p` of `Skel.halfF p i (y_p)`:
  `1_{y_p + h_i = 0}` if `p` is active at `i` and `(√q)^{1_{y_p + h_i = 0}}` otherwise
  (`Skel.visitA_eq`, from `bigRes_state_damping`). The product of the two half factors of a visit
  is the factor of `Skel.onePrimeExp` (`Skel.fullF_eq`). Hence `Skel.bigPhysAt y` is the label
  normalization times the indicator of `Skel.BigInj` times a product over the big primes of
  functions of the single residues `y_p` (`Skel.bigPhysAt_eq`).
* **Independence.** The mean over `y` of such a product is the product of the one-prime means
  (`bigRes_resAvg_prod`), which are the `Skel.onePrimeExp p`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {D : MemData 𝒢 J ℓ N}

/-! ### The factors of one prime -/

/-- **The half factor of the prime `p` at the visit `i`**, for the residue `t` at the visit `0`:
`1_{t + h_i = 0}` if `p` is active at the visit `i`, and `(√q)^{1_{t + h_i = 0}}` otherwise. An
interior visit contributes two half factors (one for each of its edges), the visits `0` and `N`
one. -/
def Skel.halfF (sk : Skel D) (p i : ℕ) (t : Res p) : ℝ :=
  if i ∈ sk.activeVisits p then
    (if t + ((sk.off i : ℤ) : Res p) = 0 then (1 : ℝ) else 0)
  else (if t + ((sk.off i : ℤ) : Res p) = 0 then Real.sqrt D.q else 1)

/-- **The product over the visits of the factors of the prime `p`**, for the residue `t`: the
function whose mean over `t` is `Skel.onePrimeExp p`. -/
def Skel.primeProd (sk : Skel D) (p : ℕ) (t : Res p) : ℝ :=
  ∏ i ∈ Finset.range (D.n + 1),
    if i ∈ sk.activeVisits p then
      (if t + ((sk.off i : ℤ) : Res p) = 0 then (1 : ℝ) else 0)
    else (if t + ((sk.off i : ℤ) : Res p) = 0 then visitQ D.q D.n i else 1)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **The factor of a visit is the product of its half factors**: for `N ≥ 1` the visit `i ≤ N`
has a half factor for the edge `i` (if `i < N`) and one for the edge `i - 1` (if `0 < i`); their
product is `1_{t + h_i = 0}` if `p` is active and `q_i^{1_{t + h_i = 0}}` otherwise, with
`q_0 = q_N = √q` and `q_i = q` for `0 < i < N` [S-02:0223–0224]. -/
theorem Skel.fullF_eq (sk : Skel D) (hn : 1 ≤ D.n) (hq : 0 < D.q) (p i : ℕ) (hi : i ≤ D.n)
    (t : Res p) :
    (if i ∈ sk.activeVisits p then
        (if t + ((sk.off i : ℤ) : Res p) = 0 then (1 : ℝ) else 0)
      else (if t + ((sk.off i : ℤ) : Res p) = 0 then visitQ D.q D.n i else 1)) =
      (if i < D.n then sk.halfF p i t else 1) * (if 0 < i then sk.halfF p i t else 1) := by
  have hsq : Real.sqrt D.q * Real.sqrt D.q = D.q := Real.mul_self_sqrt hq.le
  by_cases h0 : 0 < i
  · by_cases hN : i < D.n
    · have hv : visitQ D.q D.n i = D.q := by
        unfold visitQ
        exact if_neg (by omega)
      rw [if_pos hN, if_pos h0, hv]
      unfold Skel.halfF
      rw [bigRes_phi_mul, hsq]
    · have hv : visitQ D.q D.n i = Real.sqrt D.q := by
        unfold visitQ
        exact if_pos (Or.inr (by omega))
      rw [if_neg hN, if_pos h0, hv]
      exact (one_mul _).symm
  · have hN : i < D.n := by omega
    have hv : visitQ D.q D.n i = Real.sqrt D.q := by
      unfold visitQ
      exact if_pos (Or.inl (by omega))
    rw [if_pos hN, if_neg h0, hv]
    exact (mul_one _).symm

/-! ### The factor of a visit -/

open _root_.Classical in
/-- **The factor of the visit `j`** in the big part of the physical weight, for the big residues
`y` at the visit `0`: the big endpoint damping at `y + h_j` if the big list of the skeleton at the
visit `j` is a big state there, and zero otherwise. -/
def Skel.visitA (sk : Skel D) (y : ResVec (bigPrimes 𝒢)) (j : ℕ) : ℝ :=
  if IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off j) y) (sk.lists j).2 then
    bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off j) y)
  else 0

omit [DecidableEq S] [Fintype N] in
open _root_.Classical in
/-- **The factor of a visit is a product over the big primes** [S-02:0226–0231]: for pairwise
disjoint big groups, `A_j = 1_{lists injective at j} · ∏_{p big} halfF p j (y_p)`. -/
theorem Skel.visitA_eq (sk : Skel D) (hq : 0 < D.q)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (y : ResVec (bigPrimes 𝒢))
    (j : ℕ) (hj : j ≤ D.n) :
    sk.visitA y j =
      (if ∀ g, Function.Injective ((sk.lists j).2 g) then (1 : ℝ) else 0) *
        ∏ p : {p : ℕ // p ∈ bigPrimes 𝒢}, sk.halfF p.1 j (y p) := by
  have hact : ∀ p : ℕ, (∃ g sl, ((sk.lists j).2 g sl : ℕ) = p) ↔ j ∈ sk.activeVisits p := by
    intro p
    unfold Skel.activeVisits
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨Nat.lt_succ_of_le hj, h⟩, fun h => h.2⟩
  refine (bigRes_state_damping hq hdisj ((resModel (bigPrimes 𝒢)).shift (sk.off j) y)
    (sk.lists j).2).trans ?_
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun p _ => ?_)
  unfold Skel.halfF
  exact bigRes_ite_congr (hact p.1) rfl rfl

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
open _root_.Classical in
/-- **The big part of the physical weight as a product over the visits**: for `N ≥ 1`,
`bigPhysAt y = (label normalization) · ∏_{i ≤ N} A_i^{[i < N]} A_i^{[0 < i]}`. -/
theorem Skel.bigPhysAt_eq_visitA (sk : Skel D) (hn : 1 ≤ D.n) (y : ResVec (bigPrimes 𝒢)) :
    sk.bigPhysAt y = sk.bigNormAll *
      ∏ i ∈ Finset.range (D.n + 1),
        ((if i < D.n then sk.visitA y i else 1) * (if 0 < i then sk.visitA y i else 1)) := by
  have hvA : ∀ j : ℕ, sk.visitA y j =
      if IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off j) y) (sk.lists j).2 then
        bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off j) y)
      else 0 := fun j => rfl
  have h1 : ∀ i : Fin D.n,
      (IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) y) (sk.src i).2 ↔
        IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) y) (sk.lists i.val).2) :=
    fun i => isBigState_permuteSlots (sk.edge i).1.2 _ (sk.lists i.val).2
  have h2 : ∀ i : Fin D.n,
      (IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) y) (sk.tgt i).2 ↔
        IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) y)
          (sk.lists (i.val + 1)).2) := by
    intro i
    rw [sk.lists_succ i.val i.isLt]
    exact (isBigState_permuteSlots (sk.edge i).2.2.2 _ (sk.tgt i).2).symm
  have hA0 : ¬IsBigState 𝒢 y sk.xb₀ → sk.visitA y 0 = 0 := by
    intro h
    rw [hvA, sk.off_zero, memId_shift_zero]
    exact if_neg h
  have hedges : (∏ i : Fin D.n,
        if IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) y) (sk.src i).2 ∧
            IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) y)
              (sk.tgt i).2 then
          bigTargetNorm 𝒢 ℓ (sk.Cset i) *
            (bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) y) *
              bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) y))
        else 0) =
      (∏ i : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset i)) *
        ∏ i ∈ Finset.range (D.n + 1),
          ((if i < D.n then sk.visitA y i else 1) * (if 0 < i then sk.visitA y i else 1)) := by
    calc (∏ i : Fin D.n,
          if IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) y) (sk.src i).2 ∧
              IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) y)
                (sk.tgt i).2 then
            bigTargetNorm 𝒢 ℓ (sk.Cset i) *
              (bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) y) *
                bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) y))
          else 0)
        = ∏ i : Fin D.n, (bigTargetNorm 𝒢 ℓ (sk.Cset i) *
            (sk.visitA y i.val * sk.visitA y (i.val + 1))) :=
          Finset.prod_congr rfl fun i _ => by
            rw [hvA, hvA]
            exact bigRes_ite_and (h1 i) (h2 i) _ _ _
      _ = (∏ i : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset i)) *
            ∏ i : Fin D.n, (sk.visitA y i.val * sk.visitA y (i.val + 1)) :=
          Finset.prod_mul_distrib
      _ = (∏ i : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset i)) *
            ∏ i ∈ Finset.range D.n, (sk.visitA y i * sk.visitA y (i + 1)) :=
          congrArg (fun t => (∏ i : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset i)) * t)
            (Fin.prod_univ_eq_prod_range (fun j => sk.visitA y j * sk.visitA y (j + 1)) D.n)
      _ = (∏ i : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset i)) *
            ∏ i ∈ Finset.range (D.n + 1),
              ((if i < D.n then sk.visitA y i else 1) *
                (if 0 < i then sk.visitA y i else 1)) :=
          congrArg (fun t => (∏ i : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset i)) * t)
            (bigRes_prod_adjacent (sk.visitA y) D.n)
  have hstart : sk.bigPhysAt y =
      (if IsBigState 𝒢 y sk.xb₀ then bigListNorm 𝒢 J ℓ else 0) *
        ((∏ i : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset i)) *
          ∏ i ∈ Finset.range (D.n + 1),
            ((if i < D.n then sk.visitA y i else 1) *
              (if 0 < i then sk.visitA y i else 1))) :=
    congrArg (fun t => (if IsBigState 𝒢 y sk.xb₀ then bigListNorm 𝒢 J ℓ else 0) * t) hedges
  rw [hstart]
  unfold Skel.bigNormAll
  by_cases h0 : IsBigState 𝒢 y sk.xb₀
  · rw [if_pos h0]
    exact (mul_assoc _ _ _).symm
  · have hX : ∏ i ∈ Finset.range (D.n + 1),
          ((if i < D.n then sk.visitA y i else 1) * (if 0 < i then sk.visitA y i else 1)) =
        0 := by
      refine Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos D.n)) ?_
      rw [if_pos (show 0 < D.n from hn), hA0 h0, zero_mul]
    rw [if_neg h0, hX, zero_mul, mul_zero]

omit [DecidableEq S] [Fintype N] in
open _root_.Classical in
/-- **The big part of the physical weight as a product over the big primes** [S-02:0226–0234]:
for `N ≥ 1`, `q > 0` and pairwise disjoint big groups, `bigPhysAt y` is the label normalization
times the indicator that the big lists are injective at all visits times the product over the big
primes `p` of `primeProd p (y_p)`. -/
theorem Skel.bigPhysAt_eq (sk : Skel D) (hn : 1 ≤ D.n) (hq : 0 < D.q)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (y : ResVec (bigPrimes 𝒢)) :
    sk.bigPhysAt y = sk.bigNormAll * (if sk.BigInj then 1 else 0) *
      ∏ p : {p : ℕ // p ∈ bigPrimes 𝒢}, sk.primeProd p.1 (y p) := by
  rw [sk.bigPhysAt_eq_visitA hn y, mul_assoc sk.bigNormAll]
  refine congrArg (fun t => sk.bigNormAll * t) ?_
  by_cases hinj : sk.BigInj
  · rw [if_pos hinj, one_mul]
    unfold Skel.primeProd
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i ≤ D.n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hA : sk.visitA y i = ∏ p : {p : ℕ // p ∈ bigPrimes 𝒢}, sk.halfF p.1 i (y p) := by
      rw [sk.visitA_eq hq hdisj y i hi', if_pos (hinj i hi'), one_mul]
    rw [hA, bigRes_ite_prod, bigRes_ite_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => (sk.fullF_eq hn hq p.1 i hi' (y p)).symm
  · rw [if_neg hinj, zero_mul]
    obtain ⟨i, hi, g, hg⟩ : ∃ i, i ≤ D.n ∧ ∃ g, ¬Function.Injective ((sk.lists i).2 g) := by
      by_contra hcon
      exact hinj fun i hi g => not_not.mp fun h => hcon ⟨i, hi, g, h⟩
    have hA : sk.visitA y i = 0 := by
      unfold Skel.visitA
      exact if_neg fun h => hg (h.1 g)
    refine Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)) ?_
    by_cases hlt : i < D.n
    · rw [if_pos hlt, hA, zero_mul]
    · have hpos : 0 < i := by omega
      rw [if_pos hpos, hA, mul_zero]

/-! ### The expectation -/

open _root_.Classical in
/-- **(C1) The big residue expectation is a product over the big primes**
[S-02:0226–0234, 0327–0334]: for `N ≥ 1`, `q > 0`, pairwise disjoint big groups of positive
integers and every skeleton,
`bigPhys = (label normalization) · 1_{big lists injective at all visits} · ∏_{p big} onePrimeExp p`.
-/
theorem bigResidueProduct : BigResidueProduct := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D sk hn hq hdisj hpos
  have hsum : ∑ y : ResVec (bigPrimes 𝒢), sk.bigPhysAt y =
      sk.bigNormAll * (if sk.BigInj then 1 else 0) *
        ∑ y : ResVec (bigPrimes 𝒢),
          ∏ p : {p : ℕ // p ∈ bigPrimes 𝒢}, sk.primeProd p.1 (y p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => sk.bigPhysAt_eq hn hq hdisj y
  have hprod : ∏ p : {p : ℕ // p ∈ bigPrimes 𝒢},
        ((p.1 : ℝ)⁻¹ * ∑ t : Res p.1, sk.primeProd p.1 t) =
      ∏ p ∈ bigPrimes 𝒢, sk.onePrimeExp p :=
    (Finset.prod_subtype (bigPrimes 𝒢) (fun _ => Iff.rfl) (fun p => sk.onePrimeExp p)).symm
  calc sk.bigPhys
      = (Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ)⁻¹ *
          (sk.bigNormAll * (if sk.BigInj then 1 else 0) *
            ∑ y : ResVec (bigPrimes 𝒢),
              ∏ p : {p : ℕ // p ∈ bigPrimes 𝒢}, sk.primeProd p.1 (y p)) :=
        congrArg (fun t => (Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ)⁻¹ * t) hsum
    _ = sk.bigNormAll * (if sk.BigInj then 1 else 0) *
          ((Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ)⁻¹ *
            ∑ y : ResVec (bigPrimes 𝒢),
              ∏ p : {p : ℕ // p ∈ bigPrimes 𝒢}, sk.primeProd p.1 (y p)) :=
        mul_left_comm _ _ _
    _ = sk.bigNormAll * (if sk.BigInj then 1 else 0) *
          ∏ p ∈ bigPrimes 𝒢, sk.onePrimeExp p :=
        congrArg (fun t => sk.bigNormAll * (if sk.BigInj then 1 else 0) * t)
          ((bigRes_resAvg_prod (bigPrimes 𝒢) hpos (fun p t => sk.primeProd p.1 t)).trans hprod)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
