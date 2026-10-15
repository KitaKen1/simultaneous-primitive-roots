module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.ChainSkel
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.OnePrime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The closed forms of the transfer chain of one big prime

Source: `verification/stage7-sources/S-02.tex`, lines 538–567 (`[S-02:0538–0567]`).

"The `ρ` factors cancel locally. At an internal visit a continuing pending zero pays
`ρ (q_i/ρ²) ρ = q_i`. A ghost birth pays `(-η_i/ρ) ρ = -η_i`, and a ghost termination pays
`ρ (-η_i/ρ) = -η_i`. … a first active birth costs `1/(V_g p b_p)` and each of its `r - 1` later
promotions costs `1/V_g`. A first ghost birth costs `1/(p b_p)` and its `r` promotions cost
`V_g^{-r}`."

For a skeleton with `BigValid`, under `RawHyp`, and a big prime `p` of the group `g`, the values
`Skel.chain (N - i)` at the visit `i` (before `G_i`) which are *consistent with the skeleton* have
closed forms (`Skel.ChainInv`, proved by backward induction in `Skel.chainInv_chain`). With
`f_t(y) = 1_{y + h_t = 0}` if `p` is active at the visit `t` and `q_t^{1_{y + h_t = 0}}` otherwise
(`Skel.resF`), `F_i(y) = ∏_{t ≥ i} f_t(y)` (`Skel.tailF`), `Z_i` the product of the weights of the
edges `t ≥ i` (`Skel.zTail`: `1` without entry, `V_g⁻¹` for one entry of a prime which is not a
shared source label, `0` otherwise) and `ν_i = 1` iff `p` is not active at any visit `≥ i`
(`Skel.nv`):

* `p` active at the visit `i`:      `act = Z_i ∑_y F_i(y)`;
* `p` not active at the visit `i`:  `pend(r) = ρ^{-1_{r = 0}} (Z_i F_i(r - h_i) - ν_i)`,
  `dead = ν_i`, `unborn = (Z_i ∑_y F_i(y) - ν_i ∑_{j < i} η_j) / (p b_p)`.

The other values (for instance `unborn` for a prime which is active at the visit `i`) have no
such form, and are not used by the consistent ones. At the visit `0`: `Skel.chain_act_zero`,
`Skel.chain_unborn_zero`, with `∑_y F_0(y) = p b_p · lifeSum p` (`onePrimeLifespan`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type}
  {D : MemData 𝒢 J ℓ N}

/-! ### The weights of the edges -/

open _root_.Classical in
/-- **The weight of the edge `i` for the prime `p`**: `1` if no unshared target slot has the label
`p`; `V_g⁻¹` if exactly one has, and `p` is not a shared source label (an entry: a promotion or a
fresh birth); `0` otherwise (the target list would not be injective). `1` for `i ≥ N`. -/
def Skel.zW (sk : Skel D) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (i : ℕ) : ℝ :=
  if h : i < D.n then
    (if sk.entryCount ⟨i, h⟩ g p = 0 then 1
      else if sk.entryCount ⟨i, h⟩ g p = 1 ∧
          ¬∃ j : Fin J, j ∉ sk.Cset ⟨i, h⟩ g ∧ (sk.src ⟨i, h⟩).2 g (Sum.inl j) = p then
        (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹
      else 0)
  else 1

omit [Fintype S] [Fintype B] in
theorem Skel.zW_zero (sk : Skel D) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (e : Fin D.n)
    (he : sk.entryCount e g p = 0) : sk.zW g p e.val = 1 :=
  (dif_pos e.isLt).trans (if_pos he)

omit [Fintype S] [Fintype B] in
theorem Skel.zW_one (sk : Skel D) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (e : Fin D.n)
    (he : sk.entryCount e g p = 1)
    (hS : ¬∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p) :
    sk.zW g p e.val = (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹ := by
  have hne : sk.entryCount e g p ≠ 0 := by
    rw [he]
    exact one_ne_zero
  have hc : sk.entryCount e g p = 1 ∧
      ¬∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p := ⟨he, hS⟩
  exact (dif_pos e.isLt).trans ((if_neg hne).trans (if_pos hc))

omit [Fintype S] [Fintype B] in
theorem Skel.zW_bad (sk : Skel D) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (e : Fin D.n)
    (he : sk.entryCount e g p ≠ 0)
    (h : ¬(sk.entryCount e g p = 1 ∧
      ¬∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p)) :
    sk.zW g p e.val = 0 :=
  (dif_pos e.isLt).trans ((if_neg he).trans (if_neg h))

/-- The product of the weights of the edges `i, …, N - 1`. -/
def Skel.zTail (sk : Skel D) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (i : ℕ) : ℝ :=
  ∏ t ∈ Finset.Ico i D.n, sk.zW g p t

omit [Fintype S] [Fintype B] in
theorem Skel.zTail_succ (sk : Skel D) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (e : Fin D.n) :
    sk.zTail g p e.val = sk.zW g p e.val * sk.zTail g p (e.val + 1) := by
  unfold Skel.zTail
  exact Finset.prod_eq_prod_Ico_succ_bot e.isLt _

omit [Fintype S] [Fintype B] in
theorem Skel.zTail_last (sk : Skel D) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    sk.zTail g p D.n = 1 := by
  unfold Skel.zTail
  rw [Finset.Ico_self, Finset.prod_empty]

/-! ### The closed forms -/

/-- **The closed forms of the values of the prime `p` at the visit `i`** (before `G_i`), for the
values which are consistent with the skeleton. -/
structure Skel.ChainInv (sk : Skel D) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (i : ℕ)
    (v : PrimeVals 𝒢) : Prop where
  /-- active at the visit `i` -/
  act : i ∈ sk.activeVisits p →
    v.act g p = sk.zTail g p i * ∑ t : Res p.1, sk.tailF p i t
  /-- pending at the visit `i`, with the residue `r` -/
  pend : i ∉ sk.activeVisits p → ∀ r : Res p.1, v.pend g ⟨p, r⟩ =
    (chnPow D.ρ (r = 0))⁻¹ *
      (sk.zTail g p i * sk.tailF p i (r - ((sk.off i : ℤ) : Res p.1)) - sk.nv p i)
  /-- born earlier and no longer present at the visit `i` -/
  dead : i ∉ sk.activeVisits p → v.dead g p = sk.nv p i
  /-- not born at the visit `i` -/
  unborn : i ∉ sk.activeVisits p → v.unborn g p =
    (sk.zTail g p i * (∑ t : Res p.1, sk.tailF p i t) - sk.nv p i * chnEta D i) /
      (((p : ℕ) : ℝ) * lifeBaseline D.q D.n p)

/-! ### One step: an active prime -/

/-- An active prime in a shared source slot. -/
theorem Skel.chainInv_act_shared (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (hv : sk.ChainInv g p (e.val + 1) v)
    (hS : ∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p)
    (hA : e.val ∈ sk.activeVisits p) (hA' : e.val + 1 ∈ sk.activeVisits p)
    (hδ : ((sk.step e : ℤ) : Res p.1) = 0) :
    (ghostStepVals D e.val (sk.edgeStepVals e v)).act g p =
      sk.zTail g p e.val * ∑ t : Res p.1, sk.tailF p e.val t := by
  have hoff := sk.off_succ_res e p.1
  rw [ghostStepVals_act, sk.zTail_succ g p e,
    sk.sum_tailF_act p e.val (Nat.le_of_lt e.isLt) hA]
  by_cases he : sk.entryCount e g p = 0
  · rw [sk.edgeStepVals_act_shared e v g p hS he, hv.act hA', sk.zW_zero g p e he, one_mul,
      sk.sum_tailF_act p (e.val + 1) (Nat.succ_le_of_lt e.isLt) hA',
      sk.tailF_act p (e.val + 1) (Nat.succ_le_of_lt e.isLt) hA'
        (-((sk.off e.val : ℤ) : Res p.1)),
      hoff, hδ, add_zero, if_pos (neg_add_cancel _)]
  · rw [sk.edgeStepVals_act_shared_ne e v g p hS he,
      sk.zW_bad g p e he (fun h => h.2 hS), zero_mul, zero_mul]

/-- An active prime which is not in a shared source slot: it is stored or dropped. -/
theorem Skel.chainInv_act_unshared (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (hv : sk.ChainInv g p (e.val + 1) v)
    (hS : ¬∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p)
    (hA : e.val ∈ sk.activeVisits p)
    (hA' : e.val + 1 ∈ sk.activeVisits p ↔ sk.entryCount e g p ≠ 0)
    (hδ : ((sk.step e : ℤ) : Res p.1) ≠ 0) (hdv : ¬((p : ℕ) ∣ sk.dilAt e)) :
    (ghostStepVals D e.val (sk.edgeStepVals e v)).act g p =
      sk.zTail g p e.val * ∑ t : Res p.1, sk.tailF p e.val t := by
  have hoff := sk.off_succ_res e p.1
  rw [ghostStepVals_act, sk.zTail_succ g p e,
    sk.sum_tailF_act p e.val (Nat.le_of_lt e.isLt) hA]
  by_cases he : sk.entryCount e g p = 0
  · have hnA' : e.val + 1 ∉ sk.activeVisits p := fun h => hA'.mp h he
    have harg : ((sk.step e : ℤ) : Res p.1) -
        (((sk.off e.val : ℤ) : Res p.1) + ((sk.step e : ℤ) : Res p.1)) =
          -((sk.off e.val : ℤ) : Res p.1) := by ring
    rw [sk.edgeStepVals_act_unshared e v g p hS he hdv hδ, hv.pend hnA', hv.dead hnA',
      chnPow_neg hδ, inv_one, one_mul, sub_add_cancel, sk.zW_zero g p e he, one_mul, hoff, harg]
  · have hA1 : e.val + 1 ∈ sk.activeVisits p := hA'.mpr he
    have hne : ¬(-((sk.off e.val : ℤ) : Res p.1) +
        (((sk.off e.val : ℤ) : Res p.1) + ((sk.step e : ℤ) : Res p.1)) = 0) := by
      rw [neg_add_cancel_left]
      exact hδ
    rw [sk.edgeStepVals_act_unshared_ne e v g p hS he,
      sk.tailF_act p (e.val + 1) (Nat.succ_le_of_lt e.isLt) hA1
        (-((sk.off e.val : ℤ) : Res p.1)), hoff, if_neg hne, mul_zero]

/-! ### One step: a prime without entry which is not active -/

/-- A pending particle of a prime without entry, after the edge. -/
theorem Skel.edge_pend_keep (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (hv : sk.ChainInv g p (e.val + 1) v)
    (he : sk.entryCount e g p = 0) (hnA' : e.val + 1 ∉ sk.activeVisits p) (hρ : D.ρ ≠ 0)
    (r : Res p.1) :
    (sk.edgeStepVals e v).pend g ⟨p, r⟩ =
      chnPow D.ρ (r = 0) *
        (sk.zTail g p (e.val + 1) *
          sk.tailF p (e.val + 1) (r - ((sk.off e.val : ℤ) : Res p.1)) -
            sk.nv p (e.val + 1)) := by
  have hoff := sk.off_succ_res e p.1
  have harg : ((sk.step e : ℤ) : Res p.1) + r -
      (((sk.off e.val : ℤ) : Res p.1) + ((sk.step e : ℤ) : Res p.1)) =
        r - ((sk.off e.val : ℤ) : Res p.1) := by ring
  rw [sk.edgeStepVals_pend_zero e v g p r he, hv.pend hnA',
    mul_inv_cancel_left₀ (chnPow_ne_zero hρ _), hoff, harg]

theorem Skel.chainInv_inact_zero_pend (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (hv : sk.ChainInv g p (e.val + 1) v)
    (he : sk.entryCount e g p = 0) (hnA : e.val ∉ sk.activeVisits p)
    (hnA' : e.val + 1 ∉ sk.activeVisits p) (hρ : D.ρ ≠ 0) (r : Res p.1) :
    (ghostStepVals D e.val (sk.edgeStepVals e v)).pend g ⟨p, r⟩ =
      (chnPow D.ρ (r = 0))⁻¹ *
        (sk.zTail g p e.val * sk.tailF p e.val (r - ((sk.off e.val : ℤ) : Res p.1)) -
          sk.nv p e.val) := by
  have hkeep := sk.edge_pend_keep e g p v hv he hnA' hρ
  rw [sk.zTail_succ g p e, sk.zW_zero g p e he, one_mul, sk.nv_succ p e.val hnA,
    sk.tailF_inact p e.val (Nat.le_of_lt e.isLt) hnA]
  by_cases hr : r = 0
  · have hc : r - ((sk.off e.val : ℤ) : Res p.1) + ((sk.off e.val : ℤ) : Res p.1) = 0 := by
      rw [sub_add_cancel]
      exact hr
    rw [ghostStepVals_pend_of_eq D e.val _ g p r hr, hkeep,
      sk.edgeStepVals_dead_zero e v g p he, hv.dead hnA', chnPow_pos hr, if_pos hc]
    exact chn_alg_pend_zero hρ
  · have hc : ¬(r - ((sk.off e.val : ℤ) : Res p.1) + ((sk.off e.val : ℤ) : Res p.1) = 0) := by
      rw [sub_add_cancel]
      exact hr
    rw [ghostStepVals_pend_ne D e.val _ g p r hr, hkeep, chnPow_neg hr, inv_one,
      if_neg hc]
    simp only [one_mul]

theorem Skel.chainInv_inact_zero_dead (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (hv : sk.ChainInv g p (e.val + 1) v)
    (he : sk.entryCount e g p = 0) (hnA : e.val ∉ sk.activeVisits p)
    (hnA' : e.val + 1 ∉ sk.activeVisits p) :
    (ghostStepVals D e.val (sk.edgeStepVals e v)).dead g p = sk.nv p e.val := by
  rw [ghostStepVals_dead, sk.edgeStepVals_dead_zero e v g p he, hv.dead hnA',
    sk.nv_succ p e.val hnA]

theorem Skel.chainInv_inact_zero_unborn (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (hv : sk.ChainInv g p (e.val + 1) v)
    (he : sk.entryCount e g p = 0) (hnA : e.val ∉ sk.activeVisits p)
    (hnA' : e.val + 1 ∉ sk.activeVisits p) (hρ : D.ρ ≠ 0)
    (hV : Graph.primeGroupReciprocalMass (𝒢.big g) ≠ 0) :
    (ghostStepVals D e.val (sk.edgeStepVals e v)).unborn g p =
      (sk.zTail g p e.val * (∑ t : Res p.1, sk.tailF p e.val t) -
        sk.nv p e.val * chnEta D e.val) / (((p : ℕ) : ℝ) * lifeBaseline D.q D.n p) := by
  rw [ghostStepVals_unborn, sk.edgeStepVals_unborn_zero e v g p he, hv.unborn hnA',
    sk.edge_pend_keep e g p v hv he hnA' hρ 0, chnPow_pos (rfl : (0 : Res p.1) = 0),
    sk.zTail_succ g p e, sk.zW_zero g p e he, one_mul, sk.nv_succ p e.val hnA,
    sk.sum_tailF_inact p e.val (Nat.le_of_lt e.isLt) hnA, chnEta_succ, zero_sub]
  exact chn_alg_unborn hρ hV rfl rfl

/-! ### One step: a prime with one entry which is not active -/

theorem Skel.chainInv_inact_one_pend (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (hv : sk.ChainInv g p (e.val + 1) v)
    (he : sk.entryCount e g p = 1)
    (hS : ¬∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p)
    (hnA : e.val ∉ sk.activeVisits p) (hA' : e.val + 1 ∈ sk.activeVisits p)
    (hδ : ((sk.step e : ℤ) : Res p.1) ≠ 0) (hdv : ¬((p : ℕ) ∣ sk.dilAt e)) (r : Res p.1) :
    (ghostStepVals D e.val (sk.edgeStepVals e v)).pend g ⟨p, r⟩ =
      (chnPow D.ρ (r = 0))⁻¹ *
        (sk.zTail g p e.val * sk.tailF p e.val (r - ((sk.off e.val : ℤ) : Res p.1)) -
          sk.nv p e.val) := by
  have hoff := sk.off_succ_res e p.1
  have hne : sk.entryCount e g p ≠ 0 := by
    rw [he]
    exact one_ne_zero
  have hiff : (r - ((sk.off e.val : ℤ) : Res p.1) +
      (((sk.off e.val : ℤ) : Res p.1) + ((sk.step e : ℤ) : Res p.1)) = 0) ↔
        ((sk.step e : ℤ) : Res p.1) + r = 0 := by
    have h : r - ((sk.off e.val : ℤ) : Res p.1) +
        (((sk.off e.val : ℤ) : Res p.1) + ((sk.step e : ℤ) : Res p.1)) =
          ((sk.step e : ℤ) : Res p.1) + r := by ring
    rw [h]
  rw [sk.nv_of_mem p e.val (e.val + 1) (Nat.le_succ _) hA', sub_zero,
    sk.tailF_inact p e.val (Nat.le_of_lt e.isLt) hnA,
    sk.tailF_act p (e.val + 1) (Nat.succ_le_of_lt e.isLt) hA', hoff]
  by_cases hr : r = 0
  · have h1 : ¬(r - ((sk.off e.val : ℤ) : Res p.1) +
        (((sk.off e.val : ℤ) : Res p.1) + ((sk.step e : ℤ) : Res p.1)) = 0) := by
      intro h
      have h' := hiff.mp h
      rw [hr, add_zero] at h'
      exact hδ h'
    have h2 : ¬(sk.entryCount e g p = 1 ∧ ((sk.step e : ℤ) : Res p.1) + r = 0 ∧
        ¬((p : ℕ) ∣ sk.dilAt e)) := fun h => h1 (hiff.mpr h.2.1)
    rw [ghostStepVals_pend_of_eq D e.val _ g p r hr, sk.edgeStepVals_dead_ne e v g p hne,
      sk.edgeStepVals_pend_none e v g p r hne h2, if_neg h1]
    simp only [mul_zero, add_zero]
  · have hc : ¬(r - ((sk.off e.val : ℤ) : Res p.1) + ((sk.off e.val : ℤ) : Res p.1) = 0) := by
      rw [sub_add_cancel]
      exact hr
    rw [ghostStepVals_pend_ne D e.val _ g p r hr, chnPow_neg hr, inv_one, if_neg hc]
    by_cases hr2 : ((sk.step e : ℤ) : Res p.1) + r = 0
    · rw [sk.edgeStepVals_pend_promo e v g p r he hr2 hdv, chnPow_neg hr, hv.act hA',
        sk.sum_tailF_act p (e.val + 1) (Nat.succ_le_of_lt e.isLt) hA', hoff,
        sk.zTail_succ g p e, sk.zW_one g p e he hS, if_pos (hiff.mpr hr2)]
      ring
    · have h2 : ¬(r - ((sk.off e.val : ℤ) : Res p.1) +
          (((sk.off e.val : ℤ) : Res p.1) + ((sk.step e : ℤ) : Res p.1)) = 0) :=
        fun h => hr2 (hiff.mp h)
      rw [sk.edgeStepVals_pend_none e v g p r hne (fun h => hr2 h.2.1), if_neg h2]
      simp only [mul_zero]

theorem Skel.chainInv_inact_one_dead (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (he : sk.entryCount e g p ≠ 0)
    (hA' : e.val + 1 ∈ sk.activeVisits p) :
    (ghostStepVals D e.val (sk.edgeStepVals e v)).dead g p = sk.nv p e.val := by
  rw [ghostStepVals_dead, sk.edgeStepVals_dead_ne e v g p he,
    sk.nv_of_mem p e.val (e.val + 1) (Nat.le_succ _) hA']

theorem Skel.chainInv_inact_one_unborn (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (hv : sk.ChainInv g p (e.val + 1) v)
    (he : sk.entryCount e g p = 1)
    (hS : ¬∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p)
    (hnA : e.val ∉ sk.activeVisits p) (hA' : e.val + 1 ∈ sk.activeVisits p)
    (hδ : ((sk.step e : ℤ) : Res p.1) ≠ 0) :
    (ghostStepVals D e.val (sk.edgeStepVals e v)).unborn g p =
      (sk.zTail g p e.val * (∑ t : Res p.1, sk.tailF p e.val t) -
        sk.nv p e.val * chnEta D e.val) / (((p : ℕ) : ℝ) * lifeBaseline D.q D.n p) := by
  have hoff := sk.off_succ_res e p.1
  have hne : sk.entryCount e g p ≠ 0 := by
    rw [he]
    exact one_ne_zero
  have h0 : ¬(sk.entryCount e g p = 1 ∧ ((sk.step e : ℤ) : Res p.1) + 0 = 0 ∧
      ¬((p : ℕ) ∣ sk.dilAt e)) := fun h => hδ ((add_zero _).symm.trans h.2.1)
  have h1 : ¬(-((sk.off e.val : ℤ) : Res p.1) +
      (((sk.off e.val : ℤ) : Res p.1) + ((sk.step e : ℤ) : Res p.1)) = 0) := by
    rw [neg_add_cancel_left]
    exact hδ
  rw [ghostStepVals_unborn, sk.edgeStepVals_unborn_one e v g p he,
    sk.edgeStepVals_pend_none e v g p 0 hne h0, hv.act hA',
    sk.zTail_succ g p e, sk.zW_one g p e he hS,
    sk.nv_of_mem p e.val (e.val + 1) (Nat.le_succ _) hA',
    sk.sum_tailF_inact p e.val (Nat.le_of_lt e.isLt) hnA,
    sk.tailF_act p (e.val + 1) (Nat.succ_le_of_lt e.isLt) hA'
      (-((sk.off e.val : ℤ) : Res p.1)), hoff, if_neg h1]
  exact chn_alg_unborn_birth rfl

/-! ### One step: a prime with several entries -/

theorem Skel.chainInv_inact_big (sk : Skel D) (e : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢) (he0 : sk.entryCount e g p ≠ 0)
    (he1 : sk.entryCount e g p ≠ 1) (hA' : e.val + 1 ∈ sk.activeVisits p) :
    (∀ r : Res p.1, (ghostStepVals D e.val (sk.edgeStepVals e v)).pend g ⟨p, r⟩ =
        (chnPow D.ρ (r = 0))⁻¹ *
          (sk.zTail g p e.val * sk.tailF p e.val (r - ((sk.off e.val : ℤ) : Res p.1)) -
            sk.nv p e.val)) ∧
      (ghostStepVals D e.val (sk.edgeStepVals e v)).dead g p = sk.nv p e.val ∧
      (ghostStepVals D e.val (sk.edgeStepVals e v)).unborn g p =
        (sk.zTail g p e.val * (∑ t : Res p.1, sk.tailF p e.val t) -
          sk.nv p e.val * chnEta D e.val) / (((p : ℕ) : ℝ) * lifeBaseline D.q D.n p) := by
  have hz : sk.zTail g p e.val = 0 := by
    rw [sk.zTail_succ g p e, sk.zW_bad g p e he0 (fun h => he1 h.1), zero_mul]
  have hn : sk.nv p e.val = 0 := sk.nv_of_mem p e.val (e.val + 1) (Nat.le_succ _) hA'
  have hpend : ∀ r : Res p.1, (sk.edgeStepVals e v).pend g ⟨p, r⟩ = 0 := fun r =>
    sk.edgeStepVals_pend_none e v g p r he0 (fun h => he1 h.1)
  refine ⟨fun r => ?_, ?_, ?_⟩
  · rw [hz, hn]
    by_cases hr : r = 0
    · rw [ghostStepVals_pend_of_eq D e.val _ g p r hr, hpend,
        sk.edgeStepVals_dead_ne e v g p he0]
      simp only [zero_mul, mul_zero, sub_zero, add_zero]
    · rw [ghostStepVals_pend_ne D e.val _ g p r hr, hpend]
      simp only [zero_mul, mul_zero, sub_zero]
  · rw [ghostStepVals_dead, sk.edgeStepVals_dead_ne e v g p he0, hn]
  · rw [ghostStepVals_unborn, sk.edgeStepVals_unborn_big e v g p he0 he1, hpend, hz, hn]
    simp only [zero_mul, mul_zero, sub_zero, zero_div, add_zero]

/-! ### The backward induction -/

/-- **One step of the backward induction**: the closed forms at the visit `i + 1` give the closed
forms at the visit `i`, after the edge operation `ℰ_i` and the visit operation `G_i`. -/
theorem Skel.chainInv_step (sk : Skel D) (hR : RawHyp D) (hVal : sk.BigValid) (e : Fin D.n)
    (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (v : PrimeVals 𝒢)
    (hv : sk.ChainInv g p (e.val + 1) v) :
    sk.ChainInv g p e.val (ghostStepVals D e.val (sk.edgeStepVals e v)) := by
  obtain ⟨hSh, hA'iff, hunsh⟩ := sk.edgeFacts hR hVal e g p
  have hρ : D.ρ ≠ 0 := hR.ρ_ne
  have hV : Graph.primeGroupReciprocalMass (𝒢.big g) ≠ 0 :=
    (Graph.prime_group_reciprocal_mass_pos (𝒢.big g) ⟨p.1, p.2⟩ (hR.prime_big g)).ne'
  have hin : e.val ∉ sk.activeVisits p →
      (∀ r : Res p.1, (ghostStepVals D e.val (sk.edgeStepVals e v)).pend g ⟨p, r⟩ =
          (chnPow D.ρ (r = 0))⁻¹ *
            (sk.zTail g p e.val * sk.tailF p e.val (r - ((sk.off e.val : ℤ) : Res p.1)) -
              sk.nv p e.val)) ∧
        (ghostStepVals D e.val (sk.edgeStepVals e v)).dead g p = sk.nv p e.val ∧
        (ghostStepVals D e.val (sk.edgeStepVals e v)).unborn g p =
          (sk.zTail g p e.val * (∑ t : Res p.1, sk.tailF p e.val t) -
            sk.nv p e.val * chnEta D e.val) / (((p : ℕ) : ℝ) * lifeBaseline D.q D.n p) := by
    intro hnA
    have hS : ¬∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p :=
      fun h => hnA (hSh h).1
    by_cases he0 : sk.entryCount e g p = 0
    · have hnA' : e.val + 1 ∉ sk.activeVisits p := fun h =>
        (hA'iff.mp h).elim hS (fun h' => h' he0)
      exact ⟨fun r => sk.chainInv_inact_zero_pend e g p v hv he0 hnA hnA' hρ r,
        sk.chainInv_inact_zero_dead e g p v hv he0 hnA hnA',
        sk.chainInv_inact_zero_unborn e g p v hv he0 hnA hnA' hρ hV⟩
    · have hA' : e.val + 1 ∈ sk.activeVisits p := hA'iff.mpr (Or.inr he0)
      have hK := hunsh hS (Or.inr he0)
      by_cases he1 : sk.entryCount e g p = 1
      · exact ⟨fun r => sk.chainInv_inact_one_pend e g p v hv he1 hS hnA hA' hK.1 hK.2 r,
          sk.chainInv_inact_one_dead e g p v he0 hA',
          sk.chainInv_inact_one_unborn e g p v hv he1 hS hnA hA' hK.1⟩
      · exact sk.chainInv_inact_big e g p v he0 he1 hA'
  refine ⟨fun hA => ?_, fun hnA => (hin hnA).1, fun hnA => (hin hnA).2.1,
    fun hnA => (hin hnA).2.2⟩
  by_cases hS : ∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p
  · exact sk.chainInv_act_shared e g p v hv hS hA (hSh hS).2.1 (hSh hS).2.2
  · have hK := hunsh hS (Or.inl hA)
    have hA' : e.val + 1 ∈ sk.activeVisits p ↔ sk.entryCount e g p ≠ 0 :=
      hA'iff.trans ⟨fun h => h.elim (fun h' => absurd h' hS) id, Or.inr⟩
    exact sk.chainInv_act_unshared e g p v hv hS hA hA' hK.1 hK.2

/-- **The last visit**: the closed forms of `G_N` applied to the final values. -/
theorem Skel.chainInv_base (sk : Skel D) (hR : RawHyp D) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) :
    sk.ChainInv g p D.n (ghostStepVals D D.n (finalVals 𝒢)) := by
  have hppos : 0 < (p : ℕ) := (hR.prime_big g p p.2).pos
  have hp : ((p : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hppos.ne'
  have hb : lifeBaseline D.q D.n p ≠ 0 := hR.baseline_ne p (mem_bigPrimes.mpr ⟨g, p.2⟩)
  refine ⟨fun hA => ?_, fun hnA r => ?_, fun hnA => ?_, fun hnA => ?_⟩
  · rw [ghostStepVals_act, finalVals_act, sk.zTail_last, one_mul,
      sk.sum_tailF_act p D.n le_rfl hA, sk.tailF_last]
  · rw [sk.zTail_last, sk.nv_last p hnA, sk.tailF_inact p D.n le_rfl hnA, sk.tailF_last]
    by_cases hr : r = 0
    · have hc : r - ((sk.off D.n : ℤ) : Res p.1) + ((sk.off D.n : ℤ) : Res p.1) = 0 := by
        rw [sub_add_cancel]
        exact hr
      rw [ghostStepVals_pend_of_eq D D.n _ g p r hr, finalVals_dead, finalVals_pend,
        chnPow_pos hr, if_pos hc]
      exact chn_alg_pend_last D.ρ (visitQ D.q D.n D.n)
    · have hc : ¬(r - ((sk.off D.n : ℤ) : Res p.1) + ((sk.off D.n : ℤ) : Res p.1) = 0) := by
        rw [sub_add_cancel]
        exact hr
      rw [ghostStepVals_pend_ne D D.n _ g p r hr, finalVals_pend, if_neg hc]
      simp only [mul_one, sub_self, mul_zero]
  · rw [ghostStepVals_dead, finalVals_dead, sk.nv_last p hnA]
  · have hsum : ∑ t : Res p.1, sk.tailF p (D.n + 1) t = ((p : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl fun t _ => sk.tailF_last p t, Finset.sum_const,
        Finset.card_univ, Res.card p hppos, nsmul_eq_mul, mul_one]
    rw [ghostStepVals_unborn, finalVals_unborn, finalVals_pend, mul_zero, add_zero,
      sk.zTail_last, sk.nv_last p hnA, sk.sum_tailF_inact p D.n le_rfl hnA, hsum,
      sk.tailF_last]
    exact (chn_alg_base hp hb (lifeBaseline_eq_chnEta D p)).symm

/-- **The closed forms of the transfer chain** at the visit `N - m`, for a skeleton with
`BigValid`, under `RawHyp`: backward induction over the visits. -/
theorem Skel.chainInv_chain (sk : Skel D) (hR : RawHyp D) (hVal : sk.BigValid) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (m : ℕ) (hm : m ≤ D.n) :
    sk.ChainInv g p (D.n - m) (sk.chain m) := by
  induction m with
  | zero =>
    rw [sk.chain_zero]
    exact sk.chainInv_base hR g p
  | succ m ih =>
    have hlt : m < D.n := hm
    have ih' := ih (Nat.le_of_lt hlt)
    have heq : D.n - m = D.n - (m + 1) + 1 := by omega
    rw [heq] at ih'
    rw [sk.chain_succ m hlt]
    exact sk.chainInv_step hR hVal ⟨D.n - (m + 1), _⟩ g p (sk.chain m) ih'

/-! ### The visit `0` -/

/-- `∑_y F_0(y) = p b_p · lifeSum p`: the exact expansion for one big prime (C2). -/
theorem Skel.sum_tailF_zero [DecidableEq S] [DecidableEq B] [Fintype N] (sk : Skel D)
    (hR : RawHyp D) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    ∑ t : Res p.1, sk.tailF p 0 t =
      ((p : ℕ) : ℝ) * (lifeBaseline D.q D.n p * sk.lifeSum p) := by
  have hppos : 0 < (p : ℕ) := (hR.prime_big g p p.2).pos
  have hp : ((p : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hppos.ne'
  have hb : lifeBaseline D.q D.n p ≠ 0 := hR.baseline_ne p (mem_bigPrimes.mpr ⟨g, p.2⟩)
  rw [← onePrimeLifespan S B 𝒢 J ℓ N D sk p hppos hb, sk.onePrimeExp_eq_tail,
    mul_inv_cancel_left₀ hp]

/-- An initial label: "a first active birth costs `1/(V_g p b_p)`". -/
theorem Skel.chain_act_zero [DecidableEq S] [DecidableEq B] [Fintype N] (sk : Skel D)
    (hR : RawHyp D) (hVal : sk.BigValid) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hA : 0 ∈ sk.activeVisits p) :
    tiltLaw (𝒢.big g) D.q D.n p * (sk.chain D.n).act g p =
      (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹ * sk.zTail g p 0 * sk.lifeSum p := by
  have hppos : 0 < (p : ℕ) := (hR.prime_big g p p.2).pos
  have hp : ((p : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hppos.ne'
  have hb : lifeBaseline D.q D.n p ≠ 0 := hR.baseline_ne p (mem_bigPrimes.mpr ⟨g, p.2⟩)
  have h := sk.chainInv_chain hR hVal g p D.n le_rfl
  rw [Nat.sub_self] at h
  rw [h.act hA, sk.sum_tailF_zero hR g p]
  exact chn_alg_final_act hp hb

/-- A prime which is not an initial label: "a first ghost birth costs `1/(p b_p)`". -/
theorem Skel.chain_unborn_zero [DecidableEq S] [DecidableEq B] [Fintype N] (sk : Skel D)
    (hR : RawHyp D) (hVal : sk.BigValid) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hnA : 0 ∉ sk.activeVisits p) :
    (sk.chain D.n).unborn g p = sk.zTail g p 0 * sk.lifeSum p := by
  have hppos : 0 < (p : ℕ) := (hR.prime_big g p p.2).pos
  have hp : ((p : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hppos.ne'
  have hb : lifeBaseline D.q D.n p ≠ 0 := hR.baseline_ne p (mem_bigPrimes.mpr ⟨g, p.2⟩)
  have h := sk.chainInv_chain hR hVal g p D.n le_rfl
  rw [Nat.sub_self] at h
  rw [h.unborn hnA, sk.sum_tailF_zero hR g p, chnEta_zero]
  exact chn_alg_final_unborn hp hb

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
