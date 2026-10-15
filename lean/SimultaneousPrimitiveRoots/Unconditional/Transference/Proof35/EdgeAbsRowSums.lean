module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsCoef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The absolute edge operation: the row majorant and its partial sums

Source: `verification/stage7-sources/S-02.tex`, lines 767–786 (`[S-02:0767–0786]`), the row half of
the proof of [S] Lemma 3.8.

"For a row, fix a pattern, free labels, permutations, and transfer-slot subsets of sizes
`a_g, b_g ≤ t_g`. If `Z'` old pending particles have zero translated residue in a group, their
ordered promotions and the remaining output damping cost at most
`(Z')_{a_g} ρ^{Z' - a_g} ≤ sup_{z ≥ a_g} (z)_{a_g} ρ^{z - a_g} < ∞`. … The Schur weight contributes
`v^{b_g - a_g}`, promotion coefficients contribute `V_g^{-a_g}`, and fresh integrations have mass
`μ̃_g(𝒫_g)^{t_g - a_g} ≤ 2^{t_g}` for large `x`. There are at most `4^{t_g}` choices of transfer
subsets. Each cost is bounded by a constant per group, independent of `J`. Small transitions
satisfy (eq:physical-count-bound)."

For a fixed pattern `ν` and fixed free labels `r` the step `Δ` is fixed, and the modulus of a
coefficient times the Schur weight of its target is at most the product of

* `edgeAbsSmallW` — the small target list (`sum_edgeAbsSmallW_le`: (eq:physical-count-bound));
* `edgeAbsStoreP` — the stores (`sum_edgeAbsStoreP_le`: at most `2^{t_g}` subsets, weight
  `v^{b_g}`);
* `edgeAbsPromoP` — the promotions: `ρ^{Z'}` and, for every unshared target slot, either no
  promotion or one of the `Z'` eligible indices with the factor `(V_g ρ)^{-1}`
  (`sum_edgeAbsPromoP_le`: `ρ^{Z'} (1 + Z'/(V_g ρ))^{t_g}` is bounded uniformly in `Z'`; the
  injectivity of the promotions is not used for the row);
* `edgeAbsFreshW` — the big target list: the shared and the promoted labels are determined, and
  every fresh label carries its factor `μ̃_g`.

The last factor is kept exact (`edgeCoef_row_le`): for an arbitrary nonnegative weight `Φ` of the
fresh births, the sum over the big target lists is at most the *fresh integral*
`edgeAbsFreshIntegral` of `Φ` (`sum_edgeAbsFreshW_le`). This is the form in which "the total
fresh mass in each constrained slot [is replaced] by its single-point bound" [S-02:1127–1129].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Scalars and finite sums -/

/-- The scalar inequality behind `edgeCoef_row_le`. -/
theorem l38_row_scalar {a r1 PV PF r2 Q SN d d' sp w wt Pv nrm : ℝ} (ha : 0 ≤ a)
    (hPV : 0 ≤ PV) (hPF : 0 ≤ PF) (hr20 : 0 ≤ r2) (hSN : 0 ≤ SN)
    (hd0 : 0 ≤ d) (hd'0 : 0 ≤ d') (hsp : 0 ≤ sp) (hwt0 : 0 ≤ wt)
    (hn : nrm ≤ a * r1 * PV * PF * r2 * (SN * (d * d')) * sp) (hr1 : r1 ≤ 1) (hr2 : r2 ≤ Q)
    (hd : d ≤ 1) (hw : wt ≤ w * Pv) :
    nrm * wt ≤ a * sp * (SN * d') * Pv * (PV * Q) * PF * w := by
  have h1 : r1 * r2 * d ≤ 1 * Q * 1 :=
    mul_le_mul (mul_le_mul hr1 hr2 hr20 zero_le_one) hd hd0
      (mul_nonneg zero_le_one (hr20.trans hr2))
  have hX : 0 ≤ a * PV * PF * (SN * d') * sp :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha hPV) hPF) (mul_nonneg hSN hd'0)) hsp
  have h2 : a * r1 * PV * PF * r2 * (SN * (d * d')) * sp ≤ a * PV * PF * (SN * d') * sp * Q := by
    calc a * r1 * PV * PF * r2 * (SN * (d * d')) * sp
        = a * PV * PF * (SN * d') * sp * (r1 * r2 * d) := by ring
      _ ≤ a * PV * PF * (SN * d') * sp * (1 * Q * 1) := mul_le_mul_of_nonneg_left h1 hX
      _ = a * PV * PF * (SN * d') * sp * Q := by ring
  have hQ : 0 ≤ Q := hr20.trans hr2
  calc nrm * wt ≤ (a * PV * PF * (SN * d') * sp * Q) * (w * Pv) :=
        mul_le_mul (hn.trans h2) hw hwt0 (mul_nonneg hX hQ)
    _ = a * sp * (SN * d') * Pv * (PV * Q) * PF * w := by ring

/-- **(eq:promotion-count), in the form used here**: `ρ^Z (1 + Z κ)^T` is bounded uniformly in
`Z`, by `max(1, κ)^T sup_z (z + T)^T ρ^z`. -/
theorem l38_promo_scalar {κ κmax ρ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ κmax) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {T : ℕ} (hT : 0 < T) (Z : ℕ) :
    ρ ^ Z * (1 + (Z : ℝ) * κ) ^ T ≤ (max 1 κmax) ^ T * Schur.countSup T ρ := by
  have hm1 : (1 : ℝ) ≤ max 1 κmax := le_max_left _ _
  have hm0 : (0 : ℝ) ≤ max 1 κmax := zero_le_one.trans hm1
  have hκm : κ ≤ max 1 κmax := hκ.trans (le_max_right _ _)
  have hZ : (0 : ℝ) ≤ (Z : ℝ) := Nat.cast_nonneg Z
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have h1 : 1 + (Z : ℝ) * κ ≤ max 1 κmax * (((Z + T : ℕ) : ℝ)) := by
    have h2 : (Z : ℝ) * κ ≤ (Z : ℝ) * max 1 κmax := mul_le_mul_of_nonneg_left hκm hZ
    have h3 : max 1 κmax * 1 ≤ max 1 κmax * (T : ℝ) := mul_le_mul_of_nonneg_left hT1 hm0
    rw [Nat.cast_add, mul_add]
    linarith
  have h0 : 0 ≤ 1 + (Z : ℝ) * κ := add_nonneg zero_le_one (mul_nonneg hZ hκ0)
  calc ρ ^ Z * (1 + (Z : ℝ) * κ) ^ T
      ≤ ρ ^ Z * (max 1 κmax * ((Z + T : ℕ) : ℝ)) ^ T :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 T) (pow_nonneg hρ0.le Z)
    _ = max 1 κmax ^ T * (((Z + T : ℕ) : ℝ) ^ T * ρ ^ Z) := by
        rw [mul_pow]
        ring
    _ ≤ max 1 κmax ^ T * Schur.countSup T ρ :=
        mul_le_mul_of_nonneg_left (Schur.le_countSup T hρ0 hρ1 Z) (pow_nonneg hm0 T)

/-- A product of factors which are `κ` where a property holds and `1` elsewhere. -/
theorem l38_prod_ite_const {ι : Type*} [Fintype ι] (p : ι → Prop) {hd hd' : DecidablePred p}
    (κ : ℝ) :
    (∏ i, @ite ℝ (p i) (hd i) κ 1) = κ ^ (@Finset.filter ι p hd' Finset.univ).card := by
  have e : hd = hd' := Subsingleton.elim _ _
  subst e
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

/-- A sum over four components of a product of four factors, the last of which also depends on
the second component. -/
theorem l38_sum_four {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (a : α → ℝ) (b : β → ℝ) (c : γ → ℝ) (d : β → δ → ℝ) {Ma Mb Mc Md : ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ y, 0 ≤ b y) (hc0 : ∀ z, 0 ≤ c z) (hMc : 0 ≤ Mc)
    (hMd : 0 ≤ Md) (ha : ∑ x, a x ≤ Ma) (hb : ∑ y, b y ≤ Mb) (hc : ∑ z, c z ≤ Mc)
    (hd : ∀ y, ∑ w, d y w ≤ Md) :
    ∑ t : α × β × γ × δ, a t.1 * b t.2.1 * c t.2.2.1 * d t.2.1 t.2.2.2 ≤ Ma * Mb * Mc * Md := by
  have hMb : 0 ≤ Mb := (Finset.sum_nonneg fun y _ => hb0 y).trans hb
  have h1 : ∀ x y z, ∑ w, a x * b y * c z * d y w ≤ a x * b y * c z * Md := by
    intro x y z
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hd y) (mul_nonneg (mul_nonneg (ha0 x) (hb0 y)) (hc0 z))
  have h2 : ∀ x y, ∑ z, ∑ w, a x * b y * c z * d y w ≤ a x * b y * (Mc * Md) := by
    intro x y
    calc ∑ z, ∑ w, a x * b y * c z * d y w ≤ ∑ z, a x * b y * c z * Md :=
          Finset.sum_le_sum fun z _ => h1 x y z
      _ = a x * b y * Md * ∑ z, c z := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ a x * b y * Md * Mc :=
          mul_le_mul_of_nonneg_left hc (mul_nonneg (mul_nonneg (ha0 x) (hb0 y)) hMd)
      _ = a x * b y * (Mc * Md) := by ring
  have h3 : ∀ x, ∑ y, ∑ z, ∑ w, a x * b y * c z * d y w ≤ a x * (Mb * (Mc * Md)) := by
    intro x
    calc ∑ y, ∑ z, ∑ w, a x * b y * c z * d y w ≤ ∑ y, a x * b y * (Mc * Md) :=
          Finset.sum_le_sum fun y _ => h2 x y
      _ = a x * (Mc * Md) * ∑ y, b y := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ a x * (Mc * Md) * Mb :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (ha0 x) (mul_nonneg hMc hMd))
      _ = a x * (Mb * (Mc * Md)) := by ring
  have e : ∑ t : α × β × γ × δ, a t.1 * b t.2.1 * c t.2.2.1 * d t.2.1 t.2.2.2 =
      ∑ x, ∑ y, ∑ z, ∑ w, a x * b y * c z * d y w := by
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun x _ => ?_)
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun y _ => ?_)
    exact Fintype.sum_prod_type _
  calc ∑ t : α × β × γ × δ, a t.1 * b t.2.1 * c t.2.2.1 * d t.2.1 t.2.2.2
      = ∑ x, ∑ y, ∑ z, ∑ w, a x * b y * c z * d y w := e
    _ ≤ ∑ x, a x * (Mb * (Mc * Md)) := Finset.sum_le_sum fun x _ => h3 x
    _ = (∑ x, a x) * (Mb * (Mc * Md)) := (Finset.sum_mul _ _ _).symm
    _ ≤ Ma * (Mb * (Mc * Md)) :=
        mul_le_mul_of_nonneg_right ha (mul_nonneg hMb (mul_nonneg hMc hMd))
    _ = Ma * Mb * Mc * Md := by ring

/-! ### The small lists -/

section Small

variable {S B : Type} [Fintype S] {𝒢 : GroupFamily S B} {J ℓ : ℕ}

open _root_.Classical in
/-- **The weight of a small list `b` relative to a small list `a`, at the residues `p`**: the
normalization `∏_{g ∈ 𝒮} V_g^{-ℓ}` times the small endpoint factor at `p` if `b` is a small state
at `p` with the shared labels of `a`, and zero otherwise [S-02:0503–0507]. Rows: `a` is the
source list and `b` the target list; columns: the converse. -/
def edgeAbsSmallW (𝒢 : GroupFamily S B) (q : ℝ) (p : ResVec (smallPrimes 𝒢))
    (a b : LabelList 𝒢.small J ℓ) : ℝ :=
  if IsSmallState 𝒢 p b ∧ SharedSmall a b then
    (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) * smallDamping 𝒢 J ℓ q p
  else 0

theorem edgeAbsSmallW_of (q : ℝ) {p : ResVec (smallPrimes 𝒢)} {a b : LabelList 𝒢.small J ℓ}
    (h : IsSmallState 𝒢 p b ∧ SharedSmall a b) :
    edgeAbsSmallW 𝒢 q p a b =
      (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
        smallDamping 𝒢 J ℓ q p := by
  unfold edgeAbsSmallW
  exact if_pos h

theorem edgeAbsSmallW_nonneg {q : ℝ} (hq : 0 < q) (p : ResVec (smallPrimes 𝒢))
    (a b : LabelList 𝒢.small J ℓ) : 0 ≤ edgeAbsSmallW 𝒢 q p a b := by
  unfold edgeAbsSmallW
  split_ifs
  · exact mul_nonneg
      (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _))
      (l38_smallDamping_pos hq p).le
  · exact le_rfl

/-- **(eq:physical-count-bound) for the small groups** [S-02:0143–0153, 0783–0784]: "small
transitions satisfy (eq:physical-count-bound)". For every vector of residues `p` and every small
list `a`, the small states `b` at `p` with the shared labels of `a` have total weight at most
`∏_{g ∈ 𝒮} groupConst v₋ q T`. -/
theorem sum_edgeAbsSmallW_le [DecidableEq S] (𝒢 : GroupFamily S B) {q vMinus : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1)
    (hv : 0 < vMinus) (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g)) {T : ℕ}
    (hT : 0 < T) (hℓT : ℓ ≤ T) (p : ResVec (smallPrimes 𝒢)) (a : LabelList 𝒢.small J ℓ) :
    ∑ b : LabelList 𝒢.small J ℓ, edgeAbsSmallW 𝒢 q p a b ≤
      ∏ _g : S, Schur.groupConst vMinus q T := by
  have hW : 0 ≤ (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
      smallDamping 𝒢 J ℓ q p :=
    mul_nonneg
      (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _))
      (l38_smallDamping_pos hq0 p).le
  have hmem : ∀ b : LabelList 𝒢.small J ℓ, IsSmallState 𝒢 p b ∧ SharedSmall a b →
      b ∈ Fintype.piFinset fun g : S =>
        Schur.validSet (fun r => (resModel (smallPrimes 𝒢)).hit r p) (∅ : Finset (Fin J))
          (a g) := by
    intro b hb
    refine Fintype.mem_piFinset.mpr fun g => Schur.mem_validSet.mpr ?_
    exact ⟨hb.1.1 g, fun s => hb.1.2 g s, fun i _ => hb.2 g i⟩
  have h1 : ∑ b : LabelList 𝒢.small J ℓ, edgeAbsSmallW 𝒢 q p a b =
      ∑ b ∈ (Fintype.piFinset fun g : S =>
          Schur.validSet (fun r => (resModel (smallPrimes 𝒢)).hit r p) (∅ : Finset (Fin J))
            (a g)),
        edgeAbsSmallW 𝒢 q p a b := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_).symm
    unfold edgeAbsSmallW
    exact if_neg fun hc => hb (hmem b hc)
  have h2 : ∑ b ∈ (Fintype.piFinset fun g : S =>
          Schur.validSet (fun r => (resModel (smallPrimes 𝒢)).hit r p) (∅ : Finset (Fin J))
            (a g)),
        edgeAbsSmallW 𝒢 q p a b ≤
      (Fintype.piFinset fun g : S =>
          Schur.validSet (fun r => (resModel (smallPrimes 𝒢)).hit r p) (∅ : Finset (Fin J))
            (a g)).card •
        ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          smallDamping 𝒢 J ℓ q p) := by
    refine Finset.sum_le_card_nsmul _ _ _ fun b _ => ?_
    unfold edgeAbsSmallW
    split_ifs
    · exact le_rfl
    · exact hW
  have h3 : (Fintype.piFinset fun g : S =>
          Schur.validSet (fun r => (resModel (smallPrimes 𝒢)).hit r p) (∅ : Finset (Fin J))
            (a g)).card •
        ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          smallDamping 𝒢 J ℓ q p) =
      ∏ g : S, (((Schur.validSet (fun r => (resModel (smallPrimes 𝒢)).hit r p)
          (∅ : Finset (Fin J)) (a g)).card : ℝ) *
        (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹ *
        q ^ ((((countHits (fun r => (resModel (smallPrimes 𝒢)).hit r p) (𝒢.small g) : ℕ) : ℝ) -
          ((J + ℓ : ℕ) : ℝ)) / 2)) := by
    rw [Fintype.card_piFinset, nsmul_eq_mul, l38_smallDamping_eq_prod hq0 p, Nat.cast_prod]
    simp only [Finset.prod_mul_distrib]
    ring
  refine (le_of_eq h1).trans (h2.trans ((le_of_eq h3).trans ?_))
  refine Finset.prod_le_prod (fun g _ => ?_) (fun g _ => ?_)
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _))) (Real.rpow_nonneg hq0.le _)
  · exact Schur.group_factor_le hv (hVS g) hq0 hq1 hT
      (fun r => (resModel (smallPrimes 𝒢)).hit r p) (∅ : Finset (Fin J)) (a g) (by simp) hℓT

end Small

/-! ### One big group: promotions and stores -/

section OneGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {g : B}

open _root_.Classical in
/-- **The weight of the promotion choice of one target slot** [S-02:0494–0499]: `1` for no
promotion; `κ` for the promotion of an old pending particle with zero translated residue into an
unshared slot (`κ = (V_g ρ)^{-1}`: the transfer coefficient `V_g^{-1}` and the loss `ρ^{-1}` of
output damping); `0` for every other index. -/
def edgeAbsSlotW (κ : ℝ) (Cg : Finset (Fin J)) (Δ : ℤ) (z : Mem 𝒢 Bc g) (sl : Slot J ℓ) :
    Option (Fin Bc) → ℝ
  | none => 1
  | some j => if Unshared Cg sl ∧ edgeAbsElig Δ z j then κ else 0

theorem edgeAbsSlotW_none (κ : ℝ) (Cg : Finset (Fin J)) (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (sl : Slot J ℓ) : edgeAbsSlotW κ Cg Δ z sl none = 1 := rfl

open _root_.Classical in
theorem edgeAbsSlotW_some (κ : ℝ) (Cg : Finset (Fin J)) (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (sl : Slot J ℓ) (j : Fin Bc) :
    edgeAbsSlotW κ Cg Δ z sl (some j) =
      if Unshared Cg sl ∧ edgeAbsElig Δ z j then κ else 0 := rfl

theorem edgeAbsSlotW_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (Cg : Finset (Fin J)) (Δ : ℤ)
    (z : Mem 𝒢 Bc g) (sl : Slot J ℓ) (o : Option (Fin Bc)) :
    0 ≤ edgeAbsSlotW κ Cg Δ z sl o := by
  cases o with
  | none =>
    rw [edgeAbsSlotW_none]
    exact zero_le_one
  | some j =>
    rw [edgeAbsSlotW_some]
    split_ifs
    · exact hκ
    · exact le_rfl

/-- For admissible promotions the product of the slot weights is `κ^a`. -/
theorem prod_edgeAbsSlotW_of_valid (κ : ℝ) (Cg : Finset (Fin J)) (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (pm : Slot J ℓ → Option (Fin Bc))
    (h : ∀ sl j, pm sl = some j → Unshared Cg sl ∧ edgeAbsElig Δ z j)
    {hd : DecidablePred fun sl : Slot J ℓ => pm sl ≠ none} :
    ∏ sl, edgeAbsSlotW κ Cg Δ z sl (pm sl) =
      κ ^ (@Finset.filter _ (fun sl : Slot J ℓ => pm sl ≠ none) hd Finset.univ).card := by
  have hfac : ∀ sl : Slot J ℓ,
      edgeAbsSlotW κ Cg Δ z sl (pm sl) = if pm sl ≠ none then κ else 1 := by
    intro sl
    obtain ⟨o, ho⟩ : ∃ o, pm sl = o := ⟨_, rfl⟩
    cases o with
    | none =>
      rw [if_neg (fun hne : pm sl ≠ none => hne ho), ho, edgeAbsSlotW_none]
    | some j =>
      rw [if_pos (fun hn : pm sl = none => Option.some_ne_none j (ho.symm.trans hn)), ho,
        edgeAbsSlotW_some]
      exact if_pos (h sl j ho)
  rw [Finset.prod_congr rfl fun sl _ => hfac sl]
  exact l38_prod_ite_const (fun sl : Slot J ℓ => pm sl ≠ none) κ

open _root_.Classical in
/-- The sum of the weights of the promotion choices of one target slot: `1 + Z' κ` for an
unshared slot, `1` for a shared slot. -/
theorem sum_edgeAbsSlotW (κ : ℝ) (Cg : Finset (Fin J)) (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (sl : Slot J ℓ) :
    ∑ o : Option (Fin Bc), edgeAbsSlotW κ Cg Δ z sl o =
      if Unshared Cg sl then 1 + (edgeAbsEligCount Δ z : ℝ) * κ else 1 := by
  rw [Fintype.sum_option, edgeAbsSlotW_none,
    Finset.sum_congr rfl fun j _ => edgeAbsSlotW_some κ Cg Δ z sl j]
  by_cases hU : Unshared Cg sl
  · rw [if_pos hU]
    have e : ∀ j : Fin Bc, (if Unshared Cg sl ∧ edgeAbsElig Δ z j then κ else 0) =
        if edgeAbsElig Δ z j then κ else 0 := fun j =>
      ite_congr_of_iff (and_iff_right hU) rfl rfl
    rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  · rw [if_neg hU]
    have e : ∀ j : Fin Bc, (if Unshared Cg sl ∧ edgeAbsElig Δ z j then κ else 0) = 0 := fun j =>
      if_neg fun h => hU h.1
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_const_zero, add_zero]

open _root_.Classical in
/-- **The promotions of one big group**: summed over all promotion maps, the product of the slot
weights is `(1 + Z' κ)^{t_g}`. -/
theorem sum_prod_edgeAbsSlotW_le {κ : ℝ} (hκ : 0 ≤ κ) (Cg : Finset (Fin J)) (Δ : ℤ)
    (z : Mem 𝒢 Bc g) {T : ℕ} (hC : ℓ + Cg.card ≤ T) :
    ∑ pm : Slot J ℓ → Option (Fin Bc), ∏ sl, edgeAbsSlotW κ Cg Δ z sl (pm sl) ≤
      (1 + (edgeAbsEligCount Δ z : ℝ) * κ) ^ T := by
  have hA : (1 : ℝ) ≤ 1 + (edgeAbsEligCount Δ z : ℝ) * κ :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hκ)
  have h1 : ∑ pm : Slot J ℓ → Option (Fin Bc), ∏ sl, edgeAbsSlotW κ Cg Δ z sl (pm sl) =
      ∏ sl : Slot J ℓ, ∑ o : Option (Fin Bc), edgeAbsSlotW κ Cg Δ z sl o :=
    (Fintype.prod_sum fun (sl : Slot J ℓ) (o : Option (Fin Bc)) =>
      edgeAbsSlotW κ Cg Δ z sl o).symm
  have h2 : ∏ sl : Slot J ℓ, ∑ o : Option (Fin Bc), edgeAbsSlotW κ Cg Δ z sl o =
      ∏ sl : Slot J ℓ,
        (if Unshared Cg sl then 1 + (edgeAbsEligCount Δ z : ℝ) * κ else 1) :=
    Finset.prod_congr rfl fun sl _ => sum_edgeAbsSlotW κ Cg Δ z sl
  have h3 : ∏ sl : Slot J ℓ,
        (if Unshared Cg sl then 1 + (edgeAbsEligCount Δ z : ℝ) * κ else 1) =
      (1 + (edgeAbsEligCount Δ z : ℝ) * κ) ^ (ℓ + Cg.card) := by
    have hcard : (Finset.univ.filter fun sl : Slot J ℓ => Unshared Cg sl).card = ℓ + Cg.card :=
      l38_card_unshared Cg
    rw [← hcard]
    exact l38_prod_ite_const (fun sl : Slot J ℓ => Unshared Cg sl) _
  rw [h1, h2, h3]
  exact pow_le_pow_right₀ hA hC

open _root_.Classical in
/-- **The weight of the set of stored slots of one big group** [S-02:0487–0491, 0778–0782]: `v^b` for
a set of `b` unshared slots, `0` for every other set. -/
def edgeAbsStoreW (v : ℝ) (Cg : Finset (Fin J)) (st : Finset (Slot J ℓ)) : ℝ :=
  if ∀ sl ∈ st, Unshared Cg sl then v ^ st.card else 0

theorem edgeAbsStoreW_of (v : ℝ) {Cg : Finset (Fin J)} {st : Finset (Slot J ℓ)}
    (h : ∀ sl ∈ st, Unshared Cg sl) : edgeAbsStoreW v Cg st = v ^ st.card := by
  unfold edgeAbsStoreW
  exact if_pos h

theorem edgeAbsStoreW_nonneg {v : ℝ} (hv : 0 ≤ v) (Cg : Finset (Fin J))
    (st : Finset (Slot J ℓ)) : 0 ≤ edgeAbsStoreW v Cg st := by
  unfold edgeAbsStoreW
  split_ifs
  · exact pow_nonneg hv _
  · exact le_rfl

open _root_.Classical in
/-- **The stores of one big group**: "at most `2^{t_g}` choices" of the stored subset, each of
weight at most `v^{t_g}`. -/
theorem sum_edgeAbsStoreW_le {v : ℝ} (hv : 1 ≤ v) (Cg : Finset (Fin J)) {T : ℕ}
    (hC : ℓ + Cg.card ≤ T) :
    ∑ st : Finset (Slot J ℓ), edgeAbsStoreW v Cg st ≤ (2 * v) ^ T := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  obtain ⟨U, hUdef⟩ : ∃ U : Finset (Slot J ℓ),
      U = Finset.univ.filter fun sl : Slot J ℓ => Unshared Cg sl := ⟨_, rfl⟩
  have hUmem : ∀ sl, Unshared Cg sl → sl ∈ U := fun sl h => by
    rw [hUdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ sl, h⟩
  have hUcard : U.card = ℓ + Cg.card := by
    rw [hUdef]
    exact l38_card_unshared Cg
  have h1 : ∑ st : Finset (Slot J ℓ), edgeAbsStoreW v Cg st =
      ∑ st ∈ U.powerset, edgeAbsStoreW v Cg st := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun st _ hst => ?_).symm
    unfold edgeAbsStoreW
    exact if_neg fun h => hst (Finset.mem_powerset.mpr fun sl hsl => hUmem sl (h sl hsl))
  have h2 : ∑ st ∈ U.powerset, edgeAbsStoreW v Cg st ≤ U.powerset.card • v ^ T := by
    refine Finset.sum_le_card_nsmul _ _ _ fun st hst => ?_
    unfold edgeAbsStoreW
    split_ifs
    · exact pow_le_pow_right₀ hv
        ((Finset.card_le_card (Finset.mem_powerset.mp hst)).trans (hUcard.le.trans hC))
    · exact pow_nonneg hv0 T
  rw [h1]
  refine h2.trans ?_
  rw [Finset.card_powerset, hUcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hC) (pow_nonneg hv0 T)

end OneGroup

/-! ### All big groups -/

section Big

variable {S B : Type} [Fintype B] [DecidableEq B] {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ}

/-- **The weight of the stores of all big groups.** -/
def edgeAbsStoreP (v : ℝ) (C : B → Finset (Fin J)) (store : (g : B) → Finset (Slot J ℓ)) : ℝ :=
  ∏ g, edgeAbsStoreW v (C g) (store g)

omit [DecidableEq B] in
theorem edgeAbsStoreP_nonneg {v : ℝ} (hv : 0 ≤ v) (C : B → Finset (Fin J))
    (store : (g : B) → Finset (Slot J ℓ)) : 0 ≤ edgeAbsStoreP v C store :=
  Finset.prod_nonneg fun g _ => edgeAbsStoreW_nonneg hv (C g) (store g)

/-- The stores of all big groups: at most `(2v)^T` per group. -/
theorem sum_edgeAbsStoreP_le {v : ℝ} (hv : 1 ≤ v) (C : B → Finset (Fin J)) {T : ℕ}
    (hC : ∀ g, ℓ + (C g).card ≤ T) :
    ∑ store : (g : B) → Finset (Slot J ℓ), edgeAbsStoreP v C store ≤ ∏ _g : B, (2 * v) ^ T := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have h1 : ∑ store : (g : B) → Finset (Slot J ℓ), edgeAbsStoreP v C store =
      ∏ g : B, ∑ st : Finset (Slot J ℓ), edgeAbsStoreW v (C g) st :=
    (Fintype.prod_sum fun (g : B) (st : Finset (Slot J ℓ)) => edgeAbsStoreW v (C g) st).symm
  rw [h1]
  exact Finset.prod_le_prod
    (fun g _ => Finset.sum_nonneg fun st _ => edgeAbsStoreW_nonneg hv0 (C g) st)
    (fun g _ => sum_edgeAbsStoreW_le hv (C g) (hC g))

/-- **The weight of the promotions of all big groups**: `ρ^{Z'_g}` and the slot weights with
`κ_g = (V_g ρ)^{-1}`. -/
def edgeAbsPromoP (𝒢 : GroupFamily S B) (ρ : ℝ) (C : B → Finset (Fin J)) (Δ : ℤ)
    (mem : (g : B) → Mem 𝒢 Bc g) (promo : (g : B) → Slot J ℓ → Option (Fin Bc)) : ℝ :=
  ∏ g, (ρ ^ edgeAbsEligCount Δ (mem g) *
    ∏ sl, edgeAbsSlotW (Graph.primeGroupReciprocalMass (𝒢.big g) * ρ)⁻¹ (C g) Δ (mem g) sl
      (promo g sl))

omit [DecidableEq B] in
theorem edgeAbsPromoP_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (C : B → Finset (Fin J)) (Δ : ℤ)
    (mem : (g : B) → Mem 𝒢 Bc g) (promo : (g : B) → Slot J ℓ → Option (Fin Bc)) :
    0 ≤ edgeAbsPromoP 𝒢 ρ C Δ mem promo :=
  Finset.prod_nonneg fun g _ => mul_nonneg (pow_nonneg hρ _)
    (Finset.prod_nonneg fun sl _ => edgeAbsSlotW_nonneg
      (inv_nonneg.mpr (mul_nonneg (Schur.reciprocalMass_nonneg _) hρ)) (C g) Δ (mem g) sl _)

/-- **The promotions of all big groups** (eq:promotion-count): at most
`max(1, (v₋ ρ)^{-1})^T sup_z (z + T)^T ρ^z` per group, uniformly in the memories. -/
theorem sum_edgeAbsPromoP_le (𝒢 : GroupFamily S B) {ρ vMinus : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hvm : 0 < vMinus) (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (C : B → Finset (Fin J)) {T : ℕ} (hT : 0 < T) (hC : ∀ g, ℓ + (C g).card ≤ T) (Δ : ℤ)
    (mem : (g : B) → Mem 𝒢 Bc g) :
    ∑ promo : (g : B) → Slot J ℓ → Option (Fin Bc), edgeAbsPromoP 𝒢 ρ C Δ mem promo ≤
      ∏ _g : B, ((max 1 (vMinus * ρ)⁻¹) ^ T * Schur.countSup T ρ) := by
  have hκ0 : ∀ g, 0 ≤ (Graph.primeGroupReciprocalMass (𝒢.big g) * ρ)⁻¹ := fun g =>
    inv_nonneg.mpr (mul_nonneg (Schur.reciprocalMass_nonneg _) hρ0.le)
  have hκ : ∀ g, (Graph.primeGroupReciprocalMass (𝒢.big g) * ρ)⁻¹ ≤ (vMinus * ρ)⁻¹ := fun g =>
    inv_anti₀ (mul_pos hvm hρ0) (mul_le_mul_of_nonneg_right (hVB g) hρ0.le)
  have h1 : ∑ promo : (g : B) → Slot J ℓ → Option (Fin Bc), edgeAbsPromoP 𝒢 ρ C Δ mem promo =
      ∏ g : B, ∑ pm : Slot J ℓ → Option (Fin Bc),
        (ρ ^ edgeAbsEligCount Δ (mem g) *
          ∏ sl, edgeAbsSlotW (Graph.primeGroupReciprocalMass (𝒢.big g) * ρ)⁻¹ (C g) Δ (mem g)
            sl (pm sl)) :=
    (Fintype.prod_sum fun (g : B) (pm : Slot J ℓ → Option (Fin Bc)) =>
      ρ ^ edgeAbsEligCount Δ (mem g) *
        ∏ sl, edgeAbsSlotW (Graph.primeGroupReciprocalMass (𝒢.big g) * ρ)⁻¹ (C g) Δ (mem g)
          sl (pm sl)).symm
  rw [h1]
  refine Finset.prod_le_prod (fun g _ => Finset.sum_nonneg fun pm _ => ?_) (fun g _ => ?_)
  · exact mul_nonneg (pow_nonneg hρ0.le _)
      (Finset.prod_nonneg fun sl _ => edgeAbsSlotW_nonneg (hκ0 g) (C g) Δ (mem g) sl _)
  · rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left
      (sum_prod_edgeAbsSlotW_le (hκ0 g) (C g) Δ (mem g) (hC g)) (pow_nonneg hρ0.le _)).trans
      (l38_promo_scalar (hκ0 g) (hκ g) hρ0 hρ1 hT _)

/-! ### The fresh labels -/

open _root_.Classical in
/-- **The fresh births of an edge**, as a function of the pattern sets, the promotions and the
big target list (`edgeBirths`): the label of every unshared target slot without promotion. -/
def edgeAbsBirths (C : B → Finset (Fin J)) (promo : (g : B) → Slot J ℓ → Option (Fin Bc))
    (xbT : LabelList 𝒢.big J ℓ) : (g : B) → Slot J ℓ → Option ℕ :=
  fun g sl => if Unshared (C g) sl ∧ promo g sl = none then some (xbT g sl : ℕ) else none

/-- The labels of the target slots which are not fresh: the source label in a slot without
promotion, the label of the promoted particle in a slot with promotion. -/
def edgeAbsBase (mem : (g : B) → Mem 𝒢 Bc g) (xb : LabelList 𝒢.big J ℓ)
    (promo : (g : B) → Slot J ℓ → Option (Fin Bc)) : LabelList 𝒢.big J ℓ :=
  fun g sl =>
    ((promo g sl).bind fun j => (memAt (mem g) j).map fun pr => pr.1).getD (xb g sl)

omit [Fintype B] [DecidableEq B] in
theorem edgeAbsBase_of_none (mem : (g : B) → Mem 𝒢 Bc g) (xb : LabelList 𝒢.big J ℓ)
    {promo : (g : B) → Slot J ℓ → Option (Fin Bc)} {g : B} {sl : Slot J ℓ}
    (h : promo g sl = none) : edgeAbsBase mem xb promo g sl = xb g sl := by
  unfold edgeAbsBase
  rw [h, Option.bind_none, Option.getD_none]

omit [Fintype B] [DecidableEq B] in
theorem edgeAbsBase_of_some (mem : (g : B) → Mem 𝒢 Bc g) (xb : LabelList 𝒢.big J ℓ)
    {promo : (g : B) → Slot J ℓ → Option (Fin Bc)} {g : B} {sl : Slot J ℓ} {j : Fin Bc}
    {pr : Particle 𝒢 g} (h : promo g sl = some j) (hpr : memAt (mem g) j = some pr) :
    edgeAbsBase mem xb promo g sl = pr.1 := by
  unfold edgeAbsBase
  rw [h, Option.bind_some, hpr, Option.map_some, Option.getD_some]

open _root_.Classical in
/-- **The weight of the big target list** [S-02:0500–0502]: the product of `μ̃_g` over the fresh
labels if the list has the shared labels of the source and the labels of the promoted particles
in the slots with promotion, and zero otherwise. -/
def edgeAbsFreshW (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ) (C : B → Finset (Fin J))
    (mem : (g : B) → Mem 𝒢 Bc g) (xb : LabelList 𝒢.big J ℓ)
    (promo : (g : B) → Slot J ℓ → Option (Fin Bc)) (xbT : LabelList 𝒢.big J ℓ) : ℝ :=
  if SharedBig C xb xbT ∧
      ∀ g sl j, promo g sl = some j →
        ∃ pr : Particle 𝒢 g, memAt (mem g) j = some pr ∧ xbT g sl = pr.1 then
    ∏ g, ∏ sl : Slot J ℓ,
      if Unshared (C g) sl ∧ promo g sl = none then tiltLaw (𝒢.big g) q n (xbT g sl) else 1
  else 0

omit [DecidableEq B] in
theorem edgeAbsFreshW_nonneg {q : ℝ} {n : ℕ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (C : B → Finset (Fin J))
    (mem : (g : B) → Mem 𝒢 Bc g) (xb : LabelList 𝒢.big J ℓ)
    (promo : (g : B) → Slot J ℓ → Option (Fin Bc)) (xbT : LabelList 𝒢.big J ℓ) :
    0 ≤ edgeAbsFreshW 𝒢 q n C mem xb promo xbT := by
  unfold edgeAbsFreshW
  split_ifs
  · refine Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ => ?_
    split_ifs
    · exact hν g _ (xbT g sl).2
    · exact zero_le_one
  · exact le_rfl

open _root_.Classical in
/-- **The fresh integral of a weight `Φ` of the births** [S-02:1121–1130]: for a family `F` of
sets of target slots (the fresh slots) and a list `x₀` (the labels of the other slots), the
integral of `Φ` over the labels of the slots of `F` against `⊗ μ̃_g`:
`∑_x 1[x = x₀ outside F] ∏_{g, sl ∈ F_g} μ̃_g(x_{g,sl}) Φ(births)`, where the births are the labels
of the slots of `F`. For `Φ = 1` it is `∏_g μ̃_g(𝒫_g)^{|F_g|}`; if `Φ` vanishes unless prescribed
slots of `F` carry prescribed labels, each of these slots contributes a point mass of `μ̃_g`
instead of the total mass (`edgeAbsFreshIntegral_pinned_le`). -/
def edgeAbsFreshIntegral (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ)
    (F : (g : B) → Finset (Slot J ℓ)) (x₀ : LabelList 𝒢.big J ℓ)
    (Φ : ((g : B) → Slot J ℓ → Option ℕ) → ℝ) : ℝ :=
  ∑ x : LabelList 𝒢.big J ℓ,
    if ∀ g sl, sl ∉ F g → x g sl = x₀ g sl then
      (∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl)) *
        Φ (fun g sl => if sl ∈ F g then some (x g sl : ℕ) else none)
    else 0

open _root_.Classical in
/-- **The sum over the big target lists is at most the fresh integral**: for fixed promotions
the shared and the promoted labels are determined, and the fresh labels are integrated against
`μ̃_g`. -/
theorem sum_edgeAbsFreshW_le {q : ℝ} {n : ℕ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (C : B → Finset (Fin J))
    (mem : (g : B) → Mem 𝒢 Bc g) (xb : LabelList 𝒢.big J ℓ)
    (promo : (g : B) → Slot J ℓ → Option (Fin Bc))
    (Φ : ((g : B) → Slot J ℓ → Option ℕ) → ℝ) (hΦ0 : ∀ b, 0 ≤ Φ b) :
    ∑ xbT : LabelList 𝒢.big J ℓ,
        edgeAbsFreshW 𝒢 q n C mem xb promo xbT * Φ (edgeAbsBirths C promo xbT) ≤
      edgeAbsFreshIntegral 𝒢 q n
        (fun g => Finset.univ.filter fun sl : Slot J ℓ => Unshared (C g) sl ∧ promo g sl = none)
        (edgeAbsBase mem xb promo) Φ := by
  unfold edgeAbsFreshIntegral
  refine Finset.sum_le_sum fun xbT _ => ?_
  have hbirth : edgeAbsBirths C promo xbT =
      fun g sl =>
        if sl ∈ Finset.univ.filter (fun sl : Slot J ℓ => Unshared (C g) sl ∧ promo g sl = none)
        then some (xbT g sl : ℕ) else none := by
    funext g sl
    have hmem : sl ∈ Finset.univ.filter
          (fun sl : Slot J ℓ => Unshared (C g) sl ∧ promo g sl = none) ↔
        Unshared (C g) sl ∧ promo g sl = none := by
      rw [Finset.mem_filter]
      exact and_iff_right (Finset.mem_univ sl)
    unfold edgeAbsBirths
    exact ite_congr_of_iff hmem.symm rfl rfl
  have hRnn : 0 ≤ (∏ g, ∏ sl ∈ Finset.univ.filter
        (fun sl : Slot J ℓ => Unshared (C g) sl ∧ promo g sl = none),
        tiltLaw (𝒢.big g) q n (xbT g sl)) *
      Φ (fun g sl =>
        if sl ∈ Finset.univ.filter (fun sl : Slot J ℓ => Unshared (C g) sl ∧ promo g sl = none)
        then some (xbT g sl : ℕ) else none) :=
    mul_nonneg (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ =>
      hν g _ (xbT g sl).2) (hΦ0 _)
  by_cases hc : SharedBig C xb xbT ∧
      ∀ g sl j, promo g sl = some j →
        ∃ pr : Particle 𝒢 g, memAt (mem g) j = some pr ∧ xbT g sl = pr.1
  · have hagree : ∀ g sl,
        sl ∉ Finset.univ.filter (fun sl : Slot J ℓ => Unshared (C g) sl ∧ promo g sl = none) →
          xbT g sl = edgeAbsBase mem xb promo g sl := by
      intro g sl hsl
      have hnf : ¬(Unshared (C g) sl ∧ promo g sl = none) := fun h =>
        hsl (Finset.mem_filter.mpr ⟨Finset.mem_univ sl, h⟩)
      obtain ⟨o, ho⟩ : ∃ o, promo g sl = o := ⟨_, rfl⟩
      cases o with
      | none =>
        have hnU : ¬Unshared (C g) sl := fun hU => hnf ⟨hU, ho⟩
        rw [edgeAbsBase_of_none mem xb ho]
        rcases sl with i | j
        · exact hc.1 g i hnU
        · exact absurd trivial hnU
      | some j =>
        obtain ⟨pr, hpr, hx⟩ := hc.2 g sl j ho
        rw [edgeAbsBase_of_some mem xb ho hpr, hx]
    have hW : edgeAbsFreshW 𝒢 q n C mem xb promo xbT =
        ∏ g, ∏ sl ∈ Finset.univ.filter
          (fun sl : Slot J ℓ => Unshared (C g) sl ∧ promo g sl = none),
          tiltLaw (𝒢.big g) q n (xbT g sl) := by
      unfold edgeAbsFreshW
      rw [if_pos hc]
      exact Finset.prod_congr rfl fun g _ => (Finset.prod_filter _ _).symm
    refine le_of_eq ?_
    rw [if_pos hagree, hW, hbirth]
  · have hW : edgeAbsFreshW 𝒢 q n C mem xb promo xbT = 0 := by
      unfold edgeAbsFreshW
      exact if_neg hc
    rw [hW, zero_mul]
    split_ifs
    · exact hRnn
    · exact le_rfl

end Big

/-! ### The row majorant of one coefficient -/

section Edge

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- `edgeBirths` in terms of the pattern sets, the promotions and the big target list. -/
theorem edgeBirths_eq_abs {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) :
    edgeBirths c = edgeAbsBirths (𝔉 c.ν).C c.promo c.xbT := by
  funext g sl
  unfold edgeBirths edgeAbsBirths
  exact ite_congr_of_iff Iff.rfl rfl rfl

open _root_.Classical in
omit [DecidableEq S] in
/-- **The row majorant of one coefficient** [S-02:0767–0786]: the modulus of the coefficient of
the row transition of an edge, times the Schur weight `v^{j'_tot}` of its target, is at most the
probability of the free labels, times `sup |K_ν|`, times the weights of the small target list, of
the stores, of the promotions and of the big target list, times the Schur weight `v^{j_tot}` of
the source. The factors `μ̃_g` of the fresh labels are exact (`edgeAbsFreshW`). -/
theorem edgeCoef_row_le (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v : ℝ} (hq0 : 0 < D.q)
    (hq1 : D.q ≤ 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ ≤ 1) (hv : 1 ≤ v)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) :
    ‖edgeCoef D θ i s c‖ * schurWeight v (edgeTgt D i s c) ≤
      auxWeight 𝒢.big (D.fam c.ν).C c.r * ((D.fam c.ν).supNorm : ℝ) *
        (edgeAbsSmallW 𝒢 D.q ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y) s.xs
            c.xsT *
          edgeAbsStoreP v (D.fam c.ν).C c.store *
          edgeAbsPromoP 𝒢 D.ρ (D.fam c.ν).C (edgeStep D i s c) s.mem c.promo *
          edgeAbsFreshW 𝒢 D.q D.n (D.fam c.ν).C s.mem s.xb c.promo c.xbT) *
        schurWeight v s := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have haux : 0 ≤ auxWeight 𝒢.big (D.fam c.ν).C c.r := Schur.auxWeight_nonneg _ _ _
  have hsup : (0 : ℝ) ≤ ((D.fam c.ν).supNorm : ℝ) := NNReal.coe_nonneg _
  have hws : 0 ≤ schurWeight v s := pow_nonneg hv0 _
  have hmaj : 0 ≤
      edgeAbsSmallW 𝒢 D.q ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y) s.xs c.xsT *
        edgeAbsStoreP v (D.fam c.ν).C c.store *
        edgeAbsPromoP 𝒢 D.ρ (D.fam c.ν).C (edgeStep D i s c) s.mem c.promo *
        edgeAbsFreshW 𝒢 D.q D.n (D.fam c.ν).C s.mem s.xb c.promo c.xbT :=
    mul_nonneg (mul_nonneg (mul_nonneg (edgeAbsSmallW_nonneg hq0 _ _ _)
      (edgeAbsStoreP_nonneg hv0 _ _)) (edgeAbsPromoP_nonneg hρ0.le _ _ _ _))
      (edgeAbsFreshW_nonneg hν _ _ _ _ _)
  by_cases h : EdgeAbsCond D i s c
  · obtain ⟨_, h2, h3, h4, h5, h6, _, _, h9, h10⟩ := id h
    -- the factors of the real prefactor
    have hr10 : 0 ≤ D.ρ ^ memZeros s := pow_nonneg hρ0.le _
    have hr1 : D.ρ ^ memZeros s ≤ 1 := pow_le_one₀ hρ0.le hρ1
    have hPV : 0 ≤ ∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount c g)⁻¹ :=
      Finset.prod_nonneg fun g _ =>
        inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
    have hPF : 0 ≤ ∏ g, ∏ sl : Slot J ℓ,
        (if Fresh c g sl then tiltLaw (𝒢.big g) D.q D.n (c.xbT g sl) else 1) := by
      refine Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ => ?_
      split_ifs
      · exact hν g _ (c.xbT g sl).2
      · exact zero_le_one
    have hr20 : 0 ≤ D.ρ ^ memZeros (edgeTgt D i s c) := pow_nonneg hρ0.le _
    have hSN : 0 ≤ ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹ :=
      Finset.prod_nonneg fun g _ =>
        inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
    have hd0 : 0 ≤ smallDamping 𝒢 J ℓ D.q s.y := (l38_smallDamping_pos hq0 _).le
    have hd1 : smallDamping 𝒢 J ℓ D.q s.y ≤ 1 := l38_smallDamping_le_one hq0 hq1 h3
    have hd'0 : 0 ≤ smallDamping 𝒢 J ℓ D.q
        ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y) :=
      (l38_smallDamping_pos hq0 _).le
    have hR : 0 ≤ edgeAbsReal D i s c := by
      unfold edgeAbsReal
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg haux hr10) hPV) hPF) hr20)
        (mul_nonneg hSN (mul_nonneg hd0 hd'0))
    have hn : ‖edgeCoef D θ i s c‖ ≤
        auxWeight 𝒢.big (D.fam c.ν).C c.r * D.ρ ^ memZeros s *
            (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount c g)⁻¹) *
            (∏ g, ∏ sl : Slot J ℓ,
              if Fresh c g sl then tiltLaw (𝒢.big g) D.q D.n (c.xbT g sl) else 1) *
            D.ρ ^ memZeros (edgeTgt D i s c) *
            ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
              (smallDamping 𝒢 J ℓ D.q s.y *
                smallDamping 𝒢 J ℓ D.q
                  ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y))) *
          ((D.fam c.ν).supNorm : ℝ) := norm_edgeCoef_le D θ i s c h hR
    have hr2 := rho_pow_memZeros_edgeTgt_le D i s c hρ0 hρ1 h2
    have hw := schurWeight_edgeTgt_le D i s c hv h2
    have hwt0 : 0 ≤ schurWeight v (edgeTgt D i s c) := pow_nonneg hv0 _
    have key := l38_row_scalar haux hPV hPF hr20 hSN hd0 hd'0 hsup hwt0 hn hr1 hr2 hd1 hw
    -- the weights of the majorant where the conditions hold
    have e_small : edgeAbsSmallW 𝒢 D.q
          ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y) s.xs c.xsT =
        (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          smallDamping 𝒢 J ℓ D.q ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y) :=
      edgeAbsSmallW_of D.q ⟨h4, h5⟩
    have e_store : edgeAbsStoreP v (D.fam c.ν).C c.store = ∏ g, v ^ (c.store g).card :=
      Finset.prod_congr rfl fun g _ => edgeAbsStoreW_of v fun sl hsl => (h9 g sl hsl).1
    have e_promo : edgeAbsPromoP 𝒢 D.ρ (D.fam c.ν).C (edgeStep D i s c) s.mem c.promo =
        (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount c g)⁻¹) *
          ∏ g, (D.ρ ^ edgeAbsEligCount (edgeStep D i s c) (s.mem g) *
            D.ρ⁻¹ ^ promoCount c g) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun g _ => ?_
      have hval : ∀ sl j, c.promo g sl = some j →
          Unshared ((D.fam c.ν).C g) sl ∧ edgeAbsElig (edgeStep D i s c) (s.mem g) j := by
        intro sl j hj
        obtain ⟨hU, _, pr, hpr, h0, _, _⟩ := h10 g sl j hj
        exact ⟨hU, pr, hpr, h0⟩
      have hprod : ∏ sl, edgeAbsSlotW (Graph.primeGroupReciprocalMass (𝒢.big g) * D.ρ)⁻¹
            ((D.fam c.ν).C g) (edgeStep D i s c) (s.mem g) sl (c.promo g sl) =
          (Graph.primeGroupReciprocalMass (𝒢.big g) * D.ρ)⁻¹ ^ promoCount c g := by
        unfold promoCount
        exact prod_edgeAbsSlotW_of_valid _ _ _ _ (c.promo g) hval
      have hκ : (Graph.primeGroupReciprocalMass (𝒢.big g) * D.ρ)⁻¹ ^ promoCount c g =
          (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount c g)⁻¹ *
            D.ρ⁻¹ ^ promoCount c g := by
        rw [mul_inv, mul_pow, inv_pow (Graph.primeGroupReciprocalMass (𝒢.big g)) (promoCount c g)]
      rw [hprod, hκ]
      ring
    have e_fresh : edgeAbsFreshW 𝒢 D.q D.n (D.fam c.ν).C s.mem s.xb c.promo c.xbT =
        ∏ g, ∏ sl : Slot J ℓ,
          (if Fresh c g sl then tiltLaw (𝒢.big g) D.q D.n (c.xbT g sl) else 1) := by
      have hcomp : SharedBig (D.fam c.ν).C s.xb c.xbT ∧
          ∀ g sl j, c.promo g sl = some j →
            ∃ pr : Particle 𝒢 g, memAt (s.mem g) j = some pr ∧ c.xbT g sl = pr.1 := by
        refine ⟨h6, fun g sl j hj => ?_⟩
        obtain ⟨_, _, pr, hpr, _, _, hx⟩ := h10 g sl j hj
        exact ⟨pr, hpr, hx⟩
      unfold edgeAbsFreshW
      rw [if_pos hcomp]
      exact Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun sl _ =>
        ite_congr_of_iff Iff.rfl rfl rfl
    rw [e_small, e_store, e_promo, e_fresh]
    refine key.trans (le_of_eq ?_)
    ring
  · rw [edgeCoef_of_not_cond D θ i s c h, norm_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg haux hsup) hmaj) hws

end Edge

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
