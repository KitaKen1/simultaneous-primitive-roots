module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsRow
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsColGroup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The column bound of the absolute edge: the majorant and its integral over a fibre

Source: `verification/stage7-sources/S-02.tex`, lines 704–756 and 788–794
(`[S-02:0704–0756, 0788–0794]`), the column half of the proof of [S] Lemma 3.8.

"Fixing shared and free `D`-labels fixes `Δ` independently of which memory indices are retrieved,
as required for this change of variables. In small groups Haar translation and the joint
normalization `V_g^{-M-ℓ}` are invariant on reversal." [S-02:0744–0748]

The coefficient of a row transition vanishes unless the source and the target lists have the same
shared labels; then `D` and the step `Δ = σ_i k D` are functions of the pattern, the free labels
and the *target* lists ("the shared product and hence `D` are unchanged on reversal",
[S-02:0122–0123]): `edgeAbsStepT`, `edgeAbsStep_eq_stepT`.

* `edgeAbsColMaj` — **the column majorant**: for a fixed pattern, fixed free labels and fixed
  target lists, a product of a weight of the small source data (`edgeAbsSmallW`, with the two
  small endpoint factors), the shared big labels, and the one-group column weights `edgeAbsColW`
  of the big source data, times the value of the test function at the target.
* `edgeAbs_col_pointwise` — the measure and the Schur weight of the source, times the modulus of
  the coefficient, times a nonnegative function of the target, is at most
  `P(r) · sup |K_ν|` times the majorant.
* `edgeAbs_col_fiber` — **the integral of the majorant over the sources of a fixed target
  fibre** (fixed step, fixed target lists) is at most
  `(∏_{g ∈ 𝒮} C_𝒮)(∏_{g ∈ ℬ} C_ℬ)` times the integral of the test function over the target
  states with these lists, against the measure of `ℋ` and the Schur weight. The small groups are
  (eq:physical-count-bound) for the reversed transition (`sum_edgeAbsSmallW_le`); the big groups
  are the product of the one-group column inequalities (`edgeAbs_col_group`,
  `l38_tensor_rows_le`); the position is translated by `Δ`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Scalars and finite sums -/

/-- The scalar inequality behind `edgeAbs_col_pointwise`. -/
theorem l38_col_scalar {W nrm ft a r1 PV PF r2 SN d d' sp hs bl mm sw LS Pω : ℝ}
    (hW : W = hs * bl * mm * sw) (hbl : LS * Pω = bl) (hW0 : 0 ≤ W) (hft : 0 ≤ ft) (ha : 0 ≤ a)
    (hr10 : 0 ≤ r1) (hPV : 0 ≤ PV) (hPF : 0 ≤ PF) (hSN : 0 ≤ SN) (hd : 0 ≤ d) (hd' : 0 ≤ d')
    (hsp : 0 ≤ sp) (hn : nrm ≤ a * r1 * PV * PF * r2 * (SN * (d * d')) * sp) (hr2 : r2 ≤ 1) :
    W * (nrm * ft) ≤
      a * sp * (hs * (SN * d * d') * (LS * (Pω * PV * mm * sw * r1 * PF * ft))) := by
  have hX : 0 ≤ a * r1 * PV * PF := mul_nonneg (mul_nonneg (mul_nonneg ha hr10) hPV) hPF
  have hZ : 0 ≤ SN * (d * d') := mul_nonneg hSN (mul_nonneg hd hd')
  have h2 : a * r1 * PV * PF * r2 ≤ a * r1 * PV * PF * 1 := mul_le_mul_of_nonneg_left hr2 hX
  have h1 : nrm ≤ a * r1 * PV * PF * (SN * (d * d')) * sp := by
    refine hn.trans ?_
    calc a * r1 * PV * PF * r2 * (SN * (d * d')) * sp
        ≤ a * r1 * PV * PF * 1 * (SN * (d * d')) * sp :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hZ) hsp
      _ = a * r1 * PV * PF * (SN * (d * d')) * sp := by ring
  calc W * (nrm * ft) ≤ W * (a * r1 * PV * PF * (SN * (d * d')) * sp * ft) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hft) hW0
    _ = a * sp * (hs * (SN * d * d') * (LS * (Pω * PV * mm * sw * r1 * PF * ft))) := by
        rw [hW, ← hbl]
        ring

/-- The number of elements with a property does not depend on the decidability instance. -/
theorem l38_filter_card_inst {α : Type*} [Fintype α] (p : α → Prop) {h1 h2 : DecidablePred p} :
    (@Finset.filter α p h1 Finset.univ).card = (@Finset.filter α p h2 Finset.univ).card := by
  have e : h1 = h2 := Subsingleton.elim _ _
  subst e
  rfl

/-- A double sum of products of a factor of the first and a factor of the second variable. -/
theorem l38_sum_two_factor {α β : Type*} [Fintype α] [Fintype β] (c d e : ℝ) (a : α → ℝ)
    (b : β → ℝ) :
    ∑ x, ∑ y, c * (a x * d) * (e * b y) = c * ((∑ x, a x) * d) * (e * ∑ y, b y) := by
  have h1 : ∀ x, ∑ y, c * (a x * d) * (e * b y) = c * (a x * d) * (e * ∑ y, b y) := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.sum_mul]

/-- The translation by `h` of the vectors of residues, as a bijection. -/
def l38_shiftEquiv (Q : Finset ℕ) (h : ℤ) : ResVec Q ≃ ResVec Q where
  toFun := (resModel Q).shift h
  invFun := (resModel Q).shift (-h)
  left_inv y := (resModel Q).shift_neg_shift h y
  right_inv y := (resModel Q).shift_shift_neg h y

section OneGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {g : B}

/-- In a shared slot the weight of the target label is one. -/
theorem edgeAbsSrcW_shared_self (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) {Cg : Finset (Fin J)}
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) {sl : Slot J ℓ} (h : ¬Unshared Cg sl) :
    edgeAbsSrcW μ Cg τ sl (τ sl) = 1 :=
  (edgeAbsSrcW_of_shared μ τ h (τ sl) (hd := _root_.Classical.propDecidable _)).trans
    (if_pos rfl)

open _root_.Classical in
/-- The column weight where its conditions hold. -/
theorem edgeAbsColW_of (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (v ρ V : ℝ) (Cg : Finset (Fin J))
    (Δ : ℤ) (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (X : EdgeAbsSrc 𝒢 J ℓ Bc g)
    (h2 : ∀ sl ∈ X.1, Unshared Cg sl) (h3 : EdgeAbsPromoValid Cg Δ X.2.2.1 X.2.2.2 τ)
    (h4 : (edgeAbsNewList Δ X.2.2.1 X.2.1 X.1 X.2.2.2).length ≤ Bc) :
    edgeAbsColW μ v ρ V Cg Δ τ X =
      (∏ sl, edgeAbsSrcW μ Cg τ sl (X.2.1 sl)) *
        ((V ^ edgeAbsPromoNum X.2.2.2)⁻¹ *
          (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) X.2.2.1 *
            v ^ X.2.2.1.1.val * ρ ^ memZeroCount X.2.2.1 *
            (∏ sl, if Unshared Cg sl ∧ X.2.2.2 sl = none then μ (τ sl) else 1))) := by
  unfold edgeAbsColW
  rw [edgeAbsStoreW_of 1 h2, one_pow, one_mul,
    if_pos (show EdgeAbsPromoValid Cg Δ X.2.2.1 X.2.2.2 τ ∧
      (edgeAbsNewList Δ X.2.2.1 X.2.1 X.1 X.2.2.2).length ≤ Bc from ⟨h3, h4⟩)]

end OneGroup

section Edge

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-! ### The step in terms of the target lists -/

/-- **The step `Δ = σ_i k D` of an edge in terms of the target lists**: `D` is formed from the
shared labels of the target lists and the free labels ("the shared product and hence `D` are
unchanged on reversal", [S-02:0122–0123]). -/
def edgeAbsStepT (D : MemData 𝒢 J ℓ N) (i : ℕ) (ν : N) (r : AuxList 𝒢.big (D.fam ν).C)
    (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) : ℤ :=
  edgeSign i * D.k * ((dil (D.fam ν).C ((xsT, xbT) : Lists 𝒢 J ℓ) r : ℕ) : ℤ)

omit [DecidableEq S] [DecidableEq B] in
/-- Source and target lists with the same shared labels give the same step. -/
theorem edgeAbsStep_eq_stepT (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ)
    (h1 : SharedSmall s.xs xsT) (h2 : SharedBig (D.fam ν).C s.xb xbT) :
    edgeAbsStep D i s ν r = edgeAbsStepT D i ν r xsT xbT := by
  have h : dil (D.fam ν).C ((xsT, xbT) : Lists 𝒢 J ℓ) r =
      dil (D.fam ν).C ((s.xs, s.xb) : Lists 𝒢 J ℓ) r := by
    show smallDil xsT * bigDil (D.fam ν).C xbT r = smallDil s.xs * bigDil (D.fam ν).C s.xb r
    rw [smallDil_eq_of_shared h1, bigDil_eq_of_shared h2]
  unfold edgeAbsStep edgeAbsStepT
  rw [h]

/-! ### The column majorant -/

open _root_.Classical in
/-- **The column majorant of the absolute edge**, for a pattern with sets `C`, a step `Δ` and
target lists `xsT`, `xbT`, as a function of the source: the residues `y`, the small source list
`xs`, and the source data `X` of the big groups. It is the product of

* the Haar mass and the mass of the small source list, the weight `edgeAbsSmallW` of the reversed
  small transition (normalization `∏ V_g^{-ℓ}` and endpoint factor at `y`), and the endpoint
  factor at `y + Δ` if the target is a small state there;
* `μ̃_g` of the shared big labels;
* the one-group column weights `edgeAbsColW` of the big source data;
* the value of the test function `f` at the target state. -/
def edgeAbsColMaj (𝒢 : GroupFamily S B) (q ρ v : ℝ) (n : ℕ) (C : B → Finset (Fin J))
    (f : MState 𝒢 J ℓ Bc → ℝ) (Δ : ℤ) (xsT : LabelList 𝒢.small J ℓ)
    (xbT : LabelList 𝒢.big J ℓ) (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ)
    (X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g) : ℝ :=
  haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ *
    (edgeAbsSmallW 𝒢 q y xsT xs *
      (if IsSmallState 𝒢 ((resModel (smallPrimes 𝒢)).shift Δ y) xsT then
        smallDamping 𝒢 J ℓ q ((resModel (smallPrimes 𝒢)).shift Δ y) else 0)) *
    ((∏ g, ∏ sl : Slot J ℓ,
        if Unshared (C g) sl then 1 else tiltLaw (𝒢.big g) q n (xbT g sl)) *
      ((∏ g, edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p) v ρ
          (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) (X g)) *
        f ⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, fun g => edgeAbsSrcMem Δ (X g)⟩))

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
theorem edgeAbsColMaj_nonneg (𝒢 : GroupFamily S B) (n : ℕ) {q ρ v : ℝ} (hq0 : 0 < q)
    (hρ : 0 ≤ ρ) (hv : 0 ≤ v) (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (C : B → Finset (Fin J)) (f : MState 𝒢 J ℓ Bc → ℝ) (hf0 : ∀ s, 0 ≤ f s) (Δ : ℤ)
    (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) (X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g) :
    0 ≤ edgeAbsColMaj 𝒢 q ρ v n C f Δ xsT xbT y xs X := by
  have h1 : 0 ≤ haarMass (smallPrimes 𝒢) := inv_nonneg.mpr (Nat.cast_nonneg _)
  have h2 : 0 ≤ smallListMass 𝒢 J ℓ :=
    Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
  have h3 : 0 ≤ (if IsSmallState 𝒢 ((resModel (smallPrimes 𝒢)).shift Δ y) xsT then
      smallDamping 𝒢 J ℓ q ((resModel (smallPrimes 𝒢)).shift Δ y) else 0) := by
    split_ifs
    · exact (l38_smallDamping_pos hq0 _).le
    · exact le_rfl
  have h4 : 0 ≤ ∏ g, ∏ sl : Slot J ℓ,
      (if Unshared (C g) sl then 1 else tiltLaw (𝒢.big g) q n (xbT g sl)) := by
    refine Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ => ?_
    split_ifs
    · exact zero_le_one
    · exact hν g _ (xbT g sl).2
  have h5 : 0 ≤ ∏ g, edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
      v ρ (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) (X g) :=
    Finset.prod_nonneg fun g _ => edgeAbsColW_nonneg (fun p => hν g p.1 p.2) hv hρ
      (Schur.reciprocalMass_nonneg _) (C g) Δ (xbT g) (X g)
  unfold edgeAbsColMaj
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2)
    (mul_nonneg (edgeAbsSmallW_nonneg hq0 _ _ _) h3)) (mul_nonneg h4 (mul_nonneg h5 (hf0 _)))

/-! ### One coefficient -/

open _root_.Classical in
omit [DecidableEq S] in
/-- **The column majorant of one coefficient** [S-02:0704–0756]: the measure of `ℋ` and the Schur
weight at the source, times the modulus of the coefficient of a row transition, times a
nonnegative function of the target, is at most `P(r) · sup |K_ν|` times the column majorant for
the step `edgeAbsStepT` of the target lists. Where the coefficient does not vanish the two sides
differ only by the output damping `ρ^{#zeros}` of the target, which is discarded. -/
theorem edgeAbs_col_pointwise (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v : ℝ} (hq0 : 0 < D.q)
    (hρ0 : 0 < D.ρ) (hρ1 : D.ρ ≤ 1) (hv : 0 ≤ v)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (f : MState 𝒢 J ℓ Bc → ℝ) (hf0 : ∀ s, 0 ≤ f s) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) (t : EdgeAbsTail 𝒢 J ℓ Bc) :
    memWeight 𝒢 D.q D.n s * schurWeight v s *
        (‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
          f (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t))) ≤
      auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
        edgeAbsColMaj 𝒢 D.q D.ρ v D.n (D.fam ν).C f (edgeAbsStepT D i ν r t.2.2.1 t.2.2.2)
          t.2.2.1 t.2.2.2 s.y s.xs (fun g => (t.1 g, s.xb g, s.mem g, t.2.1 g)) := by
  have haux : 0 ≤ auxWeight 𝒢.big (D.fam ν).C r := Schur.auxWeight_nonneg _ _ _
  have hsup : (0 : ℝ) ≤ ((D.fam ν).supNorm : ℝ) := NNReal.coe_nonneg _
  have hmaj0 := edgeAbsColMaj_nonneg 𝒢 D.n hq0 hρ0.le hv hν (D.fam ν).C f hf0
    (edgeAbsStepT D i ν r t.2.2.1 t.2.2.2) t.2.2.1 t.2.2.2 s.y s.xs
    (fun g => (t.1 g, s.xb g, s.mem g, t.2.1 g))
  by_cases h : EdgeAbsCond D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)
  · obtain ⟨_, h2, h3, h4, h5, h6, _, _, h9, h10⟩ := id h
    have hΔ : edgeStep D i s (edgeAbsChoice (𝔉 := D.fam) ν r t) =
        edgeAbsStepT D i ν r t.2.2.1 t.2.2.2 :=
      edgeAbsStep_eq_stepT D i s ν r t.2.2.1 t.2.2.2 h5 h6
    obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℤ, Δ = edgeAbsStepT D i ν r t.2.2.1 t.2.2.2 := ⟨_, rfl⟩
    rw [← hΔdef] at hΔ ⊢
    have h4' : IsSmallState 𝒢 ((resModel (smallPrimes 𝒢)).shift Δ s.y) t.2.2.1 := by
      rw [← hΔ]
      exact h4
    have htgt : edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t) =
        (⟨(resModel (smallPrimes 𝒢)).shift Δ s.y, t.2.2.1, t.2.2.2,
          fun g => edgeAbsSrcMem Δ (t.1 g, s.xb g, s.mem g, t.2.1 g)⟩ : MState 𝒢 J ℓ Bc) :=
      congrArg (fun Δ' : ℤ => (⟨(resModel (smallPrimes 𝒢)).shift Δ' s.y, t.2.2.1, t.2.2.2,
        fun g => edgeAbsSrcMem Δ' (t.1 g, s.xb g, s.mem g, t.2.1 g)⟩ : MState 𝒢 J ℓ Bc)) hΔ
    have hmw : memWeight 𝒢 D.q D.n s = haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ *
        bigListMass 𝒢 D.q D.n s.xb * memMass 𝒢 D.q D.n s.mem := by
      unfold memWeight
      exact if_pos h3
    -- the factors of the real prefactor
    have hr10 : 0 ≤ D.ρ ^ memZeros s := pow_nonneg hρ0.le _
    have hPV : 0 ≤ ∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^
        promoCount (edgeAbsChoice (𝔉 := D.fam) ν r t) g)⁻¹ :=
      Finset.prod_nonneg fun g _ =>
        inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
    have hPF : 0 ≤ ∏ g, ∏ sl : Slot J ℓ,
        (if Fresh (edgeAbsChoice (𝔉 := D.fam) ν r t) g sl then
          tiltLaw (𝒢.big g) D.q D.n ((edgeAbsChoice (𝔉 := D.fam) ν r t).xbT g sl) else 1) := by
      refine Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ => ?_
      split_ifs
      · exact hν g _ ((edgeAbsChoice (𝔉 := D.fam) ν r t).xbT g sl).2
      · exact zero_le_one
    have hr20 : 0 ≤ D.ρ ^ memZeros (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) :=
      pow_nonneg hρ0.le _
    have hr2 : D.ρ ^ memZeros (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) ≤ 1 :=
      pow_le_one₀ hρ0.le hρ1
    have hSN : 0 ≤ ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹ :=
      Finset.prod_nonneg fun g _ =>
        inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
    have hd0 : 0 ≤ smallDamping 𝒢 J ℓ D.q s.y := (l38_smallDamping_pos hq0 _).le
    have hd'0 : 0 ≤ smallDamping 𝒢 J ℓ D.q ((resModel (smallPrimes 𝒢)).shift Δ s.y) :=
      (l38_smallDamping_pos hq0 _).le
    have hR : 0 ≤ edgeAbsReal D i s (edgeAbsChoice (𝔉 := D.fam) ν r t) := by
      unfold edgeAbsReal
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg haux hr10) hPV) hPF) hr20)
        (mul_nonneg hSN (mul_nonneg hd0 (l38_smallDamping_pos hq0 _).le))
    have hn : ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ ≤
        auxWeight 𝒢.big (D.fam ν).C r * D.ρ ^ memZeros s *
            (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^
              promoCount (edgeAbsChoice (𝔉 := D.fam) ν r t) g)⁻¹) *
            (∏ g, ∏ sl : Slot J ℓ,
              if Fresh (edgeAbsChoice (𝔉 := D.fam) ν r t) g sl then
                tiltLaw (𝒢.big g) D.q D.n ((edgeAbsChoice (𝔉 := D.fam) ν r t).xbT g sl)
              else 1) *
            D.ρ ^ memZeros (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) *
            ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
              (smallDamping 𝒢 J ℓ D.q s.y *
                smallDamping 𝒢 J ℓ D.q ((resModel (smallPrimes 𝒢)).shift Δ s.y))) *
          ((D.fam ν).supNorm : ℝ) := by
      have h0 := norm_edgeCoef_le D θ i s _ h hR
      unfold edgeAbsReal at h0
      rw [hΔ] at h0
      exact h0
    -- the column weights of the big groups
    have hcol : ∀ g : B,
        edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) D.q D.n p) v D.ρ
            (Graph.primeGroupReciprocalMass (𝒢.big g)) ((D.fam ν).C g) Δ (t.2.2.2 g)
            (t.1 g, s.xb g, s.mem g, t.2.1 g) =
          (∏ sl, edgeAbsSrcW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) D.q D.n p)
              ((D.fam ν).C g) (t.2.2.2 g) sl (s.xb g sl)) *
            ((Graph.primeGroupReciprocalMass (𝒢.big g) ^
                promoCount (edgeAbsChoice (𝔉 := D.fam) ν r t) g)⁻¹ *
              (Graph.finiteMemoryPointMass
                  (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (s.mem g) *
                v ^ (s.mem g).1.val * D.ρ ^ memZeroCount (s.mem g) *
                ∏ sl : Slot J ℓ,
                  (if Fresh (edgeAbsChoice (𝔉 := D.fam) ν r t) g sl then
                    tiltLaw (𝒢.big g) D.q D.n ((edgeAbsChoice (𝔉 := D.fam) ν r t).xbT g sl)
                  else 1))) := by
      intro g
      have hC2 : ∀ sl ∈ t.1 g, Unshared ((D.fam ν).C g) sl := fun sl hsl => (h9 g sl hsl).1
      have hC3 : EdgeAbsPromoValid ((D.fam ν).C g) Δ (s.mem g) (t.2.1 g) (t.2.2.2 g) := by
        intro sl j hj
        obtain ⟨hU, hinj, pr, hpr, h0, _, hx⟩ := h10 g sl j hj
        refine ⟨hU, hinj, pr, hpr, ?_, hx⟩
        rw [← hΔ]
        exact h0
      have hC4 : (edgeAbsNewList Δ (s.mem g) (s.xb g) (t.1 g) (t.2.1 g)).length ≤ Bc := by
        have h0 := edgeNewList_length_le_of_sum D i s _ h2 g
        rw [← hΔ]
        exact h0
      have hp : edgeAbsPromoNum (t.2.1 g) = promoCount (edgeAbsChoice (𝔉 := D.fam) ν r t) g :=
        l38_filter_card_inst _
      have hfr : (∏ sl : Slot J ℓ, if Unshared ((D.fam ν).C g) sl ∧ t.2.1 g sl = none then
            tiltLaw (𝒢.big g) D.q D.n (t.2.2.2 g sl) else 1) =
          ∏ sl : Slot J ℓ, (if Fresh (edgeAbsChoice (𝔉 := D.fam) ν r t) g sl then
            tiltLaw (𝒢.big g) D.q D.n ((edgeAbsChoice (𝔉 := D.fam) ν r t).xbT g sl) else 1) :=
        Finset.prod_congr rfl fun sl _ => ite_congr_of_iff Iff.rfl rfl rfl
      refine (edgeAbsColW_of (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) D.q D.n p)
        v D.ρ (Graph.primeGroupReciprocalMass (𝒢.big g)) ((D.fam ν).C g) Δ (t.2.2.2 g)
        (t.1 g, s.xb g, s.mem g, t.2.1 g) hC2 hC3 hC4).trans ?_
      show (∏ sl, edgeAbsSrcW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) D.q D.n p)
            ((D.fam ν).C g) (t.2.2.2 g) sl (s.xb g sl)) *
          ((Graph.primeGroupReciprocalMass (𝒢.big g) ^ edgeAbsPromoNum (t.2.1 g))⁻¹ *
            (Graph.finiteMemoryPointMass
                (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (s.mem g) *
              v ^ (s.mem g).1.val * D.ρ ^ memZeroCount (s.mem g) *
              ∏ sl : Slot J ℓ, (if Unshared ((D.fam ν).C g) sl ∧ t.2.1 g sl = none then
                tiltLaw (𝒢.big g) D.q D.n (t.2.2.2 g sl) else 1))) = _
      rw [hp, hfr]
    have hsw : schurWeight v s = ∏ g, v ^ (s.mem g).1.val :=
      (Finset.prod_pow_eq_pow_sum Finset.univ (fun g => (s.mem g).1.val) v).symm
    have hρZ : D.ρ ^ memZeros s = ∏ g, D.ρ ^ memZeroCount (s.mem g) :=
      (Finset.prod_pow_eq_pow_sum Finset.univ (fun g => memZeroCount (s.mem g)) D.ρ).symm
    have hmm : memMass 𝒢 D.q D.n s.mem = ∏ g, Graph.finiteMemoryPointMass
        (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (s.mem g) := rfl
    have hprod : ∏ g, edgeAbsColW
          (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) D.q D.n p) v D.ρ
          (Graph.primeGroupReciprocalMass (𝒢.big g)) ((D.fam ν).C g) Δ (t.2.2.2 g)
          (t.1 g, s.xb g, s.mem g, t.2.1 g) =
        (∏ g, ∏ sl, edgeAbsSrcW
            (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) D.q D.n p)
            ((D.fam ν).C g) (t.2.2.2 g) sl (s.xb g sl)) *
          (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^
            promoCount (edgeAbsChoice (𝔉 := D.fam) ν r t) g)⁻¹) *
          memMass 𝒢 D.q D.n s.mem * schurWeight v s * D.ρ ^ memZeros s *
          (∏ g, ∏ sl : Slot J ℓ,
            if Fresh (edgeAbsChoice (𝔉 := D.fam) ν r t) g sl then
              tiltLaw (𝒢.big g) D.q D.n ((edgeAbsChoice (𝔉 := D.fam) ν r t).xbT g sl)
            else 1) := by
      rw [Finset.prod_congr rfl fun g _ => hcol g, hsw, hρZ, hmm]
      simp only [Finset.prod_mul_distrib]
      ring
    -- the labels of the big source list
    have hbl : (∏ g, ∏ sl : Slot J ℓ, if Unshared ((D.fam ν).C g) sl then 1
            else tiltLaw (𝒢.big g) D.q D.n (t.2.2.2 g sl)) *
          (∏ g, ∏ sl, edgeAbsSrcW
            (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) D.q D.n p)
            ((D.fam ν).C g) (t.2.2.2 g) sl (s.xb g sl)) =
        bigListMass 𝒢 D.q D.n s.xb := by
      unfold bigListMass
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun sl _ => ?_
      by_cases hU : Unshared ((D.fam ν).C g) sl
      · rw [if_pos hU, one_mul, edgeAbsSrcW_of_unshared _ _ hU]
      · have hx : s.xb g sl = t.2.2.2 g sl := by
          cases sl with
          | inl i => exact (h6 g i hU).symm
          | inr j => exact absurd trivial hU
        rw [if_neg hU, hx, edgeAbsSrcW_shared_self _ _ hU, mul_one]
    have hW0 : 0 ≤ memWeight 𝒢 D.q D.n s * schurWeight v s :=
      mul_nonneg (memWeight_nonneg 𝒢 D.q D.n hν s) (pow_nonneg hv _)
    have hW : memWeight 𝒢 D.q D.n s * schurWeight v s =
        haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * bigListMass 𝒢 D.q D.n s.xb *
          memMass 𝒢 D.q D.n s.mem * schurWeight v s := by
      rw [hmw]
    have key := l38_col_scalar hW hbl hW0
      (hf0 (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t))) haux hr10 hPV hPF hSN hd0 hd'0
      hsup hn hr2
    refine key.trans (le_of_eq ?_)
    unfold edgeAbsColMaj
    rw [edgeAbsSmallW_of D.q (show IsSmallState 𝒢 s.y s.xs ∧ SharedSmall t.2.2.1 s.xs from
        ⟨h3, fun g i => (h5 g i).symm⟩),
      if_pos h4', hprod, htgt]
  · rw [edgeCoef_of_not_cond D θ i s _ h, norm_zero, zero_mul, mul_zero]
    exact mul_nonneg (mul_nonneg haux hsup) hmaj0

/-! ### The integral over the sources of a target fibre -/

open _root_.Classical in
/-- **The integral of the column majorant over the sources of a target fibre**
[S-02:0704–0756, 0788–0794]: for a fixed step `Δ`, fixed target lists and pattern sets `C` with
at most `T` unshared slots, and every nonnegative symmetric test function `f`, the sum of the
column majorant over the residues, the small source lists and the big source data is at most
`(∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ)` times the integral of `f` over the states with the given target
lists, against the measure of `ℋ` and the Schur weight `v^{j_tot}`. -/
theorem edgeAbs_col_fiber (𝒢 : GroupFamily S B) {q ρ v vMinus Mmax : ℝ} (n : ℕ) {T : ℕ}
    (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (hM : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) q n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (C : B → Finset (Fin J)) (hC : ∀ g, ℓ + (C g).card ≤ T)
    (f : MState 𝒢 J ℓ Bc → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hfsym : MemSymmetric f) (Δ : ℤ)
    (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) :
    ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
        ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g, edgeAbsColMaj 𝒢 q ρ v n C f Δ xsT xbT y xs X ≤
      (∏ _g : S, Schur.groupConst vMinus q T) *
          (∏ _g : B, edgeAbsColConst vMinus ρ v Mmax T) *
        ∑ y' : ResVec (smallPrimes 𝒢), ∑ mem' : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 q n (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) *
            f ⟨y', xsT, xbT, mem'⟩ := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hne : ∀ g : B, Nonempty (Mem 𝒢 Bc g) := fun g => ⟨emptyMem 𝒢 Bc g⟩
  have hhaar : 0 ≤ haarMass (smallPrimes 𝒢) := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hsLM : 0 ≤ smallListMass 𝒢 J ℓ :=
    Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
  obtain ⟨GS, hGS⟩ : ∃ GS : ℝ, GS = ∏ _g : S, Schur.groupConst vMinus q T := ⟨_, rfl⟩
  have hGS0 : 0 ≤ GS := by
    rw [hGS]
    exact Finset.prod_nonneg fun g _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _)
  obtain ⟨KB, hKB⟩ : ∃ KB : ℝ, KB = ∏ _g : B, edgeAbsColConst vMinus ρ v Mmax T := ⟨_, rfl⟩
  obtain ⟨LS, hLS⟩ : ∃ LS : ℝ, LS = ∏ g, ∏ sl : Slot J ℓ,
      (if Unshared (C g) sl then 1 else tiltLaw (𝒢.big g) q n (xbT g sl)) := ⟨_, rfl⟩
  have hLS0 : 0 ≤ LS := by
    rw [hLS]
    refine Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ => ?_
    split_ifs
    · exact zero_le_one
    · exact hν g _ (xbT g sl).2
  obtain ⟨LU, hLU⟩ : ∃ LU : B → ℝ, ∀ g, LU g = ∏ sl : Slot J ℓ,
      (if Unshared (C g) sl then tiltLaw (𝒢.big g) q n (xbT g sl) else 1) :=
    ⟨_, fun _ => rfl⟩
  have hLU0 : ∀ g, 0 ≤ LU g := by
    intro g
    rw [hLU]
    refine Finset.prod_nonneg fun sl _ => ?_
    split_ifs
    · exact hν g _ (xbT g sl).2
    · exact zero_le_one
  have hLSLU : LS * ∏ g, LU g = bigListMass 𝒢 q n xbT := by
    rw [hLS, ← Finset.prod_mul_distrib]
    unfold bigListMass
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [hLU, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun sl _ => ?_
    by_cases hU : Unshared (C g) sl
    · rw [if_pos hU, if_pos hU, one_mul]
    · rw [if_neg hU, if_neg hU, mul_one]
  obtain ⟨pmv, hpmv⟩ : ∃ pmv : (g : B) → Mem 𝒢 Bc g → ℝ, ∀ g u, pmv g u =
      Graph.finiteMemoryPointMass (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) q n z.1) u *
        v ^ u.1.val := ⟨_, fun _ _ => rfl⟩
  have hpmv0 : ∀ g u, 0 ≤ pmv g u := by
    intro g u
    rw [hpmv]
    exact mul_nonneg (l38_pointMass_nonneg
      (μ := fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
      (fun p => hν g p.1 p.2) u) (pow_nonneg hv0 _)
  have hcolW0 : ∀ (g : B) (X : EdgeAbsSrc 𝒢 J ℓ Bc g),
      0 ≤ edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p) v ρ
        (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) X := fun g X =>
    edgeAbsColW_nonneg (fun p => hν g p.1 p.2) hv0 hρ0.le (Schur.reciprocalMass_nonneg _)
      (C g) Δ (xbT g) X
  -- the big groups, for a fixed position of the target
  have hbig : ∀ y' : ResVec (smallPrimes 𝒢),
      ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
          (∏ g, edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p) v ρ
              (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) (X g)) *
            f ⟨y', xsT, xbT, fun g => edgeAbsSrcMem Δ (X g)⟩ ≤
        KB * ((∏ g, LU g) * ∑ mem' : (g : B) → Mem 𝒢 Bc g,
          (∏ g, pmv g (mem' g)) * f ⟨y', xsT, xbT, mem'⟩) := by
    intro y'
    have hten := l38_tensor_rows_le (X := fun g : B => Mem 𝒢 Bc g)
      (I := fun g : B => EdgeAbsSrc 𝒢 J ℓ Bc g)
      (fun g X => edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p) v ρ
        (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) X)
      (fun g X => edgeAbsSrcMem Δ X)
      (fun g u => edgeAbsColConst vMinus ρ v Mmax T * LU g * pmv g u)
      (fun mem' => f ⟨y', xsT, xbT, mem'⟩)
      (fun g X => hcolW0 g X)
      (fun g u => mul_nonneg (mul_nonneg (edgeAbsColConst_nonneg hvm hρ0 hρ1 hv0 T) (hLU0 g))
        (hpmv0 g u))
      (fun g x => by
        have h := edgeAbs_col_group
          (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p) (fun p => hν g p.1 p.2)
          hv hρ0 hρ1 hvm (hVB g) (hM g) (C g) hT (hC g) Δ (xbT g)
          (fun u => f ⟨y', xsT, xbT, Function.update x g u⟩) (fun u => hf0 _)
          (fun m σ y₀ => memSymmetric_update hfsym y' xsT xbT x g m σ y₀)
        refine h.trans (le_of_eq ?_)
        rw [← hLU g, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hpmv]
        ring)
    refine hten.trans (le_of_eq ?_)
    rw [hKB, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  -- a fixed position of the source
  have hy : ∀ y : ResVec (smallPrimes 𝒢),
      ∑ xs : LabelList 𝒢.small J ℓ, ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
          edgeAbsColMaj 𝒢 q ρ v n C f Δ xsT xbT y xs X ≤
        GS * KB * ∑ mem' : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 q n (⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, mem'⟩ :
              MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, mem'⟩ :
              MState 𝒢 J ℓ Bc) *
            f ⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, mem'⟩ := by
    intro y
    obtain ⟨y', hy'⟩ : ∃ y' : ResVec (smallPrimes 𝒢),
        y' = (resModel (smallPrimes 𝒢)).shift Δ y := ⟨_, rfl⟩
    rw [← hy']
    obtain ⟨dmp, hdmp⟩ : ∃ dmp : ℝ,
        dmp = if IsSmallState 𝒢 y' xsT then smallDamping 𝒢 J ℓ q y' else 0 := ⟨_, rfl⟩
    obtain ⟨ind, hind⟩ : ∃ ind : ℝ,
        ind = if IsSmallState 𝒢 y' xsT then (1 : ℝ) else 0 := ⟨_, rfl⟩
    have hdmp0 : 0 ≤ dmp := by
      rw [hdmp]
      split_ifs
      · exact (l38_smallDamping_pos hq0 _).le
      · exact le_rfl
    have hdi : dmp ≤ ind := by
      rw [hdmp, hind]
      by_cases hI : IsSmallState 𝒢 y' xsT
      · rw [if_pos hI, if_pos hI]
        exact l38_smallDamping_le_one hq0 hq1.le hI
      · rw [if_neg hI, if_neg hI]
    have hind0 : 0 ≤ ind := hdmp0.trans hdi
    have hmaj : ∀ (xs : LabelList 𝒢.small J ℓ) (X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g),
        edgeAbsColMaj 𝒢 q ρ v n C f Δ xsT xbT y xs X =
          haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ *
              (edgeAbsSmallW 𝒢 q y xsT xs * dmp) *
            (LS * ((∏ g, edgeAbsColW
                (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p) v ρ
                (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) (X g)) *
              f ⟨y', xsT, xbT, fun g => edgeAbsSrcMem Δ (X g)⟩)) := by
      intro xs X
      unfold edgeAbsColMaj
      rw [hdmp, hLS, hy']
    obtain ⟨Tm, hTm⟩ : ∃ Tm : ℝ, Tm = ∑ mem' : (g : B) → Mem 𝒢 Bc g,
        (∏ g, pmv g (mem' g)) * f ⟨y', xsT, xbT, mem'⟩ := ⟨_, rfl⟩
    have hXsum : ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
          (∏ g, edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p) v ρ
              (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) (X g)) *
            f ⟨y', xsT, xbT, fun g => edgeAbsSrcMem Δ (X g)⟩ ≤ KB * ((∏ g, LU g) * Tm) := by
      rw [hTm]
      exact hbig y'
    have hXsum0 : 0 ≤ ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
          (∏ g, edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p) v ρ
              (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) (X g)) *
            f ⟨y', xsT, xbT, fun g => edgeAbsSrcMem Δ (X g)⟩ :=
      Finset.sum_nonneg fun X _ =>
        mul_nonneg (Finset.prod_nonneg fun g _ => hcolW0 g (X g)) (hf0 _)
    have hxs : ∑ xs : LabelList 𝒢.small J ℓ, edgeAbsSmallW 𝒢 q y xsT xs ≤ GS := by
      rw [hGS]
      exact sum_edgeAbsSmallW_le 𝒢 hq0 hq1 hvm hVS hT hℓT y xsT
    have hL : ∑ xs : LabelList 𝒢.small J ℓ, ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
          edgeAbsColMaj 𝒢 q ρ v n C f Δ xsT xbT y xs X =
        haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ *
            ((∑ xs : LabelList 𝒢.small J ℓ, edgeAbsSmallW 𝒢 q y xsT xs) * dmp) *
          (LS * ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
            (∏ g, edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
                v ρ (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) (X g)) *
              f ⟨y', xsT, xbT, fun g => edgeAbsSrcMem Δ (X g)⟩) :=
      (Finset.sum_congr rfl fun xs _ => Finset.sum_congr rfl fun X _ => hmaj xs X).trans
        (l38_sum_two_factor (haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ) dmp LS
          (fun xs : LabelList 𝒢.small J ℓ => edgeAbsSmallW 𝒢 q y xsT xs)
          (fun X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g =>
            (∏ g, edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
                v ρ (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) (X g)) *
              f ⟨y', xsT, xbT, fun g => edgeAbsSrcMem Δ (X g)⟩))
    have hR : ∑ mem' : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 q n (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) *
            f ⟨y', xsT, xbT, mem'⟩ =
        ind * (haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * bigListMass 𝒢 q n xbT *
          Tm) := by
      rw [hTm, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun mem' _ => ?_
      have hpp : ∏ g, pmv g (mem' g) = memMass 𝒢 q n mem' *
          schurWeight v (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) := by
        rw [Finset.prod_congr rfl fun g _ => hpmv g (mem' g), Finset.prod_mul_distrib]
        exact congrArg (fun t => memMass 𝒢 q n mem' * t)
          (Finset.prod_pow_eq_pow_sum Finset.univ (fun g => (mem' g).1.val) v)
      by_cases hI : IsSmallState 𝒢 y' xsT
      · have hmw : memWeight 𝒢 q n (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) =
            haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * bigListMass 𝒢 q n xbT *
              memMass 𝒢 q n mem' := by
          unfold memWeight
          exact if_pos hI
        have hi1 : ind = 1 := by
          rw [hind]
          exact if_pos hI
        rw [hmw, hi1, hpp]
        ring
      · have hmw : memWeight 𝒢 q n (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) = 0 := by
          unfold memWeight
          exact if_neg hI
        have hi0 : ind = 0 := by
          rw [hind]
          exact if_neg hI
        rw [hmw, hi0]
        ring
    rw [hL, hR]
    calc haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ *
            ((∑ xs : LabelList 𝒢.small J ℓ, edgeAbsSmallW 𝒢 q y xsT xs) * dmp) *
          (LS * ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
            (∏ g, edgeAbsColW (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
                v ρ (Graph.primeGroupReciprocalMass (𝒢.big g)) (C g) Δ (xbT g) (X g)) *
              f ⟨y', xsT, xbT, fun g => edgeAbsSrcMem Δ (X g)⟩)
        ≤ haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * (GS * ind) *
            (LS * (KB * ((∏ g, LU g) * Tm))) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (mul_le_mul hxs hdi hdmp0 hGS0) (mul_nonneg hhaar hsLM))
            (mul_le_mul_of_nonneg_left hXsum hLS0) (mul_nonneg hLS0 hXsum0)
            (mul_nonneg (mul_nonneg hhaar hsLM) (mul_nonneg hGS0 hind0))
      _ = GS * KB * (ind * (haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ *
            bigListMass 𝒢 q n xbT * Tm)) := by
          rw [← hLSLU]
          ring
  rw [← hGS, ← hKB]
  calc ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
        ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g, edgeAbsColMaj 𝒢 q ρ v n C f Δ xsT xbT y xs X
      ≤ ∑ y : ResVec (smallPrimes 𝒢), GS * KB * ∑ mem' : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 q n (⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, mem'⟩ :
              MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, mem'⟩ :
              MState 𝒢 J ℓ Bc) *
            f ⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, mem'⟩ :=
        Finset.sum_le_sum fun y _ => hy y
    _ = GS * KB * ∑ y : ResVec (smallPrimes 𝒢), ∑ mem' : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 q n (⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, mem'⟩ :
              MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, mem'⟩ :
              MState 𝒢 J ℓ Bc) *
            f ⟨(resModel (smallPrimes 𝒢)).shift Δ y, xsT, xbT, mem'⟩ :=
        (Finset.mul_sum _ _ _).symm
    _ = GS * KB * ∑ y' : ResVec (smallPrimes 𝒢), ∑ mem' : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 q n (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) *
            f ⟨y', xsT, xbT, mem'⟩ :=
        congrArg (fun t => GS * KB * t)
          (Equiv.sum_comp (l38_shiftEquiv (smallPrimes 𝒢) Δ)
            (fun y' : ResVec (smallPrimes 𝒢) => ∑ mem' : (g : B) → Mem 𝒢 Bc g,
              memWeight 𝒢 q n (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) *
                schurWeight v (⟨y', xsT, xbT, mem'⟩ : MState 𝒢 J ℓ Bc) *
                f ⟨y', xsT, xbT, mem'⟩))

end Edge

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
