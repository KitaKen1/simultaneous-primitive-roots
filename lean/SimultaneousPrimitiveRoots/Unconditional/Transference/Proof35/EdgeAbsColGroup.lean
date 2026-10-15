module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsColInsert
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The column bound of the absolute edge in one big group

Source: `verification/stage7-sources/S-02.tex`, lines 704–756 and 788–794
(`[S-02:0704–0756, 0788–0794]`).

"For the column, use (eq:edge-joint-memory), (eq:edge-factorial-reversal) in reverse. Original
stores are now ordered retrievals. Their count is controlled by the original input `ρ` factors
after reversed translation, in exactly the form in (eq:promotion-count). The remaining factor
`V_g^{b_g - a_g}` is bounded per group. This proves the column bound." [S-02:0788–0793]

For one big group, a fixed step `Δ` and fixed target labels `τ`:

* `EdgeAbsSrc` — the source data of the group: the stored slots, the source labels, the old
  memory and the promotions; `edgeAbsSrcMem` — the new memory.
* `edgeAbsColW` — the column weight of the source data: the measure of the source
  (`μ̃_g` of the unshared source labels, `λ^{⊗j}/j!` of the memory), the Schur weight `v^j`, the
  source damping `ρ^{#zeros}`, `V_g^{-a}` and `μ̃_g` of the fresh target labels. The shared source
  labels are the target labels.
* `edgeAbs_col_group` — **the one-group column inequality**: the integral of a symmetric
  nonnegative function of the new memory against `edgeAbsColW` is at most
  `edgeAbsColConst · ∏_{sl unshared} μ̃_g(τ(sl))` times its integral against `λ^{⊗j}/j! · v^j`.
  The proof removes the promoted particles (`edgeAbs_remove_sum_le`) and inserts the stored ones
  (`edgeAbs_insert_le`); there are at most `2^{t_g}` sets of stored slots.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- A triple sum of products with a constant factor and a factor of the first variable. -/
theorem l38_sum_three_factor {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (c : ℝ)
    (a : α → ℝ) (r : α → β → γ → ℝ) :
    ∑ x, ∑ y, ∑ z, c * (a x * r x y z) = c * ∑ x, a x * ∑ y, ∑ z, r x y z := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : ∀ y, ∑ z, c * (a x * r x y z) = c * (a x * ∑ z, r x y z) := by
    intro y
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun y _ => h1 y, ← Finset.mul_sum, ← Finset.mul_sum]

section OneGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {g : B}

/-- **The source data of one big group in an edge**: the set of stored slots, the source labels,
the old memory and the promotions (steps 2 and 3 of [S-02:0487–0502]). -/
abbrev EdgeAbsSrc (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) (g : B) : Type :=
  Finset (Slot J ℓ) × (Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) × Mem 𝒢 Bc g ×
    (Slot J ℓ → Option (Fin Bc))

/-- The new memory of the group for the step `Δ` and the source data `X`. -/
def edgeAbsSrcMem (Δ : ℤ) (X : EdgeAbsSrc 𝒢 J ℓ Bc g) : Mem 𝒢 Bc g :=
  memOfList (edgeAbsNewList Δ X.2.2.1 X.2.1 X.1 X.2.2.2)

open _root_.Classical in
/-- **The column weight of the source data of one big group**, for the step `Δ` and the target
labels `τ`: zero unless the stored slots are unshared, the shared source labels are those of the
target, the promotions are admissible and produce the labels `τ`, and the new memory has at most
`Bc` particles; then the product of `μ̃_g` of the unshared source labels, the point mass
`λ^{⊗j}/j!` of the old memory, the Schur weight `v^j`, the source damping `ρ^{#zeros}`, `V_g^{-a}`
and `μ̃_g` of the fresh target labels. -/
def edgeAbsColW (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (v ρ V : ℝ) (Cg : Finset (Fin J)) (Δ : ℤ)
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (X : EdgeAbsSrc 𝒢 J ℓ Bc g) : ℝ :=
  edgeAbsStoreW 1 Cg X.1 * ((∏ sl, edgeAbsSrcW μ Cg τ sl (X.2.1 sl)) *
    (if EdgeAbsPromoValid Cg Δ X.2.2.1 X.2.2.2 τ ∧
        (edgeAbsNewList Δ X.2.2.1 X.2.1 X.1 X.2.2.2).length ≤ Bc then
      (V ^ edgeAbsPromoNum X.2.2.2)⁻¹ *
        (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) X.2.2.1 *
          v ^ X.2.2.1.1.val * ρ ^ memZeroCount X.2.2.1 *
          (∏ sl, if Unshared Cg sl ∧ X.2.2.2 sl = none then μ (τ sl) else 1))
    else 0))

theorem edgeAbsColW_nonneg {μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ} (hμ : ∀ p, 0 ≤ μ p) {v ρ V : ℝ}
    (hv : 0 ≤ v) (hρ : 0 ≤ ρ) (hV : 0 ≤ V) (Cg : Finset (Fin J)) (Δ : ℤ)
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (X : EdgeAbsSrc 𝒢 J ℓ Bc g) :
    0 ≤ edgeAbsColW μ v ρ V Cg Δ τ X := by
  unfold edgeAbsColW
  refine mul_nonneg (edgeAbsStoreW_nonneg zero_le_one Cg X.1)
    (mul_nonneg (Finset.prod_nonneg fun sl _ => edgeAbsSrcW_nonneg hμ Cg τ sl _) ?_)
  split_ifs
  · refine mul_nonneg (inv_nonneg.mpr (pow_nonneg hV _)) (mul_nonneg (mul_nonneg (mul_nonneg
      (l38_pointMass_nonneg hμ _) (pow_nonneg hv _)) (pow_nonneg hρ _))
      (Finset.prod_nonneg fun sl _ => ?_))
    split_ifs
    · exact hμ _
    · exact zero_le_one
  · exact le_rfl

/-- The size of the new memory: the survivors and the stored particles. -/
theorem edgeAbsNewList_length (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (st : Finset (Slot J ℓ))
    (pm : Slot J ℓ → Option (Fin Bc)) :
    (edgeAbsNewList Δ z xg st pm).length = (edgeAbsSurv z pm).length + st.card := by
  have h : (edgeAbsStored Δ xg st).length = st.card := by
    unfold edgeAbsStored
    rw [List.length_map]
    exact l38_length_filter_slotList st
  rw [edgeAbsNewList_eq_surv, List.length_append, List.length_map, h]

/-- The function of the survivors of the old memory through which the new memory enters: the
value of `Ψ` at `T_Δ u ⊔ ((s_h, Δ))_h`, and zero beyond the truncation. -/
def edgeAbsG (Δ : ℤ) (Ψ : Mem 𝒢 Bc g → ℝ) (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (st : Finset (Slot J ℓ)) (l : List (Particle 𝒢 g)) : ℝ :=
  if l.length + st.card ≤ Bc then
    Ψ (memOfList (l.map (shiftParticle Δ) ++ edgeAbsStored Δ xg st))
  else 0

theorem edgeAbsG_nonneg (Δ : ℤ) {Ψ : Mem 𝒢 Bc g → ℝ} (hΨ : ∀ u, 0 ≤ Ψ u)
    (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (st : Finset (Slot J ℓ))
    (l : List (Particle 𝒢 g)) : 0 ≤ edgeAbsG Δ Ψ xg st l := by
  unfold edgeAbsG
  split_ifs
  · exact hΨ _
  · exact le_rfl

open _root_.Classical in
/-- The column weight times a function of the new memory, with the new memory expressed through
the survivors. -/
theorem edgeAbsColW_mul (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (v ρ V : ℝ) (Cg : Finset (Fin J))
    (Δ : ℤ) (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (Ψ : Mem 𝒢 Bc g → ℝ)
    (X : EdgeAbsSrc 𝒢 J ℓ Bc g) :
    edgeAbsColW μ v ρ V Cg Δ τ X * Ψ (edgeAbsSrcMem Δ X) =
      edgeAbsStoreW 1 Cg X.1 * ((∏ sl, edgeAbsSrcW μ Cg τ sl (X.2.1 sl)) *
        (if EdgeAbsPromoValid Cg Δ X.2.2.1 X.2.2.2 τ then
          (V ^ edgeAbsPromoNum X.2.2.2)⁻¹ *
            (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) X.2.2.1 *
              v ^ X.2.2.1.1.val * ρ ^ memZeroCount X.2.2.1 *
              (∏ sl, if Unshared Cg sl ∧ X.2.2.2 sl = none then μ (τ sl) else 1) *
              edgeAbsG Δ Ψ X.2.1 X.1 (edgeAbsSurv X.2.2.1 X.2.2.2))
        else 0)) := by
  have hlen := edgeAbsNewList_length Δ X.2.2.1 X.2.1 X.1 X.2.2.2
  unfold edgeAbsColW edgeAbsSrcMem edgeAbsG
  by_cases h3 : EdgeAbsPromoValid Cg Δ X.2.2.1 X.2.2.2 τ
  · by_cases h4 : (edgeAbsNewList Δ X.2.2.1 X.2.1 X.1 X.2.2.2).length ≤ Bc
    · have h4' : (edgeAbsSurv X.2.2.1 X.2.2.2).length + X.1.card ≤ Bc := by
        rw [← hlen]
        exact h4
      rw [if_pos (show EdgeAbsPromoValid Cg Δ X.2.2.1 X.2.2.2 τ ∧
          (edgeAbsNewList Δ X.2.2.1 X.2.1 X.1 X.2.2.2).length ≤ Bc from ⟨h3, h4⟩),
        if_pos h3, if_pos h4', edgeAbsNewList_eq_surv]
      ring
    · have h4' : ¬(edgeAbsSurv X.2.2.1 X.2.2.2).length + X.1.card ≤ Bc := by
        rw [← hlen]
        exact h4
      rw [if_neg (fun h : EdgeAbsPromoValid Cg Δ X.2.2.1 X.2.2.2 τ ∧
          (edgeAbsNewList Δ X.2.2.1 X.2.1 X.1 X.2.2.2).length ≤ Bc => h4 h.2),
        if_pos h3, if_neg h4']
      ring
  · rw [if_neg (fun h : EdgeAbsPromoValid Cg Δ X.2.2.1 X.2.2.2 τ ∧
        (edgeAbsNewList Δ X.2.2.1 X.2.1 X.1 X.2.2.2).length ≤ Bc => h3 h.1),
      if_neg h3]
    ring

/-- **The constant of one big group in the column bound of the absolute edge**:
`(1 + T v / v₋)^T` for the promotions (`V_g^{-a}`, the Schur weight `v^a` and the count
`j^a` of the reversed promotions against `j!/(j-a)!`), `2^T` for the sets of stored slots,
`max(1, μ̃_g(𝒫_g))^T` for the labels which are integrated out, and
`ρ^{-T} sup_z (z+T)^T ρ^z` for the reversed stores [S-02:0788–0793]. -/
def edgeAbsColConst (vMinus ρ v Mmax : ℝ) (T : ℕ) : ℝ :=
  (1 + (T : ℝ) * v / vMinus) ^ T *
    ((2 : ℝ) ^ T * ((max 1 Mmax) ^ T * (ρ⁻¹ ^ T * Schur.countSup T ρ)))

theorem edgeAbsColConst_nonneg {vMinus ρ v Mmax : ℝ} (hvm : 0 < vMinus) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hv : 0 ≤ v) (T : ℕ) : 0 ≤ edgeAbsColConst vMinus ρ v Mmax T := by
  unfold edgeAbsColConst
  have h1 : 0 ≤ 1 + (T : ℝ) * v / vMinus :=
    add_nonneg zero_le_one (div_nonneg (mul_nonneg (Nat.cast_nonneg T) hv) hvm.le)
  exact mul_nonneg (pow_nonneg h1 T) (mul_nonneg (pow_nonneg zero_le_two T)
    (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) T)
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr hρ0.le) T) (l38_countSup_nonneg T hρ0 hρ1))))

open _root_.Classical in
/-- **The one-group column inequality of the absolute edge** [S-02:0704–0756, 0788–0793]: for a
fixed step `Δ` and fixed target labels `τ` of the big group, and every nonnegative function `Ψ` of
the memory which is symmetric in the particle indices, the integral of `Ψ(new memory)` against the
column weight of the source data is at most
`edgeAbsColConst · ∏_{sl unshared} μ̃_g(τ(sl))` times the integral of `Ψ` against
`λ_g^{⊗j}/j! · v^j`. -/
theorem edgeAbs_col_group (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    {v ρ V vMinus Mmax : ℝ} (hv : 1 ≤ v) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hvm : 0 < vMinus)
    (hV : vMinus ≤ V) (hM : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, μ p ≤ Mmax) (Cg : Finset (Fin J))
    {T : ℕ} (hT : 0 < T) (hC : ℓ + Cg.card ≤ T) (Δ : ℤ)
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (Ψ : Mem 𝒢 Bc g → ℝ) (hΨ0 : ∀ u, 0 ≤ Ψ u)
    (hΨ : ∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      Ψ ⟨m, y ∘ σ⟩ = Ψ ⟨m, y⟩) :
    ∑ X : EdgeAbsSrc 𝒢 J ℓ Bc g, edgeAbsColW μ v ρ V Cg Δ τ X * Ψ (edgeAbsSrcMem Δ X) ≤
      edgeAbsColConst vMinus ρ v Mmax T * (∏ sl, if Unshared Cg sl then μ (τ sl) else 1) *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            Ψ u := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hV0 : 0 < V := lt_of_lt_of_le hvm hV
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ∑ u : Mem 𝒢 Bc g,
      Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val * Ψ u :=
    ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact Finset.sum_nonneg fun u _ =>
      mul_nonneg (mul_nonneg (l38_pointMass_nonneg hμ u) (pow_nonneg hv0 _)) (hΨ0 u)
  obtain ⟨LU, hLU⟩ : ∃ LU : ℝ, LU = ∏ sl, (if Unshared Cg sl then μ (τ sl) else 1) :=
    ⟨_, rfl⟩
  have hLU0 : 0 ≤ LU := by
    rw [hLU]
    refine Finset.prod_nonneg fun sl _ => ?_
    split_ifs
    · exact hμ _
    · exact zero_le_one
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = (1 + (T : ℝ) * v / V) ^ T := ⟨_, rfl⟩
  have hTv : 0 ≤ (T : ℝ) * v := mul_nonneg (Nat.cast_nonneg T) hv0
  have hK10 : 0 ≤ K1 := by
    rw [hK1]
    exact pow_nonneg (add_nonneg zero_le_one (div_nonneg hTv hV0.le)) T
  have hK1le : K1 ≤ (1 + (T : ℝ) * v / vMinus) ^ T := by
    rw [hK1]
    refine pow_le_pow_left₀ (add_nonneg zero_le_one (div_nonneg hTv hV0.le)) ?_ T
    have h : (T : ℝ) * v / V ≤ (T : ℝ) * v / vMinus := div_le_div_of_nonneg_left hTv hvm hV
    linarith
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ,
      K2 = (max 1 Mmax) ^ T * (ρ⁻¹ ^ T * Schur.countSup T ρ) := ⟨_, rfl⟩
  have hK20 : 0 ≤ K2 := by
    rw [hK2]
    exact mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) T)
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr hρ0.le) T) (l38_countSup_nonneg T hρ0 hρ1))
  -- the removal of the promoted particles, for fixed stores and source labels
  have hrem : ∀ (st : Finset (Slot J ℓ)) (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}),
      ∑ z : Mem 𝒢 Bc g, ∑ pm : Slot J ℓ → Option (Fin Bc),
          (if EdgeAbsPromoValid Cg Δ z pm τ then
            (V ^ edgeAbsPromoNum pm)⁻¹ *
              (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z * v ^ z.1.val *
                ρ ^ memZeroCount z *
                (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
                edgeAbsG Δ Ψ xg st (edgeAbsSurv z pm))
          else 0) ≤
        K1 * LU * ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            ρ ^ memZeroCount u * edgeAbsG Δ Ψ xg st (List.ofFn u.2) := by
    intro st xg
    rw [hK1, hLU]
    exact edgeAbs_remove_sum_le μ hμ hv0 hρ0.le hρ1.le hV0 Cg hT hC Δ τ (edgeAbsG Δ Ψ xg st)
      (fun l => edgeAbsG_nonneg Δ hΨ0 xg st l)
  -- the insertion of the stored particles, for fixed stores
  have hins : ∀ st : Finset (Slot J ℓ), (∀ sl ∈ st, Unshared Cg sl) →
      ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}, (∏ sl, edgeAbsSrcW μ Cg τ sl (xg sl)) *
          ∑ u : Mem 𝒢 Bc g,
            Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
              ρ ^ memZeroCount u * edgeAbsG Δ Ψ xg st (List.ofFn u.2) ≤ K2 * R := by
    intro st hst
    rw [hK2, hR]
    refine (le_of_eq (Finset.sum_congr rfl fun xg _ =>
      congrArg (fun t => (∏ sl, edgeAbsSrcW μ Cg τ sl (xg sl)) * t)
        (Finset.sum_congr rfl fun u _ => ?_))).trans
      (edgeAbs_insert_le μ hμ hv hρ0 hρ1 hM Cg hT hC Δ τ st hst Ψ hΨ0 hΨ)
    unfold edgeAbsG
    rw [List.length_ofFn]
  -- fixed stores
  have hst : ∀ st : Finset (Slot J ℓ),
      ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}, ∑ z : Mem 𝒢 Bc g,
          ∑ pm : Slot J ℓ → Option (Fin Bc),
            edgeAbsColW μ v ρ V Cg Δ τ (st, xg, z, pm) *
              Ψ (edgeAbsSrcMem Δ (st, xg, z, pm)) ≤
        edgeAbsStoreW 1 Cg st * (K1 * LU * (K2 * R)) := by
    intro st
    have e : ∀ (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (z : Mem 𝒢 Bc g)
        (pm : Slot J ℓ → Option (Fin Bc)),
        edgeAbsColW μ v ρ V Cg Δ τ (st, xg, z, pm) * Ψ (edgeAbsSrcMem Δ (st, xg, z, pm)) =
          edgeAbsStoreW 1 Cg st * ((∏ sl, edgeAbsSrcW μ Cg τ sl (xg sl)) *
            (if EdgeAbsPromoValid Cg Δ z pm τ then
              (V ^ edgeAbsPromoNum pm)⁻¹ *
                (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z *
                  v ^ z.1.val * ρ ^ memZeroCount z *
                  (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
                  edgeAbsG Δ Ψ xg st (edgeAbsSurv z pm))
            else 0)) :=
      fun xg z pm => edgeAbsColW_mul μ v ρ V Cg Δ τ Ψ (st, xg, z, pm)
    have hS0 : 0 ≤ edgeAbsStoreW 1 Cg st := edgeAbsStoreW_nonneg zero_le_one Cg st
    by_cases hC2 : ∀ sl ∈ st, Unshared Cg sl
    · have hswap : ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
            (∏ sl, edgeAbsSrcW μ Cg τ sl (xg sl)) * (K1 * LU * ∑ u : Mem 𝒢 Bc g,
              Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
                ρ ^ memZeroCount u * edgeAbsG Δ Ψ xg st (List.ofFn u.2)) =
          K1 * LU * ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
            (∏ sl, edgeAbsSrcW μ Cg τ sl (xg sl)) * ∑ u : Mem 𝒢 Bc g,
              Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
                ρ ^ memZeroCount u * edgeAbsG Δ Ψ xg st (List.ofFn u.2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun xg _ => by ring
      calc ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}, ∑ z : Mem 𝒢 Bc g,
            ∑ pm : Slot J ℓ → Option (Fin Bc),
              edgeAbsColW μ v ρ V Cg Δ τ (st, xg, z, pm) *
                Ψ (edgeAbsSrcMem Δ (st, xg, z, pm))
          = edgeAbsStoreW 1 Cg st * ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
              (∏ sl, edgeAbsSrcW μ Cg τ sl (xg sl)) * ∑ z : Mem 𝒢 Bc g,
                ∑ pm : Slot J ℓ → Option (Fin Bc),
                  (if EdgeAbsPromoValid Cg Δ z pm τ then
                    (V ^ edgeAbsPromoNum pm)⁻¹ *
                      (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z *
                        v ^ z.1.val * ρ ^ memZeroCount z *
                        (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
                        edgeAbsG Δ Ψ xg st (edgeAbsSurv z pm))
                  else 0) :=
            (Finset.sum_congr rfl fun xg _ => Finset.sum_congr rfl fun z _ =>
              Finset.sum_congr rfl fun pm _ => e xg z pm).trans
              (l38_sum_three_factor (edgeAbsStoreW 1 Cg st)
                (fun xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g} =>
                  ∏ sl, edgeAbsSrcW μ Cg τ sl (xg sl))
                (fun (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (z : Mem 𝒢 Bc g)
                    (pm : Slot J ℓ → Option (Fin Bc)) =>
                  if EdgeAbsPromoValid Cg Δ z pm τ then
                    (V ^ edgeAbsPromoNum pm)⁻¹ *
                      (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z *
                        v ^ z.1.val * ρ ^ memZeroCount z *
                        (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
                        edgeAbsG Δ Ψ xg st (edgeAbsSurv z pm))
                  else 0))
        _ ≤ edgeAbsStoreW 1 Cg st * ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
              (∏ sl, edgeAbsSrcW μ Cg τ sl (xg sl)) * (K1 * LU * ∑ u : Mem 𝒢 Bc g,
                Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u *
                  v ^ u.1.val * ρ ^ memZeroCount u * edgeAbsG Δ Ψ xg st (List.ofFn u.2)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun xg _ =>
              mul_le_mul_of_nonneg_left (hrem st xg)
                (Finset.prod_nonneg fun sl _ => edgeAbsSrcW_nonneg hμ Cg τ sl _)) hS0
        _ = edgeAbsStoreW 1 Cg st * (K1 * LU * ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
              (∏ sl, edgeAbsSrcW μ Cg τ sl (xg sl)) * ∑ u : Mem 𝒢 Bc g,
                Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u *
                  v ^ u.1.val * ρ ^ memZeroCount u * edgeAbsG Δ Ψ xg st (List.ofFn u.2)) :=
            congrArg (fun t => edgeAbsStoreW 1 Cg st * t) hswap
        _ ≤ edgeAbsStoreW 1 Cg st * (K1 * LU * (K2 * R)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hins st hC2) (mul_nonneg hK10 hLU0)) hS0
    · have hz : edgeAbsStoreW 1 Cg st = 0 := by
        unfold edgeAbsStoreW
        exact if_neg hC2
      rw [hz, zero_mul]
      refine le_of_eq (Finset.sum_eq_zero fun xg _ => Finset.sum_eq_zero fun z _ =>
        Finset.sum_eq_zero fun pm _ => ?_)
      rw [e xg z pm, hz, zero_mul]
  have hsplit : ∑ X : EdgeAbsSrc 𝒢 J ℓ Bc g,
        edgeAbsColW μ v ρ V Cg Δ τ X * Ψ (edgeAbsSrcMem Δ X) =
      ∑ st : Finset (Slot J ℓ), ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
        ∑ z : Mem 𝒢 Bc g, ∑ pm : Slot J ℓ → Option (Fin Bc),
          edgeAbsColW μ v ρ V Cg Δ τ (st, xg, z, pm) *
            Ψ (edgeAbsSrcMem Δ (st, xg, z, pm)) := by
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun st _ => ?_)
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun xg _ => ?_)
    exact Fintype.sum_prod_type _
  have hstores : ∑ st : Finset (Slot J ℓ), edgeAbsStoreW 1 Cg st ≤ (2 : ℝ) ^ T := by
    have h := sum_edgeAbsStoreW_le (v := 1) le_rfl Cg hC
    rw [mul_one] at h
    exact h
  have hKR : 0 ≤ K1 * LU * (K2 * R) :=
    mul_nonneg (mul_nonneg hK10 hLU0) (mul_nonneg hK20 hR0)
  rw [hsplit, ← hR, ← hLU]
  calc ∑ st : Finset (Slot J ℓ), ∑ xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
        ∑ z : Mem 𝒢 Bc g, ∑ pm : Slot J ℓ → Option (Fin Bc),
          edgeAbsColW μ v ρ V Cg Δ τ (st, xg, z, pm) *
            Ψ (edgeAbsSrcMem Δ (st, xg, z, pm))
      ≤ ∑ st : Finset (Slot J ℓ), edgeAbsStoreW 1 Cg st * (K1 * LU * (K2 * R)) :=
        Finset.sum_le_sum fun st _ => hst st
    _ = (∑ st : Finset (Slot J ℓ), edgeAbsStoreW 1 Cg st) * (K1 * LU * (K2 * R)) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ (2 : ℝ) ^ T * (K1 * LU * (K2 * R)) := mul_le_mul_of_nonneg_right hstores hKR
    _ = K1 * ((2 : ℝ) ^ T * K2 * (LU * R)) := by ring
    _ ≤ (1 + (T : ℝ) * v / vMinus) ^ T * ((2 : ℝ) ^ T * K2 * (LU * R)) :=
        mul_le_mul_of_nonneg_right hK1le
          (mul_nonneg (mul_nonneg (pow_nonneg zero_le_two T) hK20) (mul_nonneg hLU0 hR0))
    _ = edgeAbsColConst vMinus ρ v Mmax T * LU * R := by
        unfold edgeAbsColConst
        rw [← hK2]
        ring

end OneGroup

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
