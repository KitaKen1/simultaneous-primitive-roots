module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RareCol
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Scalars
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# [S] Lemma 3.9 (rare transfer), proved

Source: `verification/stage7-sources/S-02.tex`, lines 824–894 (`[S-02:0824–0894]`).

"With the memory truncation in (eq:memory-truncation), the aggregate of all dirty terms of any
edge has norm at most `2 L^{C_a} (B/𝒟)^{1/2}`, after enlarging `C_a` independently of `J` if
necessary."

`rareTransfer : RareTransfer`, with the exponent `C_d = memAbsExponent P m C₁` of Lemma 3.8 (no
enlargement is needed).

* `edgeDirtyPromo`, `edgeDirtyStore`, `edgeDirty_eq_promo_add_store` — the dirty part is the sum of
  the terms with a promotion and of the terms with a store and no promotion.
* `rare_promo_opBound` — "the promotion part improves its row bound to `L^{C_a} B/𝒟`, while its
  column bound remains `L^{C_a}`. Schur's test gives the first half of (eq:dirty-norm)":
  `rare_rowBound` and the column bound of Lemma 3.8.
* `rare_store_opBound` — "terms with stores and no promotion have the same improvement in their
  column bound": the row bound of Lemma 3.8 and `rare_colBound`.
* `rare_dirty_opBound` — "add these two bounds".
* `eventually_rareArith` — the arithmetic hypotheses for the prime groups of Definition 3.1 and
  large `x`: `U ≤ exp(ℓ|𝒮|L^b) < exp(L^c) ≤ p` [S-02:0863–0865], and `0 < |k| ≤ L^{C₂} < p`, so
  `k` is invertible modulo every big prime. This is the only place where `C₂` enters; the
  threshold depends on `P` and `C₂`.

The cutoff `B` of the statement is `memCutoff L = ⌈L²⌉`, but the proof works for every cutoff
(`rare_dirty_opBound`): only "at most `B` old pending particles" is used.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

/-! ### Kernels dominated by a kernel with row and column bounds -/

theorem rare_rowBound_mono_kernel {X Ξ : Type*} [Fintype Ξ] {w : X → ℝ} {κ κ' : X → Ξ → ℝ}
    {tgt : X → Ξ → X} {R : ℝ} (h : RowBound w κ tgt R) (hw : ∀ s, 0 ≤ w s)
    (hκ : ∀ s ξ, κ' s ξ ≤ κ s ξ) : RowBound w κ' tgt R :=
  fun s => (Finset.sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_right (hκ s ξ) (hw _)).trans (h s)

theorem rare_colBound_mono_kernel {X Ξ : Type*} [Fintype X] [Fintype Ξ] {m w : X → ℝ}
    {Sy : (X → ℝ) → Prop} {κ κ' : X → Ξ → ℝ} {tgt : X → Ξ → X} {C : ℝ}
    (h : ColBound m w Sy κ tgt C) (hm : ∀ s, 0 ≤ m s) (hw : ∀ s, 0 ≤ w s)
    (hκ : ∀ s ξ, κ' s ξ ≤ κ s ξ) : ColBound m w Sy κ' tgt C :=
  fun f hf0 hfS => (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_right (hκ s ξ) (hf0 _))
    (mul_nonneg (hm s) (hw s))).trans (h f hf0 hfS)

/-- `√(R F C) ≤ Λ √F` when `0 ≤ R, C ≤ Λ` and `F ≥ 0`. -/
theorem rare_sqrt_scalar {R C Λ F : ℝ} (hR0 : 0 ≤ R) (hC0 : 0 ≤ C) (hR : R ≤ Λ) (hC : C ≤ Λ)
    (hF : 0 ≤ F) : Real.sqrt (R * F * C) ≤ Λ * Real.sqrt F := by
  have hΛ : 0 ≤ Λ := hR0.trans hR
  have h1 : R * F * C ≤ Λ ^ 2 * F := by
    calc R * F * C ≤ Λ * F * Λ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hR hF) hC hC0 (mul_nonneg hΛ hF)
      _ = Λ ^ 2 * F := by ring
  calc Real.sqrt (R * F * C) ≤ Real.sqrt (Λ ^ 2 * F) := Real.sqrt_le_sqrt h1
    _ = Λ * Real.sqrt F := by rw [Real.sqrt_mul (sq_nonneg Λ), Real.sqrt_sq hΛ]

/-- `K · (X / (2K)) = X/2`. -/
theorem rare_half {K : ℝ} (hK : 0 < K) (X : ℝ) : K * (1 / (2 * K) * X) = 1 / 2 * X := by
  have h : K * (1 / (2 * K)) = 1 / 2 := by
    rw [mul_one_div, div_eq_iff (mul_pos two_pos hK).ne']
    ring
  calc K * (1 / (2 * K) * X) = K * (1 / (2 * K)) * X := by ring
    _ = 1 / 2 * X := by rw [h]

/-! ### The two parts of the dirty edge -/

section Dirty

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type} [Fintype N]

open _root_.Classical in
/-- **The promotion part of the dirty edge** [S-02:0849]: the terms with at least one
promotion. -/
def edgeDirtyPromo (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (i : ℕ) :
    (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  rowOp (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
      if HasPromo ξ.2.1 then edgeFullCoef D (fun _ => 1) θ i s ξ else 0)
    (edgeFullTgt D i)

open _root_.Classical in
/-- **The store part of the dirty edge** [S-02:0877–0878]: the "terms with stores and no
promotion". -/
def edgeDirtyStore (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (i : ℕ) :
    (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  rowOp (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
      if ¬HasPromo ξ.2.1 ∧ HasStore ξ.2.1 then edgeFullCoef D (fun _ => 1) θ i s ξ else 0)
    (edgeFullTgt D i)

/-- `ℰ_{i,dirty}` is the sum of its promotion part and of its store part: "a term is dirty if it
has at least one store or promotion" [S-02:0829]. -/
theorem edgeDirty_eq_promo_add_store (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (i : ℕ) :
    edgeDirty D Bc θ i = edgeDirtyPromo D Bc θ i + edgeDirtyStore D Bc θ i := by
  refine LinearMap.ext fun F => funext fun s => ?_
  simp only [edgeDirty, edgeDirtyPromo, edgeDirtyStore, LinearMap.add_apply, Pi.add_apply,
    rowOp_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  by_cases hP : HasPromo ξ.2.1
  · have hnc : ¬IsClean ξ.2.1 := fun hc => by
      obtain ⟨g, sl, j, hj⟩ := hP
      have h0 := hc.2 g sl
      rw [hj] at h0
      exact Option.some_ne_none j h0
    rw [if_neg hnc, if_pos hP,
      if_neg (fun h : ¬HasPromo ξ.2.1 ∧ HasStore ξ.2.1 => h.1 hP), zero_mul, add_zero]
  · by_cases hS : HasStore ξ.2.1
    · have hnc : ¬IsClean ξ.2.1 := fun hc => by
        obtain ⟨g, sl, hsl⟩ := hS
        rw [hc.1 g] at hsl
        exact Finset.notMem_empty sl hsl
      rw [if_neg hnc, if_neg hP,
        if_pos (⟨hP, hS⟩ : ¬HasPromo ξ.2.1 ∧ HasStore ξ.2.1), zero_mul, zero_add]
    · have hc : IsClean ξ.2.1 :=
        ⟨fun g => Finset.eq_empty_of_forall_notMem fun sl hsl => hS ⟨g, sl, hsl⟩,
          fun g sl => promo_none_of_not_hasPromo hP g sl⟩
      rw [if_pos hc, if_neg hP,
        if_neg (fun h : ¬HasPromo ξ.2.1 ∧ HasStore ξ.2.1 => hS h.2), zero_mul, add_zero]

open _root_.Classical in
/-- **The first half of (eq:dirty-norm)** [S-02:0875–0877]: "the promotion part improves its row
bound to `L^{C_a} B/𝒟`, while its column bound remains `L^{C_a}`. Schur's test gives the first
half". Here `R₀`, `C₀` are the row and column constants of Lemma 3.8 and `F = B/𝒟`. -/
theorem rare_promo_opBound (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (hA : RareArith 𝒢 ℓ (edgeSign i * D.k)) :
    OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeDirtyPromo D Bc θ i)
      (Real.sqrt (patternMass D.fam *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) *
          ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ)) *
        (patternMass D.fam *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T))))) := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s := memWeight_nonneg 𝒢 D.q D.n hν
  have hw : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ schurWeight v s := fun s => (schurWeight_pos hvpos s).le
  have hR0 : 0 ≤ patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) *
      ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ)) :=
    mul_nonneg (mul_nonneg (patternMass_nonneg _) (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
      (Finset.prod_nonneg fun _ _ => edgeAbsRowConst_nonneg hρ0 hρ1 hv0 _))
      (Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hC0 : 0 ≤ patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) :=
    mul_nonneg (patternMass_nonneg _) (mul_nonneg
      (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
      (Finset.prod_nonneg fun _ _ => edgeAbsColConst_nonneg hvm hρ0 hρ1 hv0 _))
  have hcol : ColBound (memWeight 𝒢 D.q D.n) (schurWeight v) (fun f => MemSymmetric f)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        if HasPromo ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) (edgeFullTgt D i)
      (patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T))) :=
    rare_colBound_mono_kernel
      (edgeAbs_colBound D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hM hT hℓT hC) hm hw
      (fun s ξ => by
        show (if HasPromo ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) ≤
          ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖
        split_ifs
        · exact le_rfl
        · exact norm_nonneg _)
  exact opBound_of_row_col (memWeight 𝒢 D.q D.n) (schurWeight v) hm
    (fun s => schurWeight_pos hvpos s) (fun F => MemSymmetric F) (fun f => MemSymmetric f)
    (fun F hF => MemSymmetric.normSq_div hF v)
    (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
      if HasPromo ξ.2.1 then edgeFullCoef D (fun _ => 1) θ i s ξ else 0)
    (edgeFullTgt D i)
    (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
      if HasPromo ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0)
    (fun s ξ => by
      show ‖(if HasPromo ξ.2.1 then edgeFullCoef D (fun _ => 1) θ i s ξ else 0)‖ ≤
        (if HasPromo ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0)
      split_ifs
      · exact le_rfl
      · exact norm_zero.le)
    _ _ hR0 hC0
    (rare_rowBound D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hM hT hℓT hC hA) hcol

open _root_.Classical in
/-- **The second half of (eq:dirty-norm)** [S-02:0877–0881]: "terms with stores and no promotion
have the same improvement in their column bound by reversing the edge". -/
theorem rare_store_opBound (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (hA : RareArith 𝒢 ℓ (edgeSign i * D.k)) :
    OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeDirtyStore D Bc θ i)
      (Real.sqrt (patternMass D.fam *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) *
        (patternMass D.fam *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
          ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ))))) := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s := memWeight_nonneg 𝒢 D.q D.n hν
  have hw : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ schurWeight v s := fun s => (schurWeight_pos hvpos s).le
  have hR0 : 0 ≤ patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) :=
    mul_nonneg (patternMass_nonneg _) (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
      (Finset.prod_nonneg fun _ _ => edgeAbsRowConst_nonneg hρ0 hρ1 hv0 _))
      (Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  have hC0 : 0 ≤ patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
      ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ)) :=
    mul_nonneg (mul_nonneg (patternMass_nonneg _) (mul_nonneg
      (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
      (Finset.prod_nonneg fun _ _ => edgeAbsColConst_nonneg hvm hρ0 hρ1 hv0 _)))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hrow : RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) (edgeFullTgt D i)
      (patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T)) :=
    rare_rowBound_mono_kernel
      (edgeAbs_rowBound D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hM hT hℓT hC) hw
      (fun s ξ => by
        show (if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) ≤
          ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖
        split_ifs
        · exact le_rfl
        · exact norm_nonneg _)
  exact opBound_of_row_col (memWeight 𝒢 D.q D.n) (schurWeight v) hm
    (fun s => schurWeight_pos hvpos s) (fun F => MemSymmetric F) (fun f => MemSymmetric f)
    (fun F hF => MemSymmetric.normSq_div hF v)
    (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
      if ¬HasPromo ξ.2.1 ∧ HasStore ξ.2.1 then edgeFullCoef D (fun _ => 1) θ i s ξ else 0)
    (edgeFullTgt D i)
    (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
      if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0)
    (fun s ξ => by
      show ‖(if ¬HasPromo ξ.2.1 ∧ HasStore ξ.2.1 then edgeFullCoef D (fun _ => 1) θ i s ξ
          else 0)‖ ≤
        (if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0)
      by_cases h : ¬HasPromo ξ.2.1 ∧ HasStore ξ.2.1
      · rw [if_pos h, if_pos h.2]
      · rw [if_neg h, norm_zero]
        split_ifs
        · exact norm_nonneg _
        · exact le_rfl)
    _ _ hR0 hC0 hrow
    (rare_colBound D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hM hT hℓT hC hA)

/-- **[S] Lemma 3.9 for an arbitrary family of groups and an arbitrary cutoff**
[S-02:0838–0845, 0882]: "add these two bounds". If the row and the column constants of Lemma 3.8
are at most `Λ`, the dirty part of the edge has norm at most `2 Λ (B/𝒟)^{1/2}` on `ℋ`. -/
theorem rare_dirty_opBound (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax Λ : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (hA : RareArith 𝒢 ℓ (edgeSign i * D.k))
    (hRow : patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) ≤ Λ)
    (hCol : patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) ≤ Λ) :
    OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeDirty D Bc θ i)
      (2 * Λ * Real.sqrt ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ))) := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s := memWeight_nonneg 𝒢 D.q D.n hν
  have hP := rare_promo_opBound (Bc := Bc) D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hM hT
    hℓT hC hA
  have hSt := rare_store_opBound (Bc := Bc) D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hM hT
    hℓT hC hA
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, R₀ = patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = (Bc : ℝ) / (omissionNumber S J ℓ : ℝ) := ⟨_, rfl⟩
  rw [← hR₀, ← hC₀, ← hF] at hP hSt
  rw [← hR₀] at hRow
  rw [← hC₀] at hCol
  rw [← hF]
  have hR₀0 : 0 ≤ R₀ := by
    rw [hR₀]
    exact mul_nonneg (patternMass_nonneg _) (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
      (Finset.prod_nonneg fun _ _ => edgeAbsRowConst_nonneg hρ0 hρ1 hv0 _))
      (Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀]
    exact mul_nonneg (patternMass_nonneg _) (mul_nonneg
      (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
      (Finset.prod_nonneg fun _ _ => edgeAbsColConst_nonneg hvm hρ0 hρ1 hv0 _))
  have hF0 : 0 ≤ F := by
    rw [hF]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsP : Real.sqrt (R₀ * F * C₀) ≤ Λ * Real.sqrt F :=
    rare_sqrt_scalar hR₀0 hC₀0 hRow hCol hF0
  have hsS : Real.sqrt (R₀ * (C₀ * F)) ≤ Λ * Real.sqrt F := by
    have e : R₀ * (C₀ * F) = C₀ * F * R₀ := by ring
    rw [e]
    exact rare_sqrt_scalar hC₀0 hR₀0 hCol hRow hF0
  intro G hG
  have h1 := hP G hG
  have h2 := hSt G hG
  have hwG := wNorm_nonneg (memWeight 𝒢 D.q D.n) G
  have e : edgeDirty D Bc θ i G = edgeDirtyPromo D Bc θ i G + edgeDirtyStore D Bc θ i G := by
    rw [edgeDirty_eq_promo_add_store]
    rfl
  rw [e]
  calc wNorm (memWeight 𝒢 D.q D.n) (edgeDirtyPromo D Bc θ i G + edgeDirtyStore D Bc θ i G)
      ≤ wNorm (memWeight 𝒢 D.q D.n) (edgeDirtyPromo D Bc θ i G) +
          wNorm (memWeight 𝒢 D.q D.n) (edgeDirtyStore D Bc θ i G) :=
        wNorm_add_le hm _ _
    _ ≤ Real.sqrt (R₀ * F * C₀) * wNorm (memWeight 𝒢 D.q D.n) G +
          Real.sqrt (R₀ * (C₀ * F)) * wNorm (memWeight 𝒢 D.q D.n) G := add_le_add h1 h2
    _ ≤ Λ * Real.sqrt F * wNorm (memWeight 𝒢 D.q D.n) G +
          Λ * Real.sqrt F * wNorm (memWeight 𝒢 D.q D.n) G :=
        add_le_add (mul_le_mul_of_nonneg_right hsP hwG) (mul_le_mul_of_nonneg_right hsS hwG)
    _ = 2 * Λ * Real.sqrt F * wNorm (memWeight 𝒢 D.q D.n) G := by ring

end Dirty

/-! ### The arithmetic hypotheses for the prime groups of Definition 3.1 -/

/-- **"`U ≤ exp(ℓ|𝒮|L^b) < exp(L^c) ≤ p` for sufficiently large `x`"** [S-02:0863–0865], and
"the quantities `F, k, D_ℬ` are invertible modulo every `p`" [S-02:0867–0868] for `k`: since
`0 < |k| ≤ L^{C₂} < exp(L^c) ≤ p`, no big prime divides `σ_i k`. For all sufficiently large `x`
(depending on `P` and `C₂`), every system of prime groups, every `k` with `0 < |k| ≤ L^{C₂}` and
every edge `i`. -/
theorem eventually_rareArith (P : GroupParams) (C₂ : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (k : ℤ), k ≠ 0 → |(k : ℝ)| ≤ Real.log x ^ C₂ → ∀ i : ℕ,
        RareArith 𝔊.toGroupFamily P.ℓ (edgeSign i * k) := by
  have hcb : 0 < P.c - P.b := sub_pos.mpr P.b_lt_c
  have hℓ : (0 : ℝ) < (P.ℓ : ℝ) := Nat.cast_pos.mpr P.ℓ_pos
  have hK1 : (0 : ℝ) < (P.ℓ : ℝ) * P.C₀ := mul_pos hℓ P.C₀_pos
  have hK2 : (0 : ℝ) < |C₂| + 1 := by positivity
  filter_upwards [eventually_log_ge 1,
    eventually_loglog_le (P.c - P.b) (1 / (2 * ((P.ℓ : ℝ) * P.C₀))) hcb
      (one_div_pos.mpr (mul_pos two_pos hK1)),
    eventually_loglog_le P.c (1 / (2 * (|C₂| + 1))) P.c_pos
      (one_div_pos.mpr (mul_pos two_pos hK2))] with x hL h1 h2
  intro S B _ _ _ _ 𝔊 k hk0 hk i
  have hL0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL
  have hT0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  have hLc : 0 < Real.log x ^ P.c := Real.rpow_pos_of_pos hL0 _
  refine ⟨𝔊.prime_small, 𝔊.prime_big, 𝔊.disjoint_small, ?_, ?_⟩
  · -- no big prime divides `σ_i k`
    intro g p hp hdvd
    have hk' : (p : ℤ) ∣ k := by
      unfold edgeSign at hdvd
      by_cases hi : i % 2 = 0
      · rw [if_pos hi, one_mul] at hdvd
        exact hdvd
      · rw [if_neg hi, neg_one_mul] at hdvd
        exact dvd_neg.mp hdvd
    have h7 : (p : ℤ) ≤ |k| := Int.le_of_dvd (abs_pos.mpr hk0) ((dvd_abs _ _).mpr hk')
    have h8 : (p : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast h7
    have h9 : Real.exp (Real.log x ^ P.c) ≤ (p : ℝ) := 𝔊.big_ge g p hp
    have hB1 : Real.log (Real.log x) * C₂ ≤ (|C₂| + 1) * Real.log (Real.log x) := by
      calc Real.log (Real.log x) * C₂ = C₂ * Real.log (Real.log x) := mul_comm _ _
        _ ≤ (|C₂| + 1) * Real.log (Real.log x) :=
            mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₂]) hT0
    have hB2 : (|C₂| + 1) * Real.log (Real.log x) ≤
        (|C₂| + 1) * (1 / (2 * (|C₂| + 1)) * Real.log x ^ P.c) :=
      mul_le_mul_of_nonneg_left h2 hK2.le
    have hB3 := rare_half hK2 (Real.log x ^ P.c)
    have h10 : Real.log x ^ C₂ < Real.exp (Real.log x ^ P.c) := by
      rw [Real.rpow_def_of_pos hL0 C₂]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  · -- products of `ℓ` labels from each small group are smaller than the big primes
    intro u g p hp
    have hE : ∀ (g' : S) (j : Fin P.ℓ), ((u g' j : ℕ) : ℝ) ≤ Real.exp (Real.log x ^ P.b) :=
      fun g' j => 𝔊.small_le g' _ (u g' j).2
    have h3 : ((∏ g', ∏ j, (u g' j : ℕ) : ℕ) : ℝ) ≤
        Real.exp ((Fintype.card S : ℝ) * ((P.ℓ : ℝ) * Real.log x ^ P.b)) := by
      rw [Nat.cast_prod]
      calc ∏ g' : S, ((∏ j : Fin P.ℓ, (u g' j : ℕ) : ℕ) : ℝ)
          ≤ ∏ _g' : S, Real.exp ((P.ℓ : ℝ) * Real.log x ^ P.b) := by
            refine Finset.prod_le_prod (fun g' _ => Nat.cast_nonneg _) fun g' _ => ?_
            rw [Nat.cast_prod]
            calc ∏ j : Fin P.ℓ, ((u g' j : ℕ) : ℝ)
                ≤ ∏ _j : Fin P.ℓ, Real.exp (Real.log x ^ P.b) :=
                  Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j _ => hE g' j
              _ = Real.exp ((P.ℓ : ℝ) * Real.log x ^ P.b) := by
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
                    Real.exp_nat_mul (Real.log x ^ P.b) P.ℓ]
        _ = Real.exp ((Fintype.card S : ℝ) * ((P.ℓ : ℝ) * Real.log x ^ P.b)) := by
            rw [Finset.prod_const, Finset.card_univ,
              Real.exp_nat_mul ((P.ℓ : ℝ) * Real.log x ^ P.b) (Fintype.card S)]
    have e : Real.log x ^ (P.c - P.b) * Real.log x ^ P.b = Real.log x ^ P.c := by
      rw [← Real.rpow_add hL0, sub_add_cancel]
    have hLb : 0 ≤ Real.log x ^ P.b := Real.rpow_nonneg hL0.le _
    have hS : (Fintype.card S : ℝ) ≤ P.C₀ * Real.log (Real.log x) := 𝔊.card_small_le
    have hA1 : (Fintype.card S : ℝ) * ((P.ℓ : ℝ) * Real.log x ^ P.b) ≤
        P.C₀ * (1 / (2 * ((P.ℓ : ℝ) * P.C₀)) * Real.log x ^ (P.c - P.b)) *
          ((P.ℓ : ℝ) * Real.log x ^ P.b) :=
      mul_le_mul_of_nonneg_right (hS.trans (mul_le_mul_of_nonneg_left h1 P.C₀_pos.le))
        (mul_nonneg hℓ.le hLb)
    have hA2 : P.C₀ * (1 / (2 * ((P.ℓ : ℝ) * P.C₀)) * Real.log x ^ (P.c - P.b)) *
          ((P.ℓ : ℝ) * Real.log x ^ P.b) = 1 / 2 * Real.log x ^ P.c := by
      calc P.C₀ * (1 / (2 * ((P.ℓ : ℝ) * P.C₀)) * Real.log x ^ (P.c - P.b)) *
            ((P.ℓ : ℝ) * Real.log x ^ P.b)
          = (P.ℓ : ℝ) * P.C₀ * (1 / (2 * ((P.ℓ : ℝ) * P.C₀)) *
              (Real.log x ^ (P.c - P.b) * Real.log x ^ P.b)) := by ring
        _ = 1 / 2 * (Real.log x ^ (P.c - P.b) * Real.log x ^ P.b) := rare_half hK1 _
        _ = 1 / 2 * Real.log x ^ P.c := by rw [e]
    have h4 : (Fintype.card S : ℝ) * ((P.ℓ : ℝ) * Real.log x ^ P.b) < Real.log x ^ P.c := by
      linarith
    have h5 : Real.exp (Real.log x ^ P.c) ≤ (p : ℝ) := 𝔊.big_ge g p hp
    have h6 : ((∏ g', ∏ j, (u g' j : ℕ) : ℕ) : ℝ) < (p : ℝ) :=
      lt_of_le_of_lt h3 (lt_of_lt_of_le (Real.exp_lt_exp.mpr h4) h5)
    exact_mod_cast h6

/-! ### Lemma 3.9 -/

/-- **Lemma 3.9 for fixed constants**, with the exponent `memAbsExponent P m C₁` of Lemma 3.8 and
a threshold depending on `P` and `C₂`. -/
theorem rareTransferBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) :
    RareTransferBound P m C₁ (memAbsExponent P m C₁) J C₂ := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ((eventually_big_tilt P one_pos).and
    ((eventually_tiltLaw_sum_le P).and ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
      (eventually_rareArith P C₂))))
  refine ⟨x₀, fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm θ i _ => ?_⟩
  obtain ⟨htilt, hsum, hL1, harith⟩ := hx₀ x hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hρ0 := memRho_pos P
  have hρ1 := memRho_lt_one P
  have hv1 : 1 ≤ memV P := (one_lt_memV P).le
  have hv0 : 0 < memV P := lt_of_lt_of_le zero_lt_one hv1
  have hT : 0 < P.ℓ + m := Nat.add_pos_left P.ℓ_pos m
  have hℓT : P.ℓ ≤ P.ℓ + m := Nat.le_add_right P.ℓ m
  have hC : ∀ ν g, P.ℓ + ((𝔉 ν).C g).card ≤ P.ℓ + m := fun ν g =>
    Nat.add_le_add_left (hadm.1 ν g) P.ℓ
  have hν : ∀ g, ∀ p ∈ 𝔊.big g,
      0 ≤ tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p :=
    fun g p hp => (htilt S B 𝔊 g p hp).2.1.le
  have hM : ∀ g : B, ∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ≤ 2 :=
    fun g => hsum S B 𝔊 g
  -- the constants of the groups, as in the proof of Lemma 3.8
  have hG1 : 1 ≤ Schur.groupConst P.vMinus P.q (P.ℓ + m) := Schur.one_le_groupConst _ _ _
  have hGpos : 0 < Schur.groupConst P.vMinus P.q (P.ℓ + m) := lt_of_lt_of_le zero_lt_one hG1
  have hK1 : 1 ≤ memAbsBigConst P m := le_max_left _ _
  have hKpos : 0 < memAbsBigConst P m := lt_of_lt_of_le zero_lt_one hK1
  have hmx0 : (0 : ℝ) ≤ max (1 : ℝ) 2 := zero_le_one.trans (le_max_left _ _)
  have hrowC0 : 0 ≤ edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m) :=
    edgeAbsRowConst_nonneg hρ0 hρ1 hv0.le _
  have hRb0 : 0 ≤ edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m) *
      (max (1 : ℝ) 2) ^ (P.ℓ + m) := mul_nonneg hrowC0 (pow_nonneg hmx0 _)
  have hRbK : edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m) *
      (max (1 : ℝ) 2) ^ (P.ℓ + m) ≤ memAbsBigConst P m :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCb0 : 0 ≤ edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m) :=
    edgeAbsColConst_nonneg P.vMinus_pos hρ0 hρ1 hv0.le _
  have hCbK : edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m) ≤ memAbsBigConst P m :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hprodS : ∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m) ≤
      Real.log x ^ (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m)) * P.C₀) :=
    𝔊.prod_small_le_rpow hL0 (fun _ => Schur.groupConst P.vMinus P.q (P.ℓ + m))
      (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m))) (Real.log_nonneg hG1)
      (fun _ => hGpos.le) (fun _ => (Real.exp_log hGpos).ge)
  have hprodRow : (∏ _g : B, edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m)) *
        ∏ _g : B, (max (1 : ℝ) 2) ^ (P.ℓ + m) ≤
      Real.log x ^ (Real.log (memAbsBigConst P m) * P.C₀) := by
    rw [← Finset.prod_mul_distrib]
    exact 𝔊.prod_big_le_rpow hL0
      (fun _ => edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m) *
        (max (1 : ℝ) 2) ^ (P.ℓ + m))
      (Real.log (memAbsBigConst P m)) (Real.log_nonneg hK1) (fun _ => hRb0)
      (fun _ => hRbK.trans (Real.exp_log hKpos).ge)
  have hprodCol : ∏ _g : B, edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m) ≤
      Real.log x ^ (Real.log (memAbsBigConst P m) * P.C₀) :=
    𝔊.prod_big_le_rpow hL0
      (fun _ => edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m))
      (Real.log (memAbsBigConst P m)) (Real.log_nonneg hK1) (fun _ => hCb0)
      (fun _ => hCbK.trans (Real.exp_log hKpos).ge)
  have hPS0 : 0 ≤ ∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m) :=
    Finset.prod_nonneg fun _ _ => hGpos.le
  have hPR0 : 0 ≤ (∏ _g : B, edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m)) *
      ∏ _g : B, (max (1 : ℝ) 2) ^ (P.ℓ + m) :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => hrowC0)
      (Finset.prod_nonneg fun _ _ => pow_nonneg hmx0 _)
  have hPC0 : 0 ≤ ∏ _g : B, edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m) :=
    Finset.prod_nonneg fun _ _ => hCb0
  have hRowLe : patternMass 𝔉 *
        ((∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m)) *
          (∏ _g : B, edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m)) *
          ∏ _g : B, (max (1 : ℝ) 2) ^ (P.ℓ + m)) ≤
      Real.log x ^ memAbsExponent P m C₁ := by
    unfold memAbsExponent
    rw [Real.rpow_add hL0, Real.rpow_add hL0,
      mul_assoc (∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m))]
    exact mul_le_mul hadm.2.1
      (mul_le_mul hprodS hprodRow hPR0 (Real.rpow_nonneg hL0.le _))
      (mul_nonneg hPS0 hPR0) (Real.rpow_nonneg hL0.le _)
  have hColLe : patternMass 𝔉 *
        ((∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m)) *
          ∏ _g : B, edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m)) ≤
      Real.log x ^ memAbsExponent P m C₁ := by
    unfold memAbsExponent
    rw [Real.rpow_add hL0, Real.rpow_add hL0]
    exact mul_le_mul hadm.2.1
      (mul_le_mul hprodS hprodCol hPC0 (Real.rpow_nonneg hL0.le _))
      (mul_nonneg hPS0 hPC0) (Real.rpow_nonneg hL0.le _)
  have hA : RareArith 𝔊.toGroupFamily P.ℓ (edgeSign i * k) :=
    harith S B 𝔊 k hadm.2.2.1 hadm.2.2.2 i
  exact rare_dirty_opBound (memData 𝔊 𝔉 k ζ) θ i (Bc := memCutoff (Real.log x))
    (v := memV P) (vMinus := P.vMinus) (Mmax := 2) (T := P.ℓ + m) P.q_pos P.q_lt_one hρ0 hρ1
    hv1 P.vMinus_pos 𝔊.mass_small_ge 𝔊.mass_big_ge 𝔊.big_law_sum hν hM hT hℓT hC hA hRowLe
    hColLe

/-- **[S] Lemma 3.9 (rare transfer, `lem:rare-transfer`)** [S-02:0838–0894], proved: for all
sufficiently large `x` the dirty part of every edge, at the truncation `B = ⌈L²⌉`, has norm at
most `2 L^{C_d} (B/𝒟)^{1/2}` on `ℋ`, with `C_d = memAbsExponent P m C₁` (the exponent `C_a` of
Lemma 3.8), which depends on `P`, `m`, `C₁` only. -/
theorem rareTransfer : RareTransfer :=
  fun P m C₁ => ⟨memAbsExponent P m C₁, fun J C₂ => rareTransferBound P m C₁ J C₂⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
