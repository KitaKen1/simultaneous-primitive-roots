module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RareCount
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# [S] Lemma 3.9 (rare transfer): the row bound of the promotion part

Source: `verification/stage7-sources/S-02.tex`, lines 847–877 (`[S-02:0847–0877]`).

"First consider the positive sum of terms with a promotion. Fix its source, pattern, big-group
permutations and shared choices, and free `D`-labels. For some one of its at most `B` old pending
particles `(p, r)`, promotion requires `r + σ_i k D_ℬ D_𝒮 ≡ 0 (mod p)`, `p ∤ D`. … At most `B` of
the `𝒟` equally likely choices allow any promotion. Conditional on every omission choice, the
remaining weighted row costs are uniformly bounded by the proof of Lemma 3.8. Thus the promotion
part improves its row bound to `L^{C_a} B/𝒟`."

* `HasPromo`, `rarePromoQ`, `rareElig_of_promo` — a choice with a promotion and a nonvanishing
  coefficient has an eligible pending particle (`RareElig`) at its source: (eq:promotion-congruence)
  is part of `PromoValid`.
* `rare_row_fixed_pattern` — fixed source state, pattern and free labels: the row sum over the
  choices with a promotion vanishes unless a pending particle is eligible, and is at most the row
  bound of Lemma 3.8 (`edgeAbs_row_fixed_pattern`) otherwise.
* `rare_rowBound` — the weighted row bound of the promotion part of the edge operation, with the
  factor `B/𝒟` (`rareFrac_le`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- The two averages over the slot permutations of a quantity which does not depend on the second
permutation. -/
theorem rare_sum_full {α β : Type*} [Fintype α] [Fintype β] {cd : ℝ}
    (hcd : cd = (Fintype.card α : ℝ)) (hpos : 0 < cd) (X : α → β → ℝ) :
    ∑ ξ : α × β × α, cd⁻¹ * (cd⁻¹ * X ξ.1 ξ.2.1) = ∑ a : α, cd⁻¹ * ∑ b : β, X a b := by
  calc ∑ ξ : α × β × α, cd⁻¹ * (cd⁻¹ * X ξ.1 ξ.2.1)
      = ∑ a : α, ∑ b : β, ∑ _a' : α, cd⁻¹ * (cd⁻¹ * X a b) := by
        refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun a _ => ?_)
        exact Fintype.sum_prod_type _
    _ = ∑ a : α, cd⁻¹ * ∑ b : β, X a b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcd, ← mul_assoc,
          mul_inv_cancel₀ hpos.ne', one_mul]

/-- The constant of the row bound of one big group is nonnegative. -/
theorem edgeAbsRowConst_nonneg {vMinus ρ v : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hv : 0 ≤ v)
    (T : ℕ) : 0 ≤ edgeAbsRowConst vMinus ρ v T := by
  unfold edgeAbsRowConst
  exact mul_nonneg (pow_nonneg (mul_nonneg zero_le_two hv) _)
    (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
      (l38_countSup_nonneg _ hρ0 hρ1))

section Row

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-- The modulus of a coefficient of the edge operation under a condition: the two averages over
the slot permutations and the modulus of the coefficient at the permuted source. -/
theorem rare_ite_norm_full (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (ξ : EdgeFullChoice D Bc) {p : Prop} {hd : Decidable p} :
    @ite ℝ p hd ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ 0 =
      (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ * ((Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ *
        @ite ℝ p hd ‖edgeCoef D θ i (s.permLists ξ.1) ξ.2.1‖ 0) := by
  by_cases h : p
  · rw [if_pos h, if_pos h, norm_edgeFullCoef_one]
    ring
  · rw [if_neg h, if_neg h, mul_zero, mul_zero]

/-- **A choice with at least one promotion** [S-02:0829]. -/
def HasPromo {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) : Prop :=
  ∃ (g : B) (sl : Slot J ℓ) (j : Fin Bc), c.promo g sl = some j

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem promo_none_of_not_hasPromo {𝔉 : N → Pattern 𝒢.big J ℓ} {c : EdgeChoice 𝒢 𝔉 Bc}
    (h : ¬HasPromo c) (g : B) (sl : Slot J ℓ) : c.promo g sl = none := by
  cases hc : c.promo g sl with
  | none => rfl
  | some j => exact absurd ⟨g, sl, j, hc⟩ h

/-- **(eq:promotion-congruence)** [S-02:0853–0855]: the residue of the pending particle
translated by the step `Δ` is zero, `r + Δ ≡ 0 (mod p)`. -/
def rarePromoQ (g : B) (pr : Particle 𝒢 g) (Δ : ℤ) : Prop := (shiftParticle Δ pr).2 = 0

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- Two steps which satisfy (eq:promotion-congruence) for the same pending particle `(p, r)` are
congruent modulo `p`. -/
theorem rarePromoQ_dvd (g : B) (pr : Particle 𝒢 g) (Δ₁ Δ₂ : ℤ) (hp : 0 < (pr.1 : ℕ))
    (h1 : rarePromoQ g pr Δ₁) (h2 : rarePromoQ g pr Δ₂) : ((pr.1 : ℕ) : ℤ) ∣ Δ₁ - Δ₂ := by
  have h1' : ((Δ₁ : ℤ) : Res (pr.1 : ℕ)) + pr.2 = 0 := h1
  have h2' : ((Δ₂ : ℤ) : Res (pr.1 : ℕ)) + pr.2 = 0 := h2
  have h3 : ((Δ₁ - Δ₂ : ℤ) : Res (pr.1 : ℕ)) = 0 := by
    rw [Int.cast_sub]
    linear_combination h1' - h2'
  exact (Res.intCast_eq_zero_iff _ hp _).mp h3

omit [DecidableEq S] [DecidableEq B] in
/-- **A choice with a promotion and a nonvanishing coefficient has an eligible pending particle at
its source** [S-02:0851–0855]: "for some one of its at most `B` old pending particles `(p, r)`,
promotion requires `r + σ_i k D ≡ 0 (mod p)`, `p ∤ D`". -/
theorem rareElig_of_promo (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) (hcond : EdgeAbsCond D i s c) (hP : HasPromo c) :
    RareElig rarePromoQ (edgeSign i * D.k) (D.fam c.ν).C c.r s := by
  obtain ⟨h1, _, h3, _, _, _, _, _, _, h10⟩ := hcond
  obtain ⟨g, sl, j, hj⟩ := hP
  obtain ⟨_, _, pr, hpr, h0, hnd, _⟩ := h10 g sl j hj
  exact ⟨h1, h3.1, g, j, pr, hpr, h0, hnd⟩

open _root_.Classical in
/-- **The row of the promotion part for a fixed source state, a fixed pattern and fixed free
labels** [S-02:0849–0855, 0873–0875]: the sum over the stores, the promotions and the target
lists of the terms with a promotion vanishes unless a pending particle of the source is eligible;
in that case it is at most the row bound of Lemma 3.8 ("conditional on every omission choice, the
remaining weighted row costs are uniformly bounded by the proof of Lemma 3.8"). -/
theorem rare_row_fixed_pattern (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ}
    {T : ℕ} (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (ν : N) (hC : ∀ g, ℓ + ((D.fam ν).C g).card ≤ T)
    (s : MState 𝒢 J ℓ Bc) (r : AuxList 𝒢.big (D.fam ν).C) :
    ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
        (if HasPromo (edgeAbsChoice (𝔉 := D.fam) ν r t) then
            ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ else 0) *
          schurWeight v (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) ≤
      (if RareElig rarePromoQ (edgeSign i * D.k) (D.fam ν).C r s then 1 else 0) *
        (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) *
          schurWeight v s) := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hMf : 0 ≤ ∏ _g : B, (max 1 Mmax) ^ T :=
    Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hfull := edgeAbs_row_fixed_pattern D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hν hT hℓT ν hC
    (fun _ => 1) (fun _ => zero_le_one) hMf
    (fun F x₀ hF => edgeAbsFreshIntegral_one_le 𝒢 hν hM (D.fam ν).C hC F x₀ hF) s r
  by_cases hE : RareElig rarePromoQ (edgeSign i * D.k) (D.fam ν).C r s
  · rw [if_pos hE, one_mul]
    refine le_trans (Finset.sum_le_sum fun t _ => ?_) hfull
    rw [mul_one]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hv0 _)
    by_cases hP : HasPromo (edgeAbsChoice (𝔉 := D.fam) ν r t)
    · exact (if_pos hP).le
    · exact (if_neg hP).le.trans (norm_nonneg _)
  · rw [if_neg hE, zero_mul]
    refine le_of_eq (Finset.sum_eq_zero fun t _ => ?_)
    by_cases hP : HasPromo (edgeAbsChoice (𝔉 := D.fam) ν r t)
    · have hz : edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t) = 0 := by
        refine edgeCoef_of_not_cond D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t) fun hcond => ?_
        have hel := rareElig_of_promo D i s (edgeAbsChoice (𝔉 := D.fam) ν r t) hcond hP
        exact hE hel
      rw [if_pos hP, hz, norm_zero, zero_mul]
    · rw [if_neg hP, zero_mul]

variable [Fintype N]

open _root_.Classical in
/-- **The row of the promotion part for a fixed source state** — in the edge operation: for a
fixed source slot permutation, i.e. a fixed omission choice [S-02:0873–0875]. -/
theorem rare_row_fixed_perm (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (s : MState 𝒢 J ℓ Bc) :
    ∑ c : EdgeChoice 𝒢 D.fam Bc,
        (if HasPromo c then ‖edgeCoef D θ i s c‖ else 0) * schurWeight v (edgeTgt D i s c) ≤
      ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
        (if RareElig rarePromoQ (edgeSign i * D.k) (D.fam ν).C r s then 1 else 0) *
          (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
            ((∏ _g : S, Schur.groupConst vMinus D.q T) *
              (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) *
            schurWeight v s) := by
  have e := edgeAbs_sum_choice (𝔉 := D.fam) (Bc := Bc)
    (fun c => (if HasPromo c then ‖edgeCoef D θ i s c‖ else 0) * schurWeight v (edgeTgt D i s c))
  refine (le_of_eq e).trans ?_
  exact Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun r _ =>
    rare_row_fixed_pattern D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hν hM hT hℓT ν (hC ν) s r

open _root_.Classical in
/-- **The weighted row bound of the promotion part of an edge** [S-02:0849–0877]: "the promotion
part improves its row bound to `L^{C_a} B/𝒟`". The kernel is the modulus of the coefficients of
the local transition choices with at least one promotion; the constant is the row constant of
Lemma 3.8 times `B/𝒟`, `B` the cutoff and `𝒟 = C(M, ℓ)^{|𝒮|}`. -/
theorem rare_rowBound (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (hA : RareArith 𝒢 ℓ (edgeSign i * D.k)) :
    RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        if HasPromo ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) (edgeFullTgt D i)
      (patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) *
        ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ))) := by
  intro s
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  obtain ⟨cd, hcd⟩ : ∃ cd : ℝ, cd = (Fintype.card (ListPerms S B J ℓ) : ℝ) := ⟨_, rfl⟩
  have hcdpos : 0 < cd := by
    rw [hcd]
    exact Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (∏ _g : S, Schur.groupConst vMinus D.q T) *
      (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = (Bc : ℝ) / (omissionNumber S J ℓ : ℝ) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg
      (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
      (Finset.prod_nonneg fun _ _ => edgeAbsRowConst_nonneg hρ0 hρ1 hv0 _))
      (Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  show ∑ ξ : EdgeFullChoice D Bc,
      (if HasPromo ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) *
        schurWeight v (edgeFullTgt D i s ξ) ≤
    patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) *
        ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ)) * schurWeight v s
  rw [← hK, ← hF]
  have hterm : ∀ ξ : EdgeFullChoice D Bc,
      (if HasPromo ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) *
          schurWeight v (edgeFullTgt D i s ξ) =
        cd⁻¹ * (cd⁻¹ *
          ((if HasPromo ξ.2.1 then ‖edgeCoef D θ i (s.permLists ξ.1) ξ.2.1‖ else 0) *
            schurWeight v (edgeTgt D i (s.permLists ξ.1) ξ.2.1))) := by
    intro ξ
    have hw : schurWeight v (edgeFullTgt D i s ξ) =
        schurWeight v (edgeTgt D i (s.permLists ξ.1) ξ.2.1) := rfl
    rw [hw, rare_ite_norm_full D θ i s ξ, ← hcd]
    ring
  have hrow : ∀ π₁ : ListPerms S B J ℓ,
      ∑ c : EdgeChoice 𝒢 D.fam Bc,
          (if HasPromo c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
            schurWeight v (edgeTgt D i (s.permLists π₁) c) ≤
        ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          (if RareElig rarePromoQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₁) then 1
            else 0) *
            (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * schurWeight v s) := by
    intro π₁
    rw [hK]
    exact rare_row_fixed_perm D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hν hM hT hℓT hC
      (s.permLists π₁)
  calc ∑ ξ : EdgeFullChoice D Bc,
        (if HasPromo ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) *
          schurWeight v (edgeFullTgt D i s ξ)
      = ∑ ξ : EdgeFullChoice D Bc, cd⁻¹ * (cd⁻¹ *
          ((if HasPromo ξ.2.1 then ‖edgeCoef D θ i (s.permLists ξ.1) ξ.2.1‖ else 0) *
            schurWeight v (edgeTgt D i (s.permLists ξ.1) ξ.2.1))) :=
        Finset.sum_congr rfl fun ξ _ => hterm ξ
    _ = ∑ π₁ : ListPerms S B J ℓ, cd⁻¹ * ∑ c : EdgeChoice 𝒢 D.fam Bc,
          (if HasPromo c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
            schurWeight v (edgeTgt D i (s.permLists π₁) c) :=
        rare_sum_full hcd hcdpos
          (fun (π₁ : ListPerms S B J ℓ) (c : EdgeChoice 𝒢 D.fam Bc) =>
            (if HasPromo c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
              schurWeight v (edgeTgt D i (s.permLists π₁) c))
    _ ≤ ∑ π₁ : ListPerms S B J ℓ, cd⁻¹ * ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          (if RareElig rarePromoQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₁) then 1
            else 0) *
            (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * schurWeight v s) :=
        Finset.sum_le_sum fun π₁ _ =>
          mul_le_mul_of_nonneg_left (hrow π₁) (inv_nonneg.mpr hcdpos.le)
    _ = ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ π₁ : ListPerms S B J ℓ,
          cd⁻¹ * ((if RareElig rarePromoQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₁)
            then 1 else 0) *
            (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * schurWeight v s)) :=
        l38_sum_swap3 (γ := fun ν : N => AuxList 𝒢.big (D.fam ν).C)
          (fun _ : ListPerms S B J ℓ => cd⁻¹)
          (fun (π₁ : ListPerms S B J ℓ) (ν : N) (r : AuxList 𝒢.big (D.fam ν).C) =>
            (if RareElig rarePromoQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₁)
              then (1 : ℝ) else 0) *
              (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * schurWeight v s))
    _ = ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * schurWeight v s) *
            rareFrac rarePromoQ (edgeSign i * D.k) (D.fam ν).C r s := by
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ => ?_
        unfold rareFrac
        rw [← hcd, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun π₁ _ => by ring
    _ ≤ ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * schurWeight v s) * F :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun r _ => by
          rw [hF]
          exact mul_le_mul_of_nonneg_left
            (rareFrac_le hA rarePromoQ rarePromoQ_dvd (D.fam ν).C r s)
            (mul_nonneg (mul_nonneg (mul_nonneg (Schur.auxWeight_nonneg _ _ _)
              (NNReal.coe_nonneg _)) hK0) (pow_nonneg hv0 _))
    _ = ∑ ν : N, ((D.fam ν).supNorm : ℝ) * (K * schurWeight v s * F) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        have h1 : ∑ r : AuxList 𝒢.big (D.fam ν).C,
              auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * schurWeight v s *
                F =
            (∑ r : AuxList 𝒢.big (D.fam ν).C, auxWeight 𝒢.big (D.fam ν).C r) *
              (((D.fam ν).supNorm : ℝ) * (K * schurWeight v s * F)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun r _ => by ring
        rw [h1, sum_auxWeight hlaw (D.fam ν).C, one_mul]
    _ = patternMass D.fam * K * F * schurWeight v s := by
        unfold patternMass
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun ν _ => by ring

end Row

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
