module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.Fibre
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lemma 3.10: the fibre operators of a clean edge are small

Source: `verification/stage7-sources/S-02.tex`, lines 981–1013 (`[S-02:0981–1013]`).

"Consequently the remaining operator, on symmetric big active tests, is `𝒯(Θ)` or its adjoint,
with two changes only … Both changes are negligible in operator norm. Across the `M|ℬ|` active
coordinates, the product density changes by `1 + O_J(sN/P_*)`. … It follows uniformly in `𝐝` that
the between-map norm is at most `2 L^{-E_id}` for large `x`."

* `clean_ideal_side_bound` — the sum over the patterns of the row operations with the multipliers
  `cleanPhi`, between two symmetrizations, is `𝒯(Θ k d)` (forward edges) or its adjoint in `ℋ_id`
  (backward edges); its norm in `ℋ_id` is at most the bound `E` of the ideal estimate.
* `clean_fibre_bound_ideal` — the fibre operator, between two symmetrizations, has norm at most
  `E + (∑_ν sup |K_ν|) (ε₁ + 2 √ε₂)` in `ℋ_id`.
* `clean_prod_two_bounds`, `cleanRho_sub_one_le`, `clean_bigListMass_bounds` — the densities
  `∏ μ̃_g/μ_g` lie between `(1 - δ)^{M|ℬ|}` and `(1 + δ)^{M|ℬ|}` if `|μ̃_g/μ_g - 1| ≤ δ`.
* `clean_fibre_bound` — the same operator in `L²(⊗ μ̃_g)`: its norm is at most `C_T` as soon as
  `(1 + δ)^{M|ℬ|} (E + (∑_ν sup |K_ν|)(ε₁ + 2 √ε₂))² ≤ C_T² (1 - δ)^{M|ℬ|}`.

Instead of the unitary identification of the two `L²` spaces by the square root of the density,
the two norms are compared directly (they differ by the factors `(1 ± δ)^{M|ℬ|/2}`), and the
perturbation is estimated in `ℋ_id`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Generic lemmas -/

section Generic

variable {X : Type*} [Fintype X]

theorem clean_wInner_sum_left {ι : Type*} (w : X → ℝ) (s : Finset ι) (F : ι → X → ℂ)
    (G : X → ℂ) : wInner w (∑ i ∈ s, F i) G = ∑ i ∈ s, wInner w (F i) G := by
  unfold wInner
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_apply, map_sum, Finset.sum_mul, Finset.mul_sum]

theorem clean_wInner_sum_right {ι : Type*} (w : X → ℝ) (s : Finset ι) (F : X → ℂ)
    (G : ι → X → ℂ) : wInner w F (∑ i ∈ s, G i) = ∑ i ∈ s, wInner w F (G i) := by
  unfold wInner
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_apply, Finset.mul_sum, Finset.mul_sum]

/-- **Comparison of the norms of two weights**: if `η₋ w₂ ≤ w₁ ≤ η₊ w₂`, a bound `A` in `L²(w₂)`
gives the bound `C_T` in `L²(w₁)` as soon as `η₊ A² ≤ C_T² η₋`. -/
theorem clean_wNorm_change {w₁ w₂ : X → ℝ} (hw₂ : ∀ x, 0 ≤ w₂ x) {ηm ηp A CT : ℝ}
    (hηp : 0 ≤ ηp) (hlo : ∀ x, ηm * w₂ x ≤ w₁ x) (hhi : ∀ x, w₁ x ≤ ηp * w₂ x)
    (hCT : 0 ≤ CT) (hsc : ηp * A ^ 2 ≤ CT ^ 2 * ηm) (F g : X → ℂ)
    (hF : wNorm w₂ F ≤ A * wNorm w₂ g) : wNorm w₁ F ≤ CT * wNorm w₁ g := by
  refine wNorm_le_of_wNormSq_le hCT ?_
  have h1 : wNormSq w₁ F ≤ ηp * wNormSq w₂ F := by
    unfold wNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc w₁ x * ‖F x‖ ^ 2 ≤ ηp * w₂ x * ‖F x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hhi x) (sq_nonneg _)
      _ = ηp * (w₂ x * ‖F x‖ ^ 2) := mul_assoc _ _ _
  have h2 : ηm * wNormSq w₂ g ≤ wNormSq w₁ g := by
    unfold wNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc ηm * (w₂ x * ‖g x‖ ^ 2) = ηm * w₂ x * ‖g x‖ ^ 2 := (mul_assoc _ _ _).symm
      _ ≤ w₁ x * ‖g x‖ ^ 2 := mul_le_mul_of_nonneg_right (hlo x) (sq_nonneg _)
  have h3 : wNormSq w₂ F ≤ A ^ 2 * wNormSq w₂ g := by
    rw [← wNorm_sq hw₂, ← wNorm_sq hw₂, ← mul_pow]
    exact pow_le_pow_left₀ (wNorm_nonneg _ _) hF 2
  calc wNormSq w₁ F ≤ ηp * wNormSq w₂ F := h1
    _ ≤ ηp * (A ^ 2 * wNormSq w₂ g) := mul_le_mul_of_nonneg_left h3 hηp
    _ = (ηp * A ^ 2) * wNormSq w₂ g := (mul_assoc _ _ _).symm
    _ ≤ (CT ^ 2 * ηm) * wNormSq w₂ g :=
        mul_le_mul_of_nonneg_right hsc (wNormSq_nonneg hw₂ g)
    _ = CT ^ 2 * (ηm * wNormSq w₂ g) := mul_assoc _ _ _
    _ ≤ CT ^ 2 * wNormSq w₁ g := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

end Generic

section FibreBound

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

omit [Fintype S] [DecidableEq S] [Fintype N] in
/-- **Symmetrization of the big lists is a contraction** of `L²(w)` for every weight which is
invariant under the permutations of the slots. -/
theorem clean_bigSym_wNorm_le {w : LabelList 𝒢.big J ℓ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hinv : ∀ (σ : SlotPerms B J ℓ) (x : LabelList 𝒢.big J ℓ), w (permuteSlots σ x) = w x)
    (H : LabelList 𝒢.big J ℓ → ℂ) : wNorm w (bigSym 𝒢.big J ℓ H) ≤ wNorm w H := by
  have e : bigSym 𝒢.big J ℓ H = fun x => (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ *
      ∑ σ : SlotPerms B J ℓ, H (permuteEquiv σ x) := funext fun x => bigSym_apply H x
  rw [e]
  exact clean_wNorm_avg_le hw (fun σ => permuteEquiv σ) (fun σ x => hinv σ x) H

omit [Fintype S] [DecidableEq S] in
/-- **The sum over the patterns of the row operations with the multipliers `cleanPhi`, between
two symmetrizations, is `𝒯(Θ k d)` or its adjoint** [S-02:0981–0983]; in `ℋ_id` its norm is at
most the bound of the ideal estimate. -/
theorem clean_ideal_side_bound (D : MemData 𝒢 J ℓ N) {E : ℝ} (hE : 0 ≤ E)
    (hid : ∀ (Θ : ℝ) (g : LabelList 𝒢.big J ℓ → ℂ),
      wNorm (idealWeight 𝒢.big J ℓ) (idealOp D.fam D.ζ Θ g) ≤
        E * wNorm (idealWeight 𝒢.big J ℓ) g)
    (i d : ℕ) (Θ : ℝ) (g : LabelList 𝒢.big J ℓ → ℂ) :
    wNorm (idealWeight 𝒢.big J ℓ)
        (bigSym 𝒢.big J ℓ ((∑ ν, cleanShRow (D.fam ν).C (cleanPhi D i d Θ ν))
          (bigSym 𝒢.big J ℓ g))) ≤
      E * wNorm (idealWeight 𝒢.big J ℓ) g := by
  have hm0 : ∀ x : LabelList 𝒢.big J ℓ, 0 ≤ idealWeight 𝒢.big J ℓ x := fun x =>
    clean_idealWeight_nonneg x
  by_cases hi : i % 2 = 0
  · have e : (∑ ν, cleanShRow (D.fam ν).C (cleanPhi D i d Θ ν)) =
        ∑ ν, idealRow (D.fam ν) D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))) := by
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [clean_idealRow_eq]
      refine congrArg (cleanShRow (D.fam ν).C)
        (funext fun x => funext fun r => funext fun x' => ?_)
      exact if_pos hi
    rw [e]
    exact hid (Θ * ((D.k : ℝ) * (d : ℝ))) g
  · have hphi : ∀ ν, cleanPhi D i d Θ ν = fun x r x' =>
        conj ((D.fam ν).K x' x r *
          dilPhase D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))) (bigDil (D.fam ν).C x' r)) := by
      intro ν
      funext x r x'
      exact if_neg hi
    refine clean_adjoint_bound hm0
      (fun g' => idealOp D.fam D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))) g')
      (fun f => bigSym 𝒢.big J ℓ ((∑ ν, cleanShRow (D.fam ν).C (cleanPhi D i d Θ ν))
        (bigSym 𝒢.big J ℓ f))) hE ?_ (hid (Θ * ((D.k : ℝ) * (d : ℝ)))) g
    intro f g'
    calc wInner (idealWeight 𝒢.big J ℓ)
          (bigSym 𝒢.big J ℓ ((∑ ν, cleanShRow (D.fam ν).C (cleanPhi D i d Θ ν))
            (bigSym 𝒢.big J ℓ f))) g'
        = wInner (idealWeight 𝒢.big J ℓ)
            ((∑ ν, cleanShRow (D.fam ν).C (cleanPhi D i d Θ ν)) (bigSym 𝒢.big J ℓ f))
            (bigSym 𝒢.big J ℓ g') := (wInner_bigSym _ _).symm
      _ = ∑ ν, wInner (idealWeight 𝒢.big J ℓ)
            (cleanShRow (D.fam ν).C (cleanPhi D i d Θ ν) (bigSym 𝒢.big J ℓ f))
            (bigSym 𝒢.big J ℓ g') := by
          rw [LinearMap.sum_apply, clean_wInner_sum_left]
      _ = ∑ ν, wInner (idealWeight 𝒢.big J ℓ) (bigSym 𝒢.big J ℓ f)
            (idealRow (D.fam ν) D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))) (bigSym 𝒢.big J ℓ g')) := by
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [hphi ν]
          exact cleanShRow_adjoint (D.fam ν).C
            (fun a r b => (D.fam ν).K a b r *
              dilPhase D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))) (bigDil (D.fam ν).C a r))
            (bigSym 𝒢.big J ℓ f) (bigSym 𝒢.big J ℓ g')
      _ = wInner (idealWeight 𝒢.big J ℓ) (bigSym 𝒢.big J ℓ f)
            ((∑ ν, idealRow (D.fam ν) D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))))
              (bigSym 𝒢.big J ℓ g')) := by
          rw [LinearMap.sum_apply, clean_wInner_sum_right]
      _ = wInner (idealWeight 𝒢.big J ℓ) f
            (bigSym 𝒢.big J ℓ ((∑ ν, idealRow (D.fam ν) D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))))
              (bigSym 𝒢.big J ℓ g'))) := (wInner_bigSym f _).symm

omit [Fintype S] [DecidableEq S] in
/-- **The two changes summed over the patterns** [S-02:0986–1012]: the multipliers
`[ban][ban] ρ_ν` change the sum of the row operations by at most
`(∑_ν sup |K_ν|) (ε₁ + 2 √ε₂)` in `ℋ_id`. -/
theorem clean_perturb_sum_bound
    (hlaw : ∀ g, ∑ q ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) q = 1) {μs : ℝ} (hμ0 : 0 ≤ μs)
    (hμ : ∀ g, ∀ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p ≤ μs) {m : ℕ}
    (D : MemData 𝒢 J ℓ N) (hCm : ∀ ν g, ((D.fam ν).C g).card ≤ m)
    (hδ : (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) ≤ 1) {ε₁ : ℝ} (hε₁ : 0 ≤ ε₁)
    (hρ : ∀ ν x', |cleanRho D ν x' - 1| ≤ ε₁) (i d : ℕ) (Θ : ℝ)
    (h : LabelList 𝒢.big J ℓ → ℂ) :
    wNorm (idealWeight 𝒢.big J ℓ)
        ((∑ ν, cleanShRow (D.fam ν).C (fun x r x' =>
            ((cleanBanInd (D.fam ν).C r x * cleanBanInd (D.fam ν).C r x' * cleanRho D ν x' :
              ℝ) : ℂ) * cleanPhi D i d Θ ν x r x')) h -
          (∑ ν, cleanShRow (D.fam ν).C (cleanPhi D i d Θ ν)) h) ≤
      patternMass D.fam * (ε₁ + 2 * Real.sqrt (((m * Fintype.card B : ℕ) : ℝ) *
        ((Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs)))) *
        wNorm (idealWeight 𝒢.big J ℓ) h := by
  have hm0 : ∀ x : LabelList 𝒢.big J ℓ, 0 ≤ idealWeight 𝒢.big J ℓ x := fun x =>
    clean_idealWeight_nonneg x
  rw [LinearMap.sum_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine (clean_wNorm_sum_le hm0 _ _).trans ?_
  unfold patternMass
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun ν _ => ?_
  exact cleanShRow_perturb hlaw hμ0 hμ (D.fam ν).C (hCm ν) hδ (cleanPhi D i d Θ ν)
    (NNReal.coe_nonneg _) (norm_cleanPhi_le D i d Θ ν) (cleanRho D ν) hε₁ (hρ ν) h

omit [Fintype S] [DecidableEq S] in
/-- **The fibre operator of a clean edge, between two symmetrizations, in `ℋ_id`**
[S-02:0981–1013]: its norm is at most `E + (∑_ν sup |K_ν|)(ε₁ + 2 √ε₂)`, where `E` bounds the
ideal operator at every frequency. -/
theorem clean_fibre_bound_ideal
    (hlaw : ∀ g, ∑ q ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) q = 1)
    (hpos : ∀ g, ∀ p ∈ 𝒢.big g, 0 < Graph.primeGroupLaw (𝒢.big g) p) {μs : ℝ} (hμ0 : 0 ≤ μs)
    (hμ : ∀ g, ∀ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p ≤ μs) {m : ℕ}
    (D : MemData 𝒢 J ℓ N) (hCm : ∀ ν g, ((D.fam ν).C g).card ≤ m)
    (hδ : (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) ≤ 1) {E ε₁ : ℝ} (hE : 0 ≤ E)
    (hε₁ : 0 ≤ ε₁)
    (hid : ∀ (Θ : ℝ) (g : LabelList 𝒢.big J ℓ → ℂ),
      wNorm (idealWeight 𝒢.big J ℓ) (idealOp D.fam D.ζ Θ g) ≤
        E * wNorm (idealWeight 𝒢.big J ℓ) g)
    (hρ : ∀ ν x', |cleanRho D ν x' - 1| ≤ ε₁) (i d : ℕ) (Θ : ℝ)
    (g : LabelList 𝒢.big J ℓ → ℂ) :
    wNorm (idealWeight 𝒢.big J ℓ)
        (bigSym 𝒢.big J ℓ (cleanFibOp (cleanKappa D i d) (cleanStep D i d) (cleanTau D) Θ
          (bigSym 𝒢.big J ℓ g))) ≤
      (E + patternMass D.fam * (ε₁ + 2 * Real.sqrt (((m * Fintype.card B : ℕ) : ℝ) *
        ((Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs))))) *
        wNorm (idealWeight 𝒢.big J ℓ) g := by
  have hm0 : ∀ x : LabelList 𝒢.big J ℓ, 0 ≤ idealWeight 𝒢.big J ℓ x := fun x =>
    clean_idealWeight_nonneg x
  have hsymc : ∀ H : LabelList 𝒢.big J ℓ → ℂ,
      wNorm (idealWeight 𝒢.big J ℓ) (bigSym 𝒢.big J ℓ H) ≤ wNorm (idealWeight 𝒢.big J ℓ) H :=
    fun H => clean_bigSym_wNorm_le hm0 (fun σ x => idealWeight_permute σ x) H
  obtain ⟨Aw, hAw⟩ : ∃ Aw : (LabelList 𝒢.big J ℓ → ℂ) →ₗ[ℂ] (LabelList 𝒢.big J ℓ → ℂ),
      Aw = ∑ ν, cleanShRow (D.fam ν).C (fun x r x' =>
        ((cleanBanInd (D.fam ν).C r x * cleanBanInd (D.fam ν).C r x' * cleanRho D ν x' : ℝ) :
          ℂ) * cleanPhi D i d Θ ν x r x') := ⟨_, rfl⟩
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : (LabelList 𝒢.big J ℓ → ℂ) →ₗ[ℂ] (LabelList 𝒢.big J ℓ → ℂ),
      A₀ = ∑ ν, cleanShRow (D.fam ν).C (cleanPhi D i d Θ ν) := ⟨_, rfl⟩
  obtain ⟨err, herr⟩ : ∃ err : ℝ, err = patternMass D.fam *
      (ε₁ + 2 * Real.sqrt (((m * Fintype.card B : ℕ) : ℝ) *
        ((Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs)))) := ⟨_, rfl⟩
  have herr0 : 0 ≤ err := by
    rw [herr]
    exact mul_nonneg (patternMass_nonneg _)
      (add_nonneg hε₁ (mul_nonneg zero_le_two (Real.sqrt_nonneg _)))
  rw [cleanFibOp_eq hpos D i d Θ, ← hAw, ← herr]
  have hsm : bigSym 𝒢.big J ℓ ((cleanUnit D i d • Aw) (bigSym 𝒢.big J ℓ g)) =
      cleanUnit D i d • bigSym 𝒢.big J ℓ (Aw (bigSym 𝒢.big J ℓ g)) := by
    rw [LinearMap.smul_apply, map_smul]
  have hsplit : bigSym 𝒢.big J ℓ (Aw (bigSym 𝒢.big J ℓ g)) =
      bigSym 𝒢.big J ℓ (A₀ (bigSym 𝒢.big J ℓ g)) +
        bigSym 𝒢.big J ℓ (Aw (bigSym 𝒢.big J ℓ g) - A₀ (bigSym 𝒢.big J ℓ g)) := by
    rw [← map_add, add_sub_cancel]
  have h1 : wNorm (idealWeight 𝒢.big J ℓ) (bigSym 𝒢.big J ℓ (A₀ (bigSym 𝒢.big J ℓ g))) ≤
      E * wNorm (idealWeight 𝒢.big J ℓ) g := by
    rw [hA₀]
    exact clean_ideal_side_bound D hE hid i d Θ g
  have h2 : wNorm (idealWeight 𝒢.big J ℓ)
        (bigSym 𝒢.big J ℓ (Aw (bigSym 𝒢.big J ℓ g) - A₀ (bigSym 𝒢.big J ℓ g))) ≤
      err * wNorm (idealWeight 𝒢.big J ℓ) g := by
    refine (hsymc _).trans ?_
    have h3 := clean_perturb_sum_bound hlaw hμ0 hμ D hCm hδ hε₁ hρ i d Θ (bigSym 𝒢.big J ℓ g)
    rw [← hAw, ← hA₀, ← herr] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (hsymc g) herr0)
  rw [hsm, wNorm_smul]
  calc ‖cleanUnit D i d‖ *
        wNorm (idealWeight 𝒢.big J ℓ) (bigSym 𝒢.big J ℓ (Aw (bigSym 𝒢.big J ℓ g)))
      ≤ 1 * wNorm (idealWeight 𝒢.big J ℓ) (bigSym 𝒢.big J ℓ (Aw (bigSym 𝒢.big J ℓ g))) :=
        mul_le_mul_of_nonneg_right (norm_cleanUnit_le D i d) (wNorm_nonneg _ _)
    _ = wNorm (idealWeight 𝒢.big J ℓ)
          (bigSym 𝒢.big J ℓ (A₀ (bigSym 𝒢.big J ℓ g)) +
            bigSym 𝒢.big J ℓ (Aw (bigSym 𝒢.big J ℓ g) - A₀ (bigSym 𝒢.big J ℓ g))) := by
        rw [one_mul, ← hsplit]
    _ ≤ wNorm (idealWeight 𝒢.big J ℓ) (bigSym 𝒢.big J ℓ (A₀ (bigSym 𝒢.big J ℓ g))) +
          wNorm (idealWeight 𝒢.big J ℓ)
            (bigSym 𝒢.big J ℓ (Aw (bigSym 𝒢.big J ℓ g) - A₀ (bigSym 𝒢.big J ℓ g))) :=
        wNorm_add_le hm0 _ _
    _ ≤ E * wNorm (idealWeight 𝒢.big J ℓ) g + err * wNorm (idealWeight 𝒢.big J ℓ) g :=
        add_le_add h1 h2
    _ = (E + err) * wNorm (idealWeight 𝒢.big J ℓ) g := by ring

/-! ### The densities -/

omit [Fintype S] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A product over all slots of all big groups of numbers between `a` and `b`. -/
theorem clean_prod_two_bounds {a b : ℝ} (ha : 0 ≤ a) (f : B → Slot J ℓ → ℝ)
    (hlo : ∀ g sl, a ≤ f g sl) (hhi : ∀ g sl, f g sl ≤ b) :
    a ^ ((J + ℓ) * Fintype.card B) ≤ ∏ g, ∏ sl, f g sl ∧
      ∏ g, ∏ sl, f g sl ≤ b ^ ((J + ℓ) * Fintype.card B) := by
  have hc : ∀ c : ℝ, ∏ _g : B, ∏ _sl : Slot J ℓ, c = c ^ ((J + ℓ) * Fintype.card B) := by
    intro c
    rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ, card_slot,
      ← pow_mul]
  constructor
  · rw [← hc a]
    exact Finset.prod_le_prod (fun g _ => Finset.prod_nonneg fun sl _ => ha)
      (fun g _ => Finset.prod_le_prod (fun sl _ => ha) (fun sl _ => hlo g sl))
  · rw [← hc b]
    exact Finset.prod_le_prod (fun g _ => Finset.prod_nonneg fun sl _ => ha.trans (hlo g sl))
      (fun g _ => Finset.prod_le_prod (fun sl _ => ha.trans (hlo g sl))
        (fun sl _ => hhi g sl))

open _root_.Classical in
omit [Fintype S] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **"The product density changes by `1 + O_J(sN/P_*)`"** [S-02:0988–0991], for the fresh target
labels: `|ρ_ν - 1| ≤ (1 + δ)^{M|ℬ|} - 1` if `|μ̃_g/μ_g - 1| ≤ δ ≤ 1`. -/
theorem cleanRho_sub_one_le (D : MemData 𝒢 J ℓ N) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hratio : ∀ g, ∀ p ∈ 𝒢.big g,
      |tiltLaw (𝒢.big g) D.q D.n p / Graph.primeGroupLaw (𝒢.big g) p - 1| ≤ δ)
    (ν : N) (x' : LabelList 𝒢.big J ℓ) :
    |cleanRho D ν x' - 1| ≤ (1 + δ) ^ ((J + ℓ) * Fintype.card B) - 1 := by
  have hf : ∀ (g : B) (sl : Slot J ℓ),
      1 - δ ≤ (if Unshared ((D.fam ν).C g) sl then
          tiltLaw (𝒢.big g) D.q D.n (x' g sl) / Graph.primeGroupLaw (𝒢.big g) (x' g sl)
          else 1) ∧
        (if Unshared ((D.fam ν).C g) sl then
          tiltLaw (𝒢.big g) D.q D.n (x' g sl) / Graph.primeGroupLaw (𝒢.big g) (x' g sl)
          else 1) ≤ 1 + δ := by
    intro g sl
    split_ifs
    · have h := abs_le.mp (hratio g _ (x' g sl).2)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · exact ⟨by linarith, by linarith⟩
  obtain ⟨h1, h2⟩ := clean_prod_two_bounds (B := B) (J := J) (ℓ := ℓ) (sub_nonneg.mpr hδ1)
    (fun g sl => if Unshared ((D.fam ν).C g) sl then
      tiltLaw (𝒢.big g) D.q D.n (x' g sl) / Graph.primeGroupLaw (𝒢.big g) (x' g sl) else 1)
    (fun g sl => (hf g sl).1) (fun g sl => (hf g sl).2)
  have hb1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) ((J + ℓ) * Fintype.card B)
  have hb2 := one_add_mul_le_pow (show (-2 : ℝ) ≤ δ by linarith) ((J + ℓ) * Fintype.card B)
  have e2 : (1 : ℝ) + -δ = 1 - δ := by ring
  rw [e2] at hb1
  have hρ : cleanRho D ν x' = ∏ g, ∏ sl : Slot J ℓ,
      (if Unshared ((D.fam ν).C g) sl then
        tiltLaw (𝒢.big g) D.q D.n (x' g sl) / Graph.primeGroupLaw (𝒢.big g) (x' g sl)
        else 1) := rfl
  rw [hρ]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- **"Across the `M|ℬ|` active coordinates, the product density changes by `1 + O_J(sN/P_*)`"**
[S-02:0988–0991]: `(1 - δ)^{M|ℬ|} ⊗μ_g ≤ ⊗μ̃_g ≤ (1 + δ)^{M|ℬ|} ⊗μ_g`. -/
theorem clean_bigListMass_bounds
    (hpos : ∀ g, ∀ p ∈ 𝒢.big g, 0 < Graph.primeGroupLaw (𝒢.big g) p) (q : ℝ) (n : ℕ) {δ : ℝ}
    (hδ1 : δ ≤ 1)
    (hratio : ∀ g, ∀ p ∈ 𝒢.big g,
      |tiltLaw (𝒢.big g) q n p / Graph.primeGroupLaw (𝒢.big g) p - 1| ≤ δ)
    (x : LabelList 𝒢.big J ℓ) :
    (1 - δ) ^ ((J + ℓ) * Fintype.card B) * idealWeight 𝒢.big J ℓ x ≤ bigListMass 𝒢 q n x ∧
      bigListMass 𝒢 q n x ≤ (1 + δ) ^ ((J + ℓ) * Fintype.card B) * idealWeight 𝒢.big J ℓ x := by
  have hf : ∀ (g : B) (sl : Slot J ℓ),
      1 - δ ≤ tiltLaw (𝒢.big g) q n (x g sl) / Graph.primeGroupLaw (𝒢.big g) (x g sl) ∧
        tiltLaw (𝒢.big g) q n (x g sl) / Graph.primeGroupLaw (𝒢.big g) (x g sl) ≤ 1 + δ := by
    intro g sl
    have h := abs_le.mp (hratio g _ (x g sl).2)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨h1, h2⟩ := clean_prod_two_bounds (B := B) (J := J) (ℓ := ℓ) (sub_nonneg.mpr hδ1)
    (fun g sl => tiltLaw (𝒢.big g) q n (x g sl) / Graph.primeGroupLaw (𝒢.big g) (x g sl))
    (fun g sl => (hf g sl).1) (fun g sl => (hf g sl).2)
  have hprod : bigListMass 𝒢 q n x =
      (∏ g, ∏ sl : Slot J ℓ,
        tiltLaw (𝒢.big g) q n (x g sl) / Graph.primeGroupLaw (𝒢.big g) (x g sl)) *
        idealWeight 𝒢.big J ℓ x := by
    unfold bigListMass idealWeight
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun sl _ => ?_
    rw [div_mul_cancel₀ _ (hpos g _ (x g sl).2).ne']
  have hm0 : 0 ≤ idealWeight 𝒢.big J ℓ x := clean_idealWeight_nonneg x
  rw [hprod]
  exact ⟨mul_le_mul_of_nonneg_right h1 hm0, mul_le_mul_of_nonneg_right h2 hm0⟩

omit [Fintype S] [DecidableEq S] in
/-- **The fibre operator of a clean edge, between two symmetrizations, in `L²(⊗ μ̃_g)`**
[S-02:0981–1013]: if `|μ̃_g/μ_g - 1| ≤ δ`, the atoms of the laws `μ_g` are at most `μ_*`, and the
ideal operator is bounded by `E` at every frequency, then the fibre operator at every frequency
has norm at most `C_T`, as soon as
`(1 + δ)^{M|ℬ|} (E + (∑_ν sup |K_ν|)((1 + δ)^{M|ℬ|} - 1 + 2 √ε₂))² ≤ C_T² (1 - δ)^{M|ℬ|}`. -/
theorem clean_fibre_bound
    (hlaw : ∀ g, ∑ q ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) q = 1)
    (hpos : ∀ g, ∀ p ∈ 𝒢.big g, 0 < Graph.primeGroupLaw (𝒢.big g) p) {μs : ℝ} (hμ0 : 0 ≤ μs)
    (hμ : ∀ g, ∀ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p ≤ μs) {m : ℕ}
    (D : MemData 𝒢 J ℓ N) (hCm : ∀ ν g, ((D.fam ν).C g).card ≤ m)
    (hδ' : (Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs) ≤ 1) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1)
    (hratio : ∀ g, ∀ p ∈ 𝒢.big g,
      |tiltLaw (𝒢.big g) D.q D.n p / Graph.primeGroupLaw (𝒢.big g) p - 1| ≤ δ)
    {E CT : ℝ} (hE : 0 ≤ E) (hCT : 0 ≤ CT)
    (hid : ∀ (Θ : ℝ) (g : LabelList 𝒢.big J ℓ → ℂ),
      wNorm (idealWeight 𝒢.big J ℓ) (idealOp D.fam D.ζ Θ g) ≤
        E * wNorm (idealWeight 𝒢.big J ℓ) g)
    (hsc : (1 + δ) ^ ((J + ℓ) * Fintype.card B) *
        (E + patternMass D.fam * ((1 + δ) ^ ((J + ℓ) * Fintype.card B) - 1 +
          2 * Real.sqrt (((m * Fintype.card B : ℕ) : ℝ) *
            ((Fintype.card B : ℝ) * (((J + ℓ : ℕ) : ℝ) * μs))))) ^ 2 ≤
      CT ^ 2 * (1 - δ) ^ ((J + ℓ) * Fintype.card B))
    (i d : ℕ) (Θ : ℝ) (g : LabelList 𝒢.big J ℓ → ℂ) :
    wNorm (bigListMass 𝒢 D.q D.n)
        (bigSym 𝒢.big J ℓ (cleanFibOp (cleanKappa D i d) (cleanStep D i d) (cleanTau D) Θ
          (bigSym 𝒢.big J ℓ g))) ≤
      CT * wNorm (bigListMass 𝒢 D.q D.n) g := by
  have hε₁ : (0 : ℝ) ≤ (1 + δ) ^ ((J + ℓ) * Fintype.card B) - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hF := clean_fibre_bound_ideal hlaw hpos hμ0 hμ D hCm hδ' hE hε₁ hid
    (fun ν x' => cleanRho_sub_one_le D hδ0 hδ1 hratio ν x') i d Θ g
  exact clean_wNorm_change (fun x => clean_idealWeight_nonneg x)
    (pow_nonneg (by linarith) _)
    (fun x => (clean_bigListMass_bounds hpos D.q D.n hδ1 hratio x).1)
    (fun x => (clean_bigListMass_bounds hpos D.q D.n hδ1 hratio x).2) hCT hsc _ g hF

end FibreBound

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
