module

public import SimultaneousPrimitiveRoots.Hecke.DedekindSeries

/-!
# Hecke's formula for the Dedekind zeta function

For each ideal class `c` choose a nonzero integral ideal `J_c` in `c⁻¹` and let `Λ_c` be Hecke's
`Λ` of the lattice `J_c` (`heckeFEPair` for `basisOfFractionalIdeal`). Then for real `σ > 1`, with
`n = [K : ℚ]` and `s' = nσ/2`,

`ζ_K(σ) = ∑_c N(J_c)^σ / (w π^{-s'} Γ(s') heckeConst K s') · Λ_c(s')`.

Each `Λ_c` is meromorphic on `ℂ` with poles at most at `0` and `n/2` and satisfies a functional
equation (`heckeFEPair_functional_equation`), so the right side continues `ζ_K` (Hecke 1917).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Ideal NumberField.Units Module
open scoped nonZeroDivisors ENNReal Real

variable (K : Type*) [Field K] [NumberField K]

/-- A nonzero integral ideal in the class `c⁻¹`. -/
def classRep (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  (ClassGroup.mk0_surjective c⁻¹).choose

theorem classRep_spec (c : ClassGroup (𝓞 K)) : ClassGroup.mk0 (classRep K c) = c⁻¹ :=
  (ClassGroup.mk0_surjective c⁻¹).choose_spec

/-- The fractional ideal of `classRep c`. -/
abbrev classFrac (c : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K (classRep K c)

/-- The index type of the lattice basis of `classRep c`. -/
abbrev classIdx (c : ClassGroup (𝓞 K)) := Free.ChooseBasisIndex ℤ (classFrac K c)

/-- A `ℚ`-basis of `K` that is a `ℤ`-basis of `classRep c`. -/
def classBasis (c : ClassGroup (𝓞 K)) : Basis (classIdx K c) ℚ K :=
  basisOfFractionalIdeal K (classFrac K c)

theorem card_classIdx (c : ClassGroup (𝓞 K)) :
    Fintype.card (classIdx K c) = Fintype.card (K →+* ℂ) := by
  rw [NumberField.Embeddings.card, Module.finrank_eq_card_basis (classBasis K c)]

theorem card_classIdx_eq_finrank (c : ClassGroup (𝓞 K)) :
    Fintype.card (classIdx K c) = finrank ℚ K := by
  rw [card_classIdx, NumberField.Embeddings.card]

/-- Indexing the lattice basis by the complex embeddings. -/
def classEmb (c : ClassGroup (𝓞 K)) : classIdx K c ≃ (K →+* ℂ) :=
  Fintype.equivOfCardEq (card_classIdx K c)

instance (c : ClassGroup (𝓞 K)) : Nonempty (classIdx K c) := by
  rw [← Fintype.card_pos_iff, card_classIdx_eq_finrank]
  exact Module.finrank_pos

open scoped Classical in
/-- Hecke's FE-pair of the class `c`. -/
def classFEPair (c : ClassGroup (𝓞 K)) : WeakFEPair ℂ :=
  heckeFEPair (classBasis K c) (classEmb K c)

theorem latticeSet_classBasis (c : ClassGroup (𝓞 K)) :
    latticeSet (classBasis K c : classIdx K c → K) =
      idealInK (classRep K c : Ideal (𝓞 K)) :=
  latticeSet_basisOfFractionalIdeal (classRep K c)

variable {K}

theorem ennreal_tsum_ofReal_eq {α : Type*} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a)
    (h : ∑' a, ENNReal.ofReal (f a) ≠ ⊤) :
    ∑' a, ENNReal.ofReal (f a) = ENNReal.ofReal (∑' a, f a) := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal h
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  rw [ENNReal.ofReal_tsum_of_nonneg hf hs]

variable (K)

/-- The weight `N(J_c)^σ`. -/
def classNormPow (c : ClassGroup (𝓞 K)) (σ : ℝ) : ℝ :=
  (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ σ

theorem absNorm_classRep_pos (c : ClassGroup (𝓞 K)) :
    (0 : ℝ) < absNorm (classRep K c : Ideal (𝓞 K)) := by
  exact_mod_cast absNorm_pos_of_nonZeroDivisors (classRep K c)

/-- The class sum `A_c = ∑_{I ∈ c} N(I)^{-σ}` and the cone sum agree up to `w N(J_c)^{-σ}`. -/
theorem cone_class_relation {σ : ℝ} (hσ : 1 < σ) (c : ClassGroup (𝓞 K)) :
    ∑' x : coneSet (idealInK (classRep K c : Ideal (𝓞 K))),
        |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| ^ (-σ) =
      torsionOrder K * (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ (-σ) *
        ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
          (absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) := by
  set J := classRep K c with hJdef
  have hJ := classRep_spec K c
  -- the `ℝ≥0∞` identity
  have hE := tsum_coneSet_eq_class J hJ (fun t => ENNReal.ofReal (t ^ (-σ)))
  have hsplit : ∀ I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
      ENNReal.ofReal (((absNorm (J : Ideal (𝓞 K)) : ℝ) * absNorm (I.1 : Ideal (𝓞 K))) ^ (-σ)) =
        ENNReal.ofReal ((absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-σ)) *
          ENNReal.ofReal ((absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ)) := fun I => by
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  simp_rw [hsplit] at hE
  rw [ENNReal.tsum_mul_left] at hE
  -- finiteness of the class sum
  have hζ := tsum_ideal_eq_dedekindZeta K hσ
  have hcfin : ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
      ENNReal.ofReal ((absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_comp_le_tsum_of_injective
      (Subtype.val_injective (p := fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I = c))
      (fun I : (Ideal (𝓞 K))⁰ => ENNReal.ofReal ((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-σ))))
    rw [hζ]
    exact ENNReal.ofReal_ne_top
  have hxfin : ∑' x : coneSet (idealInK (J : Ideal (𝓞 K))),
      ENNReal.ofReal (|((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| ^ (-σ)) ≠ ⊤ := by
    rw [hE]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcfin)
  rw [ennreal_tsum_ofReal_eq (fun _ => Real.rpow_nonneg (abs_nonneg _) _) hxfin,
    ennreal_tsum_ofReal_eq (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hcfin] at hE
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hE
  rw [ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)))] at hE
  rw [hE]
  ring

/-- `ζ_K(σ) = ∑_c A_c` for real `σ > 1`. -/
theorem dedekindZeta_re_eq_sum_class {σ : ℝ} (hσ : 1 < σ) :
    (dedekindZeta K σ).re = ∑ c : ClassGroup (𝓞 K),
      ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
        (absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) := by
  have hζ := tsum_ideal_eq_dedekindZeta K hσ
  rw [tsum_ideal_eq_sum_class] at hζ
  have hcfin : ∀ c : ClassGroup (𝓞 K), ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
      ENNReal.ofReal ((absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ)) ≠ ⊤ := fun c => by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_comp_le_tsum_of_injective
      (Subtype.val_injective (p := fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I = c))
      (fun I : (Ideal (𝓞 K))⁰ => ENNReal.ofReal ((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-σ))))
    rw [tsum_ideal_eq_dedekindZeta K hσ]
    exact ENNReal.ofReal_ne_top
  simp_rw [fun c => ennreal_tsum_ofReal_eq
    (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c} =>
      Real.rpow_nonneg (Nat.cast_nonneg (absNorm (I.1 : Ideal (𝓞 K)))) (-σ)) (hcfin c)] at hζ
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => tsum_nonneg fun _ =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hζ
  have hre : 0 ≤ (dedekindZeta K σ).re := (hasSum_zetaTerm K hσ).nonneg (zetaTerm_nonneg K σ)
  exact ((ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun c _ => tsum_nonneg fun _ =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _) hre).mp hζ).symm

theorem dedekindZeta_ofReal {σ : ℝ} (hσ : 1 < σ) :
    dedekindZeta K σ = ((dedekindZeta K σ).re : ℂ) := by
  have h1 : HasSum (LSeries.term (fun n => (idealCount K n : ℂ)) σ) (dedekindZeta K σ) :=
    (dedekindZeta_summable K (s := (σ : ℂ)) (by simpa using hσ)).LSeriesHasSum
  have h2 := (Complex.ofRealCLM.hasSum (hasSum_zetaTerm K hσ))
  have h3 : HasSum (LSeries.term (fun n => (idealCount K n : ℂ)) σ)
      ((dedekindZeta K σ).re : ℂ) := by
    refine h2.congr_fun fun n => ?_
    simp only [Complex.ofRealCLM_apply]
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      simp [zetaTerm, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, zetaTerm, if_neg hn]
      have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hc : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow hn']
        push_cast
        rfl
      rw [hc, Real.rpow_neg hn', ← div_eq_mul_inv]
      push_cast
      rfl
  exact h1.unique h3

/-- **Hecke's formula for `ζ_K` at real `σ > 1`.** -/
theorem dedekindZeta_eq_sum_classFEPair {σ : ℝ} (hσ : 1 < σ) :
    dedekindZeta K σ = ∑ c : ClassGroup (𝓞 K),
      (((absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ σ /
        (torsionOrder K * (π ^ (-(finrank ℚ K * σ / 2)) * Real.Gamma (finrank ℚ K * σ / 2) *
          heckeConst K (finrank ℚ K * σ / 2))) : ℝ) : ℂ) *
        (classFEPair K c).Λ ((finrank ℚ K * σ / 2 : ℝ) : ℂ) := by
  classical
  set n : ℝ := (finrank ℚ K : ℝ) with hn
  have hn0 : 0 < n := by
    rw [hn]
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  set s' : ℝ := n * σ / 2 with hs'
  have hs'0 : 0 < s' := by positivity
  have hσeq : 2 * s' / n = σ := by rw [hs']; field_simp
  rw [dedekindZeta_ofReal K hσ, dedekindZeta_re_eq_sum_class K hσ, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro c _
  -- Hecke's identity for the class `c`
  have hcard : (Fintype.card (classIdx K c) : ℝ) / 2 < s' := by
    rw [card_classIdx_eq_finrank, hs']
    have : n / 2 < n * σ / 2 := by nlinarith
    exact this
  have hΛ := heckeFEPair_ofReal (classBasis K c) (classEmb K c)
    (by rw [latticeSet_classBasis]; exact idealInK_unit_mul _) hcard
  rw [latticeSet_classBasis, ← hn, hσeq] at hΛ
  change (classFEPair K c).Λ (s' : ℂ) = _ at hΛ
  rw [hΛ, ← Complex.ofReal_mul]
  congr 1
  rw [tsum_mul_left, cone_class_relation K hσ c]
  have hN := absNorm_classRep_pos K c
  have hw : (0 : ℝ) < torsionOrder K := by exact_mod_cast torsionOrder_pos K
  have hπ : 0 < π ^ (-s') := Real.rpow_pos_of_pos Real.pi_pos _
  have hΓ : 0 < Real.Gamma s' := Real.Gamma_pos_of_pos hs'0
  have hH : 0 < heckeConst K s' := heckeConst_pos hs'0
  have hNσ : (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ σ *
      (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ (-σ) = 1 := by
    rw [← Real.rpow_add hN, add_neg_cancel, Real.rpow_zero]
  set A := ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
    (absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) with hA
  field_simp
  linear_combination (-A) * hNσ

end SimultaneousPrimitiveRoots.Hecke

end
