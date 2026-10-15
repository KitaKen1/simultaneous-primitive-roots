module

public import SimultaneousPrimitiveRoots.FrozenIdealSeries

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain MeasureTheory
noncomputable section

/-- The paper's additional condition on each frozen exponent. -/
def frozenIdealAdmissible (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (I : FrozenIdealCarrier K s) : Prop :=
  ∀ v : s, multiplicity v.val.asIdeal I.val % 3 = 0 ∨
    multiplicity v.val.asIdeal I.val % 3 = 1

/-- Actual supported ideals with all exponents congruent to zero or one.
For empty support this has only the unit ideal, as in A(1). -/
def AdmissibleFrozenIdealCarrier (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) : Type _ :=
  {I : FrozenIdealCarrier K s // frozenIdealAdmissible K s I}

def admissibleFrozenIdealEquiv (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    {e : s → ℕ // ∀ v : s, e v % 3 = 0 ∨ e v % 3 = 1} ≃
      AdmissibleFrozenIdealCarrier K s :=
  (frozenIdealEquiv K s).subtypeEquiv (by
    intro e
    simp only [frozenIdealAdmissible, frozenIdealEquiv_apply_val, frozenIdeal_multiplicity])

theorem frozenLocalMajorant_of_mod_two (Q : ℝ) {e : ℕ} (he : e % 3 = 2) :
    frozenLocalMajorant Q e = 0 := by
  have he0 : e ≠ 0 := by omega
  simp [frozenLocalMajorant, he0, he]

theorem frozenIdealMajorant_of_not_admissible
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (I : FrozenIdealCarrier K s)
    (hI : ¬frozenIdealAdmissible K s I) : frozenIdealMajorant K s I = 0 := by
  classical
  obtain ⟨v, hv⟩ := not_forall.mp hI
  have he : multiplicity v.val.asIdeal I.val % 3 = 2 := by
    have hlt := Nat.mod_lt (multiplicity v.val.asIdeal I.val) (by omega : 0 < 3)
    omega
  exact Finset.prod_eq_zero (Finset.mem_univ v) (frozenLocalMajorant_of_mod_two _ he)

theorem frozenIdealDirichletTerm_of_not_admissible
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (I : FrozenIdealCarrier K s)
    (hI : ¬frozenIdealAdmissible K s I) : frozenIdealDirichletTerm K s σ I = 0 := by
  rw [frozenIdealDirichletTerm, frozenIdealMajorant_of_not_admissible K s I hI, zero_mul]

def admissibleFrozenDirichletTerm (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ)
    (I : AdmissibleFrozenIdealCarrier K s) : ℝ := frozenIdealDirichletTerm K s σ I.val

theorem admissibleFrozenDirichletTerm_hasSum
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 0 ≤ σ) :
    HasSum (admissibleFrozenDirichletTerm K s σ)
      (∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ) := by
  have hs : Function.support (frozenIdealDirichletTerm K s σ) ⊆
      {I | frozenIdealAdmissible K s I} := by
    intro I hI
    by_contra hn
    exact hI (frozenIdealDirichletTerm_of_not_admissible K s σ I hn)
  exact (hasSum_subtype_iff_of_support_subset hs).mpr
    (frozenIdealDirichletTerm_hasSum K s hσ)

theorem admissibleFrozenDirichletTerm_summable
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 0 ≤ σ) :
    Summable (admissibleFrozenDirichletTerm K s σ) :=
  (admissibleFrozenDirichletTerm_hasSum K s hσ).summable

theorem admissibleFrozenDirichletTerm_tsum
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑' I : AdmissibleFrozenIdealCarrier K s, admissibleFrozenDirichletTerm K s σ I) =
      ∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ :=
  (admissibleFrozenDirichletTerm_hasSum K s hσ).tsum_eq

def admissibleFrozenTripleTerm (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ)
    (x : AdmissibleFrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K)) : ℝ :=
  frozenIdealTripleTerm K s σ (x.1.val, x.2)

theorem admissibleFrozenTripleTerm_nonneg
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ)
    (x : AdmissibleFrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K)) :
    0 ≤ admissibleFrozenTripleTerm K s σ x := by
  exact mul_nonneg (frozenIdealDirichletTerm_nonneg K s σ x.1.val)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem admissibleFrozenTripleTerm_hasSum
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSum (admissibleFrozenTripleTerm K s σ)
      ((∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ) *
        ((∑' c : Ideal (𝓞 K), (c.absNorm : ℝ) ^ (-(σ + 1 / 2))) *
          ∑' n : Ideal (𝓞 K), (n.absNorm : ℝ) ^ (-(3 * σ + 1)))) := by
  have hc := numberField_idealNorm_rpow_summable K (σ := σ + 1 / 2) (by linarith)
  have hn := numberField_idealNorm_rpow_summable K (σ := 3 * σ + 1) (by linarith)
  have hcn := hc.mul_of_nonneg hn (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have he := admissibleFrozenDirichletTerm_hasSum K s (by linarith : 0 ≤ σ)
  have hprod := he.summable.mul_of_nonneg hcn
    (fun I => frozenIdealDirichletTerm_nonneg K s σ I.val)
    (fun _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  exact he.mul (hc.hasSum.mul hn.hasSum hcn) hprod

theorem admissibleFrozenTripleTerm_subpower
    (K : Type*) [Field K] [NumberField K] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ), 1 / 2 < σ →
      (∑' x, admissibleFrozenTripleTerm K s σ x) ≤
        C * (∏ v ∈ s, (v.asIdeal.absNorm : ℝ)) ^ ε *
          ((∑' c : Ideal (𝓞 K), (c.absNorm : ℝ) ^ (-(σ + 1 / 2))) *
            ∑' n : Ideal (𝓞 K), (n.absNorm : ℝ) ^ (-(3 * σ + 1))) := by
  obtain ⟨C, hC, h⟩ := numberField_frozenLocalDirichlet_product_bound K hε
  refine ⟨C, hC, fun s σ hσ => ?_⟩
  rw [(admissibleFrozenTripleTerm_hasSum K s hσ).tsum_eq]
  exact mul_le_mul_of_nonneg_right (h s σ (by linarith))
    (mul_nonneg (tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem admissibleFrozenIndices_countable (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    Countable (AdmissibleFrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K)) := by
  let := numberField_ideals_countable K
  let : Countable (FrozenIdealCarrier K s) := by
    unfold FrozenIdealCarrier
    infer_instance
  let : Countable (AdmissibleFrozenIdealCarrier K s) := by
    unfold AdmissibleFrozenIdealCarrier
    infer_instance
  infer_instance

theorem admissibleFrozenTripleTerm_restricted
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    (U : Set (AdmissibleFrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K))) :
    Summable (fun x : U => admissibleFrozenTripleTerm K s σ x.val) ∧
      (∑' x : U, admissibleFrozenTripleTerm K s σ x.val) ≤
        ∑' x, admissibleFrozenTripleTerm K s σ x := by
  have h := (admissibleFrozenTripleTerm_hasSum K s hσ).summable
  exact ⟨h.subtype U, Summable.tsum_subtype_le _ U
    (admissibleFrozenTripleTerm_nonneg K s σ) h⟩

theorem admissibleFrozen_integral_norm_summable
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (M : X → ℝ)
    (hM : Integrable M μ)
    (F : AdmissibleFrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K) → X → ℂ)
    (hF : ∀ x, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x t, ‖F x t‖ ≤ admissibleFrozenTripleTerm K s σ x * M t) :
    (∀ x, Integrable (F x) μ) ∧ Summable (fun x => ∫ t, ‖F x t‖ ∂μ) := by
  have hi (x) : Integrable (F x) μ :=
    (hM.const_mul _).mono' (hF x) (Filter.Eventually.of_forall (hbound x))
  refine ⟨hi, ?_⟩
  apply ((admissibleFrozenTripleTerm_hasSum K s hσ).summable.mul_right
    (∫ t, M t ∂μ)).of_nonneg_of_le
  · intro x
    exact integral_nonneg fun _ => norm_nonneg _
  · intro x
    calc
      _ ≤ ∫ t, admissibleFrozenTripleTerm K s σ x * M t ∂μ :=
        integral_mono (hi x).norm (hM.const_mul _) (hbound x)
      _ = _ := integral_const_mul _ _

theorem admissibleFrozen_integral_tsum
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (M : X → ℝ)
    (hM : Integrable M μ)
    (F : AdmissibleFrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K) → X → ℂ)
    (hF : ∀ x, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x t, ‖F x t‖ ≤ admissibleFrozenTripleTerm K s σ x * M t) :
    (∑' x, ∫ t, F x t ∂μ) = ∫ t, (∑' x, F x t) ∂μ := by
  let := admissibleFrozenIndices_countable K s
  have h := admissibleFrozen_integral_norm_summable K s hσ μ M hM F hF hbound
  exact integral_tsum_of_summable_integral_norm h.1 h.2

/-- The original admissible ideal family has a finite total absolute integral
once the actual measurable profile envelope has been supplied. -/
theorem admissibleFrozen_total_integral_norm_le
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (M : X → ℝ)
    (hM : Integrable M μ)
    (F : AdmissibleFrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K) → X → ℂ)
    (hF : ∀ x, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x t, ‖F x t‖ ≤ admissibleFrozenTripleTerm K s σ x * M t) :
    (∑' x, ∫ t, ‖F x t‖ ∂μ) ≤
      (∑' x, admissibleFrozenTripleTerm K s σ x) * ∫ t, M t ∂μ := by
  have h := admissibleFrozen_integral_norm_summable K s hσ μ M hM F hF hbound
  have hi (x) : (∫ t, ‖F x t‖ ∂μ) ≤
      admissibleFrozenTripleTerm K s σ x * ∫ t, M t ∂μ := by
    calc
      _ ≤ ∫ t, admissibleFrozenTripleTerm K s σ x * M t ∂μ :=
        integral_mono (h.1 x).norm (hM.const_mul _) (hbound x)
      _ = _ := integral_const_mul _ _
  have hb := (admissibleFrozenTripleTerm_hasSum K s hσ).summable.mul_right (∫ t, M t ∂μ)
  simpa only [tsum_mul_right] using h.2.tsum_le_tsum hi hb

end
end SimultaneousPrimitiveRoots
