module

public import SimultaneousPrimitiveRoots.FrozenIdealEquivalence
public import SimultaneousPrimitiveRoots.FrozenMajorantFubini

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain MeasureTheory
noncomputable section

/-- The frozen coefficient is computed from the multiplicities of an
actual supported ideal. -/
def frozenIdealMajorant (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (I : FrozenIdealCarrier K s) : ℝ :=
  ∏ v : s, frozenLocalMajorant (v.val.asIdeal.absNorm : ℝ)
    (multiplicity v.val.asIdeal I.val)

def frozenIdealDirichletTerm (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (I : FrozenIdealCarrier K s) : ℝ :=
  frozenIdealMajorant K s I * (I.val.absNorm : ℝ) ^ (-σ)

theorem frozenIdealDirichletTerm_equiv (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (e : s → ℕ) :
    frozenIdealDirichletTerm K s σ (frozenIdealEquiv K s e) =
      frozenExponentTerm (fun v : s => (v.val.asIdeal.absNorm : ℝ)) σ e := by
  rw [numberFieldFrozenIdeal_dirichletTerm]
  simp only [frozenIdealDirichletTerm, frozenIdealMajorant, frozenIdealEquiv_apply_val,
    frozenIdeal_multiplicity]

theorem frozenIdealDirichletTerm_nonneg (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (I : FrozenIdealCarrier K s) :
    0 ≤ frozenIdealDirichletTerm K s σ I := by
  exact mul_nonneg (Finset.prod_nonneg fun _ _ =>
    frozenLocalMajorant_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem frozenIdealDirichletTerm_hasSum (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 0 ≤ σ) :
    HasSum (frozenIdealDirichletTerm K s σ)
      (∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ) := by
  apply (frozenIdealEquiv K s).hasSum_iff.mp
  have hQ (v : s) : 2 ≤ (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (show 2 ≤ v.val.asIdeal.absNorm by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v.val
      omega)
  have hprod : (∏ v : s, frozenLocalDirichlet (v.val.asIdeal.absNorm : ℝ) σ) =
      ∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ := by
    simpa only [Finset.attach_eq_univ] using
      Finset.prod_attach s (fun v => frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ)
  simpa only [Function.comp_def, frozenIdealDirichletTerm_equiv, hprod] using
    frozenExponentTerm_hasSum (fun v : s => (v.val.asIdeal.absNorm : ℝ)) hQ hσ

theorem frozenIdealDirichletTerm_summable (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 0 ≤ σ) :
    Summable (frozenIdealDirichletTerm K s σ) :=
  (frozenIdealDirichletTerm_hasSum K s hσ).summable

theorem frozenIdealDirichletTerm_tsum (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑' I : FrozenIdealCarrier K s, frozenIdealDirichletTerm K s σ I) =
      ∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ :=
  (frozenIdealDirichletTerm_hasSum K s hσ).tsum_eq

theorem frozenIdeal_empty_eq_top (K : Type*) [Field K] [NumberField K]
    (I : FrozenIdealCarrier K ∅) : I.val = ⊤ := by
  have h := frozenIdeal_reconstruct K ∅ I
  simpa only [numberFieldFrozenIdeal, Finset.univ_eq_empty, Finset.prod_empty,
    Ideal.one_eq_top] using h.symm

def frozenIdealTripleEquiv (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ((s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K)) ≃
      (FrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K)) :=
  Equiv.prodCongr (frozenIdealEquiv K s) (Equiv.refl _)

def frozenIdealTripleTerm (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ)
    (x : FrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K)) : ℝ :=
  frozenIdealDirichletTerm K s σ x.1 *
    ((x.2.1.absNorm : ℝ) ^ (-(σ + 1 / 2)) *
      (x.2.2.absNorm : ℝ) ^ (-(3 * σ + 1)))

theorem frozenIdealTripleTerm_equiv (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ)
    (x : (s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K)) :
    frozenIdealTripleTerm K s σ (frozenIdealTripleEquiv K s x) =
      numberFieldFrozenMajorantTerm K s σ x := by
  change frozenIdealDirichletTerm K s σ (frozenIdealEquiv K s x.1) *
    ((x.2.1.absNorm : ℝ) ^ (-(σ + 1 / 2)) *
      (x.2.2.absNorm : ℝ) ^ (-(3 * σ + 1))) = _
  rw [frozenIdealDirichletTerm_equiv]
  rfl

theorem frozenIdealTripleTerm_hasSum (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSum (frozenIdealTripleTerm K s σ)
      ((∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ) *
        ((∑' c : Ideal (𝓞 K), (c.absNorm : ℝ) ^ (-(σ + 1 / 2))) *
          ∑' n : Ideal (𝓞 K), (n.absNorm : ℝ) ^ (-(3 * σ + 1)))) := by
  apply (frozenIdealTripleEquiv K s).hasSum_iff.mp
  simpa only [Function.comp_def, frozenIdealTripleTerm_equiv] using
    numberFieldFrozenMajorantTerm_hasSum K s hσ

/-- The weight on the original ideal carrier is exactly the frequency norm
weight, including when c and n have common prime factors. -/
theorem frozenIdealTripleTerm_eq_frequency (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (I : FrozenIdealCarrier K s)
    (c n : Ideal (𝓞 K)) (hc : c ≠ ⊥) (hn : n ≠ ⊥) :
    frozenIdealTripleTerm K s σ (I, c, n) =
      frozenIdealMajorant K s I * (c.absNorm : ℝ) ^ (-(1 / 2 : ℝ)) *
        (n.absNorm : ℝ) ^ (-1 : ℝ) * ((I.val * c * n ^ 3).absNorm : ℝ) ^ (-σ) := by
  obtain ⟨e, rfl⟩ := (frozenIdealEquiv K s).surjective I
  change frozenIdealTripleTerm K s σ (frozenIdealTripleEquiv K s (e, c, n)) = _
  rw [frozenIdealTripleTerm_equiv]
  simpa only [frozenIdealMajorant, frozenIdealEquiv_apply_val, frozenIdeal_multiplicity]
    using numberFieldFrozenMajorantTerm_eq_frequency K s σ e c n hc hn

theorem frozenIdealTripleTerm_summable (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (frozenIdealTripleTerm K s σ) :=
  (frozenIdealTripleTerm_hasSum K s hσ).summable

/-- Fubini on the original supported ideal carrier. The actual profile
envelope is still required, but summability of integral norms is derived. -/
theorem frozenIdeal_integral_tsum (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (M : X → ℝ)
    (hM0 : ∀ t, 0 ≤ M t) (hM : Integrable M μ)
    (F : FrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K) → X → ℂ)
    (hF : ∀ x, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x t, ‖F x t‖ ≤ frozenIdealTripleTerm K s σ x * M t) :
    (∑' x, ∫ t, F x t ∂μ) = ∫ t, (∑' x, F x t) ∂μ := by
  let E := frozenIdealTripleEquiv K s
  have h := frozenMajorant_integral_tsum K s hσ μ M hM0 hM
    (fun x => F (E x)) (fun x => hF (E x))
    (fun x t => by simpa only [E, frozenIdealTripleTerm_equiv] using hbound (E x) t)
  have hl := E.tsum_eq (fun x => ∫ t, F x t ∂μ)
  have hr (t) := E.tsum_eq (fun x => F x t)
  simpa only [hl, hr] using h

end
end SimultaneousPrimitiveRoots
