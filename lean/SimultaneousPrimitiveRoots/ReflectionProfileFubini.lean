module

public import SimultaneousPrimitiveRoots.AdmissibleFrozenIdeals
public import SimultaneousPrimitiveRoots.PositiveMultiplicativeMeasure

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain MeasureTheory Set
noncomputable section

/-- The actual admissible frozen ideal and two nonzero integral ideals.
Further exterior, squarefree or coprimality restrictions may be imposed later. -/
def ReflectionIdealIndices (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) : Type _ :=
  {x : AdmissibleFrozenIdealCarrier K s × Ideal (𝓞 K) × Ideal (𝓞 K) //
    x.2.1 ≠ ⊥ ∧ x.2.2 ≠ ⊥}

def reflectionIdealWeight (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ)
    (x : ReflectionIdealIndices K s) : ℝ := admissibleFrozenTripleTerm K s σ x.val

def reflectionIdealAmplitude (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (x : ReflectionIdealIndices K s) : ℝ :=
  frozenIdealMajorant K s x.val.1.val * (x.val.2.1.absNorm : ℝ) ^ (-(1 / 2 : ℝ)) *
    (x.val.2.2.absNorm : ℝ) ^ (-1 : ℝ)

def reflectionFrequencyNorm (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (x : ReflectionIdealIndices K s) : ℝ :=
  ((x.val.1.val.val * x.val.2.1 * x.val.2.2 ^ 3).absNorm : ℝ)

theorem reflectionIdealAmplitude_nonneg (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (x : ReflectionIdealIndices K s) :
    0 ≤ reflectionIdealAmplitude K s x := by
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ =>
    frozenLocalMajorant_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem reflectionFrequencyNorm_pos (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (x : ReflectionIdealIndices K s) :
    0 < reflectionFrequencyNorm K s x := by
  have ha : 0 < (x.val.1.val.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp x.val.1.val.property.1)
  have hc : 0 < (x.val.2.1.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp x.property.1)
  have hn : 0 < (x.val.2.2.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp x.property.2)
  unfold reflectionFrequencyNorm
  rw [map_mul, map_mul, map_pow, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  exact mul_pos (mul_pos ha hc) (pow_pos hn _)

theorem reflectionIdealWeight_eq_frequency (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (x : ReflectionIdealIndices K s) :
    reflectionIdealWeight K s σ x = reflectionIdealAmplitude K s x *
      reflectionFrequencyNorm K s x ^ (-σ) := by
  exact frozenIdealTripleTerm_eq_frequency K s σ x.val.1.val x.val.2.1 x.val.2.2
    x.property.1 x.property.2

theorem reflectionIdealWeight_nonneg (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (x : ReflectionIdealIndices K s) :
    0 ≤ reflectionIdealWeight K s σ x := admissibleFrozenTripleTerm_nonneg K s σ x.val

theorem reflectionIdealWeight_summable (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (reflectionIdealWeight K s σ) :=
  (admissibleFrozenTripleTerm_hasSum K s hσ).summable.subtype _

theorem reflectionIdealWeight_tsum_le (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' x, reflectionIdealWeight K s σ x) ≤ ∑' x, admissibleFrozenTripleTerm K s σ x := by
  exact (admissibleFrozenTripleTerm_restricted K s hσ _).2

theorem reflectionIdealIndices_countable (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) : Countable (ReflectionIdealIndices K s) := by
  let := admissibleFrozenIndices_countable K s
  unfold ReflectionIdealIndices
  infer_instance

/-- The exact scaling needed in Q/(t_d*T). No asymptotic estimate or Jacobian is used. -/
theorem reflectionProfile_scaled_rpow {Q t T : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (hT : 0 < T) (σ : ℝ) :
    (Q / (t * T)) ^ (-σ) = t ^ σ * T ^ σ * Q ^ (-σ) := by
  rw [Real.div_rpow hQ.le (mul_pos ht hT).le,
    Real.rpow_neg (mul_pos ht hT).le, div_inv_eq_mul, Real.mul_rpow ht.le hT.le]
  ring

/-- A grouped term with an explicit kernel, coefficient and profile family.
The actual theta/Whittaker identities and the profile bound remain separate inputs. -/
def reflectionProfileTerm (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (κ : ℝ → ℂ)
    (a : ReflectionIdealIndices K s → ℂ)
    (ψ : ReflectionIdealIndices K s → ℝ → ℂ) (t : ℝ)
    (x : ReflectionIdealIndices K s) (T : ℝ) : ℂ :=
  κ T * a x * ψ x (reflectionFrequencyNorm K s x / (t * T))

theorem reflectionProfileTerm_bound (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (κ : ℝ → ℂ)
    (a : ReflectionIdealIndices K s → ℂ) (ψ : ReflectionIdealIndices K s → ℝ → ℂ)
    (σ C t : ℝ) (ht : 0 < t)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x)
    (hψ : ∀ x u, 0 < u → ‖ψ x u‖ ≤ C * u ^ (-σ))
    (x : ReflectionIdealIndices K s) {T : ℝ} (hT : 0 < T) :
    ‖reflectionProfileTerm K s κ a ψ t x T‖ ≤ reflectionIdealWeight K s σ x *
      (C * t ^ σ * (T ^ σ * ‖κ T‖)) := by
  have hQ := reflectionFrequencyNorm_pos K s x
  calc
    _ = ‖κ T‖ * ‖a x‖ * ‖ψ x (reflectionFrequencyNorm K s x / (t * T))‖ := by
      simp only [reflectionProfileTerm, norm_mul]
    _ ≤ ‖κ T‖ * reflectionIdealAmplitude K s x *
        (C * (reflectionFrequencyNorm K s x / (t * T)) ^ (-σ)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha x) (norm_nonneg _))
        (hψ x _ (div_pos hQ (mul_pos ht hT))) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (reflectionIdealAmplitude_nonneg K s x))
    _ = _ := by
      rw [reflectionProfile_scaled_rpow hQ ht hT, reflectionIdealWeight_eq_frequency]
      ring

theorem reflectionProfileTerm_aestronglyMeasurable
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {κ : ℝ → ℂ}
    (hκ : ContinuousOn κ (Ioi 0)) (a : ReflectionIdealIndices K s → ℂ)
    (ψ : ReflectionIdealIndices K s → ℝ → ℂ)
    (hψ : ∀ x, ContinuousOn (ψ x) (Ioi 0)) {t : ℝ} (ht : 0 < t)
    (x : ReflectionIdealIndices K s) :
    AEStronglyMeasurable (reflectionProfileTerm K s κ a ψ t x)
      artinPositiveMultiplicativeMeasure := by
  have hQ := reflectionFrequencyNorm_pos K s x
  have hq : ContinuousOn (fun T : ℝ => reflectionFrequencyNorm K s x / (t * T))
      (Ioi 0) := continuousOn_const.div (continuousOn_const.mul continuousOn_id)
        (fun T hT => (mul_pos ht hT).ne')
  have hp := (hψ x).comp hq (fun T hT => div_pos hQ (mul_pos ht hT))
  have hf : ContinuousOn (reflectionProfileTerm K s κ a ψ t x) (Ioi 0) :=
    (hκ.mul continuousOn_const).mul hp
  exact (hf.aestronglyMeasurable measurableSet_Ioi).mono_ac
    (withDensity_absolutelyContinuous _ _)

theorem reflectionProfile_integral_norm_summable
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {κ : ℝ → ℂ}
    (hκ : ReflectionKernelDecay κ) (a : ReflectionIdealIndices K s → ℂ)
    (ψ : ReflectionIdealIndices K s → ℝ → ℂ)
    (hψc : ∀ x, ContinuousOn (ψ x) (Ioi 0)) {σ C t : ℝ}
    (hσ : 1 / 2 < σ) (ht : 0 < t)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x)
    (hψ : ∀ x u, 0 < u → ‖ψ x u‖ ≤ C * u ^ (-σ)) :
    (∀ x, Integrable (reflectionProfileTerm K s κ a ψ t x)
      artinPositiveMultiplicativeMeasure) ∧
    Summable (fun x => ∫ T, ‖reflectionProfileTerm K s κ a ψ t x T‖
      ∂artinPositiveMultiplicativeMeasure) := by
  let M : ℝ → ℝ := fun T => C * t ^ σ * (T ^ σ * ‖κ T‖)
  have hM : Integrable M artinPositiveMultiplicativeMeasure :=
    (reflectionKernelDecay_moment_integrable hκ σ).const_mul _
  have hb (x) : ∀ᵐ T ∂artinPositiveMultiplicativeMeasure,
      ‖reflectionProfileTerm K s κ a ψ t x T‖ ≤ reflectionIdealWeight K s σ x * M T := by
    filter_upwards [artinPositiveMultiplicative_ae_pos] with T hT
    exact reflectionProfileTerm_bound K s κ a ψ σ C t ht ha hψ x hT
  have hi (x) : Integrable (reflectionProfileTerm K s κ a ψ t x)
      artinPositiveMultiplicativeMeasure :=
    (hM.const_mul _).mono' (reflectionProfileTerm_aestronglyMeasurable K s hκ.1 a ψ hψc ht x)
      (hb x)
  refine ⟨hi, ?_⟩
  apply ((reflectionIdealWeight_summable K s hσ).mul_right
    (∫ T, M T ∂artinPositiveMultiplicativeMeasure)).of_nonneg_of_le
  · intro x
    exact integral_nonneg fun _ => norm_nonneg _
  · intro x
    calc
      _ ≤ ∫ T, reflectionIdealWeight K s σ x * M T
          ∂artinPositiveMultiplicativeMeasure := integral_mono_ae (hi x).norm
            (hM.const_mul _) (hb x)
      _ = _ := integral_const_mul _ _

theorem reflectionProfile_integral_tsum
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {κ : ℝ → ℂ}
    (hκ : ReflectionKernelDecay κ) (a : ReflectionIdealIndices K s → ℂ)
    (ψ : ReflectionIdealIndices K s → ℝ → ℂ)
    (hψc : ∀ x, ContinuousOn (ψ x) (Ioi 0)) {σ C t : ℝ}
    (hσ : 1 / 2 < σ) (ht : 0 < t)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x)
    (hψ : ∀ x u, 0 < u → ‖ψ x u‖ ≤ C * u ^ (-σ)) :
    (∑' x, ∫ T, reflectionProfileTerm K s κ a ψ t x T
      ∂artinPositiveMultiplicativeMeasure) =
      ∫ T, (∑' x, reflectionProfileTerm K s κ a ψ t x T)
        ∂artinPositiveMultiplicativeMeasure := by
  let := reflectionIdealIndices_countable K s
  have h := reflectionProfile_integral_norm_summable K s hκ a ψ hψc hσ ht ha hψ
  exact integral_tsum_of_summable_integral_norm h.1 h.2

/-- Positive-time convergence is derived from the actual scalar ideal series. -/
theorem reflectionProfileTerm_summable_of_pos
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (κ : ℝ → ℂ)
    (a : ReflectionIdealIndices K s → ℂ) (ψ : ReflectionIdealIndices K s → ℝ → ℂ)
    {σ C t T : ℝ} (hσ : 1 / 2 < σ) (ht : 0 < t) (hT : 0 < T)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x)
    (hψ : ∀ x u, 0 < u → ‖ψ x u‖ ≤ C * u ^ (-σ)) :
    Summable (fun x => reflectionProfileTerm K s κ a ψ t x T) := by
  exact (((reflectionIdealWeight_summable K s hσ).mul_right
    (C * t ^ σ * (T ^ σ * ‖κ T‖))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun x =>
      reflectionProfileTerm_bound K s κ a ψ σ C t ht ha hψ x hT)).of_norm

/-- The precise t_d^sigma*M_sigma(kappa)*D_f(sigma) bound, in dT/T.
Actual kernel construction and actual profile estimates are not asserted. -/
theorem reflectionProfile_total_integral_norm_le
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {κ : ℝ → ℂ}
    (hκ : ReflectionKernelDecay κ) (a : ReflectionIdealIndices K s → ℂ)
    (ψ : ReflectionIdealIndices K s → ℝ → ℂ)
    (hψc : ∀ x, ContinuousOn (ψ x) (Ioi 0)) {σ C t : ℝ}
    (hσ : 1 / 2 < σ) (hC : 0 ≤ C) (ht : 0 < t)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x)
    (hψ : ∀ x u, 0 < u → ‖ψ x u‖ ≤ C * u ^ (-σ)) :
    (∑' x, ∫ T, ‖reflectionProfileTerm K s κ a ψ t x T‖
      ∂artinPositiveMultiplicativeMeasure) ≤
      C * t ^ σ * artinKernelMoment κ σ *
        ∑' x, admissibleFrozenTripleTerm K s σ x := by
  have h := reflectionProfile_integral_norm_summable K s hκ a ψ hψc hσ ht ha hψ
  have hM := (reflectionKernelDecay_moment_integrable hκ σ).const_mul (C * t ^ σ)
  have hb (x) : (∫ T, ‖reflectionProfileTerm K s κ a ψ t x T‖
      ∂artinPositiveMultiplicativeMeasure) ≤
      reflectionIdealWeight K s σ x * (C * t ^ σ * artinKernelMoment κ σ) := by
    calc
      _ ≤ ∫ T, reflectionIdealWeight K s σ x * (C * t ^ σ * (T ^ σ * ‖κ T‖))
          ∂artinPositiveMultiplicativeMeasure := by
        apply integral_mono_ae (h.1 x).norm (hM.const_mul _)
        filter_upwards [artinPositiveMultiplicative_ae_pos] with T hT
        exact reflectionProfileTerm_bound K s κ a ψ σ C t ht ha hψ x hT
      _ = _ := by rw [integral_const_mul, integral_const_mul, artinKernelMoment]
  have he := (reflectionIdealWeight_summable K s hσ).mul_right
    (C * t ^ σ * artinKernelMoment κ σ)
  have hle := h.2.tsum_le_tsum hb he
  have hfactor : 0 ≤ C * t ^ σ * artinKernelMoment κ σ :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg ht.le _)) (artinKernelMoment_nonneg _ _)
  calc
    _ ≤ (∑' x, reflectionIdealWeight K s σ x) *
        (C * t ^ σ * artinKernelMoment κ σ) := by simpa only [tsum_mul_right] using hle
    _ ≤ (∑' x, admissibleFrozenTripleTerm K s σ x) *
        (C * t ^ σ * artinKernelMoment κ σ) :=
      mul_le_mul_of_nonneg_right (reflectionIdealWeight_tsum_le K s hσ) hfactor
    _ = _ := mul_comm _ _

/-- The integral of the full pointwise absolute series obeys the same bound.
Both integral/sum exchange and moment convergence are conclusions here. -/
theorem reflectionProfile_absolute_integral_le
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {κ : ℝ → ℂ}
    (hκ : ReflectionKernelDecay κ) (a : ReflectionIdealIndices K s → ℂ)
    (ψ : ReflectionIdealIndices K s → ℝ → ℂ)
    (hψc : ∀ x, ContinuousOn (ψ x) (Ioi 0)) {σ C t : ℝ}
    (hσ : 1 / 2 < σ) (hC : 0 ≤ C) (ht : 0 < t)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x)
    (hψ : ∀ x u, 0 < u → ‖ψ x u‖ ≤ C * u ^ (-σ)) :
    (∫ T, (∑' x, ‖reflectionProfileTerm K s κ a ψ t x T‖)
      ∂artinPositiveMultiplicativeMeasure) ≤
      C * t ^ σ * artinKernelMoment κ σ *
        ∑' x, admissibleFrozenTripleTerm K s σ x := by
  let := reflectionIdealIndices_countable K s
  have h := reflectionProfile_integral_norm_summable K s hκ a ψ hψc hσ ht ha hψ
  have hs : Summable (fun x => ∫ T, ‖‖reflectionProfileTerm K s κ a ψ t x T‖‖
      ∂artinPositiveMultiplicativeMeasure) := by simpa only [norm_norm] using h.2
  rw [← integral_tsum_of_summable_integral_norm (fun x => (h.1 x).norm) hs]
  exact reflectionProfile_total_integral_norm_le K s hκ a ψ hψc hσ hC ht ha hψ

end
end SimultaneousPrimitiveRoots
