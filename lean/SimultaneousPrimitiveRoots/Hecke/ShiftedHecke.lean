module

public import SimultaneousPrimitiveRoots.Hecke.ShiftedMellin
public import SimultaneousPrimitiveRoots.Hecke.ShiftedTraceDualTheta
public import SimultaneousPrimitiveRoots.Hecke.PartialZeta

/-!
# Hecke's `Λ` of a unit-stable union of lattice cosets

Let `b` be a `ℚ`-basis of `K` and `r : R → K` finitely many shifts such that the cosets
`r ρ + ℤ b` are pairwise disjoint and avoid `0`, and their union `S = cosetSet b r` is stable under
multiplication by units. Each coset has Hecke's FE-pair of averaged shifted theta functions over
the unit cube (`heckeShiftedFEPair`), whose `Λ` is holomorphic on `ℂ \ {n/2}`
(`heckeShiftedFEPair_differentiableAt`): the constant term `f₀` vanishes, so there is no pole at
`0`. For real `s > n/2`,

`∑_ρ Λ_ρ(s) = π^{-s} Γ(s) ∑_{x ∈ S ∩ cone} heckeConst K s · |N x|^{-2s/n}`

(`sum_heckeShiftedFEPair_ofReal`). The chain of identities is the one of `heckeFEPair_ofReal`:
the averaged Epstein series of the coset (`ThetaFamily.shiftedΛ_eq_integral`), the unit weights on
the cube, unfolding the units over `S` (`tsum_lintegral_unfold`), and Hecke's integral.

For a ray class `C` modulo `𝔪`, `S` is the set of elements of an ideal `𝔟 ∈ C⁻¹` congruent to a
unit modulo `𝔟𝔪`, and the right side is the partial zeta function of `C` (step Z2 of
`docs/unconditional-roadmap.md`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units MeasureTheory Set Function Filter Complex
open scoped ENNReal Real Topology

/-! ### Real values of the averaged shifted `Λ` -/

section Family

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- `∑_m C ‖m + v‖^{-2σ}` converges for `σ > d/2` when the coset `ℤ^d + v` avoids `0`. -/
theorem summable_norm_shift_rpow {v : d → ℝ} (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) {σ : ℝ}
    (hσ : (Fintype.card d : ℝ) / 2 < σ) (C : ℝ) :
    Summable fun m : d → ℤ => C * ‖intVec m + v‖ ^ (-(2 * σ)) := by
  obtain ⟨c, hc, hcm⟩ := exists_norm_shift_ge v hv
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  have hr : -(2 * σ) < -(Module.finrank ℤ (intSpan d) : ℝ) := by
    rw [finrank_intSpan]
    linarith
  have hL := ZLattice.summable_norm_rpow (intSpan d) (-(2 * σ)) hr
  have hL' : Summable fun m : d → ℤ => |C| * c ^ (-(2 * σ)) * ‖intVec m‖ ^ (-(2 * σ)) :=
    ((intSpanEquiv (d := d)).summable_iff.mpr hL).mul_left _
  refine Summable.of_norm_bounded_eventually hL' ?_
  filter_upwards [(Set.finite_singleton (0 : d → ℤ)).compl_mem_cofinite] with m hm
  have hm0 : m ≠ 0 := hm
  have h1 := one_le_norm_intVec hm0
  have hn0 : 0 < ‖intVec m‖ := by linarith
  have hpos : 0 < c * ‖intVec m‖ := by positivity
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
  calc ‖intVec m + v‖ ^ (-(2 * σ)) ≤ (c * ‖intVec m‖) ^ (-(2 * σ)) :=
        Real.rpow_le_rpow_of_nonpos hpos (hcm m) (by linarith)
    _ = c ^ (-(2 * σ)) * ‖intVec m‖ ^ (-(2 * σ)) := Real.mul_rpow hc.le hn0.le

omit [DecidableEq d] in
/-- The terms of the shifted Epstein series of a uniformly elliptic family, bounded uniformly. -/
theorem sqNorm_shift_rpow_le {A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)} {κ : ℝ} (hκ : 0 < κ)
    (hlow : ∀ u : d → ℝ, κ * ‖u‖ ^ 2 ≤ sqNorm (A u)) {v : d → ℝ}
    (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) {σ : ℝ} (hσ : 0 < σ) (m : d → ℤ) :
    sqNorm (A (intVec m + v)) ^ (-σ) ≤ κ ^ (-σ) * ‖intVec m + v‖ ^ (-(2 * σ)) := by
  have hn0 : 0 < ‖intVec m + v‖ := norm_pos_iff.mpr (hv m)
  have hpos : 0 < κ * ‖intVec m + v‖ ^ 2 := by positivity
  calc sqNorm (A (intVec m + v)) ^ (-σ) ≤ (κ * ‖intVec m + v‖ ^ 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hpos (hlow _) (by linarith)
    _ = κ ^ (-σ) * ‖intVec m + v‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow hκ.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 2
        push_cast
        ring

/-- The real Epstein series of a coset is continuous in the parameter of a family. -/
theorem ThetaFamily.continuous_shifted_epstein {P : Type*} [TopologicalSpace P]
    (F : ThetaFamily d P) {v : d → ℝ} (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) {σ : ℝ}
    (hσ : (Fintype.card d : ℝ) / 2 < σ) :
    Continuous fun p => ∑' m : d → ℤ, sqNorm (F.A p (intVec m + v)) ^ (-σ) := by
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  refine continuous_tsum (u := fun m : d → ℤ => F.κ ^ (-σ) * ‖intVec m + v‖ ^ (-(2 * σ)))
    (fun m => ?_) (summable_norm_shift_rpow hv hσ _) (fun m p => ?_)
  · have hs : Continuous (sqNorm (d := d)) := by
      unfold sqNorm
      fun_prop
    exact (hs.comp (F.continuous_A (intVec m + v))).rpow_const
      fun p => Or.inl (sqNorm_shift_pos (F.A p) hv m).ne'
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sqNorm_nonneg _) _)]
    exact sqNorm_shift_rpow_le F.κ_pos (F.lower p) hv hσ0 m

/-- The real Epstein series of a coset is bounded uniformly over a family. -/
theorem ThetaFamily.shifted_epstein_le {P : Type*} [TopologicalSpace P]
    (F : ThetaFamily d P) {v : d → ℝ} (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) {σ : ℝ}
    (hσ : (Fintype.card d : ℝ) / 2 < σ) (p : P) :
    ∑' m : d → ℤ, sqNorm (F.A p (intVec m + v)) ^ (-σ) ≤
      ∑' m : d → ℤ, F.κ ^ (-σ) * ‖intVec m + v‖ ^ (-(2 * σ)) := by
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  refine Summable.tsum_le_tsum (fun m => sqNorm_shift_rpow_le F.κ_pos (F.lower p) hv hσ0 m) ?_
    (summable_norm_shift_rpow hv hσ _)
  exact (summable_norm_shift_rpow hv hσ _).of_nonneg_of_le
    (fun m => Real.rpow_nonneg (sqNorm_nonneg _) _)
    (fun m => sqNorm_shift_rpow_le F.κ_pos (F.lower p) hv hσ0 m)

/-- **Real values of the averaged shifted `Λ`.** -/
theorem ThetaFamily.shiftedΛ_ofReal {P : Type*} [TopologicalSpace P] [MeasurableSpace P]
    [OpensMeasurableSpace P] (F : ThetaFamily d P) (μ : Measure P) [IsFiniteMeasure μ]
    (v : d → ℝ) [Nonempty d] (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) {s : ℝ}
    (hs : (Fintype.card d : ℝ) / 2 < s) :
    (F.shiftedFEPair μ v hv).Λ (s : ℂ) = ((π ^ (-s) * Real.Gamma s *
      ∫ p, ∑' m : d → ℤ, sqNorm (F.A p (intVec m + v)) ^ (-s) ∂μ : ℝ) : ℂ) := by
  rw [F.shiftedΛ_eq_integral μ v hv (by simpa using hs)]
  have hpt : ∀ p, (∑' m : d → ℤ, (π : ℂ) ^ (-(s : ℂ)) * Complex.Gamma (s : ℂ) * 1 /
      ((sqNorm (F.A p (intVec m + v)) : ℝ) : ℂ) ^ (s : ℂ)) =
      ((π ^ (-s) * Real.Gamma s * ∑' m : d → ℤ, sqNorm (F.A p (intVec m + v)) ^ (-s) : ℝ) :
        ℂ) := by
    intro p
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    have hq := sqNorm_nonneg (F.A p (intVec m + v))
    rw [Real.rpow_neg hq, ← Complex.ofReal_cpow hq, Complex.Gamma_ofReal,
      show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_complex_ofReal, integral_const_mul]

end Family

/-! ### Hecke's FE-pair of a coset of a number field lattice -/

section NumberField

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The coset `α₀ + ℤ b` avoids `0` when `α₀ ∉ ℤ b`. -/
theorem intVec_add_basisCoords_ne_zero (b : Module.Basis ι ℚ K) {α₀ : K}
    (hα₀ : α₀ ∉ latticeSet (b : ι → K)) (m : ι → ℤ) : intVec m + basisCoords b α₀ ≠ 0 := by
  intro h
  apply hα₀
  refine ⟨-m, ?_⟩
  have hq : ∀ j, b.repr α₀ j = ((-m j : ℤ) : ℚ) := fun j => by
    have h1 := congrFun h j
    simp only [Pi.add_apply, intVec, basisCoords, Pi.zero_apply] at h1
    have h2 : ((b.repr α₀ j : ℚ) : ℝ) = (((-m j : ℤ) : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h2
  have hrepr : α₀ = ∑ j, b.repr α₀ j • b j := (b.sum_repr α₀).symm
  unfold latticePt
  conv_rhs => rw [hrepr]
  apply Finset.sum_congr rfl
  intro j _
  rw [hq j, Int.cast_smul_eq_zsmul ℚ]
  rfl

/-- **Hecke's FE-pair of the coset `α₀ + ℤ b`**: averaged shifted theta functions over the unit
cube. -/
def heckeShiftedFEPair [Nonempty ι] (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) {α₀ : K}
    (hα₀ : α₀ ∉ latticeSet (b : ι → K)) : WeakFEPair ℂ :=
  (heckeFamily b e).shiftedFEPair (heckeMeasure K) (basisCoords b α₀)
    (intVec_add_basisCoords_ne_zero b hα₀)

/-- The `Λ` of a coset is holomorphic away from `n/2`. -/
theorem heckeShiftedFEPair_differentiableAt [Nonempty ι] (b : Module.Basis ι ℚ K)
    (e : ι ≃ (K →+* ℂ)) {α₀ : K} (hα₀ : α₀ ∉ latticeSet (b : ι → K)) {s : ℂ}
    (hsk : s ≠ ((Fintype.card ι : ℝ) / 2 : ℝ)) :
    DifferentiableAt ℂ (heckeShiftedFEPair b e hα₀).Λ s :=
  ThetaFamily.shiftedFEPair_differentiableAt _ _ _ _ hsk

theorem sqNorm_heckeFamily_shift (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    (p : Fin (rank K) → ℝ) (m : ι → ℤ) (α₀ : K) :
    sqNorm ((heckeFamily b e).A p (intVec m + basisCoords b α₀)) =
      ∑ σ, (unitWeights K).y p σ * Complex.normSq (σ (latticePt (b : ι → K) m + α₀)) := by
  rw [heckeFamily, WeightFamily.thetaFamily_A, casEquiv_apply,
    sqNorm_casMatrix_mulVec_shift b e ((unitWeights K).w_conj p) m α₀,
    WeightFamily.weightedNormSq_w]
  rfl

theorem sqNorm_heckeFamily_shift_of_mem_cube (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {p : Fin (rank K) → ℝ} (hp : p ∈ unitCube K) (m : ι → ℤ) (α₀ : K) :
    sqNorm ((heckeFamily b e).A p (intVec m + basisCoords b α₀)) =
      normForm (latticePt (b : ι → K) m + α₀) p := by
  rw [sqNorm_heckeFamily_shift]
  unfold normForm
  apply Finset.sum_congr rfl
  intro σ _
  rw [unitWeights_y_of_mem_cube hp]

/-- The cube integral of the shifted Epstein series of a coset, in `ℝ≥0∞`. -/
def cosetIntegral (b : Module.Basis ι ℚ K) (α₀ : K) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in unitCube K, ∑' m : ι → ℤ,
    ENNReal.ofReal (normForm (latticePt (b : ι → K) m + α₀) p ^ (-s))

theorem cosetIntegral_eq (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) {α₀ : K}
    (hα₀ : α₀ ∉ latticeSet (b : ι → K)) {s : ℝ} (hs : (Fintype.card ι : ℝ) / 2 < s) :
    cosetIntegral b α₀ s = ∫⁻ p in unitCube K, ENNReal.ofReal
      (∑' m : ι → ℤ, sqNorm ((heckeFamily b e).A p (intVec m + basisCoords b α₀)) ^ (-s)) := by
  have hv := intVec_add_basisCoords_ne_zero b hα₀
  have hsumG : ∀ p, Summable fun m : ι → ℤ =>
      sqNorm ((heckeFamily b e).A p (intVec m + basisCoords b α₀)) ^ (-s) := fun p => by
    refine (summable_shifted_epstein ((heckeFamily b e).A p) hv hs).congr fun m => ?_
    rw [norm_one, one_div, Real.rpow_neg (sqNorm_nonneg _)]
  refine setLIntegral_congr_fun measurableSet_unitCube (fun p hp => ?_)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun m => Real.rpow_nonneg (sqNorm_nonneg _) _) (hsumG p)]
  apply tsum_congr
  intro m
  rw [sqNorm_heckeFamily_shift_of_mem_cube b e hp]

theorem cosetIntegral_ne_top (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) {α₀ : K}
    (hα₀ : α₀ ∉ latticeSet (b : ι → K)) {s : ℝ} (hs : (Fintype.card ι : ℝ) / 2 < s) :
    cosetIntegral b α₀ s ≠ ∞ := by
  have hv := intVec_add_basisCoords_ne_zero b hα₀
  rw [cosetIntegral_eq b e hα₀ hs]
  refine (lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal
    ((heckeFamily b e).shifted_epstein_le hv hs p)) ?_).ne
  rw [lintegral_const, Measure.restrict_apply_univ, volume_unitCube, mul_one]
  exact ENNReal.ofReal_lt_top

/-- **Real values of the `Λ` of a coset**, through the cube integral of its Epstein series. -/
theorem heckeShiftedFEPair_ofReal [Nonempty ι] (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {α₀ : K} (hα₀ : α₀ ∉ latticeSet (b : ι → K)) {s : ℝ} (hs : (Fintype.card ι : ℝ) / 2 < s) :
    (heckeShiftedFEPair b e hα₀).Λ (s : ℂ) =
      ((π ^ (-s) * Real.Gamma s * (cosetIntegral b α₀ s).toReal : ℝ) : ℂ) := by
  have hv := intVec_add_basisCoords_ne_zero b hα₀
  rw [heckeShiftedFEPair, ThetaFamily.shiftedΛ_ofReal _ _ _ _ hs, cosetIntegral_eq b e hα₀ hs]
  congr 2
  have hGcont := (heckeFamily b e).continuous_shifted_epstein hv hs
  have hGnn : ∀ p, 0 ≤ ∑' m : ι → ℤ,
      sqNorm ((heckeFamily b e).A p (intVec m + basisCoords b α₀)) ^ (-s) :=
    fun p => tsum_nonneg fun m => Real.rpow_nonneg (sqNorm_nonneg _) _
  rw [heckeMeasure,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hGnn) hGcont.aestronglyMeasurable]

/-! ### A unit-stable union of cosets -/

/-- The union of the cosets `r ρ + ℤ b`. -/
def cosetSet (b : ι → K) {R : Type*} (r : R → K) : Set K :=
  Set.range fun z : R × (ι → ℤ) => latticePt b z.2 + r z.1

omit [DecidableEq ι] in
/-- **Unfolding over a unit-stable union of cosets**: the cube integrals of the cosets add up to
Hecke's integrals over the cone points of the union. -/
theorem sum_cosetIntegral_eq (b : Module.Basis ι ℚ K) {R : Type*} [Fintype R] (r : R → K)
    (hinj : Injective fun z : R × (ι → ℤ) => latticePt (b : ι → K) z.2 + r z.1)
    (hS : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ cosetSet (b : ι → K) r → (u : K) * x ∈ cosetSet b r)
    {s : ℝ} (hs : 0 < s) :
    ∑ ρ, cosetIntegral b (r ρ) s = ∑' x : coneSet (cosetSet (b : ι → K) r), ENNReal.ofReal
      (heckeConst K s * |(Algebra.norm ℚ (x : K) : ℝ)| ^ (-(2 * s / Module.finrank ℚ K))) := by
  set F : K → (Fin (rank K) → ℝ) → ℝ≥0∞ := fun x p => ENNReal.ofReal (normForm x p ^ (-s))
    with hF
  have hcontF : ∀ x : K, Continuous (fun p => normForm x p) := fun x => by
    unfold normForm unitWeight
    fun_prop
  have hmeas : ∀ x : K, Measurable (F x) := fun x => by
    have : Measurable fun p => normForm x p ^ (-s) :=
      ((hcontF x).measurable).pow_const _
    exact ENNReal.measurable_ofReal.comp this
  have hF0 : ∀ p, F 0 p = 0 := fun p => by
    have : normForm (0 : K) p = 0 := by simp [normForm]
    simp [hF, this, Real.zero_rpow (by linarith : -s ≠ 0)]
  have hFshift : ∀ k x p, F (((unitPow k : (𝓞 K)ˣ) : K) * x) p = F x (p + intVec k) :=
    fun k x p => by simp only [hF, normForm_unitPow_mul]
  have h1 : ∀ ρ, cosetIntegral b (r ρ) s =
      ∑' m : ι → ℤ, ∫⁻ p in unitCube K, F (latticePt (b : ι → K) m + r ρ) p := by
    intro ρ
    unfold cosetIntegral
    rw [lintegral_tsum (fun m => (hmeas _).aemeasurable)]
  simp_rw [h1]
  rw [← tsum_fintype (L := .unconditional _), ← ENNReal.tsum_prod]
  have heq := (Equiv.ofInjective _ hinj).tsum_eq
    (fun x : cosetSet (b : ι → K) r => ∫⁻ p in unitCube K, F x p)
  simp only [Equiv.ofInjective_apply] at heq
  rw [show (∑' z : R × (ι → ℤ), ∫⁻ p in unitCube K, F (latticePt (b : ι → K) z.2 + r z.1) p) =
    ∑' x : cosetSet (b : ι → K) r, ∫⁻ p in unitCube K, F x p from heq,
    tsum_lintegral_unfold hS F hF0 hFshift]
  apply tsum_congr
  intro x
  have hx0 : (x : K) ≠ 0 := x.2.2.1
  have hI := integral_normForm_rpow hx0 hs
  have hne : ∫ p : Fin (rank K) → ℝ, normForm (x : K) p ^ (-s) ≠ 0 := by
    rw [hI]
    have hN : 0 < |(Algebra.norm ℚ (x : K) : ℝ)| := by
      rw [abs_pos]
      exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx0)
    exact (mul_pos (heckeConst_pos hs) (Real.rpow_pos_of_pos hN _)).ne'
  have hint := Integrable.of_integral_ne_zero hne
  rw [← hI, ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun p => Real.rpow_nonneg (Finset.sum_nonneg fun σ _ =>
      mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)) _)]

/-- **Hecke's `Λ` of a unit-stable union of cosets is a partial zeta function of the cone**: for
real `s > n/2`, the sum of the `Λ`s of the cosets is
`π^{-s} Γ(s) ∑_{x ∈ S ∩ cone} heckeConst K s · |N x|^{-2s/n}`. -/
theorem sum_heckeShiftedFEPair_ofReal [Nonempty ι] (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {R : Type*} [Fintype R] (r : R → K) (hr : ∀ ρ, r ρ ∉ latticeSet (b : ι → K))
    (hinj : Injective fun z : R × (ι → ℤ) => latticePt (b : ι → K) z.2 + r z.1)
    (hS : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ cosetSet (b : ι → K) r → (u : K) * x ∈ cosetSet b r)
    {s : ℝ} (hs : (Fintype.card ι : ℝ) / 2 < s) :
    ∑ ρ, (heckeShiftedFEPair b e (hr ρ)).Λ (s : ℂ) = ((π ^ (-s) * Real.Gamma s *
      ∑' x : coneSet (cosetSet (b : ι → K) r), heckeConst K s *
        |(Algebra.norm ℚ (x : K) : ℝ)| ^ (-(2 * s / Module.finrank ℚ K)) : ℝ) : ℂ) := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  simp_rw [heckeShiftedFEPair_ofReal b e (hr _) hs]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum,
    ← ENNReal.toReal_sum (fun ρ _ => cosetIntegral_ne_top b e (hr ρ) hs),
    sum_cosetIntegral_eq b r hinj hS hs0, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  congr 2
  apply tsum_congr
  intro x
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (heckeConst_pos hs0).le (Real.rpow_nonneg (abs_nonneg _) _)

end NumberField

end SimultaneousPrimitiveRoots.Hecke

end
