module

public import SimultaneousPrimitiveRoots.Hecke.PartialZeta
public import SimultaneousPrimitiveRoots.Hecke.DualFamily

/-!
# The dual side of Hecke's functional equation

The `symm` side of `heckeFEPair b e` is the averaged theta function of the trace-dual lattice
`L^∨ = ℤ b^∨` with the inverse weights `y_p⁻¹ = y_{-p}`. Unfolding over the negated cube gives, for
real `s > n/2`,

`(heckeFEPair b e).symm.Λ s = π^{-s} Γ(s) ∑_{x ∈ L^∨ ∩ cone} heckeConst K s · |N x|^{-2s/n}`.

The trace dual of a unit-stable lattice is unit-stable (`latticeSet_traceDual_unit_mul`). With the
functional equation of the FE-pair this is Hecke's functional equation relating the cone sums of
`L` at `n/2 - s` and of `L^∨` at `s`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units MeasureTheory Set
open scoped ENNReal Real

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitWeight_neg (p : Fin (rank K) → ℝ) (σ : K →+* ℂ) :
    unitWeight (-p) σ = (unitWeight p σ)⁻¹ := by
  unfold unitWeight
  rw [← Real.exp_neg]
  congr 1
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg]

theorem sqNorm_heckeFamily_dual_of_mem_cube (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {p : Fin (rank K) → ℝ} (hp : p ∈ unitCube K) (m : ι → ℤ) :
    sqNorm (dualEquiv ((heckeFamily b e).A p) (intVec m)) =
      normForm (latticePt (b.traceDual : ι → K) m) (-p) := by
  rw [heckeFamily, WeightFamily.sqNorm_thetaFamily_dual, WeightFamily.weightedNormSq_w']
  unfold normForm latticePt
  apply Finset.sum_congr rfl
  intro σ _
  rw [unitWeights_y_of_mem_cube hp, unitWeight_neg]

/-- Unfolding over the negated cube. -/
theorem tsum_lintegral_unfold_neg {L : Set K}
    (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ L → (u : K) * x ∈ L)
    (F : K → (Fin (rank K) → ℝ) → ℝ≥0∞) (hF0 : ∀ p, F 0 p = 0)
    (hFshift : ∀ k x p, F (((unitPow k : (𝓞 K)ˣ) : K) * x) p = F x (p + intVec k)) :
    ∑' x : L, ∫⁻ p in unitCube K, F x (-p) = ∑' x : coneSet L, ∫⁻ p, F x p := by
  classical
  have h1 : ∑' x : L, ∫⁻ p in unitCube K, F x (-p) =
      ∑' x : nzSet L, ∫⁻ p in unitCube K, F x (-p) := by
    rw [tsum_subtype L (fun x => ∫⁻ p in unitCube K, F x (-p)),
      tsum_subtype (nzSet L) (fun x => ∫⁻ p in unitCube K, F x (-p))]
    congr 1
    funext x
    by_cases hx0 : x = 0
    · subst hx0
      simp [hF0, Set.indicator]
    · by_cases hxL : x ∈ L
      · have : x ∈ nzSet L := ⟨hxL, hx0⟩
        rw [Set.indicator_of_mem hxL, Set.indicator_of_mem this]
      · have : x ∉ nzSet L := fun h => hxL h.1
        rw [Set.indicator_of_notMem hxL, Set.indicator_of_notMem this]
  rw [h1, ← (unfoldEquiv hL).tsum_eq, ENNReal.tsum_prod']
  apply tsum_congr
  intro x
  have hneg := lintegral_neg_eq_self (μ := (volume : Measure (Fin (rank K) → ℝ)))
    (fun p => F (x : K) p)
  rw [← hneg, lintegral_eq_tsum_unitCube K,
    ← (Equiv.neg (Fin (rank K) → ℤ)).tsum_eq
      (fun k => ∫⁻ p in unitCube K, F (x : K) (-(p + intVec k)))]
  apply tsum_congr
  intro k
  change ∫⁻ p in unitCube K, F (((unitPow k : (𝓞 K)ˣ) : K) * (x : K)) (-p) = _
  simp_rw [hFshift]
  congr 1
  funext p
  congr 1
  simp only [Equiv.neg_apply, intVec_neg]
  abel

omit [NumberField K] [DecidableEq ι] in
theorem latticePt_mem_latticeSet (b : ι → K) (m : ι → ℤ) : latticePt b m ∈ latticeSet b :=
  ⟨m, rfl⟩

theorem trace_mul_latticePt_traceDual (b : Module.Basis ι ℚ K) (m : ι → ℤ) (j : ι) :
    Algebra.trace ℚ K (latticePt (b.traceDual : ι → K) m * b j) = m j := by
  unfold latticePt
  rw [Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, map_zsmul, Module.Basis.trace_traceDual_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · simp

/-- Membership in the trace dual lattice. -/
theorem mem_latticeSet_traceDual_iff (b : Module.Basis ι ℚ K) (x : K) :
    x ∈ latticeSet (b.traceDual : ι → K) ↔ ∀ j, ∃ k : ℤ, Algebra.trace ℚ K (x * b j) = k := by
  constructor
  · rintro ⟨m, rfl⟩ j
    exact ⟨m j, trace_mul_latticePt_traceDual b m j⟩
  · intro h
    choose k hk using h
    refine ⟨k, ?_⟩
    have hx := (b.traceDual).sum_repr x
    unfold latticePt
    conv_rhs => rw [← hx]
    apply Finset.sum_congr rfl
    intro j _
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, hk j,
      Int.cast_smul_eq_zsmul]

/-- **The trace dual of a unit-stable lattice is unit-stable.** -/
theorem latticeSet_traceDual_unit_mul (b : Module.Basis ι ℚ K)
    (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ latticeSet (b : ι → K) → (u : K) * x ∈ latticeSet b)
    (u : (𝓞 K)ˣ) (x : K) (hx : x ∈ latticeSet (b.traceDual : ι → K)) :
    (u : K) * x ∈ latticeSet (b.traceDual : ι → K) := by
  rw [mem_latticeSet_traceDual_iff] at hx ⊢
  choose k hk using hx
  intro j
  obtain ⟨n, hn⟩ := hL u (b j) ⟨fun i => if i = j then 1 else 0, by
    unfold latticePt
    simp⟩
  have hub : (u : K) * b j = ∑ i, n i • b i := hn.symm
  refine ⟨∑ i, n i * k i, ?_⟩
  rw [mul_comm (u : K) x, mul_assoc, hub, Finset.mul_sum, map_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul_comm, map_zsmul, hk i, zsmul_eq_mul]

/-- The unfolded `ℝ≥0∞` identity on the dual side. -/
theorem lintegral_cube_tsum_eq_dual (b : Module.Basis ι ℚ K)
    (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ latticeSet (b.traceDual : ι → K) →
      (u : K) * x ∈ latticeSet (b.traceDual : ι → K))
    {s : ℝ} (hs : 0 < s) :
    ∫⁻ p in unitCube K, ∑' m : ι → ℤ,
        ENNReal.ofReal (normForm (latticePt (b.traceDual : ι → K) m) (-p) ^ (-s)) =
      ∑' x : coneSet (latticeSet (b.traceDual : ι → K)), ENNReal.ofReal
        (heckeConst K s * |(Algebra.norm ℚ (x : K) : ℝ)| ^ (-(2 * s / Module.finrank ℚ K))) := by
  set F : K → (Fin (rank K) → ℝ) → ℝ≥0∞ := fun x p => ENNReal.ofReal (normForm x p ^ (-s))
    with hF
  have hcontF : ∀ x : K, Continuous (fun p => normForm x p) := fun x => by
    unfold normForm unitWeight
    fun_prop
  have hmeas : ∀ x : K, Measurable (fun p => F x (-p)) := fun x => by
    have : Measurable fun p : Fin (rank K) → ℝ => normForm x (-p) ^ (-s) :=
      (((hcontF x).comp continuous_neg).measurable).pow_const _
    exact ENNReal.measurable_ofReal.comp this
  have hF0 : ∀ p, F 0 p = 0 := fun p => by
    have : normForm (0 : K) p = 0 := by simp [normForm]
    simp [hF, this, Real.zero_rpow (by linarith : -s ≠ 0)]
  have hFshift : ∀ k x p, F (((unitPow k : (𝓞 K)ˣ) : K) * x) p = F x (p + intVec k) :=
    fun k x p => by simp only [hF, normForm_unitPow_mul]
  rw [lintegral_tsum (fun m => (hmeas _).aemeasurable)]
  have heq := (Equiv.ofInjective _ (latticePt_injective b.traceDual)).tsum_eq
    (fun x : latticeSet (b.traceDual : ι → K) => ∫⁻ p in unitCube K, F x (-p))
  simp only [Equiv.ofInjective_apply] at heq
  change ∑' m, ∫⁻ p in unitCube K, F (latticePt (b.traceDual : ι → K) m) (-p) = _
  rw [show (∑' m, ∫⁻ p in unitCube K, F (latticePt (b.traceDual : ι → K) m) (-p)) =
    ∑' x : latticeSet (b.traceDual : ι → K), ∫⁻ p in unitCube K, F x (-p) from heq,
    tsum_lintegral_unfold_neg hL F hF0 hFshift]
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

/-- **The dual real identity.** -/
theorem heckeFEPair_symm_ofReal [Nonempty ι] (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ latticeSet (b : ι → K) → (u : K) * x ∈ latticeSet b)
    {s : ℝ} (hs : (Fintype.card ι : ℝ) / 2 < s) :
    (heckeFEPair b e).symm.Λ (s : ℂ) = ((π ^ (-s) * Real.Gamma s *
      ∑' x : coneSet (latticeSet (b.traceDual : ι → K)),
        heckeConst K s * |(Algebra.norm ℚ (x : K) : ℝ)| ^ (-(2 * s / Module.finrank ℚ K)) :
        ℝ) : ℂ) := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  rw [heckeFEPair, ThetaFamily.Λ_symm_eq_integral _ _ (by simpa using hs)]
  set G : (Fin (rank K) → ℝ) → ℝ := fun p =>
    ∑' m : ι → ℤ, sqNorm (dualEquiv ((heckeFamily b e).A p) (intVec m)) ^ (-s) with hG
  have hpt : ∀ p, (∑' m : ι → ℤ, (π : ℂ) ^ (-(s : ℂ)) * Complex.Gamma (s : ℂ) * 1 /
      ((sqNorm (dualEquiv ((heckeFamily b e).A p) (intVec m)) : ℝ) : ℂ) ^ (s : ℂ))
      = ((π ^ (-s) * Real.Gamma s * G p : ℝ) : ℂ) := by
    intro p
    rw [hG, ← tsum_mul_left, Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    have hq := sqNorm_nonneg (dualEquiv ((heckeFamily b e).A p) (intVec m))
    rw [Real.rpow_neg hq, ← Complex.ofReal_cpow hq, Complex.Gamma_ofReal,
      show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    ring
  simp_rw [hpt]
  rw [heckeMeasure, integral_complex_ofReal, integral_const_mul]
  congr 1
  congr 1
  have hGcont : Continuous G := (heckeFamily b e).dual.continuous_epstein hs
  have hGnn : ∀ p, 0 ≤ G p := fun p =>
    tsum_nonneg fun m => Real.rpow_nonneg (sqNorm_nonneg _) _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hGnn) hGcont.aestronglyMeasurable]
  have hsumG : ∀ p, Summable fun m : ι → ℤ =>
      sqNorm (dualEquiv ((heckeFamily b e).A p) (intVec m)) ^ (-s) := fun p => by
    have hσ := summable_epstein (dualEquiv ((heckeFamily b e).A p)) hs
    refine hσ.congr fun m => ?_
    rw [norm_one, one_div, Real.rpow_neg (sqNorm_nonneg _)]
  have hlin : ∫⁻ p in unitCube K, ENNReal.ofReal (G p) =
      ∫⁻ p in unitCube K, ∑' m : ι → ℤ,
        ENNReal.ofReal (normForm (latticePt (b.traceDual : ι → K) m) (-p) ^ (-s)) := by
    refine setLIntegral_congr_fun measurableSet_unitCube (fun p hp => ?_)
    rw [hG, ENNReal.ofReal_tsum_of_nonneg (fun m => Real.rpow_nonneg (sqNorm_nonneg _) _)
      (hsumG p)]
    apply tsum_congr
    intro m
    rw [sqNorm_heckeFamily_dual_of_mem_cube b e hp]
  rw [hlin, lintegral_cube_tsum_eq_dual b (latticeSet_traceDual_unit_mul b hL) hs0,
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro x
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (heckeConst_pos hs0).le (Real.rpow_nonneg (abs_nonneg _) _)

end SimultaneousPrimitiveRoots.Hecke

end
