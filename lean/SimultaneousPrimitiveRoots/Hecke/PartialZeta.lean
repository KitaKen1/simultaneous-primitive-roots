module

public import SimultaneousPrimitiveRoots.Hecke.Unfolding

/-!
# Hecke's `Λ` of a unit-stable lattice is a partial Dedekind zeta function

Let `b` be a `ℚ`-basis of `K` whose `ℤ`-span `L` is stable under multiplication by units (a
fractional ideal). For real `s > n/2`,

`(heckeFEPair b e).Λ s = π^{-s} Γ(s) ∑_{x ∈ L ∩ cone} heckeConst K s · |N x|^{-2s/n}`.

Together with the meromorphic continuation and the functional equation of `heckeFEPair` this is
Hecke's continuation of the partial zeta function `∑_{x ∈ L ∩ cone} |N x|^{-t}`, `t = 2s/n`.
The chain of identities: the averaged Epstein series (`heckeFEPair_eq_integral`), the unit weights
on the cube (`unitWeights_y_of_mem_cube`), unfolding the units (`tsum_lintegral_unfold`), and
Hecke's integral (`integral_normForm_rpow`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units MeasureTheory Set
open scoped ENNReal Real

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The lattice point `∑_j m_j b_j`. -/
def latticePt (b : ι → K) (m : ι → ℤ) : K := ∑ j, m j • b j

omit [DecidableEq ι] in
theorem latticePt_injective (b : Module.Basis ι ℚ K) :
    Function.Injective (latticePt (b : ι → K)) := by
  intro m m' h
  have h2 : ∑ j, ((m j - m' j : ℤ) : ℚ) • b j = 0 := by
    simp only [Int.cast_smul_eq_zsmul, sub_smul, Finset.sum_sub_distrib]
    unfold latticePt at h
    rw [h, sub_self]
  have hc := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h2
  funext j
  exact sub_eq_zero.mp (Int.cast_eq_zero.mp (hc j))

/-- The lattice `ℤ b ⊂ K`. -/
def latticeSet (b : ι → K) : Set K := Set.range (latticePt b)

omit [DecidableEq ι] in
theorem summable_intVec_rpow {σ : ℝ} (hσ : (Fintype.card ι : ℝ) / 2 < σ) (c : ℝ) :
    Summable fun m : ι → ℤ => c * ‖intVec m‖ ^ (-(2 * σ)) := by
  have hr : -(2 * σ) < -(Module.finrank ℤ (intSpan ι) : ℝ) := by
    rw [finrank_intSpan]
    linarith
  have hL := ZLattice.summable_norm_rpow (intSpan ι) (-(2 * σ)) hr
  exact ((intSpanEquiv (d := ι)).summable_iff.mpr hL).mul_left c

/-- The real Epstein series of a family is continuous in the parameter. -/
theorem ThetaFamily.continuous_epstein {P : Type*} [TopologicalSpace P] (F : ThetaFamily ι P)
    {σ : ℝ} (hσ : (Fintype.card ι : ℝ) / 2 < σ) :
    Continuous fun p => ∑' m : ι → ℤ, sqNorm (F.A p (intVec m)) ^ (-σ) := by
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  have hκ := F.κ_pos
  refine continuous_tsum (u := fun m : ι → ℤ => F.κ ^ (-σ) * ‖intVec m‖ ^ (-(2 * σ)))
    (fun m => ?_) (summable_intVec_rpow hσ _) (fun m p => ?_)
  · by_cases hm : m = 0
    · subst hm
      have : ∀ p, sqNorm (F.A p (intVec (0 : ι → ℤ))) ^ (-σ) = 0 := fun p => by
        rw [sqNorm_intVec_zero, Real.zero_rpow (by linarith)]
      simp_rw [this]
      exact continuous_const
    · have hs : Continuous (sqNorm (d := ι)) := by
        unfold sqNorm
        fun_prop
      have hpos : ∀ p, sqNorm (F.A p (intVec m)) ≠ 0 := fun p => by
        have h1 := one_le_norm_intVec hm
        have h2 := F.lower p (intVec m)
        have : 0 < F.κ * ‖intVec m‖ ^ 2 := by positivity
        linarith
      exact (hs.comp (F.continuous_A (intVec m))).rpow_const fun p => Or.inl (hpos p)
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sqNorm_nonneg _) _)]
    by_cases hm : m = 0
    · subst hm
      rw [sqNorm_intVec_zero, Real.zero_rpow (by linarith)]
      exact mul_nonneg (Real.rpow_nonneg hκ.le _) (Real.rpow_nonneg (norm_nonneg _) _)
    · have h1 := one_le_norm_intVec hm
      have hn0 : 0 < ‖intVec m‖ := by linarith
      have hlow := F.lower p (intVec m)
      have hpos : 0 < F.κ * ‖intVec m‖ ^ 2 := by positivity
      calc sqNorm (F.A p (intVec m)) ^ (-σ) ≤ (F.κ * ‖intVec m‖ ^ 2) ^ (-σ) :=
            Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
        _ = F.κ ^ (-σ) * ‖intVec m‖ ^ (-(2 * σ)) := by
            rw [Real.mul_rpow hκ.le (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul hn0.le]
            congr 2
            push_cast
            ring

theorem mem_unitCube_iff {p : Fin (rank K) → ℝ} :
    p ∈ unitCube K ↔ ∀ i, p i ∈ Ico (0 : ℝ) 1 := by
  simp [unitCube]

theorem measurableSet_unitCube : MeasurableSet (unitCube K) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem unitWeights_y_of_mem_cube {p : Fin (rank K) → ℝ} (hp : p ∈ unitCube K)
    (σ : K →+* ℂ) : (unitWeights K).y p σ = unitWeight p σ := by
  have hp' := mem_unitCube_iff.mp hp
  simp only [unitWeights, unitExponent, unitWeight]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [clamp01_of_mem (Ico_subset_Icc_self (hp' i))]

theorem sqNorm_heckeFamily (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    (p : Fin (rank K) → ℝ) (m : ι → ℤ) :
    sqNorm ((heckeFamily b e).A p (intVec m)) =
      ∑ σ, (unitWeights K).y p σ * Complex.normSq (σ (latticePt (b : ι → K) m)) := by
  rw [heckeFamily, WeightFamily.sqNorm_thetaFamily, WeightFamily.weightedNormSq_w]
  rfl

theorem sqNorm_heckeFamily_of_mem_cube (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {p : Fin (rank K) → ℝ} (hp : p ∈ unitCube K) (m : ι → ℤ) :
    sqNorm ((heckeFamily b e).A p (intVec m)) = normForm (latticePt (b : ι → K) m) p := by
  rw [sqNorm_heckeFamily]
  unfold normForm
  apply Finset.sum_congr rfl
  intro σ _
  rw [unitWeights_y_of_mem_cube hp]

theorem heckeConst_pos {s : ℝ} (hs : 0 < s) : 0 < heckeConst K s := by
  unfold heckeConst
  have hdet := det_heckeLin_ne_zero (K := K)
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  refine div_pos (mul_pos (inv_pos.mpr (abs_pos.mpr hdet)) (Finset.prod_pos fun o _ => ?_))
    (Real.Gamma_pos_of_pos hs)
  have hm := placeMult_pos (K := K) o
  exact mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.rpow_pos_of_pos hm _)

omit [DecidableEq ι] in
/-- The unfolded `ℝ≥0∞` identity. -/
theorem lintegral_cube_tsum_eq (b : Module.Basis ι ℚ K)
    (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ latticeSet (b : ι → K) → (u : K) * x ∈ latticeSet b)
    {s : ℝ} (hs : 0 < s) :
    ∫⁻ p in unitCube K, ∑' m : ι → ℤ,
        ENNReal.ofReal (normForm (latticePt (b : ι → K) m) p ^ (-s)) =
      ∑' x : coneSet (latticeSet (b : ι → K)), ENNReal.ofReal
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
  rw [lintegral_tsum (fun m => (hmeas _).aemeasurable)]
  have heq := (Equiv.ofInjective _ (latticePt_injective b)).tsum_eq
    (fun x : latticeSet (b : ι → K) => ∫⁻ p in unitCube K, F x p)
  simp only [Equiv.ofInjective_apply] at heq
  change ∑' m, ∫⁻ p in unitCube K, F (latticePt (b : ι → K) m) p = _
  rw [show (∑' m, ∫⁻ p in unitCube K, F (latticePt (b : ι → K) m) p) =
    ∑' x : latticeSet (b : ι → K), ∫⁻ p in unitCube K, F x p from heq,
    tsum_lintegral_unfold hL F hF0 hFshift]
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

/-- **The real identity**: Hecke's `Λ` at real `s > n/2` is the partial zeta function of the cone. -/
theorem heckeFEPair_ofReal [Nonempty ι] (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ latticeSet (b : ι → K) → (u : K) * x ∈ latticeSet b)
    {s : ℝ} (hs : (Fintype.card ι : ℝ) / 2 < s) :
    (heckeFEPair b e).Λ (s : ℂ) = ((π ^ (-s) * Real.Gamma s *
      ∑' x : coneSet (latticeSet (b : ι → K)),
        heckeConst K s * |(Algebra.norm ℚ (x : K) : ℝ)| ^ (-(2 * s / Module.finrank ℚ K)) :
        ℝ) : ℂ) := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  rw [heckeFEPair_eq_integral b e (by simpa using hs)]
  set G : (Fin (rank K) → ℝ) → ℝ := fun p =>
    ∑' m : ι → ℤ, sqNorm ((heckeFamily b e).A p (intVec m)) ^ (-s) with hG
  -- the complex integrand is real
  have hpt : ∀ p, (∑' m : ι → ℤ, (π : ℂ) ^ (-(s : ℂ)) * Complex.Gamma (s : ℂ) * 1 /
      ((∑ σ, (unitWeights K).y p σ * Complex.normSq (σ (∑ j, m j • b j)) : ℝ) : ℂ) ^ (s : ℂ))
      = ((π ^ (-s) * Real.Gamma s * G p : ℝ) : ℂ) := by
    intro p
    rw [hG, ← tsum_mul_left, Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    have hq : 0 ≤ ∑ σ, (unitWeights K).y p σ * Complex.normSq (σ (∑ j, m j • b j)) :=
      Finset.sum_nonneg fun σ _ =>
        mul_nonneg ((unitWeights K).y_pos p σ).le (Complex.normSq_nonneg _)
    have hsq := sqNorm_heckeFamily b e p m
    unfold latticePt at hsq
    rw [hsq, Real.rpow_neg hq, ← Complex.ofReal_cpow hq, Complex.Gamma_ofReal,
      show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_complex_ofReal, integral_const_mul]
  congr 1
  congr 1
  -- the real integral over the cube
  have hGcont : Continuous G := (heckeFamily b e).continuous_epstein hs
  have hGnn : ∀ p, 0 ≤ G p := fun p =>
    tsum_nonneg fun m => Real.rpow_nonneg (sqNorm_nonneg _) _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hGnn) hGcont.aestronglyMeasurable]
  have hsumG : ∀ p, Summable fun m : ι → ℤ => sqNorm ((heckeFamily b e).A p (intVec m)) ^ (-s) :=
    fun p => by
      have hσ := summable_epstein ((heckeFamily b e).A p) hs
      refine hσ.congr fun m => ?_
      rw [norm_one, one_div, Real.rpow_neg (sqNorm_nonneg _)]
  have hlin : ∫⁻ p in unitCube K, ENNReal.ofReal (G p) =
      ∫⁻ p in unitCube K, ∑' m : ι → ℤ,
        ENNReal.ofReal (normForm (latticePt (b : ι → K) m) p ^ (-s)) := by
    refine setLIntegral_congr_fun measurableSet_unitCube (fun p hp => ?_)
    rw [hG, ENNReal.ofReal_tsum_of_nonneg (fun m => Real.rpow_nonneg (sqNorm_nonneg _) _)
      (hsumG p)]
    apply tsum_congr
    intro m
    rw [sqNorm_heckeFamily_of_mem_cube b e hp]
  rw [hlin, lintegral_cube_tsum_eq b hL hs0, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro x
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (heckeConst_pos hs0).le (Real.rpow_nonneg (abs_nonneg _) _)

end SimultaneousPrimitiveRoots.Hecke

end
