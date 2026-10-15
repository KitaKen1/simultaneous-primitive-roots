module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Poisson summation on `ℤ^d`

For a continuous `f : ℝ^d → ℂ` whose integer translates are summable uniformly on compact sets,
and whose Fourier coefficients at integer frequencies are summable,

`∑_{m ∈ ℤ^d} f(m) = ∑_{n ∈ ℤ^d} ∫_{ℝ^d} e(-n·x) f(x) dx`.

This is the multi-dimensional analogue of Mathlib's `Real.tsum_eq_tsum_fourier`, proved by the
same route: periodize `f`, lift the periodization to the torus `(ℝ/ℤ)^d`, compute its Fourier
coefficients by unfolding over the fundamental domain `[0,1)^d`, and evaluate the Fourier series
at `0` with `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`.

It is the first step towards the theta-function proof of the analytic continuation of Dedekind
zeta functions (step B7 of the project roadmap).
-/

@[expose] public section
noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Complex Filter TopologicalSpace ContinuousMap UnitAddTorus
open scoped Real

variable {d : Type*} [Fintype d]

/-- An integer point of `ℤ^d` as a real vector. -/
def intVec (m : d → ℤ) : d → ℝ := fun i => (m i : ℝ)

omit [Fintype d] in
@[simp] theorem intVec_apply (m : d → ℤ) (i : d) : intVec m i = (m i : ℝ) := rfl

omit [Fintype d] in
theorem intVec_add (m n : d → ℤ) : intVec (m + n) = intVec m + intVec n := by
  ext i
  simp [intVec]

omit [Fintype d] in
theorem intVec_neg (m : d → ℤ) : intVec (-m) = -intVec m := by
  ext i
  simp [intVec]

/-- The quotient map `ℝ^d → (ℝ/ℤ)^d`. -/
def torusMk (x : d → ℝ) : UnitAddTorus d := fun i => ((x i : ℝ) : UnitAddCircle)

theorem isOpenQuotientMap_torusMk : IsOpenQuotientMap (torusMk (d := d)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem continuous_torusMk : Continuous (torusMk (d := d)) :=
  isOpenQuotientMap_torusMk.continuous

/-- The quotient map as a bundled continuous map. -/
def torusMkCM : C(d → ℝ, UnitAddTorus d) := ⟨torusMk, continuous_torusMk⟩

theorem isQuotientMap_torusMkCM : Topology.IsQuotientMap (torusMkCM (d := d)) :=
  isOpenQuotientMap_torusMk.isQuotientMap

theorem torusMk_add_intVec (x : d → ℝ) (m : d → ℤ) :
    torusMk (x + intVec m) = torusMk x := by
  funext i
  simp only [torusMk, Pi.add_apply, intVec_apply]
  rw [AddCircle.coe_add]
  have h : (((m i : ℤ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr ⟨m i, by simp⟩
  rw [h, add_zero]

theorem exists_intVec_of_torusMk_eq {x y : d → ℝ} (h : torusMk x = torusMk y) :
    ∃ m : d → ℤ, x = y + intVec m := by
  have hi : ∀ i, ∃ k : ℤ, x i = y i + k := by
    intro i
    have hxy := congrFun h i
    simp only [torusMk] at hxy
    have hmem := (QuotientAddGroup.eq_iff_sub_mem).mp hxy
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    refine ⟨k, ?_⟩
    have : (k : ℝ) = x i - y i := by simpa using hk
    linarith
  choose m hm using hi
  exact ⟨m, funext fun i => by simpa [intVec] using hm i⟩

/-- The torus character `x ↦ e(-n·x)` pulled back to `ℝ^d`. -/
def charPi (n : d → ℤ) (x : d → ℝ) : ℂ := mFourier (-n) (torusMk x)

theorem continuous_charPi (n : d → ℤ) : Continuous (charPi n) :=
  (mFourier (-n)).continuous.comp continuous_torusMk

theorem norm_charPi (n : d → ℤ) (x : d → ℝ) : ‖charPi n x‖ = 1 := by
  unfold charPi
  have h := (mFourier_norm (n := -n) : ‖(mFourier (-n) : C(UnitAddTorus d, ℂ))‖ = 1)
  simp only [mFourier, ContinuousMap.coe_mk]
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i _
  exact (AddCircle.toCircle _).norm_coe

theorem charPi_add_intVec (n : d → ℤ) (x : d → ℝ) (m : d → ℤ) :
    charPi n (x + intVec m) = charPi n x := by
  simp only [charPi, torusMk_add_intVec]

/-- The Fourier coefficient of `f : ℝ^d → ℂ` at an integer frequency. -/
def fourierInt (f : (d → ℝ) → ℂ) (n : d → ℤ) : ℂ := ∫ x, charPi n x * f x

/-- Integer translates of `f` are summable, uniformly on compact sets. -/
def TranslatesSummable (f : C(d → ℝ, ℂ)) : Prop :=
  ∀ K : Compacts (d → ℝ), Summable fun m : d → ℤ =>
    ‖(f.comp (ContinuousMap.addRight (intVec m))).restrict K‖

theorem summable_translates {f : C(d → ℝ, ℂ)} (hf : TranslatesSummable f) :
    Summable fun m : d → ℤ => f.comp (ContinuousMap.addRight (intVec m)) :=
  ContinuousMap.summable_of_locally_summable_norm hf

/-- The periodization `x ↦ ∑_m f(x + m)`. -/
def periodization (f : C(d → ℝ, ℂ)) : C(d → ℝ, ℂ) :=
  ∑' m : d → ℤ, f.comp (ContinuousMap.addRight (intVec m))

theorem periodization_apply {f : C(d → ℝ, ℂ)} (hf : TranslatesSummable f) (x : d → ℝ) :
    periodization f x = ∑' m : d → ℤ, f (x + intVec m) := by
  unfold periodization
  rw [← ContinuousMap.tsum_apply (summable_translates hf)]
  rfl

theorem periodization_add_intVec {f : C(d → ℝ, ℂ)} (hf : TranslatesSummable f)
    (x : d → ℝ) (k : d → ℤ) : periodization f (x + intVec k) = periodization f x := by
  rw [periodization_apply hf, periodization_apply hf]
  have h : ∀ m : d → ℤ, f (x + intVec k + intVec m) = f (x + intVec (k + m)) := by
    intro m
    rw [intVec_add, add_assoc]
  simp_rw [h]
  exact (Equiv.addLeft k).tsum_eq (fun m => f (x + intVec m))

theorem periodization_factorsThrough {f : C(d → ℝ, ℂ)} (hf : TranslatesSummable f) :
    Function.FactorsThrough (periodization f) (torusMkCM (d := d)) := by
  intro x y hxy
  obtain ⟨m, rfl⟩ := exists_intVec_of_torusMk_eq hxy
  exact periodization_add_intVec hf y m

/-- The periodization descends to a continuous function on the torus. -/
def torusLift (f : C(d → ℝ, ℂ)) (hf : TranslatesSummable f) : C(UnitAddTorus d, ℂ) :=
  isQuotientMap_torusMkCM.lift (periodization f) (periodization_factorsThrough hf)

theorem torusLift_torusMk {f : C(d → ℝ, ℂ)} (hf : TranslatesSummable f) (x : d → ℝ) :
    torusLift f hf (torusMk x) = periodization f x :=
  DFunLike.congr_fun
    (isQuotientMap_torusMkCM.lift_comp (periodization f) (periodization_factorsThrough hf)) x

/-- The unit box `(0,1]^d` used by `mFourierCoeff_eq_integral`. -/
def boxIoc : Set (d → ℝ) := {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

/-- The closed unit cube, as a compact set. -/
def cubeIcc : Compacts (d → ℝ) :=
  ⟨Set.pi univ fun _ => Icc (0 : ℝ) 1, isCompact_univ_pi fun _ => isCompact_Icc⟩

theorem boxIoc_subset_cube : boxIoc (d := d) ⊆ (cubeIcc (d := d) : Set (d → ℝ)) := by
  intro x hx
  simp only [cubeIcc, Compacts.coe_mk, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact Ioc_subset_Icc_self (hx i)

theorem measurableSet_boxIoc : MeasurableSet (boxIoc (d := d)) := by
  have : boxIoc (d := d) = Set.pi univ fun _ => Ioc (0 : ℝ) 1 := by
    ext x
    simp [boxIoc]
  rw [this]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem volume_boxIoc : volume (boxIoc (d := d)) = 1 := by
  have : boxIoc (d := d) = Set.pi univ fun _ => Ioc (0 : ℝ) 1 := by
    ext x
    simp [boxIoc]
  rw [this, Real.volume_pi_Ioc]
  simp

/-- Sup bound for a translate on the cube. -/
theorem norm_le_restrict_cube (g : C(d → ℝ, ℂ)) {x : d → ℝ} (hx : x ∈ boxIoc (d := d)) :
    ‖g x‖ ≤ ‖g.restrict (cubeIcc (d := d))‖ := by
  have hmem : x ∈ (cubeIcc (d := d) : Set (d → ℝ)) := boxIoc_subset_cube hx
  have := (g.restrict (cubeIcc (d := d))).norm_coe_le_norm ⟨x, hmem⟩
  rwa [ContinuousMap.restrict_apply] at this

theorem integrableOn_boxIoc (g : C(d → ℝ, ℂ)) : IntegrableOn g (boxIoc (d := d)) := by
  have hc : IntegrableOn g (cubeIcc (d := d) : Set (d → ℝ)) :=
    g.continuous.continuousOn.integrableOn_compact (cubeIcc (d := d)).isCompact
  exact hc.mono_set boxIoc_subset_cube

theorem integral_norm_boxIoc_le (g : C(d → ℝ, ℂ)) :
    ∫ x in boxIoc (d := d), ‖g x‖ ≤ ‖g.restrict (cubeIcc (d := d))‖ := by
  have hfin : volume (boxIoc (d := d)) < ⊤ := by rw [volume_boxIoc]; exact ENNReal.one_lt_top
  have h := setIntegral_mono_on (s := boxIoc (d := d)) (μ := volume)
    (f := fun x => ‖g x‖) (g := fun _ => ‖g.restrict (cubeIcc (d := d))‖)
    (integrableOn_boxIoc g).norm (integrableOn_const hfin.ne) measurableSet_boxIoc
    (fun x hx => norm_le_restrict_cube g hx)
  refine h.trans ?_
  rw [setIntegral_const, smul_eq_mul]
  rw [Measure.real, volume_boxIoc]
  simp

/-- The lattice `ℤ^d` inside `ℝ^d`, as the additive subgroup spanned by the standard basis. -/
abbrev intLattice (d : Type*) [Fintype d] : AddSubgroup (d → ℝ) :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))).toAddSubgroup

theorem intVec_mem_intLattice (m : d → ℤ) : intVec m ∈ intLattice d := by
  classical
  have h : intVec m = ∑ i, (m i) • (Pi.basisFun ℝ d i) := by
    ext j
    simp [intVec, Finset.sum_apply, Pi.single_apply]
  rw [h]
  exact (Submodule.mem_toAddSubgroup _).mpr (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem exists_intVec_of_mem (g : intLattice d) : ∃ m : d → ℤ, (g : d → ℝ) = intVec m := by
  have h := fun i => ((Pi.basisFun ℝ d).mem_span_iff_repr_mem ℤ (g : d → ℝ)).mp
    ((Submodule.mem_toAddSubgroup _).mp g.2) i
  choose m hm using h
  refine ⟨m, funext fun i => ?_⟩
  have := hm i
  simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this
  simp [intVec, this]

/-- The lattice `ℤ^d` is indexed by `d → ℤ`. -/
def intLatticeEquiv : (d → ℤ) ≃ intLattice d :=
  Equiv.ofBijective (fun m => ⟨intVec m, intVec_mem_intLattice m⟩) (by
    constructor
    · intro m n h
      have h' := congrArg (fun g : intLattice d => (g : d → ℝ)) h
      funext i
      have := congrFun h' i
      simpa [intVec] using this
    · intro g
      obtain ⟨m, hm⟩ := exists_intVec_of_mem g
      exact ⟨m, Subtype.ext hm.symm⟩)

theorem intLatticeEquiv_coe (m : d → ℤ) : ((intLatticeEquiv m : intLattice d) : d → ℝ) = intVec m :=
  rfl

instance countable_intLattice : Countable (intLattice d) :=
  Function.Injective.countable (intLatticeEquiv (d := d)).symm.injective

/-- `[0,1)^d` is a fundamental domain for `ℤ^d`, and agrees a.e. with `(0,1]^d`. -/
theorem isAddFundamentalDomain_cube :
    IsAddFundamentalDomain (intLattice d) (Set.pi univ fun _ : d => Ico (0 : ℝ) 1) volume := by
  rw [← ZSpan.fundamentalDomain_pi_basisFun]
  exact ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ d) volume

theorem pi_Ico_ae_eq_boxIoc :
    (Set.pi univ fun _ : d => Ico (0 : ℝ) 1) =ᵐ[volume] (boxIoc (d := d)) := by
  have h1 := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : d => (volume : Measure ℝ))
    (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
  have h2 := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : d => (volume : Measure ℝ))
    (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
  have hbox : boxIoc (d := d) = Set.pi univ fun _ => Ioc (0 : ℝ) 1 := by
    ext x
    simp [boxIoc]
  rw [hbox, MeasureTheory.volume_pi]
  exact h1.trans h2.symm

/-- Unfolding an integral over `ℝ^d` along `ℤ^d`. -/
theorem integral_eq_tsum_boxIoc {F : (d → ℝ) → ℂ} (hF : Integrable F) :
    ∫ x, F x = ∑' m : d → ℤ, ∫ x in boxIoc (d := d), F (x + intVec m) := by
  rw [isAddFundamentalDomain_cube.integral_eq_tsum' F hF]
  rw [← (intLatticeEquiv (d := d)).tsum_eq]
  rw [← (Equiv.neg (d → ℤ)).tsum_eq]
  apply tsum_congr
  intro m
  rw [setIntegral_congr_set pi_Ico_ae_eq_boxIoc]
  apply setIntegral_congr_fun measurableSet_boxIoc
  intro x _
  simp only [Equiv.neg_apply, AddSubgroup.vadd_def, vadd_eq_add]
  congr 1
  rw [AddSubgroup.coe_neg, intLatticeEquiv_coe, intVec_neg, neg_neg]
  exact add_comm _ _

/-- Integrability from summable translates. -/
theorem integrable_of_translatesSummable {g : C(d → ℝ, ℂ)} (hg : TranslatesSummable g) :
    Integrable g := by
  refine ⟨g.continuous.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, isAddFundamentalDomain_cube.lintegral_eq_tsum']
  rw [← (intLatticeEquiv (d := d)).tsum_eq]
  rw [← (Equiv.neg (d → ℤ)).tsum_eq]
  have hbound : ∀ m : d → ℤ,
      ∫⁻ x in Set.pi univ (fun _ : d => Ico (0 : ℝ) 1),
        ‖g (-(intLatticeEquiv (Equiv.neg (d → ℤ) m) : intLattice d) +ᵥ x)‖ₑ ≤
      ENNReal.ofReal ‖(g.comp (ContinuousMap.addRight (intVec m))).restrict (cubeIcc (d := d))‖ := by
    intro m
    rw [setLIntegral_congr pi_Ico_ae_eq_boxIoc]
    have hvol : volume (boxIoc (d := d)) = 1 := volume_boxIoc
    calc ∫⁻ x in boxIoc (d := d),
          ‖g (-(intLatticeEquiv (Equiv.neg (d → ℤ) m) : intLattice d) +ᵥ x)‖ₑ
        ≤ ∫⁻ _x in boxIoc (d := d),
            ENNReal.ofReal ‖(g.comp (ContinuousMap.addRight (intVec m))).restrict
              (cubeIcc (d := d))‖ := by
          apply setLIntegral_mono measurable_const
          intro x hx
          have hpt : g (-(intLatticeEquiv (Equiv.neg (d → ℤ) m) : intLattice d) +ᵥ x) =
              (g.comp (ContinuousMap.addRight (intVec m))) x := by
            simp only [Equiv.neg_apply, AddSubgroup.vadd_def, vadd_eq_add,
              ContinuousMap.comp_apply, ContinuousMap.coe_addRight]
            congr 1
            rw [AddSubgroup.coe_neg, intLatticeEquiv_coe, intVec_neg, neg_neg]
            exact add_comm _ _
          rw [hpt, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_le_restrict_cube _ hx)
      _ = ENNReal.ofReal ‖(g.comp (ContinuousMap.addRight (intVec m))).restrict
            (cubeIcc (d := d))‖ := by
          rw [setLIntegral_const, hvol, mul_one]
  calc ∑' m : d → ℤ, ∫⁻ x in Set.pi univ (fun _ : d => Ico (0 : ℝ) 1),
        ‖g (-(intLatticeEquiv (Equiv.neg (d → ℤ) m) : intLattice d) +ᵥ x)‖ₑ
      ≤ ∑' m : d → ℤ, ENNReal.ofReal
          ‖(g.comp (ContinuousMap.addRight (intVec m))).restrict (cubeIcc (d := d))‖ :=
        ENNReal.tsum_le_tsum hbound
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hg cubeIcc)]
        exact ENNReal.ofReal_lt_top

/-- **Fourier coefficients of the periodization.** -/
theorem mFourierCoeff_torusLift {f : C(d → ℝ, ℂ)} (hf : TranslatesSummable f) (n : d → ℤ) :
    mFourierCoeff (torusLift f hf) n = fourierInt f n := by
  set e : C(d → ℝ, ℂ) := ⟨charPi n, continuous_charPi n⟩ with he
  have hint := integrable_of_translatesSummable (g := e * f) (by
    intro K
    have heq : ∀ m : d → ℤ, ‖((e * f).comp (ContinuousMap.addRight (intVec m))).restrict K‖ =
        ‖(f.comp (ContinuousMap.addRight (intVec m))).restrict K‖ := by
      intro m
      simp_rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.restrict_apply,
        ContinuousMap.comp_apply, ContinuousMap.mul_apply, norm_mul, he, ContinuousMap.coe_mk,
        norm_charPi, one_mul]
    simp_rw [heq]
    exact hf K)
  rw [mFourierCoeff_eq_integral _ n 0]
  have hS : {x : d → ℝ | ∀ i, x i ∈ Ioc ((0 : d → ℝ) i) ((0 : d → ℝ) i + 1)} = boxIoc := by
    ext x
    simp [boxIoc]
  rw [hS]
  have hfun : ∀ x : d → ℝ,
      mFourier (-n) (fun i => (x i : UnitAddCircle)) • torusLift f hf (fun i => (x i : UnitAddCircle)) =
        ∑' m : d → ℤ, charPi n (x + intVec m) * f (x + intVec m) := by
    intro x
    have h1 : torusLift f hf (fun i => (x i : UnitAddCircle)) = periodization f x :=
      torusLift_torusMk hf x
    rw [h1, periodization_apply hf, smul_eq_mul, ← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [charPi_add_intVec]
    rfl
  simp_rw [hfun]
  have hFm : ∀ m : d → ℤ, Integrable (fun x => charPi n (x + intVec m) * f (x + intVec m))
      (volume.restrict boxIoc) := by
    intro m
    exact integrableOn_boxIoc ((e * f).comp (ContinuousMap.addRight (intVec m)))
  have hsum : Summable fun m : d → ℤ =>
      ∫ x in boxIoc (d := d), ‖charPi n (x + intVec m) * f (x + intVec m)‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun x => norm_nonneg _)
      (fun m => ?_) (hf cubeIcc)
    have h := integral_norm_boxIoc_le ((e * f).comp (ContinuousMap.addRight (intVec m)))
    have heq : ‖((e * f).comp (ContinuousMap.addRight (intVec m))).restrict (cubeIcc (d := d))‖ =
        ‖(f.comp (ContinuousMap.addRight (intVec m))).restrict (cubeIcc (d := d))‖ := by
      simp_rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.restrict_apply,
        ContinuousMap.comp_apply, ContinuousMap.mul_apply, norm_mul, he, ContinuousMap.coe_mk,
        norm_charPi, one_mul]
    rw [heq] at h
    exact h
  rw [← integral_tsum_of_summable_integral_norm hFm hsum]
  have hint' : Integrable (fun x => charPi n x * f x) := hint
  unfold fourierInt
  rw [integral_eq_tsum_boxIoc hint']

/-- **Poisson summation on `ℤ^d`.** -/
theorem tsum_eq_tsum_fourierInt {f : C(d → ℝ, ℂ)} (hf : TranslatesSummable f)
    (hF : Summable fun n : d → ℤ => fourierInt f n) :
    ∑' m : d → ℤ, f (intVec m) = ∑' n : d → ℤ, fourierInt f n := by
  have hcoeff : Summable (mFourierCoeff (torusLift f hf)) := by
    have : mFourierCoeff (torusLift f hf) = fun n => fourierInt f n :=
      funext (mFourierCoeff_torusLift hf)
    rw [this]
    exact hF
  have h := (hasSum_mFourier_series_apply_of_summable hcoeff (torusMk 0)).tsum_eq
  have hone : ∀ n : d → ℤ, mFourier n (torusMk (0 : d → ℝ)) = 1 := by
    intro n
    simp only [mFourier, ContinuousMap.coe_mk, torusMk, Pi.zero_apply]
    apply Finset.prod_eq_one
    intro i _
    rw [show ((0 : ℝ) : UnitAddCircle) = 0 by rfl, fourier_eval_zero]
  simp_rw [hone, smul_eq_mul, mul_one, mFourierCoeff_torusLift hf] at h
  rw [h, torusLift_torusMk hf, periodization_apply hf]
  simp

end SimultaneousPrimitiveRoots.Hecke
