module

public import SimultaneousPrimitiveRoots.LogNormSheetDisintegration
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Set Complex
open scoped Topology
noncomputable section

/-- Translate the distinguished log coordinate by the sum of all free coordinates. -/
def artinFiniteLogShearEquiv (n : ℕ) :
    (ℝ × (Fin n → ℝ)) ≃ᵐ (ℝ × (Fin n → ℝ)) where
  toFun p := (p.1 - ∑ i, p.2 i, p.2)
  invFun p := (p.1 + ∑ i, p.2 i, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := by
    change Measurable (fun p : ℝ × (Fin n → ℝ) => (p.1 - ∑ i, p.2 i, p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × (Fin n → ℝ) => (p.1 + ∑ i, p.2 i, p.2))
    fun_prop

theorem artinFiniteLogShear_measurePreserving (n : ℕ) :
    MeasurePreserving (artinFiniteLogShearEquiv n) (volume.prod volume)
      (volume.prod volume) := by
  have h : MeasurePreserving
      (fun p : (Fin n → ℝ) × ℝ => (p.1, p.2 - ∑ i, p.1 i))
      (volume.prod volume) (volume.prod volume) := by
    exact (MeasurePreserving.id (volume : Measure (Fin n → ℝ))).skew_product
      (g := fun x w => w - ∑ i, x i) (by fun_prop)
      (Filter.Eventually.of_forall fun x => by
        simpa only [sub_eq_add_neg] using
          (measurePreserving_add_right volume (-(∑ i, x i))).map_eq)
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

/-- A global coordinate system for every nonempty finite log-norm sheet.
The free coordinates carry actual product Lebesgue measure. -/
def artinFiniteLogNormSheetEquiv (n : ℕ) :
    (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
  (artinFiniteLogShearEquiv n).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm

theorem artinFiniteLogNormSheet_coordinates (n : ℕ) (w : ℝ) (x : Fin n → ℝ) :
    artinFiniteLogNormSheetEquiv n (w, x) = Fin.cons (w - ∑ i, x i) x := by
  simp [artinFiniteLogNormSheetEquiv, artinFiniteLogShearEquiv,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem artinFiniteLogNormSheet_total (n : ℕ) (w : ℝ) (x : Fin n → ℝ) :
    (∑ i, artinFiniteLogNormSheetEquiv n (w, x) i) = w := by
  rw [artinFiniteLogNormSheet_coordinates, Fin.sum_univ_succ]
  simp

theorem artinFiniteLogNormSheet_measurePreserving (n : ℕ) :
    MeasurePreserving (artinFiniteLogNormSheetEquiv n) (volume.prod volume) volume :=
  ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)).comp
      (artinFiniteLogShear_measurePreserving n)

/-- Positive radial coordinates on the actual product-norm sheet. -/
def artinFinitePositiveNormSheetCoordinates (n : ℕ) (u : ℝ) (x : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => Real.exp (artinFiniteLogNormSheetEquiv n (Real.log u, x) i)

theorem artinFinitePositiveNormSheetCoordinates_pos (n : ℕ) (u : ℝ)
    (x : Fin n → ℝ) (i : Fin (n + 1)) :
    0 < artinFinitePositiveNormSheetCoordinates n u x i := Real.exp_pos _

theorem artinFinitePositiveNormSheetCoordinates_product (n : ℕ) {u : ℝ}
    (hu : 0 < u) (x : Fin n → ℝ) :
    (∏ i, artinFinitePositiveNormSheetCoordinates n u x i) = u := by
  unfold artinFinitePositiveNormSheetCoordinates
  rw [← Real.exp_sum, artinFiniteLogNormSheet_total, Real.exp_log hu]

theorem artinFinitePositiveNormSheetCoordinates_explicit (n : ℕ) {u : ℝ}
    (hu : 0 < u) (x : Fin n → ℝ) :
    artinFinitePositiveNormSheetCoordinates n u x =
      Fin.cons (u / Real.exp (∑ i, x i)) (fun i => Real.exp (x i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [artinFinitePositiveNormSheetCoordinates, artinFiniteLogNormSheet_coordinates,
      Real.exp_sub, Real.exp_log hu]
  · simp [artinFinitePositiveNormSheetCoordinates, artinFiniteLogNormSheet_coordinates]

/-- The product-norm section supported on the distinguished coordinate. -/
def artinFinitePositiveNormSection (n : ℕ) (u : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons u (fun _ => 1)

theorem artinFinitePositiveNormSection_mul (n : ℕ) (u v : ℝ) :
    artinFinitePositiveNormSection n (u * v) =
      artinFinitePositiveNormSection n u * artinFinitePositiveNormSection n v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [artinFinitePositiveNormSection]

theorem artinFinitePositiveNormSheetCoordinates_transport (n : ℕ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (x : Fin n → ℝ) :
    artinFinitePositiveNormSheetCoordinates n (u * v) x =
      artinFinitePositiveNormSection n v * artinFinitePositiveNormSheetCoordinates n u x := by
  rw [artinFinitePositiveNormSheetCoordinates_explicit n (mul_pos hu hv),
    artinFinitePositiveNormSheetCoordinates_explicit n hu]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [artinFinitePositiveNormSection, Pi.mul_apply, Fin.cons_zero]
    ring
  · simp [artinFinitePositiveNormSection]

/-- The actual integral of f over the affine sheet whose total log norm is w. -/
def artinFiniteLogNormSheetProfile (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ)
    (w : ℝ) : ℂ :=
  ∫ x : Fin n → ℝ, f (artinFiniteLogNormSheetEquiv n (w, x))

theorem artinFiniteLogNormSheet_joint_integrable {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℂ} (hf : Integrable f) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => f (artinFiniteLogNormSheetEquiv n p))
      (volume.prod volume) :=
  (artinFiniteLogNormSheet_measurePreserving n).integrable_comp_of_integrable hf

theorem artinFiniteLogNormSheetProfile_integrable {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℂ} (hf : Integrable f) :
    Integrable (artinFiniteLogNormSheetProfile n f) :=
  (artinFiniteLogNormSheet_joint_integrable hf).integral_prod_left

theorem artinFiniteLogNormSheet_disintegration {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℂ} (hf : Integrable f) :
    (∫ w, artinFiniteLogNormSheetProfile n f w) = ∫ p, f p := by
  unfold artinFiniteLogNormSheetProfile
  rw [← integral_prod _ (artinFiniteLogNormSheet_joint_integrable hf)]
  exact (artinFiniteLogNormSheet_measurePreserving n).integral_comp' f

theorem artinFiniteLogNormSheet_weighted_profile (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℂ) (s : ℂ) (w : ℝ) :
    artinFiniteLogNormSheetProfile n
      (fun p => Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) * f p) w =
      Complex.exp (s * w) * artinFiniteLogNormSheetProfile n f w := by
  simp only [artinFiniteLogNormSheetProfile, artinFiniteLogNormSheet_total,
    ← integral_const_mul]

theorem artinFiniteLogNormSheet_weighted_integrable {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) * f p)) :
    Integrable (fun w : ℝ => Complex.exp (s * w) * artinFiniteLogNormSheetProfile n f w) := by
  have he := funext (artinFiniteLogNormSheet_weighted_profile n f s)
  rw [← he]
  exact artinFiniteLogNormSheetProfile_integrable hf

theorem artinFiniteLogNormSheet_weighted_disintegration {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) * f p)) :
    (∫ w : ℝ, Complex.exp (s * w) * artinFiniteLogNormSheetProfile n f w) =
      ∫ p, Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) * f p := by
  have he := funext (artinFiniteLogNormSheet_weighted_profile n f s)
  rw [← he]
  exact artinFiniteLogNormSheet_disintegration hf

def artinFinitePositiveNormSheetProfile (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℂ) (u : ℝ) : ℂ :=
  artinFiniteLogNormSheetProfile n f (Real.log u)

theorem artinFinitePositiveNormSheetProfile_mellin_convergent {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) * f p)) :
    MellinConvergent (artinFinitePositiveNormSheetProfile n f) s := by
  rw [artinMellin_convergent_iff_multiplicative,
    artinPositiveMultiplicative_integrable_exp_iff]
  simpa only [artinFinitePositiveNormSheetProfile, Real.log_exp,
    artinMellin_positive_exp_power] using artinFiniteLogNormSheet_weighted_integrable hf

theorem artinFinitePositiveNormSheetProfile_mellin {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) * f p)) :
    mellin (artinFinitePositiveNormSheetProfile n f) s =
      ∫ p, Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) * f p := by
  rw [artinMellin_eq_multiplicative, artinPositiveMultiplicative_integral_exp]
  simp only [artinFinitePositiveNormSheetProfile, Real.log_exp,
    artinMellin_positive_exp_power]
  exact artinFiniteLogNormSheet_weighted_disintegration hf

/-- Answer-first factorization of the global Mellin weight, before applying Fubini. -/
theorem artinFiniteRadialProduct_weighted {n : ℕ}
    (f : Fin (n + 1) → ℝ → ℂ) (s : ℂ) (p : Fin (n + 1) → ℝ) :
    Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) * (∏ i, f i (Real.exp (p i))) =
      ∏ i, Complex.exp (s * p i) * f i (Real.exp (p i)) := by
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  simp [Finset.mul_sum]

theorem artinFiniteRadialProduct_weighted_integrable {n : ℕ}
    {f : Fin (n + 1) → ℝ → ℂ} {s : ℂ} (hf : ∀ i, MellinConvergent (f i) s) :
    Integrable (fun p : Fin (n + 1) → ℝ =>
      Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) * ∏ i, f i (Real.exp (p i))) := by
  have hi : ∀ i, Integrable (fun v : ℝ => Complex.exp (s * v) * f i (Real.exp v)) := by
    intro i
    have h := (artinPositiveMultiplicative_integrable_exp_iff _).mp
      ((artinMellin_convergent_iff_multiplicative (f i) s).mp (hf i))
    simpa only [artinMellin_positive_exp_power] using h
  have he := funext (artinFiniteRadialProduct_weighted f s)
  rw [he]
  exact Integrable.fintype_prod hi

theorem artinFiniteRadialProduct_mellin_convergent {n : ℕ}
    {f : Fin (n + 1) → ℝ → ℂ} {s : ℂ} (hf : ∀ i, MellinConvergent (f i) s) :
    MellinConvergent (artinFinitePositiveNormSheetProfile n
      (fun p => ∏ i, f i (Real.exp (p i)))) s :=
  artinFinitePositiveNormSheetProfile_mellin_convergent
    (artinFiniteRadialProduct_weighted_integrable hf)

/-- Direct finite-dimensional Fubini computes the actual sheet Mellin transform.
No pointwise identification with a recursively defined convolution is required. -/
theorem artinFiniteRadialProduct_mellin {n : ℕ}
    {f : Fin (n + 1) → ℝ → ℂ} {s : ℂ} (hf : ∀ i, MellinConvergent (f i) s) :
    mellin (artinFinitePositiveNormSheetProfile n
      (fun p => ∏ i, f i (Real.exp (p i)))) s = ∏ i, mellin (f i) s := by
  rw [artinFinitePositiveNormSheetProfile_mellin
    (artinFiniteRadialProduct_weighted_integrable hf)]
  simp_rw [artinFiniteRadialProduct_weighted]
  rw [integral_fintype_prod_volume_eq_prod
    (fun i (v : ℝ) => Complex.exp (s * v) * f i (Real.exp v))]
  apply Finset.prod_congr rfl
  intro i _
  rw [artinMellin_eq_multiplicative, artinPositiveMultiplicative_integral_exp]
  simp only [artinMellin_positive_exp_power]

end
end SimultaneousPrimitiveRoots
