module

public import Compat4331.CircleMeasure
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

/-- Angular coordinate of an actual nonzero complex number; no choice of argument. -/
def artinComplexUnitAngle (z : ℂˣ) : Circle :=
  ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self]
    exact norm_ne_zero_iff.mpr z.ne_zero)⟩

/-- x is the logarithm of the normalized complex absolute value |z|². -/
def artinComplexPolarUnit (p : Multiplicative ℝ × Circle) : ℂˣ :=
  Units.mk0 ((Real.exp (Multiplicative.toAdd p.1 / 2) : ℂ) * (p.2 : ℂ))
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) p.2.coe_ne_zero)

theorem artinComplexPolarUnit_val (p : Multiplicative ℝ × Circle) :
    (artinComplexPolarUnit p : ℂ) =
      (Real.exp (Multiplicative.toAdd p.1 / 2) : ℂ) * (p.2 : ℂ) := rfl

theorem artinComplexPolarUnit_norm (p : Multiplicative ℝ × Circle) :
    ‖(artinComplexPolarUnit p : ℂ)‖ = Real.exp (Multiplicative.toAdd p.1 / 2) := by
  rw [artinComplexPolarUnit_val, norm_mul, Circle.norm_coe, mul_one]
  exact Complex.norm_of_nonneg (Real.exp_pos _).le

theorem artinComplexPolarUnit_norm_sq (p : Multiplicative ℝ × Circle) :
    ‖(artinComplexPolarUnit p : ℂ)‖ ^ 2 = Real.exp (Multiplicative.toAdd p.1) := by
  rw [artinComplexPolarUnit_norm, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem artinComplexPolarUnit_mul (p q : Multiplicative ℝ × Circle) :
    artinComplexPolarUnit (p * q) = artinComplexPolarUnit p * artinComplexPolarUnit q := by
  apply Units.ext
  simp only [artinComplexPolarUnit, Units.val_mk0, Units.val_mul,
    Prod.fst_mul, Prod.snd_mul, toAdd_mul, Circle.coe_mul]
  rw [add_div, Real.exp_add, Complex.ofReal_mul]
  ring

theorem artinComplexPolarUnit_right_inv (z : ℂˣ) :
    artinComplexPolarUnit (Multiplicative.ofAdd (2 * Real.log ‖(z : ℂ)‖),
      artinComplexUnitAngle z) = z := by
  apply Units.ext
  have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  simp only [artinComplexPolarUnit, Units.val_mk0, toAdd_ofAdd,
    artinComplexUnitAngle]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.exp_log hn]
  field_simp

theorem artinComplexPolarUnit_left_inv (p : Multiplicative ℝ × Circle) :
    (Multiplicative.ofAdd (2 * Real.log ‖(artinComplexPolarUnit p : ℂ)‖),
      artinComplexUnitAngle (artinComplexPolarUnit p)) = p := by
  apply Prod.ext
  · rw [artinComplexPolarUnit_norm, Real.log_exp]
    change 2 * (Multiplicative.toAdd p.1 / 2) = Multiplicative.toAdd p.1
    ring
  · apply Circle.ext
    change (artinComplexPolarUnit p : ℂ) / (‖(artinComplexPolarUnit p : ℂ)‖ : ℂ) = (p.2 : ℂ)
    rw [artinComplexPolarUnit_norm, artinComplexPolarUnit_val]
    field_simp

theorem artinComplexPolarUnit_continuous : Continuous artinComplexPolarUnit := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun p : Multiplicative ℝ × Circle =>
    (Real.exp (Multiplicative.toAdd p.1 / 2) : ℂ) * (p.2 : ℂ))
  exact (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp ((continuous_toAdd.comp continuous_fst).div_const 2))).mul
      (continuous_subtype_val.comp continuous_snd)

theorem artinComplexUnitAngle_continuous : Continuous artinComplexUnitAngle := by
  apply Continuous.subtype_mk
  exact Units.continuous_val.div
    (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero))

/-- The actual complex multiplicative group splits into log(|z|²) and Circle. -/
def artinComplexPlaceCoordinates : (Multiplicative ℝ × Circle) ≃ₜ* ℂˣ where
  toFun := artinComplexPolarUnit
  invFun z := (Multiplicative.ofAdd (2 * Real.log ‖(z : ℂ)‖), artinComplexUnitAngle z)
  left_inv := artinComplexPolarUnit_left_inv
  right_inv := artinComplexPolarUnit_right_inv
  map_mul' := artinComplexPolarUnit_mul
  continuous_toFun := artinComplexPolarUnit_continuous
  continuous_invFun :=
    (continuous_ofAdd.comp (continuous_const.mul
      (Units.continuous_val.norm.log (fun z => norm_ne_zero_iff.mpr z.ne_zero)))).prodMk
        artinComplexUnitAngle_continuous

end
end SimultaneousPrimitiveRoots
