module

public import SimultaneousPrimitiveRoots.Hecke.Covolume
public import SimultaneousPrimitiveRoots.Hecke.DedekindHecke

/-!
# The covolume of the lattice of an ideal

For a fractional ideal `I` and Mathlib's `basisOfFractionalIdeal`,
`|disc(b_I)| = |d_K| · N(I)²` (change of basis from `integralBasis`, whose determinant has absolute
value `N(I)`). Hence the Hartley covolume of the lattice of `I` is `√|d_K| · N(I)`. For the class
representatives this is the constant `ε_c⁻¹` of Hecke's functional equation.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Module Matrix
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- `|disc(b_I)| = |d_K| · N(I)²`. -/
theorem abs_discr_basisOfFractionalIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    |((Algebra.discr ℚ (basisOfFractionalIdeal K I : _ → K) : ℚ) : ℝ)| =
      |((discr K : ℤ) : ℝ)| * ((FractionalIdeal.absNorm I.1 : ℚ) : ℝ) ^ 2 := by
  classical
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K)) =
      Fintype.card (Free.ChooseBasisIndex ℤ I) := by
    rw [← Module.finrank_eq_card_basis (integralBasis K),
      ← Module.finrank_eq_card_basis (basisOfFractionalIdeal K I)]
  let e : Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Free.ChooseBasisIndex ℤ I :=
    Fintype.equivOfCardEq hcard
  set b' := (basisOfFractionalIdeal K I).reindex e.symm with hb'
  have hre : Algebra.discr ℚ (b' : _ → K) = Algebra.discr ℚ (basisOfFractionalIdeal K I : _ → K) := by
    rw [hb', Module.Basis.coe_reindex, Algebra.discr_reindex]
  set P := (integralBasis K).toMatrix b' with hP
  have hvec : (b' : _ → K) = (integralBasis K : _ → K) ᵥ* P.map (algebraMap ℚ K) := by
    funext j
    rw [Matrix.vecMul, dotProduct, ← (integralBasis K).sum_toMatrix_smul_self b' j]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.map_apply, Algebra.smul_def, mul_comm]
  have hdisc : Algebra.discr ℚ (b' : _ → K) = P.det ^ 2 * (discr K : ℚ) := by
    rw [hvec, Algebra.discr_of_matrix_vecMul, coe_discr]
  have hdet : |P.det| = FractionalIdeal.absNorm I.1 := by
    rw [hP, ← Module.Basis.det_apply]
    exact det_basisOfFractionalIdeal_eq_absNorm K I e
  rw [← hre, hdisc, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow, ← Rat.cast_abs, hdet,
    Rat.cast_intCast]
  ring

/-- **The covolume of the lattice of `I` is `√|d_K| · N(I)`.** -/
theorem abs_det_casMatrix_basisOfFractionalIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (e : Free.ChooseBasisIndex ℤ I ≃ (K →+* ℂ)) :
    |(casMatrix (fun _ => 1) (basisOfFractionalIdeal K I : _ → K) e).det| =
      Real.sqrt |((discr K : ℤ) : ℝ)| * ((FractionalIdeal.absNorm I.1 : ℚ) : ℝ) := by
  classical
  have h := det_casMatrix_sq_eq_abs_discr (basisOfFractionalIdeal K I) e
  rw [abs_discr_basisOfFractionalIdeal] at h
  have hN : (0 : ℝ) ≤ ((FractionalIdeal.absNorm I.1 : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg I.1
  rw [← Real.sqrt_sq (abs_nonneg _), sq_abs, h, Real.sqrt_mul (abs_nonneg _),
    Real.sqrt_sq hN]

end SimultaneousPrimitiveRoots.Hecke

end
