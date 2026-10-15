module

public import SimultaneousPrimitiveRoots.Hecke.CovolumeIdeal
public import SimultaneousPrimitiveRoots.Hecke.DualPartialZeta

/-!
# Hecke's functional equation, class by class

For each ideal class `c` with representative `J_c` (in `c⁻¹`), Hecke's `Λ_c` satisfies

`Λ_c(n/2 - s) = (√|d_K| · N(J_c))⁻¹ · Λ_c^∨(s)`,

where `Λ_c^∨` is the `symm` side of the FE-pair. For real `s > n/2` the two sides are the cone sums

`Λ_c(s)   = π^{-s} Γ(s) ∑_{x ∈ J_c ∩ cone} heckeConst · |N x|^{-2s/n}`,
`Λ_c^∨(s) = π^{-s} Γ(s) ∑_{x ∈ J_c^∨ ∩ cone} heckeConst · |N x|^{-2s/n}`,

with `J_c^∨` the trace dual of `J_c` (`= (J_c 𝔡)⁻¹`). The constant `√|d_K|` is the source of the
`|d_K|^{s/2}` in the completed Dedekind zeta function.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Ideal NumberField.Units Module
open scoped nonZeroDivisors Real

variable (K : Type*) [Field K] [NumberField K]

/-- The covolume of the lattice of the class representative `J_c`. -/
theorem abs_det_casMatrix_classBasis (c : ClassGroup (𝓞 K)) :
    |(casMatrix (fun _ => 1) (classBasis K c : classIdx K c → K) (classEmb K c)).det| =
      Real.sqrt |((discr K : ℤ) : ℝ)| * (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) := by
  rw [classBasis, abs_det_casMatrix_basisOfFractionalIdeal, classFrac, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rfl

/-- **Hecke's functional equation for the class `c`.** -/
theorem classFEPair_functional_equation (c : ClassGroup (𝓞 K)) (s : ℂ) :
    (classFEPair K c).Λ ((finrank ℚ K : ℝ) / 2 - s) =
      (((Real.sqrt |((discr K : ℤ) : ℝ)| * (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ))⁻¹ : ℝ) :
        ℂ) * (classFEPair K c).symm.Λ s := by
  classical
  have h := heckeFEPair_functional_equation (classBasis K c) (classEmb K c) s
  rw [card_classIdx_eq_finrank] at h
  rw [← abs_det_casMatrix_classBasis]
  exact h

/-- The dual side of the class `c` at real `s > n/2`: the cone sum of the trace dual of `J_c`. -/
theorem classFEPair_symm_ofReal (c : ClassGroup (𝓞 K)) {s : ℝ}
    (hs : (finrank ℚ K : ℝ) / 2 < s) :
    (classFEPair K c).symm.Λ (s : ℂ) = ((π ^ (-s) * Real.Gamma s *
      ∑' x : coneSet (latticeSet ((classBasis K c).traceDual : classIdx K c → K)),
        heckeConst K s * |(Algebra.norm ℚ (x : K) : ℝ)| ^ (-(2 * s / finrank ℚ K)) : ℝ) : ℂ) := by
  classical
  have hcard : (Fintype.card (classIdx K c) : ℝ) / 2 < s := by
    rw [card_classIdx_eq_finrank]
    exact hs
  exact heckeFEPair_symm_ofReal (classBasis K c) (classEmb K c)
    (by rw [latticeSet_classBasis]; exact idealInK_unit_mul _) hcard

end SimultaneousPrimitiveRoots.Hecke

end
