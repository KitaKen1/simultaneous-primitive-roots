module

public import SimultaneousPrimitiveRoots.ComplexCompletionHaar
public import SimultaneousPrimitiveRoots.NumberFieldFiniteIdeleCutoff
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField NumberField.InfinitePlace MeasureTheory Set Topology
open scoped Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev ArtinNumberFieldComplexPlaces := {v : InfinitePlace K // v.IsComplex}
abbrev ArtinNumberFieldComplexUnits := (v : ArtinNumberFieldComplexPlaces K) → v.1.Completionˣ

instance artinNumberFieldComplexPlaces_fintype : Fintype (ArtinNumberFieldComplexPlaces K) :=
  inferInstance

instance artinNumberFieldComplexLocalUnits_secondCountable (v : ArtinNumberFieldComplexPlaces K) :
    SecondCountableTopology v.1.Completionˣ := artinComplexCompletionUnits_secondCountable v.2

instance artinNumberFieldComplexLocalUnits_locallyCompact (v : ArtinNumberFieldComplexPlaces K) :
    LocallyCompactSpace v.1.Completionˣ :=
  (artinComplexCompletionUnitsEquiv v.2).toHomeomorph.isOpenEmbedding.locallyCompactSpace

/-- All complex places, including their actual completions, are retained in this indexing. -/
def artinNumberFieldComplexPlaceIndex (hr : 0 < nrComplexPlaces K) :
    Fin (nrComplexPlaces K - 1 + 1) ≃ ArtinNumberFieldComplexPlaces K :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_fin]; exact Nat.sub_add_cancel hr)

theorem artinNumberFieldComplexPlaces_pos [IsTotallyComplex K] : 0 < nrComplexPlaces K := by
  have h := Module.finrank_pos (R := ℚ) (M := K)
  rw [IsTotallyComplex.finrank K] at h
  omega

/-- Reindex every actual completion unit group, then apply the existing norm-preserving local map. -/
def artinNumberFieldComplexUnitsEquiv (hr : 0 < nrComplexPlaces K) :
    ArtinNumberFieldComplexUnits K ≃ₜ* (Fin (nrComplexPlaces K - 1 + 1) → ℂˣ) where
  toFun z i := artinComplexCompletionUnitsEquiv (artinNumberFieldComplexPlaceIndex K hr i).2
    (z (artinNumberFieldComplexPlaceIndex K hr i))
  invFun z v := (artinComplexCompletionUnitsEquiv v.2).symm
    (z ((artinNumberFieldComplexPlaceIndex K hr).symm v))
  left_inv z := by
    funext v
    change (artinComplexCompletionUnitsEquiv v.2).symm
      ((fun w : ArtinNumberFieldComplexPlaces K => artinComplexCompletionUnitsEquiv w.2 (z w))
        ((artinNumberFieldComplexPlaceIndex K hr) ((artinNumberFieldComplexPlaceIndex K hr).symm v))) = z v
    rw [(artinNumberFieldComplexPlaceIndex K hr).apply_symm_apply]
    exact (artinComplexCompletionUnitsEquiv v.2).symm_apply_apply (z v)
  right_inv z := by funext i; simp
  map_mul' z w := by funext i; exact map_mul _ _ _
  continuous_toFun := continuous_pi (fun i =>
    (artinComplexCompletionUnitsEquiv (artinNumberFieldComplexPlaceIndex K hr i).2).continuous.comp
      (continuous_apply _))
  continuous_invFun := continuous_pi (fun v =>
    (artinComplexCompletionUnitsEquiv v.2).symm.continuous.comp (continuous_apply _))

theorem artinNumberFieldComplexUnitsEquiv_norm (hr : 0 < nrComplexPlaces K)
    (z : ArtinNumberFieldComplexUnits K) (i : Fin (nrComplexPlaces K - 1 + 1)) :
    ‖(artinNumberFieldComplexUnitsEquiv K hr z i : ℂ)‖ =
      ‖(z (artinNumberFieldComplexPlaceIndex K hr i) :
        (artinNumberFieldComplexPlaceIndex K hr i).1.Completion)‖ :=
  artinComplexCompletionUnitsEquiv_norm _ _

theorem artinNumberFieldComplexUnitsEquiv_norm_product (hr : 0 < nrComplexPlaces K)
    (z : ArtinNumberFieldComplexUnits K) :
    (∏ i, ‖(artinNumberFieldComplexUnitsEquiv K hr z i : ℂ)‖ ^ 2) =
      ∏ v : ArtinNumberFieldComplexPlaces K, ‖(z v : v.1.Completion)‖ ^ 2 :=
  Fintype.prod_equiv (artinNumberFieldComplexPlaceIndex K hr) _ _
    (fun i => congrArg (fun t : ℝ => t ^ 2) (artinNumberFieldComplexUnitsEquiv_norm K hr z i))

theorem artinNumberFieldComplexUnitsEquiv_bessel_product (hr : 0 < nrComplexPlaces K)
    (c : ArtinNumberFieldComplexPlaces K → ℝ) (z : ArtinNumberFieldComplexUnits K) :
    (∏ i, artinBesselLocalProfile (c (artinNumberFieldComplexPlaceIndex K hr i))
      (‖(artinNumberFieldComplexUnitsEquiv K hr z i : ℂ)‖ ^ 2)) =
      ∏ v : ArtinNumberFieldComplexPlaces K,
        artinBesselLocalProfile (c v) (‖(z v : v.1.Completion)‖ ^ 2) :=
  Fintype.prod_equiv (artinNumberFieldComplexPlaceIndex K hr) _ _ (fun i =>
    congrArg (fun t : ℝ => artinBesselLocalProfile
      (c (artinNumberFieldComplexPlaceIndex K hr i)) (t ^ 2))
      (artinNumberFieldComplexUnitsEquiv_norm K hr z i))

def artinNumberFieldComplexLogNorm : ArtinNumberFieldComplexUnits K →* Multiplicative ℝ where
  toFun z := Multiplicative.ofAdd (∑ v : ArtinNumberFieldComplexPlaces K,
    2 * Real.log ‖(z v : v.1.Completion)‖)
  map_one' := by simp
  map_mul' z w := by
    change (∑ v : ArtinNumberFieldComplexPlaces K,
      2 * Real.log ‖((z v * w v : v.1.Completionˣ) : v.1.Completion)‖) = _
    simp only [Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (z _).ne_zero) (norm_ne_zero_iff.mpr (w _).ne_zero),
      mul_add, Finset.sum_add_distrib]
    rfl

theorem artinNumberFieldComplexLogNorm_continuous : Continuous (artinNumberFieldComplexLogNorm K) :=
  continuous_ofAdd.comp (continuous_finsetSum _ (fun v _ => continuous_const.mul
    ((Units.continuous_val.comp (continuous_apply v)).norm.log
      (fun z => norm_ne_zero_iff.mpr (z v).ne_zero))))

theorem artinNumberFieldComplexLogNorm_exp (z : ArtinNumberFieldComplexUnits K) :
    Real.exp (Multiplicative.toAdd (artinNumberFieldComplexLogNorm K z)) =
      ∏ v : ArtinNumberFieldComplexPlaces K, ‖(z v : v.1.Completion)‖ ^ 2 := by
  change Real.exp (∑ v : ArtinNumberFieldComplexPlaces K,
    2 * Real.log ‖(z v : v.1.Completion)‖) = _
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro v _
  rw [two_mul, Real.exp_add, Real.exp_log (norm_pos_iff.mpr (z v).ne_zero), pow_two]

theorem artinNumberFieldComplexUnitsEquiv_logNorm (hr : 0 < nrComplexPlaces K)
    (z : ArtinNumberFieldComplexUnits K) :
    artinComplexTotalLogNorm (nrComplexPlaces K - 1) (artinNumberFieldComplexUnitsEquiv K hr z) =
      artinNumberFieldComplexLogNorm K z := by
  apply Multiplicative.toAdd.injective
  apply Real.exp_injective
  rw [artinComplexTotalLogNorm_exp, artinNumberFieldComplexLogNorm_exp,
    artinNumberFieldComplexUnitsEquiv_norm_product]

end
end SimultaneousPrimitiveRoots
