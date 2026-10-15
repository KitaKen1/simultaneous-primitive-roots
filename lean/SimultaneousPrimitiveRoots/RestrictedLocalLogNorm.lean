module

public import SimultaneousPrimitiveRoots.RestrictedLocalUnitGeometry
public import Mathlib.Algebra.BigOperators.Finprod

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Set Filter Topology
open scoped RestrictedProduct
noncomputable section

variable {ι : Type*} (F : ι → Type*)
  [∀ i, NontriviallyNormedField (F i)] [∀ i, IsUltrametricDist (F i)]

def artinRestrictedLocalLogTerm (d : ι → ℝ) (z : ArtinRestrictedLocalUnits F) (i : ι) : ℝ :=
  d i * Real.log ‖(z i : F i)‖

theorem artinRestrictedLocalBadPlaces_finite (z : ArtinRestrictedLocalUnits F) :
    {i | z i ∉ artinLocalUnitCutoff (F i)}.Finite :=
  eventually_cofinite.mp z.2

theorem artinRestrictedLocalLogTerm_zero (d : ι → ℝ) (z : ArtinRestrictedLocalUnits F)
    {i : ι} (hi : z i ∈ artinLocalUnitCutoff (F i)) :
    artinRestrictedLocalLogTerm F d z i = 0 := by
  simp [artinRestrictedLocalLogTerm, (artinLocalUnitCutoff_mem (F i) (z i)).mp hi]

theorem artinRestrictedLocalLogTerm_finiteSupport (d : ι → ℝ)
    (z : ArtinRestrictedLocalUnits F) :
    Function.HasFiniteSupport (artinRestrictedLocalLogTerm F d z) := by
  apply (artinRestrictedLocalBadPlaces_finite F z).subset
  intro i hi hu
  exact hi (artinRestrictedLocalLogTerm_zero F d z hu)

theorem artinRestrictedLocalLogTerm_mul (d : ι → ℝ)
    (x y : ArtinRestrictedLocalUnits F) (i : ι) :
    artinRestrictedLocalLogTerm F d (x * y) i =
      artinRestrictedLocalLogTerm F d x i + artinRestrictedLocalLogTerm F d y i := by
  change d i * Real.log ‖((x i * y i : (F i)ˣ) : F i)‖ = _
  rw [Units.val_mul, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr (x i).ne_zero) (norm_ne_zero_iff.mpr (y i).ne_zero)]
  simp only [artinRestrictedLocalLogTerm]
  ring

/-- Only finitely many summands can be nonzero, because this is a restricted product. -/
def artinRestrictedLocalLogNorm (d : ι → ℝ) :
    ArtinRestrictedLocalUnits F →* Multiplicative ℝ where
  toFun z := Multiplicative.ofAdd (∑ᶠ i, artinRestrictedLocalLogTerm F d z i)
  map_one' := by simp [artinRestrictedLocalLogTerm]
  map_mul' x y := by
    change (∑ᶠ i, artinRestrictedLocalLogTerm F d (x * y) i) =
      (∑ᶠ i, artinRestrictedLocalLogTerm F d x i) + ∑ᶠ i, artinRestrictedLocalLogTerm F d y i
    simp_rw [artinRestrictedLocalLogTerm_mul]
    exact finsum_add_distrib (artinRestrictedLocalLogTerm_finiteSupport F d x)
      (artinRestrictedLocalLogTerm_finiteSupport F d y)

theorem artinRestrictedLocalLogNorm_apply (d : ι → ℝ) (z : ArtinRestrictedLocalUnits F) :
    artinRestrictedLocalLogNorm F d z =
      Multiplicative.ofAdd (∑ᶠ i, d i * Real.log ‖(z i : F i)‖) := rfl

theorem artinRestrictedLocalLogNorm_finiteChart (d : ι → ℝ) (s : Finset ι)
    (z : ArtinRestrictedLocalUnits F) (hz : ∀ i ∉ s, z i ∈ artinLocalUnitCutoff (F i)) :
    artinRestrictedLocalLogNorm F d z =
      Multiplicative.ofAdd (∑ i ∈ s, d i * Real.log ‖(z i : F i)‖) := by
  classical
  change Multiplicative.ofAdd (∑ᶠ i, artinRestrictedLocalLogTerm F d z i) = _
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  exact hi (artinRestrictedLocalLogTerm_zero F d z (hz i hn))

theorem artinRestrictedLocalLogNorm_continuous (d : ι → ℝ) :
    Continuous (artinRestrictedLocalLogNorm F d) := by
  classical
  apply RestrictedProduct.continuous_dom.mpr
  intro S hS
  have hfinite : Sᶜ.Finite := by
    simpa only [mem_cofinite] using (le_principal_iff.mp hS)
  let inc := RestrictedProduct.inclusion (fun i => (F i)ˣ)
    (fun i => (artinLocalUnitCutoff (F i) : Set (F i)ˣ)) hS
  have heq : artinRestrictedLocalLogNorm F d ∘ inc =
      fun z => Multiplicative.ofAdd
        (∑ i ∈ hfinite.toFinset, d i * Real.log ‖(inc z i : F i)‖) := by
    funext z
    apply artinRestrictedLocalLogNorm_finiteChart
    intro i hi
    exact z.2 (by simpa using hi)
  rw [heq]
  apply continuous_ofAdd.comp
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul
    ((Units.continuous_val.comp (RestrictedProduct.continuous_eval i)).norm.log
      (fun z => norm_ne_zero_iff.mpr (z i).ne_zero))

theorem artinRestrictedLocalLogNorm_cutoff (d : ι → ℝ) :
    ∀ z ∈ artinRestrictedLocalUnitCutoff F, artinRestrictedLocalLogNorm F d z = 1 := by
  intro z hz
  have hn := (artinRestrictedLocalUnitCutoff_mem F z).mp hz
  simp [artinRestrictedLocalLogNorm_apply, hn]

end
end SimultaneousPrimitiveRoots
