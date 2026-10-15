module

public import SimultaneousPrimitiveRoots.FiniteNormCutoffBessel
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Topology.Algebra.Group.Units

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set
open scoped NormedField Valued
noncomputable section

variable (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F]

/-- The valuation-ring ball of an actual nonarchimedean normed field. -/
def artinLocalIntegerBall : Submonoid F where
  carrier := {x | ‖x‖ ≤ 1}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change ‖x * y‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

/-- The actual valuation-ring units as a subgroup of the local multiplicative group. -/
def artinLocalUnitCutoff : Subgroup Fˣ := (artinLocalIntegerBall F).units

theorem artinLocalIntegerBall_eq_closedBall :
    (artinLocalIntegerBall F : Set F) = Metric.closedBall 0 1 := by
  ext x
  simp [artinLocalIntegerBall, Metric.mem_closedBall, dist_zero_right]

theorem artinLocalUnitCutoff_mem (z : Fˣ) :
    z ∈ artinLocalUnitCutoff F ↔ ‖(z : F)‖ = 1 := by
  change (‖(z : F)‖ ≤ 1 ∧ ‖((z⁻¹ : Fˣ) : F)‖ ≤ 1) ↔ _
  rw [Units.val_inv_eq_inv_val, norm_inv]
  constructor
  · intro h
    have hn : 0 < ‖(z : F)‖ := norm_pos_iff.mpr z.ne_zero
    have hge : 1 ≤ ‖(z : F)‖ := (inv_le_one₀ hn).mp h.2
    exact le_antisymm h.1 hge
  · intro h
    simp [h]

theorem artinLocalUnitCutoff_isOpen : IsOpen (artinLocalUnitCutoff F : Set Fˣ) := by
  apply Submonoid.isOpen_units
  rw [artinLocalIntegerBall_eq_closedBall]
  exact IsUltrametricDist.isOpen_closedBall (0 : F) one_ne_zero

theorem artinLocalUnitCutoff_isCompact [ProperSpace F] :
    IsCompact (artinLocalUnitCutoff F : Set Fˣ) := by
  apply Submonoid.units_isCompact
  rw [artinLocalIntegerBall_eq_closedBall]
  exact isCompact_closedBall 0 1

/-- This is an actual continuous log-norm character, with any normalization exponent. -/
def artinLocalLogNorm (d : ℝ) : Fˣ →* Multiplicative ℝ where
  toFun z := Multiplicative.ofAdd (d * Real.log ‖(z : F)‖)
  map_one' := by simp
  map_mul' := by
    intro x y
    change d * Real.log ‖((x * y : Fˣ) : F)‖ =
      d * Real.log ‖(x : F)‖ + d * Real.log ‖(y : F)‖
    rw [Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr x.ne_zero) (norm_ne_zero_iff.mpr y.ne_zero)]
    ring

theorem artinLocalLogNorm_continuous (d : ℝ) : Continuous (artinLocalLogNorm F d) :=
  continuous_ofAdd.comp (continuous_const.mul
    (Units.continuous_val.norm.log (fun z => norm_ne_zero_iff.mpr z.ne_zero)))

theorem artinLocalLogNorm_cutoff (d : ℝ) :
    ∀ z ∈ artinLocalUnitCutoff F, artinLocalLogNorm F d z = 1 := by
  intro z hz
  simp [artinLocalLogNorm, (artinLocalUnitCutoff_mem F z).mp hz]

/-- Existing valuation-ring units map into this concrete cutoff. -/
theorem artinLocalIntegerUnit_mem (z : 𝒪[F]ˣ) :
    ‖((z : 𝒪[F]) : F)‖ = 1 := Valued.integer.norm_coe_unit z

theorem artinLocalIntegerBall_eq_integer :
    (artinLocalIntegerBall F : Set F) = (𝒪[F] : Set F) := by
  ext x
  exact (Valued.integer.mem_iff (K := F)).symm

def artinLocalIntegerUnitsMap : 𝒪[F]ˣ →* Fˣ :=
  Units.map (𝒪[F]).subtype.toMonoidHom

theorem artinLocalIntegerUnitsMap_mem (z : 𝒪[F]ˣ) :
    artinLocalIntegerUnitsMap F z ∈ artinLocalUnitCutoff F := by
  rw [artinLocalUnitCutoff_mem]
  exact artinLocalIntegerUnit_mem F z

/-- The cutoff is exactly the image of the actual valuation-ring unit group. -/
theorem artinLocalIntegerUnitsMap_range :
    Set.range (artinLocalIntegerUnitsMap F) = (artinLocalUnitCutoff F : Set Fˣ) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact artinLocalIntegerUnitsMap_mem F w
  · intro hz
    have hn := (artinLocalUnitCutoff_mem F z).mp hz
    have hi : ‖((z⁻¹ : Fˣ) : F)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hn, inv_one]
    let w : 𝒪[F]ˣ :=
      { val := ⟨(z : F), Valued.integer.mem_iff.mpr hn.le⟩
        inv := ⟨((z⁻¹ : Fˣ) : F), Valued.integer.mem_iff.mpr hi.le⟩
        val_inv := Subtype.ext z.val_inv
        inv_val := Subtype.ext z.inv_val }
    exact ⟨w, Units.ext rfl⟩

variable [MeasurableSpace Fˣ] [BorelSpace Fˣ]

theorem artinLocalUnitCutoff_mass_pos [ProperSpace F]
    (ν : Measure Fˣ) [ν.IsHaarMeasure] :
    0 < artinFiniteSheetMass ν (artinLocalUnitCutoff F) :=
  artinFiniteSheetMass_haar_subgroup_pos (artinLocalUnitCutoff F)
    (artinLocalUnitCutoff_isCompact F) (artinLocalUnitCutoff_isOpen F)

theorem artinLocalUnitCutoffHaar_isHaar (ν : Measure Fˣ) [ν.IsHaarMeasure] :
    (artinFiniteUnitCutoffHaar ν (artinLocalUnitCutoff F)).IsHaarMeasure :=
  artinFiniteUnitCutoffHaar_isHaar ν _ (artinLocalUnitCutoff_isOpen F)

theorem artinLocalUnitCutoffHaar_finite [ProperSpace F]
    (ν : Measure Fˣ) [ν.IsHaarMeasure] :
    IsFiniteMeasure (artinFiniteUnitCutoffHaar ν (artinLocalUnitCutoff F)) :=
  artinFiniteUnitCutoffHaar_finite ν _ (artinLocalUnitCutoff_isCompact F)
    (artinLocalUnitCutoff_isOpen F)

variable [ProperSpace F] [SecondCountableTopology Fˣ]

/-- The previous full-kernel K integral applies with the concrete local unit cutoff. -/
theorem artinLocalUnitCutoffBessel_mellin (d : ℝ) (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinLocalLogNorm F d) n)) [μ.IsHaarMeasure]
    (ν : Measure Fˣ) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinFiniteNormCutoffBesselProfile (artinLocalLogNorm F d)
      (artinLocalUnitCutoff F) n μ c) s =
      (artinFiniteNormCutoffBesselC (artinLocalLogNorm F d) (artinLocalUnitCutoff F) n
        (artinLocalLogNorm_cutoff F d) μ ν (artinLocalUnitCutoff_isOpen F) c : ℂ) *
        (artinFiniteBesselSheetA c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (n + 1) :=
  artinFiniteNormCutoffBesselProfile_mellin _ _ _ (artinLocalLogNorm_cutoff F d) μ ν
    (artinLocalUnitCutoff_isCompact F) (artinLocalUnitCutoff_isOpen F) hc hs

theorem artinLocalUnitCutoffBessel_gaussian (d : ℝ) (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinLocalLogNorm F d) n)) [μ.IsHaarMeasure]
    (ν : Measure Fˣ) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel
      (artinFiniteNormCutoffBesselC (artinLocalLogNorm F d) (artinLocalUnitCutoff F) n
        (artinLocalLogNorm_cutoff F d) μ ν (artinLocalUnitCutoff_isOpen F) c)
      (artinFiniteBesselSheetA c) (n + 1) T *
      artinFiniteNormCutoffBesselProfile (artinLocalLogNorm F d) (artinLocalUnitCutoff F)
        n μ c (u * T) ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u :=
  artinFiniteNormCutoffBesselProfile_gaussian _ _ _ (artinLocalLogNorm_cutoff F d) μ ν
    (artinLocalUnitCutoff_isCompact F) (artinLocalUnitCutoff_isOpen F) hc hu

end
end SimultaneousPrimitiveRoots
