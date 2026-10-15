module

public import SimultaneousPrimitiveRoots.NumberFieldFiniteCompletionGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Set Topology
open scoped WithZero Valued
noncomputable section

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- Global integers represent every residue class in the actual local integer ring. -/
theorem artinNumberFieldFiniteCompletion_integer_approx
    (x : v.adicCompletion K) (hx : ‖x‖ ≤ 1) :
    ∃ r : 𝓞 K, ‖algebraMap (𝓞 K) (v.adicCompletion K) r - x‖ < 1 := by
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap K v).exists_dist_lt x
    (show (0 : ℝ) < 1 by norm_num)
  have hk' : ‖algebraMap K (v.adicCompletion K) k - x‖ < 1 := by
    simpa [dist_eq_norm, norm_sub_rev] using hk
  have hn : ‖algebraMap K (v.adicCompletion K) k‖ ≤ 1 := by
    calc
      _ = ‖(algebraMap K (v.adicCompletion K) k - x) + x‖ := by congr 1; ring
      _ ≤ max ‖algebraMap K (v.adicCompletion K) k - x‖ ‖x‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le hk'.le hx
  have hvk : v.valuation K k ≤ 1 := by
    have h : Valued.v (algebraMap K (v.adicCompletion K) k) ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.mp hn
    change Valued.v (k : v.adicCompletion K) ≤ 1 at h
    simpa only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using h
  obtain ⟨r, hr⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hvk (1 : (ℤᵐ⁰)ˣ)
  have hr' : ‖algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r - k)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff]
    change Valued.v ((algebraMap (𝓞 K) K r - k : K) : v.adicCompletion K) < 1
    simpa only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Units.val_one] using hr
  rw [map_sub, ← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)] at hr'
  refine ⟨r, ?_⟩
  calc
    _ = ‖(algebraMap (𝓞 K) (v.adicCompletion K) r -
        algebraMap K (v.adicCompletion K) k) + (algebraMap K (v.adicCompletion K) k - x)‖ := by
      congr 1; ring
    _ ≤ max ‖algebraMap (𝓞 K) (v.adicCompletion K) r -
        algebraMap K (v.adicCompletion K) k‖ ‖algebraMap K (v.adicCompletion K) k - x‖ :=
      IsUltrametricDist.norm_add_le_max _ _
    _ < 1 := max_lt hr' hk'

theorem artinNumberFieldFiniteCompletion_residue_zero_iff (x : v.adicCompletionIntegers K) :
    IsLocalRing.residue (v.adicCompletionIntegers K) x = 0 ↔
      ‖(x : v.adicCompletion K)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit x ↔ _
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    Valued.toNormedField.norm_lt_one_iff]

def artinNumberFieldFiniteCompletionResidueMap :
    𝓞 K →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue _).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))

theorem artinNumberFieldFiniteCompletionResidueMap_surjective :
    Function.Surjective (artinNumberFieldFiniteCompletionResidueMap K v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr⟩ := artinNumberFieldFiniteCompletion_integer_approx K v x
    ((artinNumberFieldFiniteCompletion_norm_le_one_iff K v x).mpr x.2)
  refine ⟨r, ?_⟩
  change IsLocalRing.residue _ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r) =
    IsLocalRing.residue _ x
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (artinNumberFieldFiniteCompletion_residue_zero_iff K v _).mpr hr

theorem artinNumberFieldFiniteCompletionResidueMap_kernel :
    v.asIdeal ≤ RingHom.ker (artinNumberFieldFiniteCompletionResidueMap K v) := by
  intro r hr
  rw [RingHom.mem_ker]
  change IsLocalRing.residue _ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r) = 0
  apply (artinNumberFieldFiniteCompletion_residue_zero_iff K v _).mpr
  exact (FinitePlace.norm_lt_one_iff_mem K v r).mpr hr

/-- A finite quotient of the global integers surjects onto the actual completion residue field. -/
instance artinNumberFieldFiniteCompletionResidue_finite :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let f := Ideal.Quotient.lift v.asIdeal (artinNumberFieldFiniteCompletionResidueMap K v)
    (artinNumberFieldFiniteCompletionResidueMap_kernel K v)
  apply Finite.of_surjective f
  intro y
  obtain ⟨r, hr⟩ := artinNumberFieldFiniteCompletionResidueMap_surjective K v y
  exact ⟨Ideal.Quotient.mk _ r, hr⟩

instance artinNumberFieldFiniteCompletion_proper : ProperSpace (v.adicCompletion K) := by
  apply (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := v.adicCompletion K) (Γ₀ := ℤᵐ⁰)).mpr
  refine ⟨inferInstance, ?_, ?_⟩
  · change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  · change Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
    infer_instance

theorem artinNumberFieldFiniteCompletionUnitCutoff_isCompact :
    IsCompact (artinLocalUnitCutoff (v.adicCompletion K) : Set (v.adicCompletion K)ˣ) :=
  artinLocalUnitCutoff_isCompact _

end
end SimultaneousPrimitiveRoots
