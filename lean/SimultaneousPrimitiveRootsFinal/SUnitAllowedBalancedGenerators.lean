import SimultaneousPrimitiveRootsFinal.SUnitSexticPreparation
import SimultaneousPrimitiveRootsFinal.SUnitBalancedRepresentatives

/-!
# Allowed and balanced generators: the arithmetic completion

Combine the actual coherent sextic Hilbert complement with the compact
norm-one representative set. Balancing multiplies a generator by an actual
sixth power of an S-unit and therefore preserves its allowed class.

The normalized local tuple has the same finite coordinates as its generator;
its infinite coordinates have been scaled to norm one. Identifying this
normalization with the analytic signal and proving its Poisson estimates
belong to the next analytic stage. Compactness itself is proved here.
-/

noncomputable section
namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge
open ClassFieldTheory Arithmetic NumberField IsDedekindDomain
open scoped NumberField BigOperators

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- Changing a generator by a sixth power of an S-unit preserves its actual local class. -/
theorem allowed_class_sixth_power_invariant (a : Fˣ) (u : SUnitGroup (K := F) S) :
    powerClassMk _ 6 (fieldToFiniteS F S ((u : Fˣ) ^ 6 * a)) =
      powerClassMk _ 6 (fieldToFiniteS F S a) := by
  rw [map_mul, map_pow, map_mul, map_pow, powerClass_pow_eq_one, one_mul]

/-- The finite coordinates of the full S-local diagonal map are the previous finite tuple. -/
theorem sUnitToSLocal_finite (u : SUnitGroup (K := F) S) :
    (sUnitToSLocal F S u).2 = sUnitToFiniteS F S u := by
  funext v
  apply Units.ext
  rfl

/-- **Balancing preserves the allowed class and uses a fixed compact norm-one set.** -/
theorem exists_compact_balancing_preserving_allowed
    (B : Subgroup (PowerClass (∀ v : S, (v.1.adicCompletion F)ˣ) 6)) :
    ∃ K : Set (SLocalUnits F S), IsCompact K ∧
      (∀ y ∈ K, sLocalNorm F S y = 1) ∧
      ∀ (a : Fˣ) (x : SLocalUnits F S),
        sLocalNorm F S x = 1 → x.2 = fieldToFiniteS F S a →
        powerClassMk _ 6 (fieldToFiniteS F S a) ∈ B →
        ∃ u : SUnitGroup (K := F) S,
          powerClassMk _ 6 (fieldToFiniteS F S ((u : Fˣ) ^ 6 * a)) ∈ B ∧
          x * sUnitToSLocal F S u ^ 6 ∈ K ∧
          (x * sUnitToSLocal F S u ^ 6).2 =
            fieldToFiniteS F S ((u : Fˣ) ^ 6 * a) := by
  obtain ⟨K, hcompact, hnorm, hcover⟩ := exists_compact_sixth_sUnit_representatives F S
  refine ⟨K, hcompact, fun y hy => (sLocalNorm_eq_one_iff F S y).mpr (hnorm y hy), ?_⟩
  intro a x hx hfin ha
  obtain ⟨u, hu⟩ := hcover x ((sLocalNorm_eq_one_iff F S x).mp hx)
  refine ⟨u, (allowed_class_sixth_power_invariant F S a u).symm ▸ ha, hu, ?_⟩
  change x.2 * (sUnitToSLocal F S u).2 ^ 6 = _
  rw [sUnitToSLocal_finite, hfin, map_mul, map_pow]
  exact mul_comm _ _

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
