module

public import SimultaneousPrimitiveRoots.NormSectionPowers
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

noncomputable section
variable {G : Type*} [CommGroup G]

theorem artinComplexUnits_exists_power_root {k : ℕ} (hk : 0 < k) (z : ℂˣ) :
    ∃ w : ℂˣ, w ^ k = z := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) hk
  have hn : w ≠ 0 := by
    intro h
    apply z.ne_zero
    rw [← hw, h, zero_pow (Nat.ne_of_gt hk)]
  refine ⟨Units.mk0 w hn, ?_⟩
  apply Units.ext
  simpa using hw

theorem artinComplexProduct_exists_power_root (n : ℕ) {k : ℕ} (hk : 0 < k)
    (z : Fin (n + 1) → ℂˣ) : ∃ w : Fin (n + 1) → ℂˣ, w ^ k = z := by
  choose w hw using fun i => artinComplexUnits_exists_power_root hk (z i)
  exact ⟨w, funext hw⟩

/-- Every exponent-k class of the product comes from its finite-place
coordinate. This uses actual complex divisibility, not only the norm section. -/
theorem artinFiniteComplexClass_only_finite {H : Type*} [Monoid H] (n : ℕ)
    {k : ℕ} (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H)
    (he : ∀ h : H, h ^ k = 1) (g : G) (z : Fin (n + 1) → ℂˣ) :
    χ (g, z) = χ (g, 1) := by
  obtain ⟨w, hw⟩ := artinComplexProduct_exists_power_root n hk z
  have hp : ((1, w) : G × (Fin (n + 1) → ℂˣ)) ^ k = (1, z) := by
    apply Prod.ext
    · simp
    · exact hw
  have hχ : χ (1, z) = 1 := by rw [← hp, map_pow, he]
  calc
    χ (g, z) = χ ((g, 1) * (1, z)) := by simp
    _ = χ (g, 1) := by rw [map_mul, hχ, mul_one]

/-- The actual quotient by k-th powers, without replacing classes by labels. -/
def artinPowerSubgroup (G : Type*) [CommGroup G] (k : ℕ) : Subgroup G :=
  (powMonoidHom k : G →* G).range

def artinPowerClass (G : Type*) [CommGroup G] (k : ℕ) :
    G →* G ⧸ artinPowerSubgroup G k :=
  QuotientGroup.mk' (artinPowerSubgroup G k)

theorem artinPowerClass_pow_one (k : ℕ) (g : G) : artinPowerClass G k (g ^ k) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨g, rfl⟩

theorem artinPowerQuotient_exponent (k : ℕ) (h : G ⧸ artinPowerSubgroup G k) :
    h ^ k = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (artinPowerSubgroup G k) h
  exact (map_pow (artinPowerClass G k) g k).symm.trans (artinPowerClass_pow_one k g)

theorem artinFiniteComplexNormSection_power_class_one (n : ℕ) {k : ℕ} (hk : 0 < k)
    (u : ℝ) :
    artinPowerClass (G × (Fin (n + 1) → ℂˣ)) k (artinFiniteComplexNormSection n u) = 1 :=
  artinFiniteComplexNormSection_class_one n hk _ (artinPowerQuotient_exponent k) u

theorem artinFiniteComplexNormSection_power_class_mul (n : ℕ) {k : ℕ} (hk : 0 < k)
    (u : ℝ) (z : G × (Fin (n + 1) → ℂˣ)) :
    artinPowerClass (G × (Fin (n + 1) → ℂˣ)) k (artinFiniteComplexNormSection n u * z) =
      artinPowerClass (G × (Fin (n + 1) → ℂˣ)) k z :=
  artinFiniteComplexNormSection_class_mul n hk _ (artinPowerQuotient_exponent k) u z

/-- The actual sheet parametrization has the same power class at every norm. -/
theorem artinComplexNormPoint_power_class_radial_invariant (n : ℕ) {k : ℕ} (hk : 0 < k)
    (g : G) (w : ℝ)
    (p : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle)) :
    artinPowerClass (G × (Fin (n + 1) → ℂˣ)) k (g, artinComplexNormPoint n w p) =
      artinPowerClass (G × (Fin (n + 1) → ℂˣ)) k (g, artinComplexNormPoint n 0 p) := by
  have h := artinFiniteComplexNormSection_power_class_mul n hk (Real.exp w)
    (g, artinComplexNormPoint n 0 p)
  simpa only [artinFiniteComplexNormSection, artinComplexNormSection, Real.log_exp,
    Prod.mk_mul_mk, one_mul, ← artinComplexNormPoint_mul, add_zero] using h

end
end SimultaneousPrimitiveRoots
