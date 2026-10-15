module

public import SimultaneousPrimitiveRoots.ComplexNormKernelCoordinates

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Complex
noncomputable section

theorem artinComplexPolarUnit_one : artinComplexPolarUnit 1 = 1 := by
  apply Units.ext
  simp [artinComplexPolarUnit]

theorem artinComplexNormPoint_zero_one (n : ℕ) :
    artinComplexNormPoint n 0 1 = 1 := by
  funext i
  apply Units.ext
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [artinComplexNormPoint, artinComplexPolarUnit]

/-- The actual positive radial points form a homomorphism in log norm. -/
def artinComplexLogNormSection (n : ℕ) :
    Multiplicative ℝ →* (Fin (n + 1) → ℂˣ) where
  toFun w := artinComplexNormPoint n (Multiplicative.toAdd w) 1
  map_one' := artinComplexNormPoint_zero_one n
  map_mul' w v := by
    simpa only [toAdd_mul, one_mul] using
      artinComplexNormPoint_mul n (Multiplicative.toAdd w) (Multiplicative.toAdd v) 1 1

theorem artinComplexNormPoint_radial_pow (n k : ℕ) (w : ℝ) :
    artinComplexNormPoint n w 1 ^ k = artinComplexNormPoint n ((k : ℝ) * w) 1 := by
  simpa only [artinComplexLogNormSection, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_pow, toAdd_ofAdd, nsmul_eq_mul] using
      ((artinComplexLogNormSection n).map_pow (Multiplicative.ofAdd w) k).symm

/-- The root is specified explicitly, rather than chosen by surjectivity. -/
def artinComplexNormSectionRoot (n k : ℕ) (u : ℝ) : Fin (n + 1) → ℂˣ :=
  artinComplexNormPoint n (Real.log u / k) 1

theorem artinComplexNormSectionRoot_pow (n : ℕ) {k : ℕ} (hk : 0 < k) (u : ℝ) :
    artinComplexNormSectionRoot n k u ^ k = artinComplexNormSection n u := by
  rw [artinComplexNormSectionRoot, artinComplexNormPoint_radial_pow,
    artinComplexNormSection]
  congr 1
  have h : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  field_simp

theorem artinComplexNormSection_sixth_power (n : ℕ) (u : ℝ) :
    artinComplexNormPoint n (Real.log u / 6) 1 ^ 6 = artinComplexNormSection n u := by
  exact artinComplexNormSectionRoot_pow n (by norm_num : 0 < (6 : ℕ)) u

theorem artinComplexNormSection_one (n : ℕ) : artinComplexNormSection n 1 = 1 := by
  simpa only [artinComplexNormSection, Real.log_one] using
    artinComplexNormPoint_zero_one n

theorem artinComplexUnitAngle_mul (z v : ℂˣ) :
    artinComplexUnitAngle (z * v) = artinComplexUnitAngle z * artinComplexUnitAngle v := by
  exact congrArg Prod.snd (artinComplexPlaceCoordinates.symm.map_mul z v)

theorem artinComplexNormSection_angle (n : ℕ) (u : ℝ) (i : Fin (n + 1)) :
    artinComplexUnitAngle (artinComplexNormSection n u i) = 1 := by
  exact artinComplexUnitAngle_polar _ _

theorem artinComplexNormSection_angle_mul (n : ℕ) (u : ℝ)
    (z : Fin (n + 1) → ℂˣ) :
    (fun i => artinComplexUnitAngle ((artinComplexNormSection n u * z) i)) =
      fun i => artinComplexUnitAngle (z i) := by
  funext i
  rw [Pi.mul_apply, artinComplexUnitAngle_mul, artinComplexNormSection_angle, one_mul]

theorem artinComplexNormSection_angular_factor (n : ℕ) (u : ℝ)
    (z : Fin (n + 1) → ℂˣ) {Y : Type*} (a : (Fin (n + 1) → Circle) → Y) :
    a (fun i => artinComplexUnitAngle ((artinComplexNormSection n u * z) i)) =
      a (fun i => artinComplexUnitAngle (z i)) := by
  rw [artinComplexNormSection_angle_mul]

variable {G H : Type*} [Monoid G] [Monoid H]

/-- A full finite/complex section leaves the finite coordinate at one. -/
def artinFiniteComplexNormSection (n : ℕ) (u : ℝ) : G × (Fin (n + 1) → ℂˣ) :=
  (1, artinComplexNormSection n u)

theorem artinFiniteComplexNormSectionRoot_pow (n : ℕ) {k : ℕ} (hk : 0 < k) (u : ℝ) :
    ((1, artinComplexNormSectionRoot n k u) : G × (Fin (n + 1) → ℂˣ)) ^ k =
      artinFiniteComplexNormSection n u := by
  apply Prod.ext
  · simp [artinFiniteComplexNormSection]
  · exact artinComplexNormSectionRoot_pow n hk u

/-- No finiteness assumption on the target is needed for section invariance.
The exponent condition, and agreement with a manuscript quotient, are explicit. -/
theorem artinFiniteComplexNormSection_class_one (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1) (u : ℝ) :
    χ (artinFiniteComplexNormSection n u) = 1 := by
  rw [← artinFiniteComplexNormSectionRoot_pow (G := G) n hk u, map_pow, he]

theorem artinFiniteComplexNormSection_class_mul (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1) (u : ℝ)
    (z : G × (Fin (n + 1) → ℂˣ)) :
    χ (artinFiniteComplexNormSection n u * z) = χ z := by
  rw [map_mul, artinFiniteComplexNormSection_class_one n hk χ he u, one_mul]

theorem artinFiniteComplexNormSection_class_factor (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1) (u : ℝ)
    (z : G × (Fin (n + 1) → ℂˣ)) {Y : Type*} (b : H → Y) :
    b (χ (artinFiniteComplexNormSection n u * z)) = b (χ z) := by
  rw [artinFiniteComplexNormSection_class_mul n hk χ he u z]

theorem artinFiniteComplexNormSection_sixth_class_factor (n : ℕ)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ 6 = 1) (u : ℝ)
    (z : G × (Fin (n + 1) → ℂˣ)) {Y : Type*} (b : H → Y) :
    b (χ (artinFiniteComplexNormSection n u * z)) = b (χ z) :=
  artinFiniteComplexNormSection_class_factor n (by norm_num : 0 < (6 : ℕ)) χ he u z b

end
end SimultaneousPrimitiveRoots
