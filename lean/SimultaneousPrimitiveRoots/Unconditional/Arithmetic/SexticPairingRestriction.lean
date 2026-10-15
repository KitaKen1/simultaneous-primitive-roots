module

public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.SexticComplement
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Prime components of one sextic pairing

Restrict the same sextic pairing along the CRT inclusions. Mixed quadratic/cubic
terms vanish because their orders divide both 2 and 3. This avoids choosing
unrelated normalizations of the two prime pairings. The cubic component is
squared so that the value projections are exactly the third and second powers.
-/

@[expose] public section
noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

variable {V V₂ V₃ : Type*} [CommGroup V] [CommGroup V₂] [CommGroup V₃]
variable {F : Type*} [Field F]

/-- Pull a bimultiplicative pairing back along a homomorphism. -/
def pairingPullback {W μ : Type*} [CommGroup W] [CommGroup μ]
    (H : V →* V →* μ) (f : W →* V) : W →* W →* μ where
  toFun x := (H (f x)).comp f
  map_one' := by ext y; simp
  map_mul' x y := by ext z; simp [MonoidHom.mul_apply]

@[simp] theorem pairingPullback_apply {W μ : Type*} [CommGroup W] [CommGroup μ]
    (H : V →* V →* μ) (f : W →* V) (x y : W) :
    pairingPullback H f x y = H (f x) (f y) := rfl

/-- Raising a sixth root to the third power gives a square root of one. -/
def sexticRootSquare : rootsOfUnity 6 F →* rootsOfUnity 2 F where
  toFun z := ⟨z.1 ^ 3, by
    change (z.1 ^ 3) ^ 2 = 1
    have hz : z.1 ^ 6 = 1 := z.2
    simpa only [← pow_mul] using hz⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_pow]

/-- Raising a sixth root to the second power gives a cube root of one. -/
def sexticRootCube : rootsOfUnity 6 F →* rootsOfUnity 3 F where
  toFun z := ⟨z.1 ^ 2, by
    change (z.1 ^ 2) ^ 3 = 1
    have hz : z.1 ^ 6 = 1 := z.2
    simpa only [← pow_mul] using hz⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_pow]

def quadraticCrtInclusion (e : V ≃* V₂ × V₃) : V₂ →* V :=
  e.symm.toMonoidHom.comp (MonoidHom.inl V₂ V₃)

def cubicCrtInclusion (e : V ≃* V₂ × V₃) : V₃ →* V :=
  e.symm.toMonoidHom.comp (MonoidHom.inr V₂ V₃)

/-- The quadratic component of the chosen sextic pairing. -/
def sexticQuadraticPairing (e : V ≃* V₂ × V₃)
    (H : V →* V →* rootsOfUnity 6 F) : V₂ →* V₂ →* rootsOfUnity 2 F where
  toFun x := sexticRootSquare.comp (pairingPullback H (quadraticCrtInclusion e) x)
  map_one' := by ext y; simp
  map_mul' x y := by ext z; simp [MonoidHom.mul_apply]

/-- The cubic component of the same sextic pairing, with the power-two normalization. -/
def sexticCubicPairing (e : V ≃* V₂ × V₃)
    (H : V →* V →* rootsOfUnity 6 F) : V₃ →* V₃ →* rootsOfUnity 3 F where
  toFun x := sexticRootCube.comp (pairingPullback H (cubicCrtInclusion e) x)
  map_one' := by ext y; simp
  map_mul' x y := by ext z; simp [MonoidHom.mul_apply]

theorem pairing_mixed_eq_one {μ : Type*} [CommGroup μ]
    (H : V →* V →* μ) {x y : V} (hx : x ^ 2 = 1) (hy : y ^ 3 = 1) :
    H x y = 1 := by
  have h2 : H x y ^ 2 = 1 := by
    rw [← MonoidHom.pow_apply, ← map_pow, hx, map_one, MonoidHom.one_apply]
  have h3 : H x y ^ 3 = 1 := by rw [← map_pow, hy, map_one]
  exact (pow_eq_one_iff_of_coprime (show Nat.Coprime 2 3 by decide)).mp ⟨h2, h3⟩

theorem pairing_mixed_eq_one' {μ : Type*} [CommGroup μ]
    (H : V →* V →* μ) {x y : V} (hx : x ^ 3 = 1) (hy : y ^ 2 = 1) :
    H x y = 1 := by
  have h3 : H x y ^ 3 = 1 := by
    rw [← MonoidHom.pow_apply, ← map_pow, hx, map_one, MonoidHom.one_apply]
  have h2 : H x y ^ 2 = 1 := by rw [← map_pow, hy, map_one]
  exact (pow_eq_one_iff_of_coprime (show Nat.Coprime 2 3 by decide)).mp ⟨h2, h3⟩

theorem crt_pairing_factorization {μ : Type*} [CommGroup μ]
    (e : V ≃* V₂ × V₃) (H : V →* V →* μ)
    (h₂ : ∀ x : V₂, x ^ 2 = 1) (h₃ : ∀ x : V₃, x ^ 3 = 1) (x y : V) :
    H x y =
      H (quadraticCrtInclusion e (e x).1) (quadraticCrtInclusion e (e y).1) *
      H (cubicCrtInclusion e (e x).2) (cubicCrtInclusion e (e y).2) := by
  have hsplit : ∀ z : V, z = quadraticCrtInclusion e (e z).1 *
      cubicCrtInclusion e (e z).2 := by
    intro z
    apply e.injective
    simp [quadraticCrtInclusion, cubicCrtInclusion]
  have hq : ∀ a : V₂, quadraticCrtInclusion e a ^ 2 = 1 := fun a => by
    rw [← map_pow, h₂, map_one]
  have hc : ∀ a : V₃, cubicCrtInclusion e a ^ 3 = 1 := fun a => by
    rw [← map_pow, h₃, map_one]
  calc
    H x y = H (quadraticCrtInclusion e (e x).1 * cubicCrtInclusion e (e x).2)
        (quadraticCrtInclusion e (e y).1 * cubicCrtInclusion e (e y).2) :=
      congrArg₂ (fun a b => H a b) (hsplit x) (hsplit y)
    _ = _ := by
      simp only [map_mul, MonoidHom.mul_apply]
      rw [
        pairing_mixed_eq_one H (hq _) (hc _), pairing_mixed_eq_one' H (hc _) (hq _)]
      simp

theorem sextic_pairing_compatibility
    (e : V ≃* V₂ × V₃) (H : V →* V →* rootsOfUnity 6 F)
    (h₂ : ∀ x : V₂, x ^ 2 = 1) (h₃ : ∀ x : V₃, x ^ 3 = 1) (x y : V) :
    sexticRootSquare (H x y) = sexticQuadraticPairing e H (e x).1 (e y).1 ∧
      sexticRootCube (H x y) = sexticCubicPairing e H (e x).2 (e y).2 := by
  have hq : H (quadraticCrtInclusion e (e x).1)
      (quadraticCrtInclusion e (e y).1) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, h₂, map_one, map_one]
  have hc : H (cubicCrtInclusion e (e x).2)
      (cubicCrtInclusion e (e y).2) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h₃, map_one, map_one]
  constructor
  · apply Subtype.ext
    change (H x y).1 ^ 3 = _
    rw [crt_pairing_factorization e H h₂ h₃, Subgroup.coe_mul, mul_pow]
    have hc' : (H (cubicCrtInclusion e (e x).2)
      (cubicCrtInclusion e (e y).2)).1 ^ 3 = 1 :=
      congrArg (fun z : rootsOfUnity 6 F => z.1) hc
    change _ = (H (quadraticCrtInclusion e (e x).1)
      (quadraticCrtInclusion e (e y).1)).1 ^ 3
    rw [hc', mul_one]
  · apply Subtype.ext
    change (H x y).1 ^ 2 = _
    rw [crt_pairing_factorization e H h₂ h₃, Subgroup.coe_mul, mul_pow]
    have hq' : (H (quadraticCrtInclusion e (e x).1)
      (quadraticCrtInclusion e (e y).1)).1 ^ 2 = 1 :=
      congrArg (fun z : rootsOfUnity 6 F => z.1) hq
    change _ = (H (cubicCrtInclusion e (e x).2)
      (cubicCrtInclusion e (e y).2)).1 ^ 2
    rw [hq', one_mul]

/-- The two components of a nondegenerate sextic pairing are nondegenerate. -/
theorem sextic_component_nondegenerate
    (e : V ≃* V₂ × V₃) (H : V →* V →* rootsOfUnity 6 F)
    (h₂ : ∀ x : V₂, x ^ 2 = 1) (h₃ : ∀ x : V₃, x ^ 3 = 1)
    (hnd : ∀ x, (∀ y, H x y = 1) → x = 1) :
    (∀ x, (∀ y, sexticQuadraticPairing e H x y = 1) → x = 1) ∧
      (∀ x, (∀ y, sexticCubicPairing e H x y = 1) → x = 1) := by
  have hq : ∀ a b : V₂, H (quadraticCrtInclusion e a) (quadraticCrtInclusion e b) ^ 2 = 1 := by
    intro a b
    rw [← map_pow, ← map_pow, h₂, map_one, map_one]
  have hc : ∀ a b : V₃, H (cubicCrtInclusion e a) (cubicCrtInclusion e b) ^ 3 = 1 := by
    intro a b
    rw [← map_pow, ← map_pow, h₃, map_one, map_one]
  constructor
  · intro x hx
    have hz : quadraticCrtInclusion e x = 1 := hnd _ (fun y => by
      rw [crt_pairing_factorization e H h₂ h₃]
      simp only [quadraticCrtInclusion, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, MonoidHom.inl_apply, e.apply_symm_apply, Prod.fst,
        Prod.snd, map_one, MonoidHom.one_apply, mul_one]
      have hp := congrArg Subtype.val (hx (e y).1)
      change (H (quadraticCrtInclusion e x) (quadraticCrtInclusion e (e y).1)).1 ^ 3 = 1 at hp
      apply Subtype.ext
      have h2 := congrArg Subtype.val (hq x (e y).1)
      exact (pow_eq_one_iff_of_coprime (show Nat.Coprime 2 3 by decide)).mp ⟨h2, hp⟩)
    have hz' := congrArg (fun z => (e z).1) hz
    simpa [quadraticCrtInclusion] using hz'
  · intro x hx
    have hz : cubicCrtInclusion e x = 1 := hnd _ (fun y => by
      rw [crt_pairing_factorization e H h₂ h₃]
      simp only [cubicCrtInclusion, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, MonoidHom.inr_apply, e.apply_symm_apply, Prod.fst,
        Prod.snd, map_one, MonoidHom.one_apply, one_mul]
      have hp := congrArg Subtype.val (hx (e y).2)
      change (H (cubicCrtInclusion e x) (cubicCrtInclusion e (e y).2)).1 ^ 2 = 1 at hp
      apply Subtype.ext
      have h3 := congrArg Subtype.val (hc x (e y).2)
      exact (pow_eq_one_iff_of_coprime (show Nat.Coprime 2 3 by decide)).mp ⟨hp, h3⟩)
    have hz' := congrArg (fun z => (e z).2) hz
    simpa [cubicCrtInclusion] using hz'

/-- The two prime components inherit alternation from the same sextic pairing. -/
theorem sextic_component_alternating
    (e : V ≃* V₂ × V₃) (H : V →* V →* rootsOfUnity 6 F)
    (halt : ∀ x, H x x = 1) :
    (∀ x, sexticQuadraticPairing e H x x = 1) ∧
      (∀ x, sexticCubicPairing e H x x = 1) := by
  constructor
  · intro x
    change sexticRootSquare (H _ _) = 1
    rw [halt, map_one]
  · intro x
    change sexticRootCube (H _ _) = 1
    rw [halt, map_one]

/-- The subgroup image is globally coupled; CRT alone supplies its component lifts. -/
theorem sextic_component_isotropic
    (e : V ≃* V₂ × V₃) (H : V →* V →* rootsOfUnity 6 F)
    {E : Subgroup V} {E₂ : Subgroup V₂} {E₃ : Subgroup V₃}
    (hE : E.map e.toMonoidHom = E₂.prod E₃)
    (hiso : ∀ x ∈ E, ∀ y ∈ E, H x y = 1) :
    (∀ x ∈ E₂, ∀ y ∈ E₂, sexticQuadraticPairing e H x y = 1) ∧
      (∀ x ∈ E₃, ∀ y ∈ E₃, sexticCubicPairing e H x y = 1) := by
  have hmem : ∀ x : V, x ∈ E ↔ e x ∈ E₂.prod E₃ := by
    intro x
    rw [← hE]
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm
  constructor
  · intro x hx y hy
    change sexticRootSquare (H _ _) = 1
    rw [hiso _ ((hmem _).mpr (by
      simpa only [quadraticCrtInclusion, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, MonoidHom.inl_apply, e.apply_symm_apply] using
        (show (x, 1) ∈ E₂.prod E₃ from ⟨hx, E₃.one_mem⟩)))
      _ ((hmem _).mpr (by
      simpa only [quadraticCrtInclusion, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, MonoidHom.inl_apply, e.apply_symm_apply] using
        (show (y, 1) ∈ E₂.prod E₃ from ⟨hy, E₃.one_mem⟩))), map_one]
  · intro x hx y hy
    change sexticRootCube (H _ _) = 1
    rw [hiso _ ((hmem _).mpr (by
      simpa only [cubicCrtInclusion, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, MonoidHom.inr_apply, e.apply_symm_apply] using
        (show (1, x) ∈ E₂.prod E₃ from ⟨E₂.one_mem, hx⟩)))
      _ ((hmem _).mpr (by
      simpa only [cubicCrtInclusion, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom, MonoidHom.inr_apply, e.apply_symm_apply] using
        (show (1, y) ∈ E₂.prod E₃ from ⟨E₂.one_mem, hy⟩))), map_one]

/-- Construct the sextic complement from one sextic pairing, with no compatibility input. -/
theorem exists_sextic_compl_of_one_pairing
    [Finite V₂] [Finite V₃]
    (e : V ≃* V₂ × V₃) (H : V →* V →* rootsOfUnity 6 F)
    (h₂ : ∀ x : V₂, x ^ 2 = 1) (h₃ : ∀ x : V₃, x ^ 3 = 1)
    (e₂ : rootsOfUnity 2 F ≃* Multiplicative (ZMod 2))
    (e₃ : rootsOfUnity 3 F ≃* Multiplicative (ZMod 3))
    (hnd : ∀ x, (∀ y, H x y = 1) → x = 1) (halt : ∀ x, H x x = 1)
    {E : Subgroup V} {E₂ : Subgroup V₂} {E₃ : Subgroup V₃}
    (hE : E.map e.toMonoidHom = E₂.prod E₃)
    (hiso : ∀ x ∈ E, ∀ y ∈ E, H x y = 1)
    (hcard₂ : Nat.card E₂ ^ 2 = Nat.card V₂)
    (hcard₃ : Nat.card E₃ ^ 2 = Nat.card V₃) :
    (∀ x, (∀ y ∈ E, H x y = 1) → x ∈ E) ∧
      ∃ B : Subgroup V, IsCompl E B ∧ ∀ x ∈ B, ∀ y ∈ B, H x y = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hnd₂, hnd₃⟩ := sextic_component_nondegenerate e H h₂ h₃ hnd
  obtain ⟨halt₂, halt₃⟩ := sextic_component_alternating e H halt
  obtain ⟨hiso₂, hiso₃⟩ := sextic_component_isotropic e H hE hiso
  obtain ⟨hself₂, B₂, hB₂, hBI₂⟩ :=
    exists_isotropic_compl h₂ e₂ (sexticQuadraticPairing e H) hnd₂ halt₂ hiso₂ hcard₂
  obtain ⟨hself₃, B₃, hB₃, hBI₃⟩ :=
    exists_isotropic_compl h₃ e₃ (sexticCubicPairing e H) hnd₃ halt₃ hiso₃ hcard₃
  let j₂ : rootsOfUnity 2 F →* rootsOfUnity 6 F :=
    Subgroup.inclusion (rootsOfUnity_le_of_dvd (by decide : 2 ∣ 6))
  let j₃ : rootsOfUnity 3 F →* rootsOfUnity 6 F :=
    Subgroup.inclusion (rootsOfUnity_le_of_dvd (by decide : 3 ∣ 6))
  have hj₂ : Function.Injective j₂ := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity 6 F => z.1) h
  have hj₃ : Function.Injective j₃ := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity 6 F => z.1) h
  have hc := sextic_pairing_compatibility e H h₂ h₃
  exact combine_isotropic_complements e H (sexticQuadraticPairing e H)
    (sexticCubicPairing e H) j₂ j₃ hj₂ hj₃
    (fun x y => Subtype.ext (congrArg (fun z : rootsOfUnity 2 F => z.1) (hc x y).1))
    (fun x y => Subtype.ext (congrArg (fun z : rootsOfUnity 3 F => z.1) (hc x y).2))
    hE hself₂ hself₃ hB₂ hB₃ hBI₂ hBI₃

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
