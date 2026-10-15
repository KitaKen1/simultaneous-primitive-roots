module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Int.GCD

/-!
# Power classes and the Chinese remainder decomposition for exponent six

The group-theoretic part of [A, `lem:balanced-generators`, A-02:0203–0207]:
for every commutative group `G`, `G/G⁶ ≃* G/G² × G/G³`. The isomorphism sends the
class of `a` to its square and cube classes. It is natural in group homomorphisms,
so the image of a subgroup in the sixth-power classes becomes the product of its
images in the square and cube classes. No local-field or finiteness assumption
is needed here.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

variable (G : Type*) [CommGroup G]

/-- The subgroup of `n`th powers. -/
def powerSubgroup (n : ℕ) : Subgroup G := (powMonoidHom n : G →* G).range

/-- The group of `n`th power classes. -/
abbrev PowerClass (n : ℕ) := G ⧸ powerSubgroup G n

/-- The canonical power-class map. -/
def powerClassMk (n : ℕ) : G →* PowerClass G n := QuotientGroup.mk' _

@[simp]
theorem mem_powerSubgroup {n : ℕ} {a : G} :
    a ∈ powerSubgroup G n ↔ ∃ b : G, b ^ n = a := Iff.rfl

theorem powerClassMk_surjective (n : ℕ) : Function.Surjective (powerClassMk G n) :=
  QuotientGroup.mk'_surjective _

@[simp]
theorem powerClassMk_eq_one_iff (n : ℕ) (a : G) :
    powerClassMk G n a = 1 ↔ ∃ b : G, b ^ n = a :=
  (QuotientGroup.eq_one_iff a).trans (mem_powerSubgroup G)

theorem powerClass_pow_eq_one (n : ℕ) (a : PowerClass G n) : a ^ n = 1 := by
  obtain ⟨b, rfl⟩ := powerClassMk_surjective G n a
  rw [← map_pow, powerClassMk_eq_one_iff]
  exact ⟨b, rfl⟩

/-- Reduce `(n*k)`th power classes to `n`th power classes. -/
def powerClassReduce (n k : ℕ) : PowerClass G (n * k) →* PowerClass G n :=
  QuotientGroup.map _ _ (MonoidHom.id G) (by
    rintro _ ⟨a, rfl⟩
    exact ⟨a ^ k, by simp [powMonoidHom_apply, ← pow_mul, mul_comm]⟩)

@[simp]
theorem powerClassReduce_mk (n k : ℕ) (a : G) :
    powerClassReduce G n k (powerClassMk G (n * k) a) = powerClassMk G n a := rfl

/-- The map from sixth-power classes to square and cube classes. -/
def sexticClassMap : PowerClass G 6 →* PowerClass G 2 × PowerClass G 3 :=
  (powerClassReduce G 2 3).prod (powerClassReduce G 3 2)

@[simp]
theorem sexticClassMap_mk (a : G) :
    sexticClassMap G (powerClassMk G 6 a) = (powerClassMk G 2 a, powerClassMk G 3 a) := rfl

theorem sexticClassMap_injective : Function.Injective (sexticClassMap G) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨a, rfl⟩ := powerClassMk_surjective G 6 x
  have h := MonoidHom.mem_ker.mp hx
  obtain ⟨b, hb⟩ := (powerClassMk_eq_one_iff G 2 a).mp (congrArg Prod.fst h)
  obtain ⟨c, hc⟩ := (powerClassMk_eq_one_iff G 3 a).mp (congrArg Prod.snd h)
  change powerClassMk G 6 a = 1
  rw [powerClassMk_eq_one_iff]
  refine ⟨b / c, ?_⟩
  calc
    (b / c) ^ 6 = (b ^ 2) ^ 3 / (c ^ 3) ^ 2 := by simp [div_pow, ← pow_mul]
    _ = a ^ 3 / a ^ 2 := by rw [hb, hc]
    _ = a := by simp [pow_succ]

theorem sexticClassMap_surjective : Function.Surjective (sexticClassMap G) := by
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := powerClassMk_surjective G 2 x
  obtain ⟨b, rfl⟩ := powerClassMk_surjective G 3 y
  refine ⟨powerClassMk G 6 (a ^ 3 * b ^ 4), ?_⟩
  rw [sexticClassMap_mk]
  apply Prod.ext
  · simp only [map_mul, map_pow]
    have ha := powerClass_pow_eq_one G 2 (powerClassMk G 2 a)
    have hb := powerClass_pow_eq_one G 2 (powerClassMk G 2 b)
    rw [show (powerClassMk G 2 a) ^ 3 = (powerClassMk G 2 a) ^ 2 * powerClassMk G 2 a
      from pow_succ _ 2, show (powerClassMk G 2 b) ^ 4 = ((powerClassMk G 2 b) ^ 2) ^ 2
      from pow_mul _ 2 2, ha, hb]
    simp
  · simp only [map_mul, map_pow]
    have ha := powerClass_pow_eq_one G 3 (powerClassMk G 3 a)
    have hb := powerClass_pow_eq_one G 3 (powerClassMk G 3 b)
    rw [pow_succ _ 3, ha, hb]
    simp

/-- **Chinese remainder for power classes**, with the canonical reduction maps. -/
def sexticClassEquiv : PowerClass G 6 ≃* PowerClass G 2 × PowerClass G 3 :=
  MulEquiv.ofBijective (sexticClassMap G)
    ⟨sexticClassMap_injective G, sexticClassMap_surjective G⟩

@[simp]
theorem sexticClassEquiv_mk (a : G) :
    sexticClassEquiv G (powerClassMk G 6 a) = (powerClassMk G 2 a, powerClassMk G 3 a) := rfl

variable {G} {U : Type*} [CommGroup U]

/-- A homomorphism induces a homomorphism on power classes. -/
def powerClassMap (f : U →* G) (n : ℕ) : PowerClass U n →* PowerClass G n :=
  QuotientGroup.map _ _ f (by
    rintro _ ⟨a, rfl⟩
    exact ⟨f a, by simp [powMonoidHom_apply, map_pow]⟩)

@[simp]
theorem powerClassMap_mk (f : U →* G) (n : ℕ) (a : U) :
    powerClassMap f n (powerClassMk U n a) = powerClassMk G n (f a) := rfl

/-- The image on power classes is also the image of the original group under the class map. -/
theorem powerClassMap_range (f : U →* G) (n : ℕ) :
    (powerClassMap f n).range = ((powerClassMk G n).comp f).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨u, rfl⟩ := powerClassMk_surjective U n a
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨powerClassMk U n u, rfl⟩

/-- The CRT decomposition commutes with homomorphisms, including the inclusion of S-units. -/
theorem sexticClassEquiv_natural (f : U →* G) (a : PowerClass U 6) :
    sexticClassEquiv G (powerClassMap f 6 a) =
      (powerClassMap f 2 (sexticClassEquiv U a).1,
        powerClassMap f 3 (sexticClassEquiv U a).2) := by
  obtain ⟨u, rfl⟩ := powerClassMk_surjective U 6 a
  rfl

/-- Injectivity of the unit map on square and cube classes gives injectivity on sixth classes. -/
theorem powerClassMap_injective_six (f : U →* G)
    (h₂ : Function.Injective (powerClassMap f 2))
    (h₃ : Function.Injective (powerClassMap f 3)) :
    Function.Injective (powerClassMap f 6) := by
  intro x y h
  apply (sexticClassEquiv U).injective
  have hc := congrArg (sexticClassEquiv G) h
  rw [sexticClassEquiv_natural, sexticClassEquiv_natural] at hc
  exact Prod.ext (h₂ (congrArg Prod.fst hc)) (h₃ (congrArg Prod.snd hc))

/-- **The sixth-power image decomposes as the product of the square and cube images.** -/
theorem sexticClassEquiv_map_range (f : U →* G) :
    (powerClassMap f 6).range.map (sexticClassEquiv G).toMonoidHom =
      (powerClassMap f 2).range.prod (powerClassMap f 3).range := by
  ext x
  constructor
  · rintro ⟨a, ⟨u, rfl⟩, rfl⟩
    change sexticClassEquiv G (powerClassMap f 6 u) ∈ _
    rw [sexticClassEquiv_natural]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨u2, hu2⟩, ⟨u3, hu3⟩⟩
    obtain ⟨u, hu⟩ := (sexticClassEquiv U).surjective (u2, u3)
    refine ⟨powerClassMap f 6 u, ⟨u, rfl⟩, ?_⟩
    change sexticClassEquiv G (powerClassMap f 6 u) = x
    rw [sexticClassEquiv_natural, hu]
    exact Prod.ext hu2 hu3

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
