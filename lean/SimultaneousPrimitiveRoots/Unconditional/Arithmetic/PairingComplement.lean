module

public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.Lagrangian
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Isotropic complements for pairings on groups of prime exponent ([A] `lem:balanced-generators`)

[A] (`A-02:0151–0207`) works with `𝒱_ℓ = F_S^× / F_S^{×ℓ}` (`ℓ = 2, 3`), a finite group of
exponent `ℓ`, and the Hilbert pairing `H_S` with values in `μ_ℓ`. It shows that the image `E` of
the `S`-units is isotropic with `|E|² = |𝒱_ℓ|`, and concludes that `E^⊥ = E` and that `E` has an
isotropic complement. This file is that conclusion for any finite commutative group `V` of prime
exponent `ℓ` and any nondegenerate alternating bimultiplicative pairing `H : V → V → μ` into a group
`μ ≃* Multiplicative (ZMod ℓ)` (`exists_isotropic_compl`). The
proof reads `Additive V` as a vector space over `ZMod ℓ` and applies `exists_isotropic_isCompl`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

open Module

variable {ℓ : ℕ} {V μ : Type*} [CommGroup V] [CommGroup μ]

/-- An alternating bimultiplicative pairing is skew. -/
theorem pairing_mul_swap_eq_one (H : V →* V →* μ) (halt : ∀ x, H x x = 1) (x y : V) :
    H x y * H y x = 1 := by
  have h := halt (x * y)
  rw [map_mul H x y, MonoidHom.mul_apply, map_mul (H x), map_mul (H y), halt x, halt y,
    one_mul, mul_one] at h
  exact h

theorem pairing_swap_eq_one_iff (H : V →* V →* μ) (halt : ∀ x, H x x = 1) (x y : V) :
    H y x = 1 ↔ H x y = 1 := by
  have h := pairing_mul_swap_eq_one H halt x y
  constructor
  · intro hyx
    rwa [hyx, mul_one] at h
  · intro hxy
    rwa [hxy, one_mul] at h

section Linear

variable (e : μ ≃* Multiplicative (ZMod ℓ)) (H : V →* V →* μ)

/-- The pairing read additively: `x ↦ (y ↦ log (H x y))`. -/
def pairingAdd : Additive V →+ Additive V →+ ZMod ℓ where
  toFun x := MonoidHom.toAdditiveLeft ((e : μ →* Multiplicative (ZMod ℓ)).comp (H x.toMul))
  map_zero' := by
    ext y
    simp
  map_add' x y := by
    ext z
    simp [toMul_add, map_mul, MonoidHom.mul_apply, toAdd_mul]

theorem pairingAdd_apply (x y : Additive V) :
    pairingAdd e H x y = (e (H x.toMul y.toMul)).toAdd :=
  rfl

theorem pairingAdd_eq_zero_iff (x y : Additive V) :
    pairingAdd e H x y = 0 ↔ H x.toMul y.toMul = 1 := by
  rw [pairingAdd_apply, ← toAdd_one, (Multiplicative.toAdd).injective.eq_iff,
    MulEquiv.map_eq_one_iff]

end Linear

private def addPairingLinear [Fact ℓ.Prime] {W : Type*} [AddCommGroup W] [Module (ZMod ℓ) W]
    (P : W →+ W →+ ZMod ℓ) : LinearMap.BilinForm (ZMod ℓ) W :=
  LinearMap.mk₂ (ZMod ℓ) (fun x y => P x y)
    (fun x y z => by
      simpa only [AddMonoidHom.add_apply] using
        congrArg (fun f : W →+ ZMod ℓ => f z) (P.map_add x y))
    (fun c x y => by
      rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact map_zsmul (P.flip y) (ZMod.cast c) x)
    (fun x y z => (P x).map_add y z)
    (fun c x y => by
      rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact map_zsmul (P x) (ZMod.cast c) y)

private theorem add_exists_isotropic_compl {W : Type*} [AddCommGroup W] [Finite W]
    [hℓ : Fact ℓ.Prime] [Module (ZMod ℓ) W]
    (P : W →+ W →+ ZMod ℓ)
    (hnd : ∀ x, (∀ y, P x y = 0) → x = 0) (halt : ∀ x, P x x = 0)
    {E : AddSubgroup W} (hE : ∀ x ∈ E, ∀ y ∈ E, P x y = 0)
    (hcard : Nat.card E ^ 2 = Nat.card W) :
    (∀ x, (∀ y ∈ E, P x y = 0) → x ∈ E) ∧
      ∃ B : AddSubgroup W, IsCompl E B ∧ ∀ x ∈ B, ∀ y ∈ B, P x y = 0 := by
  classical
  let : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  let : Fintype W := Fintype.ofFinite _
  let bf : LinearMap.BilinForm (ZMod ℓ) W := addPairingLinear P
  have hbf : ∀ x y : W, bf x y = P x y := fun _ _ => rfl
  have halt' : bf.IsAlt := fun x => (hbf x x).trans (halt x)
  have hsep : LinearMap.SeparatingLeft bf := fun x hx =>
    hnd x (fun y => (hbf x y).symm.trans (hx y))
  have hnd' : bf.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft halt'.isRefl).mpr hsep
  let φ : AddSubgroup W ≃o Submodule (ZMod ℓ) W := AddSubgroup.toZModSubmodule ℓ
  let : Fintype (φ E) := Fintype.ofFinite _
  have hφ : ∀ (S : AddSubgroup W) (x : W), x ∈ φ S ↔ x ∈ S := fun _ _ => Iff.rfl
  have hE' : ∀ x ∈ φ E, ∀ y ∈ φ E, bf x y = 0 := fun x hx y hy =>
    (hbf x y).trans (hE x ((hφ E x).mp hx) y ((hφ E y).mp hy))
  have hcardE : Nat.card E = Nat.card (φ E) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hφ E x).symm)
  have hdim : 2 * finrank (ZMod ℓ) (φ E) = finrank (ZMod ℓ) W := by
    have h1 : Nat.card (φ E) = ℓ ^ finrank (ZMod ℓ) (φ E) := by
      rw [Nat.card_eq_fintype_card (α := φ E),
        Module.card_eq_pow_finrank (K := ZMod ℓ), ZMod.card]
    have h2 : Nat.card W = ℓ ^ finrank (ZMod ℓ) W := by
      rw [Nat.card_eq_fintype_card (α := W),
        Module.card_eq_pow_finrank (K := ZMod ℓ), ZMod.card]
    rw [hcardE, h1, h2, ← pow_mul, mul_comm] at hcard
    exact Nat.pow_right_injective hℓ.out.two_le hcard
  refine ⟨fun x hx => ?_, ?_⟩
  · have hmem : x ∈ bf.orthogonal (φ E) := by
      refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun y hy => ?_
      exact halt'.isRefl x y ((hbf x y).trans (hx y ((hφ E y).mp hy)))
    rw [orthogonal_eq_self_of_isotropic hnd' hE' hdim] at hmem
    exact (hφ E x).mp hmem
  · obtain ⟨B, hB, hi⟩ := exists_isotropic_isCompl hnd' halt' hE' hdim
    refine ⟨φ.symm B, ?_, fun x hx y hy => ?_⟩
    · apply φ.isCompl_iff.mpr
      simpa only [OrderIso.apply_symm_apply] using hB
    · have hx' : x ∈ B := by
        have := (hφ (φ.symm B) x).mpr hx
        rwa [OrderIso.apply_symm_apply] at this
      have hy' : y ∈ B := by
        have := (hφ (φ.symm B) y).mpr hy
        rwa [OrderIso.apply_symm_apply] at this
      exact (hbf x y).symm.trans (hi x hx' y hy')

/-- **Self-orthogonality and isotropic complements for a pairing on a group of prime exponent.**
Let `V` be a finite commutative group of prime exponent `ℓ`, and `H : V → V → μ` a nondegenerate
alternating bimultiplicative pairing into `μ ≃* Multiplicative (ZMod ℓ)`. If `E ≤ V` is isotropic
with `|E|² = |V|`, then every element orthogonal to `E` lies in `E`, and `E` has an isotropic
complement. -/
theorem exists_isotropic_compl [hℓ : Fact ℓ.Prime] [Finite V] (hV : ∀ x : V, x ^ ℓ = 1)
    (e : μ ≃* Multiplicative (ZMod ℓ))
    (H : V →* V →* μ) (hnd : ∀ x, (∀ y, H x y = 1) → x = 1) (halt : ∀ x, H x x = 1)
    {E : Subgroup V} (hE : ∀ x ∈ E, ∀ y ∈ E, H x y = 1)
    (hcard : Nat.card E ^ 2 = Nat.card V) :
    (∀ x, (∀ y ∈ E, H x y = 1) → x ∈ E) ∧
      ∃ B : Subgroup V, IsCompl E B ∧ ∀ x ∈ B, ∀ y ∈ B, H x y = 1 := by
  have hsmul : ∀ x : Additive V, ℓ • x = 0 := fun x => by
    change Additive.ofMul (x.toMul ^ ℓ) = Additive.ofMul 1
    rw [hV]
  let : Module (ZMod ℓ) (Additive V) := AddCommGroup.zmodModule hsmul
  have hPnd : ∀ x : Additive V, (∀ y, pairingAdd e H x y = 0) → x = 0 := by
    intro x hx
    have h1 : x.toMul = 1 := hnd _ fun y =>
      (pairingAdd_eq_zero_iff e H x (Additive.ofMul y)).mp (hx _)
    exact congrArg Additive.ofMul h1
  have hPalt : ∀ x : Additive V, pairingAdd e H x x = 0 := fun x =>
    (pairingAdd_eq_zero_iff e H x x).mpr (halt _)
  have hPE : ∀ x ∈ E.toAddSubgroup, ∀ y ∈ E.toAddSubgroup,
      pairingAdd e H x y = 0 := fun x hx y hy =>
    (pairingAdd_eq_zero_iff e H x y).mpr (hE _ hx _ hy)
  have hcard' : Nat.card E.toAddSubgroup ^ 2 = Nat.card (Additive V) := hcard
  obtain ⟨hs, B, hB, hi⟩ := add_exists_isotropic_compl (pairingAdd e H)
    hPnd hPalt hPE hcard'
  refine ⟨fun x hx => hs (Additive.ofMul x) (fun y hy =>
    (pairingAdd_eq_zero_iff e H _ _).mpr (hx y.toMul hy)),
    ⟨Subgroup.toAddSubgroup.symm B, ?_, fun x hx y hy => ?_⟩⟩
  · apply Subgroup.toAddSubgroup.isCompl_iff.mpr
    simpa only [OrderIso.apply_symm_apply] using hB
  · exact (pairingAdd_eq_zero_iff e H (Additive.ofMul x) (Additive.ofMul y)).mp
      (hi _ hx _ hy)

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
