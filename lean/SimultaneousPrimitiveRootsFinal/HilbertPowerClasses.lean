import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PairingComplement
import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PowerClasses
import ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing

/-!
# ClassFieldTheory power classes and the isotropic-complement construction

The two quotient definitions are identical. We use this identification to reuse
ClassFieldTheory's power-class definitions. Actual local finiteness and perfect
Hilbert pairings are reused in `LocalHilbertProducts.lean`.

Skew-symmetry implies alternation for odd exponent. For even exponent we use the
Steinberg relation and the fact that -1 is a power (in particular, a square when
the field contains a fourth root of unity). The Steinberg calculation below
adapts the argument of ClassFieldTheory's `localHilbertSymbol_neg_self`
(Naganori Yamaguchi, Apache-2.0) to every pairing satisfying that relation.

The S-unit image's isotropy, cardinality and injectivity, and the normalization
compatibility between exponents 2, 3 and 6, remain separate inputs.
This is a non-module file because ClassFieldTheory is a non-module library.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory Arithmetic

variable {K : Type*} [Field K]

/-- Our quotient and ClassFieldTheory's quotient are the same power-class group. -/
def powerClassEquiv (K : Type*) [Field K] (n : ℕ+) :
    PowerClass Kˣ (n : ℕ) ≃* PowerClassGroup K n := MulEquiv.refl _

@[simp]
theorem powerClassEquiv_mk (n : ℕ+) (a : Kˣ) :
    powerClassEquiv K n (powerClassMk Kˣ (n : ℕ) a) = powerClass K n a := rfl

/-- Exponent six decomposes canonically on ClassFieldTheory's actual quotients. -/
def sexticPowerClassEquiv (K : Type*) [Field K] :
    PowerClassGroup K 6 ≃* PowerClassGroup K 2 × PowerClassGroup K 3 :=
  sexticClassEquiv Kˣ

@[simp]
theorem sexticPowerClassEquiv_mk (a : Kˣ) :
    sexticPowerClassEquiv K (powerClass K 6 a) =
      (powerClass K 2 a, powerClass K 3 a) := rfl

/-- A primitive root identifies the value group with the cyclic group of order `n`. -/
def rootsOfUnityZModEquiv (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    rootsOfUnity (n : ℕ) K ≃* Multiplicative (ZMod (n : ℕ)) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  apply mulEquivOfCyclicCardEq
  obtain ⟨ζ, hζ⟩ := hmu
  rw [((mem_primitiveRoots n.pos).mp hζ).card_rootsOfUnity]
  simp [Nat.card_eq_fintype_card]

/-- The Hilbert symbol on representatives, bundled as two homomorphisms. -/
def hilbertSymbolHom {n : ℕ+} (B : HilbertPairing K n) :
    Kˣ →* Kˣ →* rootsOfUnity (n : ℕ) K where
  toFun a := (B (powerClass K n a)).comp (powerClass K n)
  map_one' := by ext b; simp
  map_mul' a b := by ext c; simp [MonoidHom.mul_apply]

@[simp]
theorem hilbertSymbolHom_apply {n : ℕ+} (B : HilbertPairing K n) (a b : Kˣ) :
    hilbertSymbolHom B a b = B.symbol a b := rfl

/-- The Steinberg relation implies that the symbol of `a` and `-a` is one. -/
theorem hilbertPairing_symbol_neg_self {n : ℕ+} (B : HilbertPairing K n)
    (hB : B.IsSteinberg) (a : Kˣ) : B.symbol a (-a) = 1 := by
  let H := hilbertSymbolHom B
  change H a (-a) = 1
  by_cases ha : a = 1
  · subst a
    simp
  · have hav : (a : K) ≠ 1 := fun h => ha (Units.ext h)
    have hc0 : 1 - (a : K) ≠ 0 := fun h => hav (sub_eq_zero.mp h).symm
    have hd0 : 1 - ((a⁻¹ : Kˣ) : K) ≠ 0 := by
      intro h
      apply inv_ne_one.mpr hav
      simpa only [Units.val_inv_eq_inv_val] using (sub_eq_zero.mp h).symm
    let c := Units.mk0 (1 - (a : K)) hc0
    let d := Units.mk0 (1 - ((a⁻¹ : Kˣ) : K)) hd0
    have hd : d = (-c) * a⁻¹ := by
      apply Units.ext
      simp only [d, c, Units.val_mk0, Units.val_mul, Units.val_neg,
        Units.val_inv_eq_inv_val]
      calc
        1 - (a : K)⁻¹ = ((a : K) - 1) * (a : K)⁻¹ := by
          rw [sub_mul, mul_inv_cancel₀ (Units.ne_zero a), one_mul]
        _ = -(1 - (a : K)) * (a : K)⁻¹ := by ring
    have hs1 : H a c = 1 := hB a hc0
    have hs2 : H a⁻¹ d = 1 := hB a⁻¹ hd0
    have hs2' : H a d = 1 := by
      rw [map_inv, MonoidHom.inv_apply] at hs2
      exact inv_eq_one.mp hs2
    have hdiag : H a (-c) = H a a := by
      rw [hd, map_mul, map_inv] at hs2'
      exact mul_inv_eq_one.mp hs2'
    have hc : c = (-1 : Kˣ) * (-c) := by simp
    have hneg : H a (-1) * H a a = 1 := by
      rw [hc, map_mul, hdiag] at hs1
      exact hs1
    rw [show -a = (-1 : Kˣ) * a by simp, map_mul]
    exact hneg

/-- Odd-exponent skew pairings are alternating, including the cubic local pairing. -/
theorem hilbertPairing_isAlt_of_odd {n : ℕ+} (B : HilbertPairing K n)
    (hB : B.IsSkewSymmetric) (hn : Odd (n : ℕ)) : ∀ x, B x x = 1 := by
  intro x
  have h2 : B x x ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp (hB x x)
  have hn' : B x x ^ (n : ℕ) = 1 := by
    apply Subtype.ext
    exact (B x x).property
  exact (pow_eq_one_iff_of_coprime hn.coprime_two_left).mp ⟨h2, hn'⟩

/-- If `-1` is an `n`th power, the Steinberg relation makes the pairing alternating. -/
theorem hilbertPairing_isAlt_of_minus_one_is_power {n : ℕ+} (B : HilbertPairing K n)
    (hB : B.IsSteinberg) (hminus : ∃ u : Kˣ, u ^ (n : ℕ) = -1) :
    ∀ x, B x x = 1 := by
  obtain ⟨u, hu⟩ := hminus
  have hminus' : powerClass K n (-1) = 1 := by
    change powerClassMk Kˣ (n : ℕ) (-1) = 1
    exact (powerClassMk_eq_one_iff Kˣ (n : ℕ) (-1)).mpr ⟨u, hu⟩
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range x
  change B (powerClass K n a) (powerClass K n a) = 1
  have h := hilbertPairing_symbol_neg_self B hB a
  simpa only [HilbertPairing.symbol, show -a = (-1 : Kˣ) * a by simp,
    map_mul, hminus', map_one, one_mul] using h

/-- The prime-exponent complement theorem applies directly to CFT's Hilbert pairing. -/
theorem exists_hilbert_isotropic_compl {n : ℕ+} [Fact (n : ℕ).Prime]
    [Finite (PowerClassGroup K n)] (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (B : HilbertPairing K n) (hnd : B.IsNondegenerate) (halt : ∀ x, B x x = 1)
    {E : Subgroup (PowerClassGroup K n)}
    (hE : ∀ x ∈ E, ∀ y ∈ E, B x y = 1)
    (hcard : Nat.card E ^ 2 = Nat.card (PowerClassGroup K n)) :
    (∀ x, (∀ y ∈ E, B x y = 1) → x ∈ E) ∧
      ∃ C : Subgroup (PowerClassGroup K n), IsCompl E C ∧
        ∀ x ∈ C, ∀ y ∈ C, B x y = 1 := by
  have hV : ∀ x : PowerClassGroup K n, x ^ (n : ℕ) = 1 := by
    change ∀ x : PowerClass Kˣ (n : ℕ), x ^ (n : ℕ) = 1
    exact powerClass_pow_eq_one Kˣ (n : ℕ)
  exact exists_isotropic_compl (V := PowerClassGroup K n) hV
    (rootsOfUnityZModEquiv n hmu) B hnd.1 halt hE hcard

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
