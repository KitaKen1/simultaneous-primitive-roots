import SimultaneousPrimitiveRootsFinal.SUnitHilbertIsotropy
import SimultaneousPrimitiveRootsFinal.HilbertGivenProducts

/-!
# Coherent complements of the actual S-unit image

Global isotropy is supplied by the product formula, local finiteness by CFT,
and alternation by a global primitive root of order `2n`. The only remaining
arithmetic hypothesis here is the squared-cardinality formula for the image.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory Arithmetic NumberField IsDedekindDomain
open scoped NumberField

/-- **The actual S-unit image has a coherent isotropic complement once its size is known.** -/
theorem exists_sUnit_prime_hilbert_compl_of_card
    (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+) [Fact (n : ℕ).Prime]
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (hmu2 : (primitiveRoots (2 * (n : ℕ)) F).Nonempty)
    (hS : ∀ v ∉ S, v.valuation F ((n : ℕ) : F) = 1)
    (hcard : Nat.card (sUnitPowerLocalization F S n).range ^ 2 =
      Nat.card (∀ v : S, PowerClassGroup (v.1.adicCompletion F) n)) :
    ∃ B : GlobalHilbertPairingFamily F n,
      IsCoherentHilbertFamily F n hmu B ∧
      (∀ x ∈ (sUnitPowerLocalization F S n).range,
        ∀ y ∈ (sUnitPowerLocalization F S n).range,
          piPairing (fun v : S => finitePlaceGlobalRootPairing F n hmu B v) x y = 1) ∧
      (∀ x, (∀ y ∈ (sUnitPowerLocalization F S n).range,
        piPairing (fun v : S => finitePlaceGlobalRootPairing F n hmu B v) x y = 1) →
        x ∈ (sUnitPowerLocalization F S n).range) ∧
      ∃ C : Subgroup (∀ v : S, PowerClassGroup (v.1.adicCompletion F) n),
        IsCompl (sUnitPowerLocalization F S n).range C ∧
        ∀ x ∈ C, ∀ y ∈ C,
          piPairing (fun v : S => finitePlaceGlobalRootPairing F n hmu B v) x y = 1 := by
  classical
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let K : S → Type := fun v => v.1.adicCompletion F
  let : ∀ v, ValuativeRel (K v) := fun v => finitePlaceCompletionValuativeRel F v.1
  let : ∀ v, IsNonarchimedeanLocalField (K v) := fun v =>
    finitePlaceCompletionIsNonarchimedeanLocalField F v.1
  let : ∀ v, CharZero (K v) := fun v =>
    charZero_of_injective_algebraMap (algebraMap F (K v)).injective
  let : ∀ v, Finite (PowerClassGroup (K v) n) := fun v =>
    powerClassGroup_finite (K v) n (Nat.cast_ne_zero.mpr n.ne_zero)
  obtain ⟨B, hcoherent, hE⟩ := exists_sUnit_hilbert_isotropic F S n hmu hS
  obtain ⟨u, hu⟩ := minus_one_is_power_of_double_roots n hmu2
  have hminus : ∀ v : S, ∃ w : (K v)ˣ, w ^ (n : ℕ) = -1 := by
    intro v
    refine ⟨Units.map (algebraMap F (K v)).toMonoidHom u, ?_⟩
    rw [← map_pow, hu]
    apply Units.ext
    simp
  let e : ∀ v : S, rootsOfUnity (n : ℕ) (K v) ≃* rootsOfUnity (n : ℕ) F := fun v =>
    (rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (K v)).injective hmu).symm
  obtain ⟨hself, C, hC, hCI⟩ := exists_given_hilbert_product_compl K n
    (fun v => B v.1) (fun v => hcoherent.1 v.1) (Or.inr hminus) e
    (rootsOfUnityZModEquiv (K := F) n hmu)
    (fun v => finitePlaceGlobalRootPairing F n hmu B v.1) (fun _ _ _ => rfl) hE hcard
  exact ⟨B, hcoherent, hE, hself, C, hC, hCI⟩

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
