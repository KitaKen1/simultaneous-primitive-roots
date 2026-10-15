import SimultaneousPrimitiveRootsFinal.HilbertPowerClasses
import ClassFieldTheory.Theorems.HilbertSymbols.LocalHilbertPairingPerfectExists
import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PowerClassProducts
import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PairingProducts

/-!
# Actual local Hilbert pairings over a finite set of places

Local-field finiteness, existence and nondegeneracy are obtained from CFT.
The roots-of-unity identifications are explicit: using arbitrary unrelated
identifications does not establish the global product formula for S-units.
The S-unit image's isotropy and cardinality remain inputs of the final theorem.
There is no claim of normalized compatibility between exponents 2, 3 and 6.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory Arithmetic

variable {K : Type*} [Field K]

/-- A primitive `2n`th root makes `-1` an `n`th power of a unit. -/
theorem minus_one_is_power_of_double_roots (n : ℕ+)
    (hmu : (primitiveRoots (2 * (n : ℕ)) K).Nonempty) :
    ∃ u : Kˣ, u ^ (n : ℕ) = -1 := by
  obtain ⟨ζ, hζ⟩ := hmu
  have hpos : 0 < 2 * (n : ℕ) := Nat.mul_pos (by decide) n.pos
  have hz : IsPrimitiveRoot ζ (2 * (n : ℕ)) := (mem_primitiveRoots hpos).mp hζ
  have h2 : IsPrimitiveRoot (ζ ^ (n : ℕ)) 2 :=
    IsPrimitiveRoot.pow hpos hz (Nat.mul_comm 2 (n : ℕ))
  refine ⟨Units.mk0 ζ (hz.ne_zero hpos.ne'), ?_⟩
  apply Units.ext
  simpa using h2.eq_neg_one_of_two_right

/-- Containing primitive roots of order `m` supplies primitive roots of any positive divisor. -/
theorem primitiveRoots_nonempty_of_dvd {m : ℕ} (n : ℕ+) (hm : 0 < m)
    (hn : (n : ℕ) ∣ m) (hmu : (primitiveRoots m K).Nonempty) :
    (primitiveRoots (n : ℕ) K).Nonempty := by
  obtain ⟨ζ, hζ⟩ := hmu
  refine ⟨ζ ^ (m / (n : ℕ)), (mem_primitiveRoots n.pos).mpr ?_⟩
  exact IsPrimitiveRoot.pow hm ((mem_primitiveRoots hm).mp hζ)
    (Nat.div_mul_cancel hn).symm

/-- Transfer a local Hilbert pairing to a specified common root-of-unity group. -/
def commonRootPairing {n : ℕ+} {μ : Type*} [CommGroup μ]
    (e : rootsOfUnity (n : ℕ) K ≃* μ) (B : HilbertPairing K n) :
    PowerClassGroup K n →* PowerClassGroup K n →* μ where
  toFun x := e.toMonoidHom.comp (B x)
  map_one' := by ext y; simp
  map_mul' x y := by ext z; simp [MonoidHom.mul_apply]

@[simp]
theorem commonRootPairing_apply {n : ℕ+} {μ : Type*} [CommGroup μ]
    (e : rootsOfUnity (n : ℕ) K ≃* μ) (B : HilbertPairing K n) (x y) :
    commonRootPairing e B x y = e (B x y) := rfl

theorem commonRootPairing_nondegenerate {n : ℕ+} {μ : Type*} [CommGroup μ]
    (e : rootsOfUnity (n : ℕ) K ≃* μ) (B : HilbertPairing K n)
    (hB : B.IsNondegenerate) :
    ∀ x, (∀ y, commonRootPairing e B x y = 1) → x = 1 := by
  intro x hx
  exact hB.1 x (fun y => e.map_eq_one_iff.mp (hx y))

/-- The local product quotient uses exactly the CFT power-class groups. -/
def localPowerClassPiEquiv {ι : Type*} (K : ι → Type*) [∀ i, Field (K i)] (n : ℕ+) :
    PowerClass (∀ i, (K i)ˣ) (n : ℕ) ≃* ∀ i, PowerClassGroup (K i) n :=
  powerClassPiEquiv (fun i => (K i)ˣ) (n : ℕ)

/-- **A product of actual local Hilbert pairings gives the prime-exponent complement.**
The common-value identifications and the joint subgroup E are supplied explicitly.
Local existence, finiteness, perfectness and alternation are proved, while global
isotropy and the squared-cardinality formula of E remain hypotheses.
-/
theorem exists_local_prime_hilbert_product_complements
    {ι : Type*} [Fintype ι] (K : ι → Type*) [∀ i, Field (K i)]
    [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)]
    [∀ i, IsNonarchimedeanLocalField (K i)]
    (n : ℕ+) [Fact (n : ℕ).Prime]
    (hn : ∀ i, ((n : ℕ) : K i) ≠ 0)
    (hmu : ∀ i, (primitiveRoots (n : ℕ) (K i)).Nonempty)
    (halt : Odd (n : ℕ) ∨ ∀ i, ∃ u : (K i)ˣ, u ^ (n : ℕ) = -1)
    {μ : Type*} [CommGroup μ] (e : ∀ i, rootsOfUnity (n : ℕ) (K i) ≃* μ)
    (eμ : μ ≃* Multiplicative (ZMod (n : ℕ))) :
    ∃ B : ∀ i, HilbertPairing (K i) n,
      (∀ i, (B i).IsLocalHilbertPairing ∧ Function.Bijective (B i)) ∧
      ∀ E : Subgroup (∀ i, PowerClassGroup (K i) n),
        (∀ x ∈ E, ∀ y ∈ E, piPairing (fun i => commonRootPairing (e i) (B i)) x y = 1) →
        Nat.card E ^ 2 = Nat.card (∀ i, PowerClassGroup (K i) n) →
        (∀ x, (∀ y ∈ E, piPairing (fun i => commonRootPairing (e i) (B i)) x y = 1) → x ∈ E) ∧
          ∃ C : Subgroup (∀ i, PowerClassGroup (K i) n), IsCompl E C ∧
            ∀ x ∈ C, ∀ y ∈ C, piPairing (fun i => commonRootPairing (e i) (B i)) x y = 1 := by
  classical
  let : ∀ i, Finite (PowerClassGroup (K i) n) := fun i => powerClassGroup_finite (K i) n (hn i)
  let : ∀ i, Fintype (PowerClassGroup (K i) n) := fun i => Fintype.ofFinite _
  choose B hB hperfect using fun i => exists_perfectLocalHilbertPairing (K i) n (hn i) (hmu i)
  refine ⟨B, fun i => ⟨hB i, hperfect i⟩, fun E hE hcard => ?_⟩
  have hlocalAlt : ∀ i x, B i x x = 1 := by
    intro i
    rcases halt with hodd | hminus
    · exact hilbertPairing_isAlt_of_odd (B i) (hB i).2.1 hodd
    · exact hilbertPairing_isAlt_of_minus_one_is_power (B i) (hB i).1 (hminus i)
  have hV : ∀ i (x : PowerClassGroup (K i) n), x ^ (n : ℕ) = 1 := by
    intro i
    change ∀ x : PowerClass (K i)ˣ (n : ℕ), x ^ (n : ℕ) = 1
    exact powerClass_pow_eq_one (K i)ˣ (n : ℕ)
  exact exists_piPairing_isotropic_compl (V := fun i => PowerClassGroup (K i) n) hV eμ
    (fun i => commonRootPairing (e i) (B i))
    (fun i => commonRootPairing_nondegenerate (e i) (B i) (hB i).2.2.1)
    (fun i x => by simp only [commonRootPairing_apply, hlocalAlt, map_one]) hE hcard

/-- **An actual local perfect pairing at any prime exponent, including two and three.**
The generic exponent avoids duplicating the same construction in numeric specializations.
-/
theorem exists_local_prime_hilbert_complements
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+) [Fact (n : ℕ).Prime]
    (hn : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (halt : Odd (n : ℕ) ∨ ∃ u : Kˣ, u ^ (n : ℕ) = -1) :
    ∃ B : HilbertPairing K n, B.IsLocalHilbertPairing ∧ Function.Bijective B ∧
      ∀ E : Subgroup (PowerClassGroup K n),
        (∀ x ∈ E, ∀ y ∈ E, B x y = 1) →
        Nat.card E ^ 2 = Nat.card (PowerClassGroup K n) →
        (∀ x, (∀ y ∈ E, B x y = 1) → x ∈ E) ∧
          ∃ C : Subgroup (PowerClassGroup K n), IsCompl E C ∧
            ∀ x ∈ C, ∀ y ∈ C, B x y = 1 := by
  let : Finite (PowerClassGroup K n) := powerClassGroup_finite K n hn
  obtain ⟨B, hB, hperfect⟩ := exists_perfectLocalHilbertPairing K n hn hmu
  have hAlt : ∀ x, B x x = 1 := by
    rcases halt with hodd | hminus
    · exact hilbertPairing_isAlt_of_odd B hB.2.1 hodd
    · exact hilbertPairing_isAlt_of_minus_one_is_power B hB.1 hminus
  exact ⟨B, hB, hperfect, fun E hE hcard =>
    exists_hilbert_isotropic_compl (K := K) (n := n) hmu B hB.2.2.1 hAlt hE hcard⟩

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
