module

public import SimultaneousPrimitiveRoots.KummerConjugacy
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

noncomputable section

/-- Complex one-dimensional characters of the actual relative Galois group.
These are finite group characters; no Hecke reciprocity is assumed. -/
abbrev PrimeKummerCharacter (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :=
  Gal(PrimeKummerField a q/CyclotomicField q ℚ) →* ℂˣ

theorem primeKummerGenerator_generates (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) :
    σ ∈ Subgroup.zpowers (primeKummerGenerator a q) := by
  obtain ⟨m, hm, _⟩ := primeKummerGalois_exists_unique_coordinate a q σ
  exact Subgroup.mem_zpowers_iff.mpr ⟨(m.val : ℤ), by simpa using hm⟩

/-- Evaluation at the fixed generator classifies all complex characters. -/
def primeKummerCharacterEvaluation (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    PrimeKummerCharacter a q →* rootsOfUnity q ℂ where
  toFun χ := ⟨χ (primeKummerGenerator a q), by
    have hp : primeKummerGenerator a q ^ q = 1 := by
      simpa only [primeKummerGenerator_order] using pow_orderOf_eq_one (primeKummerGenerator a q)
    rw [mem_rootsOfUnity, ← map_pow, hp, map_one]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem primeKummerCharacter_eq_iff_generator (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) :
    χ = ψ ↔ χ (primeKummerGenerator a q) = ψ (primeKummerGenerator a q) :=
  MonoidHom.eq_iff_eq_on_generator (primeKummerGenerator_generates a q) χ ψ

theorem primeKummerCharacterEvaluation_bijective (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    Function.Bijective (primeKummerCharacterEvaluation a q) := by
  refine ⟨?_, fun ζ => ?_⟩
  · intro χ ψ h
    apply (primeKummerCharacter_eq_iff_generator a q χ ψ).mpr
    have hv := congrArg Subtype.val h
    change χ (primeKummerGenerator a q) = ψ (primeKummerGenerator a q) at hv
    exact hv
  · have horder : orderOf ζ.val ∣ orderOf (primeKummerGenerator a q) := by
      rw [primeKummerGenerator_order]
      exact orderOf_dvd_iff_pow_eq_one.mpr ζ.property
    refine ⟨monoidHomOfForallMemZpowers (primeKummerGenerator_generates a q) horder, ?_⟩
    apply Subtype.ext
    change (monoidHomOfForallMemZpowers (primeKummerGenerator_generates a q) horder)
      (primeKummerGenerator a q) = ζ.val
    exact monoidHomOfForallMemZpowers_apply_gen (primeKummerGenerator_generates a q) horder

def primeKummerCharacterEquiv (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    PrimeKummerCharacter a q ≃* rootsOfUnity q ℂ :=
  MulEquiv.ofBijective (primeKummerCharacterEvaluation a q)
    (primeKummerCharacterEvaluation_bijective a q)

theorem primeKummerCharacter_card (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] :
    Nat.card (PrimeKummerCharacter a q) = q := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  rw [Nat.card_congr (primeKummerCharacterEquiv a q).toEquiv,
    Complex.card_rootsOfUnity]

instance primeKummerCharacter_finite (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] :
    Finite (PrimeKummerCharacter a q) :=
  Nat.finite_of_card_ne_zero (by rw [primeKummerCharacter_card]; exact hq.out.ne_zero)

instance primeKummerCharacter_fintype (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    Fintype (PrimeKummerCharacter a q) := Fintype.ofFinite _

theorem primeKummer_nonprincipal_character_card (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] :
    Nat.card {χ : PrimeKummerCharacter a q // χ ≠ 1} = q - 1 := by
  classical
  let : Finite (PrimeKummerCharacter a q) :=
    Nat.finite_of_card_ne_zero (by rw [primeKummerCharacter_card]; exact hq.out.ne_zero)
  let := Fintype.ofFinite (PrimeKummerCharacter a q)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun χ => χ = 1)]
  rw [Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, primeKummerCharacter_card]

theorem primeKummer_nonprincipal_character_order (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) : orderOf χ = q := by
  have hgen : ∀ ψ : PrimeKummerCharacter a q, ψ ∈ Subgroup.zpowers χ :=
    fun _ => mem_zpowers_of_prime_card (primeKummerCharacter_card a q) hχ
  rw [orderOf_eq_card_of_forall_mem_zpowers hgen, primeKummerCharacter_card]

/-- Every nonprincipal character is a nonzero power of any fixed
nonprincipal character, with exponent strictly smaller than q. -/
theorem primeKummer_nonprincipal_character_power (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ m : Fin q, m.val ≠ 0 ∧ χ ^ m.val = ψ := by
  classical
  have horder := primeKummer_nonprincipal_character_order a q χ hχ
  have hfinite : IsOfFinOrder χ := by
    rw [← orderOf_pos_iff, horder]
    exact hq.out.pos
  have hmem := (hfinite.mem_zpowers_iff_mem_range_orderOf).mp
    (mem_zpowers_of_prime_card (primeKummerCharacter_card a q) hχ (g' := ψ))
  obtain ⟨m, hm, hpow⟩ := Finset.mem_image.mp hmem
  have hmq : m < q := by simpa only [Finset.mem_range, horder] using hm
  refine ⟨⟨m, hmq⟩, ?_, hpow⟩
  intro hm0
  change m = 0 at hm0
  apply hψ
  rw [← hpow, hm0, pow_zero]

end
end SimultaneousPrimitiveRoots
