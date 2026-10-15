module

public import SimultaneousPrimitiveRoots.KummerCharacterConjugacy

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Polynomial
open scoped Classical
noncomputable section

/-- Enumerate the complex q-th roots by powers of a primitive root,
using only the bounded exponent interval. -/
def complexRootPowerEquiv (q : ℕ) [NeZero q] : Fin q ≃ rootsOfUnity q ℂ := by
  let hζ := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
  refine Equiv.ofBijective (fun m : Fin q => hζ.toRootsOfUnity ^ m.val) ⟨?_, ?_⟩
  · intro m n h
    apply Fin.ext
    apply hζ.pow_inj m.isLt n.isLt
    simpa using congrArg (fun ξ : rootsOfUnity q ℂ => ((ξ : ℂˣ) : ℂ)) h
  · intro ξ
    have hξ : (((ξ : ℂˣ) : ℂ)) ^ q = 1 := by
      exact (mem_rootsOfUnity' q ξ.val).mp ξ.property
    obtain ⟨m, hm, hpow⟩ := hζ.eq_pow_of_pow_eq_one hξ
    refine ⟨⟨m, hm⟩, ?_⟩
    apply rootsOfUnity.coe_injective
    simpa using hpow

theorem complexRootPowerEquiv_coe (q : ℕ) [NeZero q] (m : Fin q) :
    (((complexRootPowerEquiv q m : rootsOfUnity q ℂ) : ℂˣ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / q) ^ m.val := by
  simp [complexRootPowerEquiv]

/-- The finite product of all root factors, before any Euler product
over prime ideals or any analytic continuation is introduced. -/
theorem complex_rootsOfUnity_polynomial (q : ℕ) [NeZero q]
    [Fintype (rootsOfUnity q ℂ)] :
    ∏ ξ : rootsOfUnity q ℂ, (X - C ((ξ : ℂˣ) : ℂ)) =
      (X : ℂ[X]) ^ q - 1 := by
  classical
  let hζ := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
  rw [← Fintype.prod_equiv (complexRootPowerEquiv q)
    (fun m : Fin q => X - C (Complex.exp (2 * Real.pi * Complex.I / q) ^ m.val))
    (fun ξ : rootsOfUnity q ℂ => X - C ((ξ : ℂˣ) : ℂ))
    (fun m => by rw [complexRootPowerEquiv_coe])]
  rw [Fin.prod_univ_eq_prod_range
    (fun m : ℕ => X - C (Complex.exp (2 * Real.pi * Complex.I / q) ^ m)) q]
  have hpoly := X_pow_sub_C_eq_prod hζ (NeZero.pos q) (one_pow q : (1 : ℂ) ^ q = 1)
  simpa only [mul_one, C_1] using hpoly.symm

theorem primeKummer_character_polynomial_generator (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] :
    ∏ χ : PrimeKummerCharacter a q, (X - C (χ (primeKummerGenerator a q) : ℂ)) =
      (X : ℂ[X]) ^ q - 1 := by
  classical
  let : NeZero q := ⟨hq.out.ne_zero⟩
  let := Fintype.ofFinite (rootsOfUnity q ℂ)
  rw [Fintype.prod_equiv (primeKummerCharacterEquiv a q).toEquiv
    (fun χ : PrimeKummerCharacter a q => X - C (χ (primeKummerGenerator a q) : ℂ))
    (fun ξ : rootsOfUnity q ℂ => X - C ((ξ : ℂˣ) : ℂ)) (fun _ => rfl)]
  exact complex_rootsOfUnity_polynomial q

/-- The finite character product has the two possible unramified
Frobenius shapes of a degree-q cyclic extension. This does not assert
that an actual prime-ideal Frobenius has been defined. -/
theorem primeKummer_character_polynomial (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) :
    ∏ χ : PrimeKummerCharacter a q, (X - C (χ σ : ℂ)) =
      if σ = 1 then (X - 1 : ℂ[X]) ^ q else X ^ q - 1 := by
  classical
  split_ifs with hσ
  · subst σ
    simp only [map_one, Units.val_one, Finset.prod_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, primeKummerCharacter_card]
  · obtain ⟨m, hm, _⟩ := primeKummerGalois_exists_unique_coordinate a q σ
    have hm0 : m.val ≠ 0 := by
      intro hm0
      apply hσ
      rw [← hm, hm0, pow_zero]
    have hmc : (Nat.card (PrimeKummerCharacter a q)).Coprime m.val := by
      rw [primeKummerCharacter_card]
      exact hq.out.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hm0) m.isLt)
    have hbij : Function.Bijective (fun χ : PrimeKummerCharacter a q => χ ^ m.val) :=
      hmc.pow_left_bijective
    rw [← hm]
    have hp := Fintype.prod_bijective _ hbij
      (fun χ : PrimeKummerCharacter a q => X - C (χ (primeKummerGenerator a q ^ m.val) : ℂ))
      (fun χ : PrimeKummerCharacter a q => X - C (χ (primeKummerGenerator a q) : ℂ))
      (fun χ => by simp only [map_pow, MonoidHom.pow_apply])
    exact hp.trans (primeKummer_character_polynomial_generator a q)

end
end SimultaneousPrimitiveRoots
