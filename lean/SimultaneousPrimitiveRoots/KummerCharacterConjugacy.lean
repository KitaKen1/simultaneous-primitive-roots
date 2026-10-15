module

public import SimultaneousPrimitiveRoots.KummerCharacters

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

noncomputable section

theorem primeKummer_conjugation_on_powers (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ)) (k : ℕ)
    (hτ : τ * (primeKummerGenerator a q).restrictScalars ℚ * τ⁻¹ =
      (primeKummerGenerator a q ^ k).restrictScalars ℚ)
    (σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) :
    τ * σ.restrictScalars ℚ * τ⁻¹ = (σ ^ k).restrictScalars ℚ := by
  have hr (γ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) (n : ℕ) :
      (γ ^ n).restrictScalars ℚ = γ.restrictScalars ℚ ^ n :=
    map_pow (AlgEquiv.restrictScalarsHom ℚ) γ n
  obtain ⟨m, hm, _⟩ := primeKummerGalois_exists_unique_coordinate a q σ
  change MulAut.conj τ (σ.restrictScalars ℚ) = (σ ^ k).restrictScalars ℚ
  change MulAut.conj τ ((primeKummerGenerator a q).restrictScalars ℚ) =
    (primeKummerGenerator a q ^ k).restrictScalars ℚ at hτ
  rw [← hm, hr, map_pow, hτ, ← hr]
  apply congrArg (fun γ : Gal(PrimeKummerField a q/CyclotomicField q ℚ) =>
    γ.restrictScalars ℚ)
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Every nonzero exponent modulo q is realized by absolute conjugation
on the entire actual relative Galois group. -/
theorem primeKummer_exists_power_conjugator (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (m : Fin q) (hm : m.val ≠ 0) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ),
      ∀ σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ),
        τ * σ.restrictScalars ℚ * τ⁻¹ = (σ ^ m.val).restrictScalars ℚ := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  have hmc : m.val.Coprime q :=
    (hq.out.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hm) m.isLt)).symm
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime m.val hmc
  have hu : (u : ZMod q).val = m.val := by
    change (m.val : ZMod q).val = m.val
    exact ZMod.val_natCast_of_lt m.isLt
  obtain ⟨τ, hτ⟩ := primeKummer_exists_zeta_lift a q u
  refine ⟨τ, fun σ => primeKummer_conjugation_on_powers a q τ m.val ?_ σ⟩
  rw [primeKummer_generator_conjugation a q τ u hτ, hu]

/-- All nonprincipal complex characters are related by pullback along
conjugation by an actual absolute field automorphism. The exponent and
the action on every relative automorphism are given together. -/
theorem primeKummer_nonprincipal_character_conjugacy (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ m : Fin q, m.val ≠ 0 ∧ ∃ τ : Gal(PrimeKummerField a q/ℚ),
      (∀ σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ),
        τ * σ.restrictScalars ℚ * τ⁻¹ = (σ ^ m.val).restrictScalars ℚ) ∧
      (∀ σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ), ψ σ = χ (σ ^ m.val)) := by
  obtain ⟨m, hm0, hm⟩ := primeKummer_nonprincipal_character_power a q χ ψ hχ hψ
  obtain ⟨τ, hτ⟩ := primeKummer_exists_power_conjugator a q m hm0
  refine ⟨m, hm0, τ, hτ, fun σ => ?_⟩
  rw [← hm]
  simp only [MonoidHom.pow_apply, map_pow]

end
end SimultaneousPrimitiveRoots
