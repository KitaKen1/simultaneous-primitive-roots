module

public import SimultaneousPrimitiveRoots.KummerCyclotomicAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

noncomputable section

theorem primeKummer_generator_conjugation (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] [NeZero q]
    (τ : Gal(PrimeKummerField a q/ℚ)) (u : (ZMod q)ˣ)
    (hτ : τ (algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q)
      (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ))) =
        algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q)
          (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ) ^ (u : ZMod q).val)) :
    τ * (primeKummerGenerator a q).restrictScalars ℚ * τ⁻¹ =
      (primeKummerGenerator a q ^ (u : ZMod q).val).restrictScalars ℚ := by
  rw [primeKummer_generator_semiconjugation a q τ u hτ]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Every nonidentity relative automorphism is an absolute conjugate of
the fixed generator. This avoids constructing an entire semidirect product. -/
theorem primeKummer_exists_generator_conjugator (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) (hσ : σ ≠ 1) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ),
      τ * (primeKummerGenerator a q).restrictScalars ℚ * τ⁻¹ = σ.restrictScalars ℚ := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  obtain ⟨m, hm, _⟩ := primeKummerGalois_exists_unique_coordinate a q σ
  have hm0 : m.val ≠ 0 := by
    intro hm0
    apply hσ
    rw [← hm, hm0, pow_zero]
  have hmc : m.val.Coprime q :=
    (hq.out.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hm0) m.isLt)).symm
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime m.val hmc
  have hu : (u : ZMod q).val = m.val := by
    change (m.val : ZMod q).val = m.val
    exact ZMod.val_natCast_of_lt m.isLt
  obtain ⟨τ, hτ⟩ := primeKummer_exists_zeta_lift a q u
  refine ⟨τ, ?_⟩
  rw [primeKummer_generator_conjugation a q τ u hτ, hu, hm]

/-- Absolute conjugation is transitive on all nonidentity elements of the
actual relative Galois group. No analytic input or Hecke interpretation occurs. -/
theorem primeKummer_nonidentity_conjugacy (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (σ γ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) (hσ : σ ≠ 1) (hγ : γ ≠ 1) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ),
      τ * σ.restrictScalars ℚ * τ⁻¹ = γ.restrictScalars ℚ := by
  obtain ⟨ρσ, hρσ⟩ := primeKummer_exists_generator_conjugator a q σ hσ
  obtain ⟨ργ, hργ⟩ := primeKummer_exists_generator_conjugator a q γ hγ
  refine ⟨ργ * ρσ⁻¹, ?_⟩
  rw [← hρσ, ← hργ]
  simp [mul_assoc]

end
end SimultaneousPrimitiveRoots
