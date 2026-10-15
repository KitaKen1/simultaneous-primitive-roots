module

public import SimultaneousPrimitiveRoots.KummerGaloisStructure

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Polynomial
noncomputable section

theorem prime_cyclotomic_normal (q : ℕ) : Normal ℚ (CyclotomicField q ℚ) := by
  let : IsSplittingField ℚ (CyclotomicField q ℚ) (cyclotomic q ℚ) := by
    change IsSplittingField ℚ (SplittingField (cyclotomic q ℚ)) (cyclotomic q ℚ)
    infer_instance
  exact Normal.of_isSplittingField (cyclotomic q ℚ)

def primeCyclotomicGaloisEquiv (q : ℕ) [hq : Fact q.Prime] :
    Gal(CyclotomicField q ℚ/ℚ) ≃* (ZMod q)ˣ := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  exact IsCyclotomicExtension.autEquivPow (CyclotomicField q ℚ)
    (cyclotomic.irreducible_rat hq.out.pos)

theorem primeCyclotomicGaloisEquiv_action (q : ℕ) [Fact q.Prime] [NeZero q]
    (u : (ZMod q)ˣ) :
    (primeCyclotomicGaloisEquiv q).symm u
      (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ)) =
        IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ) ^ (u : ZMod q).val := by
  have h := (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)).autToPow_spec
    ℚ ((primeCyclotomicGaloisEquiv q).symm u)
  have hu : (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)).autToPow ℚ
      ((primeCyclotomicGaloisEquiv q).symm u) = u :=
    (primeCyclotomicGaloisEquiv q).apply_symm_apply u
  rw [hu] at h
  exact h.symm

/-- Every cyclotomic automorphism lifts to an actual absolute automorphism
of the Kummer field. No homomorphic section is asserted. -/
theorem primeKummer_exists_cyclotomic_lift (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] [NeZero q] (u : (ZMod q)ˣ) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ), ∀ z : CyclotomicField q ℚ,
      τ (algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q) z) =
        algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q)
          ((primeCyclotomicGaloisEquiv q).symm u z) := by
  let := primeKummerField_galois a q
  let := prime_cyclotomic_normal q
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (PrimeKummerField a q)
    ((primeCyclotomicGaloisEquiv q).symm u)
  refine ⟨τ, fun z => ?_⟩
  rw [← hτ]
  exact (AlgEquiv.restrictNormal_commutes τ (CyclotomicField q ℚ) z).symm

theorem primeKummer_exists_zeta_lift (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] [NeZero q] (u : (ZMod q)ˣ) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ),
      τ (algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q)
          (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ))) =
        algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q)
          (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ) ^ (u : ZMod q).val) := by
  obtain ⟨τ, hτ⟩ := primeKummer_exists_cyclotomic_lift a q u
  refine ⟨τ, ?_⟩
  rw [hτ, primeCyclotomicGaloisEquiv_action]

theorem primeKummer_absolute_root_action (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] [NeZero q]
    (τ : Gal(PrimeKummerField a q/ℚ)) :
    ∃ m < q, τ (AdjoinRoot.root (primeRadicalPolynomial a q)) =
      IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ) ^ m •
        AdjoinRoot.root (primeRadicalPolynomial a q) := by
  have hζ := (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)).map_of_injective
    (algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q)).injective
  have hp : τ (AdjoinRoot.root (primeRadicalPolynomial a q)) ^ q =
      (a : PrimeKummerField a q) := by
    rw [← map_pow, primeKummerField_root_pow, map_natCast]
  have hm := (mem_nthRoots hq.out.pos).mpr hp
  rw [hζ.nthRoots_eq (primeKummerField_root_pow a q)] at hm
  obtain ⟨m, hm, heq⟩ := Multiset.mem_map.mp hm
  refine ⟨m, Multiset.mem_range.mp hm, ?_⟩
  simpa only [Algebra.smul_def, map_pow] using heq.symm

/-- The cyclotomic exponent is the conjugation exponent on the actual
relative generator. The proof only needs the generated algebra and its root. -/
theorem primeKummer_generator_semiconjugation (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] [NeZero q]
    (τ : Gal(PrimeKummerField a q/ℚ)) (u : (ZMod q)ˣ)
    (hτ : τ (algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q)
      (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ))) =
        algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q)
          (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ) ^ (u : ZMod q).val)) :
    τ * (primeKummerGenerator a q).restrictScalars ℚ =
      (primeKummerGenerator a q ^ (u : ZMod q).val).restrictScalars ℚ * τ := by
  let := prime_cyclotomic_normal q
  apply AlgEquiv.ext
  intro x
  change τ (primeKummerGenerator a q x) =
    (primeKummerGenerator a q ^ (u : ZMod q).val) (τ x)
  have hx : x ∈ Algebra.adjoin (CyclotomicField q ℚ)
      {AdjoinRoot.root (primeRadicalPolynomial a q)} := by
    rw [AdjoinRoot.adjoinRoot_eq_top]
    trivial
  refine Algebra.adjoin_induction (p := fun y _ => τ (primeKummerGenerator a q y) =
    (primeKummerGenerator a q ^ (u : ZMod q).val) (τ y)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    obtain ⟨m, _, hm⟩ := primeKummer_absolute_root_action a q τ
    have hs := primeKummerGenerator_pow_action a q 1
    simp only [pow_one] at hs
    rw [hs, Algebra.smul_def, map_mul, hτ, hm]
    rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, primeKummerGenerator_pow_action]
    simp only [Algebra.smul_def, map_pow]
    ring
  · intro z
    rw [(primeKummerGenerator a q).commutes,
      ← AlgEquiv.restrictNormal_commutes τ (CyclotomicField q ℚ), AlgEquiv.commutes]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy]
  · intro x y _ _ hx hy
    simp only [map_mul, hx, hy]

end
end SimultaneousPrimitiveRoots
