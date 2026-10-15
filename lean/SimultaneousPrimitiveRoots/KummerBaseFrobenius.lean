module

public import SimultaneousPrimitiveRoots.KummerFrobenius

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- Each actual nonzero base prime has an actual nonzero prime above it. -/
theorem primeKummer_exists_prime_above (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) :
    ∃ P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)),
      P.asIdeal.comap (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) =
        v.asIdeal := by
  let Q : Ideal.primesOver v.asIdeal (𝓞 (PrimeKummerField a q)) := Classical.choice inferInstance
  have hover : Q.1.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) = v.asIdeal :=
    Q.2.2.over.symm
  refine ⟨⟨Q.1, Q.2.1, ?_⟩, hover⟩
  intro hQ
  apply v.ne_bot
  rw [← hover, hQ, Ideal.comap_bot_of_injective _
    (FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q)))]

def primeKummerPrimeAbove (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) :
    HeightOneSpectrum (𝓞 (PrimeKummerField a q)) :=
  (primeKummer_exists_prime_above a q v).choose

theorem primeKummerPrimeAbove_contraction (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) :
    (primeKummerPrimeAbove a q v).asIdeal.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) = v.asIdeal :=
  (primeKummer_exists_prime_above a q v).choose_spec

theorem primeKummerPrimeAbove_natCast_mem (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) (n : ℕ) :
    (n : 𝓞 (PrimeKummerField a q)) ∈ (primeKummerPrimeAbove a q v).asIdeal ↔
      (n : 𝓞 (CyclotomicField q ℚ)) ∈ v.asIdeal := by
  rw [← primeKummerPrimeAbove_contraction a q v, Ideal.mem_comap, map_natCast]

/-- The actual Frobenius value at a base prime. The coherent abelian
choice is independent of which prime above it is selected. -/
def primeKummerBaseFrobenius (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) :
    Gal(PrimeKummerField a q/CyclotomicField q ℚ) :=
  primeKummerFrobenius a q (primeKummerPrimeAbove a q v)

theorem primeKummerBaseFrobenius_eq (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)))
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hP : P.asIdeal.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) = v.asIdeal) :
    primeKummerBaseFrobenius a q v = primeKummerFrobenius a q P := by
  exact primeKummerFrobenius_eq_of_contraction a q _ P
    ((primeKummerPrimeAbove_contraction a q v).trans hP.symm)

/-- Nonprincipal character values at actual base-prime Frobenius are
transported by a norm-preserving permutation, at every unramified rational prime. -/
theorem primeKummer_nonprincipal_base_frobenius_values (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ),
      (∀ v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)),
        (primeKummerBasePrimeEquiv a q τ v).asIdeal.absNorm = v.asIdeal.absNorm) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ a → ¬ p ∣ q →
        ∀ v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)),
          (p : 𝓞 (CyclotomicField q ℚ)) ∈ v.asIdeal →
          ψ (primeKummerBaseFrobenius a q v) =
            χ (primeKummerBaseFrobenius a q (primeKummerBasePrimeEquiv a q τ v))) := by
  obtain ⟨τ, hnorm, hvalues⟩ := primeKummer_nonprincipal_character_frobenius_values a q χ ψ hχ hψ
  refine ⟨τ, hnorm, ?_⟩
  intro p hp hpa hpq v hpv
  let P := primeKummerPrimeAbove a q v
  have hpP : (p : 𝓞 (PrimeKummerField a q)) ∈ P.asIdeal :=
    (primeKummerPrimeAbove_natCast_mem a q v p).mpr hpv
  have hT : (numberFieldPrimeIdealEquiv τ.toRingEquiv P).asIdeal.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) =
      (primeKummerBasePrimeEquiv a q τ v).asIdeal := by
    rw [numberFieldPrimeIdealEquiv_asIdeal, primeKummerIdeal_map_comap,
      primeKummerPrimeAbove_contraction]
    exact (numberFieldPrimeIdealEquiv_asIdeal _ v).symm
  rw [primeKummerBaseFrobenius_eq a q _ _ hT]
  exact hvalues p hp hpa hpq P hpP

/-- Finite unramified Euler-factor products are equal after the actual
base-prime permutation, for any complex weight depending only on the norm.
This is a finite identity, with no infinite-product convergence assertion. -/
theorem primeKummer_nonprincipal_finite_euler_transport (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ),
      ∀ p : ℕ, p.Prime → ¬ p ∣ a → ¬ p ∣ q →
        ∀ S : Finset (HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))),
          (∀ v ∈ S, (p : 𝓞 (CyclotomicField q ℚ)) ∈ v.asIdeal) →
          ∀ W : ℕ → ℂ,
            (∏ v ∈ S, (1 - (ψ (primeKummerBaseFrobenius a q v) : ℂ) * W v.asIdeal.absNorm)) =
              ∏ v ∈ S.map (primeKummerBasePrimeEquiv a q τ).toEmbedding,
                (1 - (χ (primeKummerBaseFrobenius a q v) : ℂ) * W v.asIdeal.absNorm) := by
  obtain ⟨τ, hnorm, hvalues⟩ := primeKummer_nonprincipal_base_frobenius_values a q χ ψ hχ hψ
  refine ⟨τ, ?_⟩
  intro p hp hpa hpq S hS W
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro v hv
  change (1 - (ψ (primeKummerBaseFrobenius a q v) : ℂ) * W v.asIdeal.absNorm) =
    (1 - (χ (primeKummerBaseFrobenius a q (primeKummerBasePrimeEquiv a q τ v)) : ℂ) *
      W (primeKummerBasePrimeEquiv a q τ v).asIdeal.absNorm)
  rw [hvalues p hp hpa hpq v (hS v hv), hnorm v]

end
end SimultaneousPrimitiveRoots
