module

public import SimultaneousPrimitiveRoots.KummerBaseFrobenius
public import SimultaneousPrimitiveRoots.NumberFieldNormSeries

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- Base primes over rational primes away from a*q. These are the actual
unramified primes used in the incomplete Euler product. -/
def PrimeKummerEulerGood (a q : ℕ) [Fact q.Prime]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) : Prop :=
  ∃ p : ℕ, p.Prime ∧ ¬ p ∣ a ∧ ¬ p ∣ q ∧
    (p : 𝓞 (CyclotomicField q ℚ)) ∈ v.asIdeal

abbrev PrimeKummerEulerPrime (a q : ℕ) [Fact q.Prime] :=
  {v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)) // PrimeKummerEulerGood a q v}

theorem primeKummerEulerGood_transport (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ))
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) :
    PrimeKummerEulerGood a q v ↔
      PrimeKummerEulerGood a q (primeKummerBasePrimeEquiv a q τ v) := by
  simp only [PrimeKummerEulerGood, primeKummerBasePrimeEquiv_natCast_mem]

/-- Restrict the same actual base automorphism to the good prime set. -/
def primeKummerEulerPrimeEquiv (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ)) :
    PrimeKummerEulerPrime a q ≃ PrimeKummerEulerPrime a q :=
  Equiv.subtypeEquiv (primeKummerBasePrimeEquiv a q τ)
    (primeKummerEulerGood_transport a q τ)

theorem primeKummerEulerPrimeEquiv_absNorm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ)) (v : PrimeKummerEulerPrime a q) :
    (primeKummerEulerPrimeEquiv a q τ v).val.asIdeal.absNorm = v.val.asIdeal.absNorm :=
  primeKummerBasePrimeEquiv_absNorm a q τ v.val

/-- The actual character-value transport holds on the entire good prime
set at once, rather than on one rational-prime fiber. -/
theorem primeKummer_nonprincipal_eulerPrime_values (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ), ∀ v : PrimeKummerEulerPrime a q,
      ψ (primeKummerBaseFrobenius a q v.val) =
        χ (primeKummerBaseFrobenius a q (primeKummerEulerPrimeEquiv a q τ v).val) := by
  obtain ⟨τ, _, hvalues⟩ := primeKummer_nonprincipal_base_frobenius_values a q χ ψ hχ hψ
  refine ⟨τ, ?_⟩
  intro v
  obtain ⟨p, hp, hpa, hpq, hpv⟩ := v.property
  exact hvalues p hp hpa hpq v.val hpv

/-- A single permutation transports an arbitrary finite set of good
prime ideals, even when they lie over different rational primes. -/
theorem primeKummer_nonprincipal_finite_goodEuler_transport (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ), ∀ S : Finset (PrimeKummerEulerPrime a q),
      ∀ W : ℕ → ℂ,
      (∏ v ∈ S, (1 - (ψ (primeKummerBaseFrobenius a q v.val) : ℂ) * W v.val.asIdeal.absNorm)) =
        ∏ v ∈ S.map (primeKummerEulerPrimeEquiv a q τ).toEmbedding,
          (1 - (χ (primeKummerBaseFrobenius a q v.val) : ℂ) * W v.val.asIdeal.absNorm) := by
  obtain ⟨τ, hvalues⟩ := primeKummer_nonprincipal_eulerPrime_values a q χ ψ hχ hψ
  refine ⟨τ, ?_⟩
  intro S W
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro v _
  change _ = 1 - (χ (primeKummerBaseFrobenius a q
    (primeKummerEulerPrimeEquiv a q τ v).val) : ℂ) *
      W (primeKummerEulerPrimeEquiv a q τ v).val.asIdeal.absNorm
  rw [hvalues v, primeKummerEulerPrimeEquiv_absNorm]

/-- Values of every actual relative character have complex norm one. -/
theorem primeKummerCharacter_norm (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q)
    (σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) :
    ‖(χ σ : ℂ)‖ = 1 := by
  have hp : σ ^ q = 1 := by
    simpa only [primeKummer_relative_galois_card a q] using (pow_card_eq_one' (x := σ))
  apply Complex.norm_eq_one_of_pow_eq_one _ hq.out.ne_zero
  have h := congrArg (fun z : ℂˣ => (z : ℂ)) (congrArg χ hp)
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using h

/-- The nonconstant part of the genuine unramified local Euler factor. -/
def primeKummerEulerTerm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (s : ℂ) (v : PrimeKummerEulerPrime a q) : ℂ :=
  (χ (primeKummerBaseFrobenius a q v.val) : ℂ) * (v.val.asIdeal.absNorm : ℂ) ^ (-s)

theorem numberField_prime_absNorm_gt_one (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : 1 < v.asIdeal.absNorm := by
  have hzero : v.asIdeal.absNorm ≠ 0 :=
    mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot
  have hone : v.asIdeal.absNorm ≠ 1 :=
    mt Ideal.absNorm_eq_one_iff.mp v.isPrime.ne_top
  omega

theorem primeKummerEulerTerm_norm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (s : ℂ) (v : PrimeKummerEulerPrime a q) :
    ‖primeKummerEulerTerm a q χ s v‖ = (v.val.asIdeal.absNorm : ℝ) ^ (-s.re) := by
  rw [primeKummerEulerTerm, norm_mul, primeKummerCharacter_norm, one_mul,
    Complex.norm_natCast_cpow_of_pos (by
      have h := numberField_prime_absNorm_gt_one (CyclotomicField q ℚ) v.val
      omega)]
  simp

theorem primeKummerEulerTerm_norm_lt_one (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) {s : ℂ} (hs : 1 < s.re)
    (v : PrimeKummerEulerPrime a q) : ‖primeKummerEulerTerm a q χ s v‖ < 1 := by
  rw [primeKummerEulerTerm_norm]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast numberField_prime_absNorm_gt_one (CyclotomicField q ℚ) v.val
  · linarith

/-- Absolute convergence of the actual local terms for every s with Re(s)>1. -/
theorem primeKummerEulerTerm_norm_summable (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : PrimeKummerEulerPrime a q => ‖primeKummerEulerTerm a q χ s v‖) := by
  simpa only [primeKummerEulerTerm_norm, Function.comp_def] using
    (numberField_primeNorm_rpow_summable (CyclotomicField q ℚ) hs).subtype
      (PrimeKummerEulerGood a q)

theorem primeKummerEulerFactors_multipliable (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun v : PrimeKummerEulerPrime a q => 1 - primeKummerEulerTerm a q χ s v) := by
  have hneg : Summable (fun v : PrimeKummerEulerPrime a q =>
      ‖-(primeKummerEulerTerm a q χ s v)‖) := by
    simpa only [norm_neg] using primeKummerEulerTerm_norm_summable a q χ hs
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hneg

theorem primeKummerEulerFactor_ne_zero (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) {s : ℂ} (hs : 1 < s.re)
    (v : PrimeKummerEulerPrime a q) : 1 - primeKummerEulerTerm a q χ s v ≠ 0 := by
  intro h
  have he : primeKummerEulerTerm a q χ s v = 1 := (sub_eq_zero.mp h).symm
  have hn := primeKummerEulerTerm_norm_lt_one a q χ hs v
  rw [he, norm_one] at hn
  exact lt_irrefl _ hn

theorem primeKummerEulerProduct_ne_zero (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) {s : ℂ} (hs : 1 < s.re) :
    (∏' v : PrimeKummerEulerPrime a q, (1 - primeKummerEulerTerm a q χ s v)) ≠ 0 := by
  have ht := tprod_one_add_ne_zero_of_summable
    (fun v : PrimeKummerEulerPrime a q => (by
      simpa only [sub_eq_add_neg] using primeKummerEulerFactor_ne_zero a q χ hs v))
    (show Summable (fun v : PrimeKummerEulerPrime a q => ‖-primeKummerEulerTerm a q χ s v‖)
      from by simpa only [norm_neg] using primeKummerEulerTerm_norm_summable a q χ hs)
  simpa only [sub_eq_add_neg] using ht

/-- Equality of convergent incomplete Euler products of two nonprincipal
characters, simultaneously for every s in the absolute-convergence half-plane.
No ramified factors, Hecke reciprocity or continuation are asserted here. -/
theorem primeKummer_nonprincipal_eulerProduct_eq (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∏' v : PrimeKummerEulerPrime a q, (1 - primeKummerEulerTerm a q ψ s v)) =
      ∏' v : PrimeKummerEulerPrime a q, (1 - primeKummerEulerTerm a q χ s v) := by
  obtain ⟨τ, hvalues⟩ := primeKummer_nonprincipal_eulerPrime_values a q χ ψ hχ hψ
  have heq : (fun v : PrimeKummerEulerPrime a q => 1 - primeKummerEulerTerm a q ψ s v) =
      (fun v : PrimeKummerEulerPrime a q => 1 - primeKummerEulerTerm a q χ s v) ∘
        primeKummerEulerPrimeEquiv a q τ := by
    funext v
    simp only [Function.comp_def, primeKummerEulerTerm, hvalues v,
      primeKummerEulerPrimeEquiv_absNorm]
  have hprod := (primeKummerEulerPrimeEquiv a q τ).hasProd_iff.mpr
    (primeKummerEulerFactors_multipliable a q χ hs).hasProd
  rw [← heq] at hprod
  exact hprod.tprod_eq

/-- A common, nonzero limit of actual finite Euler denominator products.
This records convergence explicitly, so no default value of tprod is used
as evidence of an analytic product identity. -/
theorem primeKummer_nonprincipal_eulerProducts_hasProd (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ∃ L : ℂ, L ≠ 0 ∧
      HasProd (fun v : PrimeKummerEulerPrime a q => 1 - primeKummerEulerTerm a q χ s v) L ∧
      HasProd (fun v : PrimeKummerEulerPrime a q => 1 - primeKummerEulerTerm a q ψ s v) L := by
  refine ⟨∏' v : PrimeKummerEulerPrime a q, (1 - primeKummerEulerTerm a q χ s v),
    primeKummerEulerProduct_ne_zero a q χ hs,
    (primeKummerEulerFactors_multipliable a q χ hs).hasProd, ?_⟩
  rw [← primeKummer_nonprincipal_eulerProduct_eq a q χ ψ hχ hψ hs]
  exact (primeKummerEulerFactors_multipliable a q ψ hs).hasProd

/-- An incomplete Artin-style Euler product, defined only from the actual
unramified Frobenius values. This definition makes no Hecke assignment. -/
def primeKummerIncompleteEulerL (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (s : ℂ) : ℂ :=
  (∏' v : PrimeKummerEulerPrime a q, (1 - primeKummerEulerTerm a q χ s v))⁻¹

/-- The reciprocals of the actual local factors converge to the displayed
incomplete L-function in Re(s)>1. -/
theorem primeKummerIncompleteEulerL_hasProd (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : PrimeKummerEulerPrime a q =>
      (1 - primeKummerEulerTerm a q χ s v)⁻¹) (primeKummerIncompleteEulerL a q χ s) :=
  (primeKummerEulerFactors_multipliable a q χ hs).hasProd.inv₀
    (primeKummerEulerProduct_ne_zero a q χ hs)

theorem primeKummerIncompleteEulerL_ne_zero (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) {s : ℂ} (hs : 1 < s.re) :
    primeKummerIncompleteEulerL a q χ s ≠ 0 :=
  inv_ne_zero (primeKummerEulerProduct_ne_zero a q χ hs)

theorem primeKummer_nonprincipal_incompleteEulerL_eq (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    primeKummerIncompleteEulerL a q ψ s = primeKummerIncompleteEulerL a q χ s := by
  exact congrArg Inv.inv (primeKummer_nonprincipal_eulerProduct_eq a q χ ψ hχ hψ hs)

/-- The finite nonprincipal character set used in the actual product. -/
instance primeKummerNonprincipalCharacter_fintype (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    Fintype {ψ : PrimeKummerCharacter a q // ψ ≠ 1} := Fintype.ofFinite _

/-- The entire nonprincipal part of the convergent incomplete Euler
product is a single actual factor raised to q-1. Ramified factors and
the comparison with Dedekind zeta are separate tasks. -/
theorem primeKummer_nonprincipal_incompleteEulerL_product (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∏ ψ : {ψ : PrimeKummerCharacter a q // ψ ≠ 1},
      primeKummerIncompleteEulerL a q ψ.val s) = (primeKummerIncompleteEulerL a q χ s) ^ (q - 1) := by
  classical
  calc
    _ = ∏ _ψ : {ψ : PrimeKummerCharacter a q // ψ ≠ 1},
        primeKummerIncompleteEulerL a q χ s := by
      apply Finset.prod_congr rfl
      intro ψ _
      exact primeKummer_nonprincipal_incompleteEulerL_eq a q χ ψ.val hχ ψ.property hs
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        primeKummer_nonprincipal_character_card]

end
end SimultaneousPrimitiveRoots
