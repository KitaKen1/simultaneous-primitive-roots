module

public import SimultaneousPrimitiveRoots.NumberFieldPrimeSupport

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- The actual ideal-counting LSeries after deleting a finite set of primes. -/
def numberFieldIncompleteZeta (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  LSeries (TauCeti.normCoeff K
    (TauCeti.MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
      S.finite_toSet).toIdealArithmeticFunction) s

theorem numberFieldIncompleteZeta_eq (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    numberFieldIncompleteZeta K S s =
      dedekindZeta K s * ∏ P ∈ S, (1 - (P.asIdeal.absNorm : ℂ) ^ (-s)) :=
  numberField_dedekindZeta_delete_factors K S hs

/-- The complementary actual prime Euler product converges to the deleted
ideal-counting LSeries. The finite correction is kept explicitly. -/
theorem numberFieldIncompleteZeta_hasProd (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : {P : HeightOneSpectrum (𝓞 K) // P ∉ S} =>
      (1 - (P.val.asIdeal.absNorm : ℂ) ^ (-s))⁻¹) (numberFieldIncompleteZeta K S s) := by
  classical
  let f := fun P : HeightOneSpectrum (𝓞 K) => 1 - (P.asIdeal.absNorm : ℂ) ^ (-s)
  have hf (P : HeightOneSpectrum (𝓞 K)) : f P ≠ 0 := by
    have h := TauCeti.prod_one_sub_absNorm_cpow_neg_ne_zero (K := K) {P}
      (zero_lt_one.trans hs)
    simpa [f] using h
  have hS : HasProd (fun P => if P ∈ S then f P else 1) (∏ P ∈ S, f P) := by
    have h := hasProd_prod_of_ne_finset_one (s := S)
      (L := SummationFilter.unconditional _)
      (f := fun P => if P ∈ S then f P else 1) (fun P hP => by simp [hP])
    simpa using h
  have hfull : HasProd (fun P => if P ∈ S then 1 else (f P)⁻¹)
      (numberFieldIncompleteZeta K S s) := by
    rw [numberFieldIncompleteZeta_eq K S hs]
    exact ((numberField_dedekindZeta_hasProd K hs).mul hS).congr_fun (fun P => by
      by_cases hP : P ∈ S
      · simp [hP, f, inv_mul_cancel₀ (hf P)]
      · simp [hP, f])
  have hsupport : Function.mulSupport (fun P => if P ∈ S then 1 else (f P)⁻¹) ⊆
      {P : HeightOneSpectrum (𝓞 K) | P ∉ S} := by
    intro P hP hmem
    exact hP (by simp [hmem])
  have h := (hasProd_subtype_iff_of_mulSupport_subset hsupport).mpr hfull
  exact h.congr_fun (fun P => by
    have hP : P.val ∉ S := P.property
    simp only [Function.comp_apply, if_neg hP, f])

theorem numberFieldIncompleteZeta_ne_zero (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    numberFieldIncompleteZeta K S s ≠ 0 := by
  rw [numberFieldIncompleteZeta_eq K S hs]
  exact mul_ne_zero (numberField_dedekindZeta_ne_zero K hs)
    (TauCeti.prod_one_sub_absNorm_cpow_neg_ne_zero S (zero_lt_one.trans hs))

/-- The nonzero residue including precisely the finite deleted factors. -/
def numberFieldIncompleteZetaResidue (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  (dedekindZeta_residue K : ℂ) * ∏ P ∈ S, (1 - (P.asIdeal.absNorm : ℂ) ^ (-1 : ℂ))

theorem numberFieldIncompleteZetaResidue_ne_zero (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : numberFieldIncompleteZetaResidue K S ≠ 0 :=
  TauCeti.dedekindZeta_residue_mul_prod_one_sub_absNorm_cpow_neg_one_ne_zero S

/-- Only the real right-hand limit is asserted here. -/
theorem numberFieldIncompleteZeta_tendsto_residue (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Filter.Tendsto (fun x : ℝ => (x - 1) * numberFieldIncompleteZeta K S x)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (numberFieldIncompleteZetaResidue K S)) :=
  TauCeti.tendsto_sub_one_mul_LSeries_ofBadPrimes S

end
end SimultaneousPrimitiveRoots
