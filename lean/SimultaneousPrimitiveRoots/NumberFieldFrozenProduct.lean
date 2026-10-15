module

public import SimultaneousPrimitiveRoots.FrozenLocalSeries
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- Actual prime ideals of bounded norm form the finite set needed to absorb
the small local factors; the finiteness is not an analytic hypothesis. -/
def numberFieldSmallNormPrimes (K : Type*) [Field K] [NumberField K] (B : ℕ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le B).toFinset

theorem numberFieldSmallNormPrimes_mem (K : Type*) [Field K] [NumberField K]
    (B : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ numberFieldSmallNormPrimes K B ↔ v.asIdeal.absNorm ≤ B :=
  Set.Finite.mem_toFinset _

/-- A bounded factor with finite exceptional support has one constant for
every finite support. The product of actual norms is kept explicit. -/
theorem finite_product_absorb_small {ι : Type*} (T : Finset ι) (c : ℝ)
    (hc : 1 ≤ c) (N f : ι → ℝ) (hN : ∀ i, 1 ≤ N i)
    (hf0 : ∀ i, 0 ≤ f i) (hf : ∀ i, f i ≤ c)
    (hlarge : ∀ i, i ∉ T → f i ≤ N i) (s : Finset ι) :
    (∏ i ∈ s, f i) ≤ c ^ T.card * ∏ i ∈ s, N i := by
  classical
  let b : ι → ℝ := fun i => if i ∈ T then c else 1
  have hpoint (i : ι) : f i ≤ b i * N i := by
    by_cases hi : i ∈ T
    · simp only [b, if_pos hi]
      exact (hf i).trans (le_mul_of_one_le_right (by linarith) (hN i))
    · simpa only [b, if_neg hi, one_mul] using hlarge i hi
  have hprod : (∏ i ∈ s, b i) = c ^ (s.filter (fun i => i ∈ T)).card := by
    simp [b, Finset.filter_mem_eq_inter]
  have hcard : (s.filter (fun i => i ∈ T)).card ≤ T.card :=
    Finset.card_le_card fun i hi => (Finset.mem_filter.mp hi).2
  have hbound : (∏ i ∈ s, b i) ≤ c ^ T.card := by
    rw [hprod]
    exact pow_le_pow_right₀ hc hcard
  calc
    _ ≤ ∏ i ∈ s, b i * N i :=
      Finset.prod_le_prod (fun i _ => hf0 i) (fun i _ => hpoint i)
    _ = (∏ i ∈ s, b i) * ∏ i ∈ s, N i := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Finset.prod_nonneg fun i _ =>
      (zero_le_one.trans (hN i)))

/-- Uniform subpower growth of the frozen Dirichlet product, for actual
number-field prime ideals, every finite support and all sigma >= 0. -/
theorem numberField_frozenLocalDirichlet_product_bound
    (K : Type*) [Field K] [NumberField K] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ), 0 ≤ σ →
      (∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ) ≤
        C * (∏ v ∈ s, (v.asIdeal.absNorm : ℝ)) ^ ε := by
  classical
  let c : ℝ := 3 + Real.sqrt 2
  have hc : 1 ≤ c := by dsimp [c]; linarith [Real.sqrt_nonneg 2]
  obtain ⟨B, hB⟩ := exists_nat_gt (c ^ ε⁻¹)
  let T := numberFieldSmallNormPrimes K B
  refine ⟨c ^ T.card, by positivity, ?_⟩
  intro s σ hσ
  have hnorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (show 2 ≤ v.asIdeal.absNorm by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v
      omega)
  have hl (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ T) :
      frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ ≤ (v.asIdeal.absNorm : ℝ) ^ ε := by
    apply (frozenLocalDirichlet_le (hnorm v) hσ).trans
    apply (Real.rpow_inv_le_iff_of_pos (by positivity : 0 ≤ c)
      (by positivity) hε).mp
    have hBv : B < v.asIdeal.absNorm := by
      exact Nat.lt_of_not_ge (by simpa only [T, numberFieldSmallNormPrimes_mem] using hv)
    exact hB.le.trans (by exact_mod_cast hBv.le)
  have hb := finite_product_absorb_small T c hc
    (fun v : HeightOneSpectrum (𝓞 K) => (v.asIdeal.absNorm : ℝ) ^ ε)
    (fun v => frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ)
    (fun v => Real.one_le_rpow (by linarith [hnorm v]) hε.le)
    (fun v => by
      rw [frozenLocalDirichlet_eq_series (by positivity)]
      exact frozenLocalSeries_nonneg (by positivity) (by positivity))
    (fun v => frozenLocalDirichlet_le (hnorm v) hσ) hl s
  convert hb using 1
  rw [Real.finsetProd_rpow]
  intro v _
  positivity

end
end SimultaneousPrimitiveRoots
