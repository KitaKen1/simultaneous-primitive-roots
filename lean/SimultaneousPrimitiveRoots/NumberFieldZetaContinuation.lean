module

public import SimultaneousPrimitiveRoots.NumberFieldIncompleteZeta
public import TauCeti.NumberTheory.NumberField.DedekindZeta

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Filter
open scoped Topology
noncomputable section

/-- The available field-dependent half-plane, not a common-width strip. -/
def numberFieldZetaContinuationDomain (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}

theorem numberFieldZetaContinuationDomain_isOpen (K : Type*) [Field K] [NumberField K] :
    IsOpen (numberFieldZetaContinuationDomain K) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem numberFieldZetaContinuationDomain_mem (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 ≤ s.re) : s ∈ numberFieldZetaContinuationDomain K :=
  TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs

/-- The actual continuation of zeta with its simple pole subtracted. -/
def numberFieldZetaRegularPart (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  Classical.choose (TauCeti.exists_differentiableOn_eq_dedekindZeta_sub K)

theorem numberFieldZetaRegularPart_differentiableOn (K : Type*) [Field K] [NumberField K] :
    DifferentiableOn ℂ (numberFieldZetaRegularPart K) (numberFieldZetaContinuationDomain K) :=
  (Classical.choose_spec (TauCeti.exists_differentiableOn_eq_dedekindZeta_sub K)).1

theorem numberFieldZetaRegularPart_eq (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    numberFieldZetaRegularPart K s = dedekindZeta K s - (dedekindZeta_residue K : ℂ) / (s - 1) :=
  (Classical.choose_spec (TauCeti.exists_differentiableOn_eq_dedekindZeta_sub K)).2 s hs

/-- Multiplication by s-1 removes the actual simple pole. -/
def numberFieldNormalizedZeta (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (s - 1) * numberFieldZetaRegularPart K s + (dedekindZeta_residue K : ℂ)

theorem numberFieldNormalizedZeta_differentiableOn (K : Type*) [Field K] [NumberField K] :
    DifferentiableOn ℂ (numberFieldNormalizedZeta K) (numberFieldZetaContinuationDomain K) :=
  ((differentiableOn_id.sub_const 1).mul
    (numberFieldZetaRegularPart_differentiableOn K)).add_const _

theorem numberFieldNormalizedZeta_at_one (K : Type*) [Field K] [NumberField K] :
    numberFieldNormalizedZeta K 1 = (dedekindZeta_residue K : ℂ) := by
  simp [numberFieldNormalizedZeta]

theorem numberFieldNormalizedZeta_eq (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    numberFieldNormalizedZeta K s = (s - 1) * dedekindZeta K s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h => by simp [h] at hs)
  simp only [numberFieldNormalizedZeta, numberFieldZetaRegularPart_eq K hs]
  field_simp [hsub]
  ring

/-- Pointwise nonvanishing on the closed convergence boundary follows
from the actual Dedekind 3-4-1 theorem; no uniform zero-free width is asserted. -/
theorem numberFieldNormalizedZeta_ne_zero (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 ≤ s.re) : numberFieldNormalizedZeta K s ≠ 0 := by
  have hdiff : DifferentiableAt ℂ (numberFieldNormalizedZeta K) s :=
    (numberFieldNormalizedZeta_differentiableOn K).differentiableAt
      ((numberFieldZetaContinuationDomain_isOpen K).mem_nhds
        (numberFieldZetaContinuationDomain_mem K hs))
  rcases hs.lt_or_eq with hs | hs
  · rw [numberFieldNormalizedZeta_eq K hs]
    exact mul_ne_zero (sub_ne_zero.mpr (fun h => by simp [h] at hs))
      (numberField_dedekindZeta_ne_zero K hs)
  rcases eq_or_ne s 1 with rfl | hs1
  · rw [numberFieldNormalizedZeta_at_one]
    exact_mod_cast (dedekindZeta_residue_pos K).ne'
  have hne := TauCeti.ne_zero_of_eqOn_dedekindZeta (K := K)
    (f := fun z => numberFieldNormalizedZeta K z / (z - 1)) hs.symm hs1
    (hdiff.div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
    (fun z hz => by
      change numberFieldNormalizedZeta K z / (z - 1) = dedekindZeta K z
      rw [numberFieldNormalizedZeta_eq K hz]
      exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr (fun h => by simp [h] at hz)))
  exact fun h => hne (by simp [h])

def numberFieldDeletedZetaCorrection (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏ P ∈ S, (1 - (P.asIdeal.absNorm : ℂ) ^ (-s))

theorem numberFieldDeletedZetaCorrection_differentiable (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Differentiable ℂ (numberFieldDeletedZetaCorrection K S) :=
  Differentiable.fun_finsetProd (fun P _ =>
    (differentiable_id.neg.const_cpow (Or.inl P.natCast_absNorm_ne_zero)).const_sub 1)

theorem numberFieldDeletedZetaCorrection_ne_zero (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 0 < s.re) :
    numberFieldDeletedZetaCorrection K S s ≠ 0 :=
  TauCeti.prod_one_sub_absNorm_cpow_neg_ne_zero S hs

/-- The actual deleted-zeta continuation normalized by its simple pole. -/
def numberFieldIncompleteZetaNormalized (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  numberFieldNormalizedZeta K s * numberFieldDeletedZetaCorrection K S s

theorem numberFieldIncompleteZetaNormalized_differentiableOn (K : Type*)
    [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DifferentiableOn ℂ (numberFieldIncompleteZetaNormalized K S)
      (numberFieldZetaContinuationDomain K) :=
  (numberFieldNormalizedZeta_differentiableOn K).mul
    (numberFieldDeletedZetaCorrection_differentiable K S).differentiableOn

theorem numberFieldIncompleteZetaNormalized_at_one (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    numberFieldIncompleteZetaNormalized K S 1 = numberFieldIncompleteZetaResidue K S := by
  simp only [numberFieldIncompleteZetaNormalized, numberFieldNormalizedZeta_at_one,
    numberFieldDeletedZetaCorrection, numberFieldIncompleteZetaResidue]

theorem numberFieldIncompleteZetaNormalized_eq (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    numberFieldIncompleteZetaNormalized K S s = (s - 1) * numberFieldIncompleteZeta K S s := by
  rw [numberFieldIncompleteZetaNormalized, numberFieldNormalizedZeta_eq K hs,
    numberFieldIncompleteZeta_eq K S hs]
  exact mul_assoc _ _ _

theorem numberFieldIncompleteZetaNormalized_ne_zero (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 ≤ s.re) :
    numberFieldIncompleteZetaNormalized K S s ≠ 0 :=
  mul_ne_zero (numberFieldNormalizedZeta_ne_zero K hs)
    (numberFieldDeletedZetaCorrection_ne_zero K S (zero_lt_one.trans_le hs))

theorem numberFieldIncompleteZetaNormalized_differentiableAt (K : Type*)
    [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    {s : ℂ} (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (numberFieldIncompleteZetaNormalized K S) s :=
  (numberFieldIncompleteZetaNormalized_differentiableOn K S).differentiableAt
    ((numberFieldZetaContinuationDomain_isOpen K).mem_nhds
      (numberFieldZetaContinuationDomain_mem K hs))

end
end SimultaneousPrimitiveRoots
