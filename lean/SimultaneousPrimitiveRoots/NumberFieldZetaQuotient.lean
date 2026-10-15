module

public import SimultaneousPrimitiveRoots.NumberFieldZetaContinuation

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Filter
open scoped Topology
noncomputable section

/-- The quotient of the actual normalized deleted-zeta continuations.
Its pole at one has already canceled. -/
def numberFieldIncompleteZetaQuotient (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset (HeightOneSpectrum (𝓞 L))) (s : ℂ) : ℂ :=
  numberFieldIncompleteZetaNormalized K S s / numberFieldIncompleteZetaNormalized L T s

theorem numberFieldIncompleteZetaQuotient_eq (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset (HeightOneSpectrum (𝓞 L))) {s : ℂ} (hs : 1 < s.re) :
    numberFieldIncompleteZetaQuotient K L S T s =
      numberFieldIncompleteZeta K S s / numberFieldIncompleteZeta L T s := by
  rw [numberFieldIncompleteZetaQuotient, numberFieldIncompleteZetaNormalized_eq K S hs,
    numberFieldIncompleteZetaNormalized_eq L T hs]
  exact mul_div_mul_left _ _ (sub_ne_zero.mpr (fun h => by simp [h] at hs))

theorem numberFieldIncompleteZetaQuotient_at_one (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset (HeightOneSpectrum (𝓞 L))) :
    numberFieldIncompleteZetaQuotient K L S T 1 =
      numberFieldIncompleteZetaResidue K S / numberFieldIncompleteZetaResidue L T := by
  simp only [numberFieldIncompleteZetaQuotient, numberFieldIncompleteZetaNormalized_at_one]

theorem numberFieldIncompleteZetaQuotient_ne_zero (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset (HeightOneSpectrum (𝓞 L))) {s : ℂ} (hs : 1 ≤ s.re) :
    numberFieldIncompleteZetaQuotient K L S T s ≠ 0 :=
  div_ne_zero (numberFieldIncompleteZetaNormalized_ne_zero K S hs)
    (numberFieldIncompleteZetaNormalized_ne_zero L T hs)

theorem numberFieldIncompleteZetaQuotient_differentiableAt (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset (HeightOneSpectrum (𝓞 L))) {s : ℂ} (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (numberFieldIncompleteZetaQuotient K L S T) s :=
  (numberFieldIncompleteZetaNormalized_differentiableAt K S hs).div
    (numberFieldIncompleteZetaNormalized_differentiableAt L T hs)
    (numberFieldIncompleteZetaNormalized_ne_zero L T hs)

/-- Every point on Re(s)>=1 has an open nonvanishing holomorphic
neighborhood. This neighborhood is allowed to depend on both fields
and on the point; no common-width zero-free strip is supplied. -/
theorem numberFieldIncompleteZetaQuotient_exists_neighborhood (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    {s : ℂ} (hs : 1 ≤ s.re) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧
      DifferentiableOn ℂ (numberFieldIncompleteZetaQuotient K L S T) U ∧
      ∀ z ∈ U, numberFieldIncompleteZetaQuotient K L S T z ≠ 0 := by
  have hK := (numberFieldIncompleteZetaNormalized_differentiableAt K S hs).continuousAt
    |>.eventually_ne (numberFieldIncompleteZetaNormalized_ne_zero K S hs)
  have hL := (numberFieldIncompleteZetaNormalized_differentiableAt L T hs).continuousAt
    |>.eventually_ne (numberFieldIncompleteZetaNormalized_ne_zero L T hs)
  have hDK := (numberFieldZetaContinuationDomain_isOpen K).mem_nhds
    (numberFieldZetaContinuationDomain_mem K hs)
  have hDL := (numberFieldZetaContinuationDomain_isOpen L).mem_nhds
    (numberFieldZetaContinuationDomain_mem L hs)
  obtain ⟨U, hUsub, hUopen, hsU⟩ := mem_nhds_iff.mp
    (inter_mem (inter_mem hDK hDL) (inter_mem hK hL))
  refine ⟨U, hUopen, hsU, ?_, ?_⟩
  · exact ((numberFieldIncompleteZetaNormalized_differentiableOn K S).mono
      (fun z hz => (hUsub hz).1.1)).div
        ((numberFieldIncompleteZetaNormalized_differentiableOn L T).mono
          (fun z hz => (hUsub hz).1.2))
        (fun z hz => (hUsub hz).2.2)
  · exact fun z hz => div_ne_zero (hUsub hz).2.1 (hUsub hz).2.2

theorem numberFieldIncompleteZeta_differentiableAt (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (numberFieldIncompleteZeta K S) s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h => by simp [h] at hs)
  have hd := (numberFieldIncompleteZetaNormalized_differentiableAt K S hs.le).div
    (differentiableAt_id.sub_const 1) hsub
  have heq : (fun z => numberFieldIncompleteZetaNormalized K S z / (z - 1)) =ᶠ[𝓝 s]
      numberFieldIncompleteZeta K S :=
    eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
      (fun z hz => by
        change numberFieldIncompleteZetaNormalized K S z / (z - 1) =
          numberFieldIncompleteZeta K S z
        rw [numberFieldIncompleteZetaNormalized_eq K S hz]
        exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr (fun h => by simp [h] at hz)))
  exact hd.congr_of_eventuallyEq heq.symm

/-- The logarithmic derivative of the actual quotient is exactly the
difference of the actual deleted-zeta logarithmic derivatives. -/
theorem numberFieldIncompleteZetaQuotient_logDeriv_eq (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset (HeightOneSpectrum (𝓞 L))) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (numberFieldIncompleteZetaQuotient K L S T) s =
      logDeriv (numberFieldIncompleteZeta K S) s - logDeriv (numberFieldIncompleteZeta L T) s := by
  have heq : numberFieldIncompleteZetaQuotient K L S T =ᶠ[𝓝 s]
      (fun z => numberFieldIncompleteZeta K S z / numberFieldIncompleteZeta L T z) :=
    eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
      (fun _ hz => numberFieldIncompleteZetaQuotient_eq K L S T hz)
  rw [(logDeriv_congr_nhds heq).eq_of_nhds]
  exact logDeriv_div s (numberFieldIncompleteZeta_ne_zero K S hs)
    (numberFieldIncompleteZeta_ne_zero L T hs)
    (numberFieldIncompleteZeta_differentiableAt K S hs)
    (numberFieldIncompleteZeta_differentiableAt L T hs)

/-- The common pole has canceled also in the logarithmic derivative,
which has a continuous extension on the entire closed boundary. -/
theorem numberFieldIncompleteZetaQuotient_logDeriv_continuousOn (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ContinuousOn (logDeriv (numberFieldIncompleteZetaQuotient K L S T)) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  obtain ⟨U, hUopen, hsU, hdU, _⟩ :=
    numberFieldIncompleteZetaQuotient_exists_neighborhood K L S T hs
  have hderiv : ContinuousAt (deriv (numberFieldIncompleteZetaQuotient K L S T)) s :=
    (hdU.deriv hUopen).continuousOn.continuousAt (hUopen.mem_nhds hsU)
  exact (hderiv.div
    (numberFieldIncompleteZetaQuotient_differentiableAt K L S T hs).continuousAt
    (numberFieldIncompleteZetaQuotient_ne_zero K L S T hs)).continuousWithinAt

end
end SimultaneousPrimitiveRoots
