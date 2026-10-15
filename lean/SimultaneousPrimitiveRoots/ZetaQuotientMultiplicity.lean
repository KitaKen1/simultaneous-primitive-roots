module

public import SimultaneousPrimitiveRoots.ZetaQuotientZeroOrder
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Filter Metric
open scoped Topology
noncomputable section
open Classical

/-- This is an input about an actual extension, not about the arbitrary values
of the existing local normalized-zeta model outside its known domain. -/
def NumberFieldFullQuotientContinuation (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (H : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ H {s : ℂ | 0 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → H s = numberFieldNormalizedZeta K s / numberFieldNormalizedZeta L s

/-- A natural multiplicity is legitimate only after finite analytic order has
been proved. The toNat value at infinite order is never used as that proof. -/
def fullQuotientZeroMultiplicity (H : ℂ → ℂ) (s : ℂ) : ℕ :=
  (analyticOrderAt H s).toNat

theorem numberFieldFullQuotientContinuation_ne_zero_two (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H) : H 2 ≠ 0 := by
  rw [hH.2 2 (by norm_num)]
  exact div_ne_zero (numberFieldNormalizedZeta_ne_zero K (by norm_num))
    (numberFieldNormalizedZeta_ne_zero L (by norm_num))

theorem numberFieldFullQuotientContinuation_analyticOrderAt_ne_top (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H)
    {s : ℂ} (hs : 0 < s.re) : analyticOrderAt H s ≠ ⊤ := by
  have htwo : analyticOrderAt H (2 : ℂ) = 0 :=
    (hH.1 2 (by norm_num)).analyticOrderAt_eq_zero.mpr
      (numberFieldFullQuotientContinuation_ne_zero_two K L hH)
  exact hH.1.analyticOrderAt_ne_top_of_isPreconnected (x := (2 : ℂ))
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num) hs
    (by rw [htwo]; simp)

theorem numberFieldFullQuotientContinuation_order_eq_nat (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H)
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt H s = ((fullQuotientZeroMultiplicity H s : ℕ) : WithTop ℤ) := by
  have hn := ENat.natCast_toNat
    (numberFieldFullQuotientContinuation_analyticOrderAt_ne_top K L hH hs)
  rw [(hH.1 s hs).meromorphicOrderAt_eq, ← hn]
  simp [fullQuotientZeroMultiplicity]

theorem numberFieldFullQuotientContinuation_multiplicity_zero_iff (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H)
    {s : ℂ} (hs : 0 < s.re) :
    fullQuotientZeroMultiplicity H s = 0 ↔ H s ≠ 0 := by
  have hn := ENat.natCast_toNat
    (numberFieldFullQuotientContinuation_analyticOrderAt_ne_top K L hH hs)
  have hz : analyticOrderAt H s = 0 ↔ (analyticOrderAt H s).toNat = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; rw [← hn, h]; rfl
  exact hz.symm.trans (hH.1 s hs).analyticOrderAt_eq_zero

theorem numberFieldFullQuotientContinuation_multiplicity_pos_iff (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H)
    {s : ℂ} (hs : 0 < s.re) :
    0 < fullQuotientZeroMultiplicity H s ↔ H s = 0 := by
  simpa only [Nat.pos_iff_ne_zero, not_not] using
    not_congr (numberFieldFullQuotientContinuation_multiplicity_zero_iff K L hH hs)

theorem numberFieldFullQuotientContinuation_deleted_order_eq_nat (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H)
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (fun z => numberFieldDeletedQuotientCorrection K L S T z * H z) s =
      ((fullQuotientZeroMultiplicity H s : ℕ) : WithTop ℤ) := by
  rw [numberFieldDeletedQuotientCorrection_mul_order K L S T H hs]
  exact numberFieldFullQuotientContinuation_order_eq_nat K L hH hs

theorem numberFieldFullQuotientContinuation_deleted_matches (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H)
    {s : ℂ} (hs : 1 < s.re) :
    numberFieldDeletedQuotientCorrection K L S T s * H s =
      numberFieldIncompleteZetaQuotient K L S T s := by
  rw [hH.2 s hs, numberFieldIncompleteZetaQuotient_eq_correction_mul_full]

theorem numberFieldFullQuotientContinuation_divisor_eq_nat (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H)
    {V : Set ℂ} (hV : V ⊆ {s : ℂ | 0 < s.re}) {s : ℂ} (hs : s ∈ V) :
    MeromorphicOn.divisor H V s = (fullQuotientZeroMultiplicity H s : ℤ) := by
  rw [(hH.1.mono hV).meromorphicOn.divisor_apply hs,
    numberFieldFullQuotientContinuation_order_eq_nat K L hH (hV hs)]
  simp

/-- This is a finite zero carrier, including every zero, since infinite order
was excluded using actual nonvanishing at two and connectedness. -/
theorem numberFieldFullQuotientContinuation_finite_zeros_compact (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H)
    {V : Set ℂ} (hV : V ⊆ {s : ℂ | 0 < s.re}) (hc : IsCompact V) :
    {s : ℂ | s ∈ V ∧ H s = 0}.Finite := by
  apply ((MeromorphicOn.divisor H V).finiteSupport hc).subset
  intro s hs
  rw [Function.mem_support, numberFieldFullQuotientContinuation_divisor_eq_nat K L hH hV hs.1]
  have hp := (numberFieldFullQuotientContinuation_multiplicity_pos_iff K L hH (hV hs.1)).mpr hs.2
  exact_mod_cast hp.ne'

/-- The global input for the Aramata--Brauer route. Its existence is not
proved by defining this interface or by the consequences below. -/
def NumberFieldEntireFullQuotientContinuation (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (H : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ H Set.univ ∧
    ∀ s : ℂ, 1 < s.re → H s = numberFieldNormalizedZeta K s / numberFieldNormalizedZeta L s

theorem numberFieldEntireFullQuotientContinuation_positive (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) :
    NumberFieldFullQuotientContinuation K L H :=
  ⟨hH.1.mono (Set.subset_univ _), hH.2⟩

theorem numberFieldEntireFullQuotientContinuation_analyticOrderAt_ne_top (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (s : ℂ) :
    analyticOrderAt H s ≠ ⊤ := by
  have htwo : analyticOrderAt H (2 : ℂ) = 0 :=
    (hH.1 2 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr
      (numberFieldFullQuotientContinuation_ne_zero_two K L
        (numberFieldEntireFullQuotientContinuation_positive K L hH))
  exact hH.1.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ _) (by rw [htwo]; simp)

theorem numberFieldEntireFullQuotientContinuation_order_eq_nat (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (s : ℂ) :
    meromorphicOrderAt H s = ((fullQuotientZeroMultiplicity H s : ℕ) : WithTop ℤ) := by
  have hn := ENat.natCast_toNat
    (numberFieldEntireFullQuotientContinuation_analyticOrderAt_ne_top K L hH s)
  rw [(hH.1 s (Set.mem_univ _)).meromorphicOrderAt_eq, ← hn]
  simp [fullQuotientZeroMultiplicity]

theorem numberFieldEntireFullQuotientContinuation_multiplicity_zero_iff (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (s : ℂ) :
    fullQuotientZeroMultiplicity H s = 0 ↔ H s ≠ 0 := by
  have hn := ENat.natCast_toNat
    (numberFieldEntireFullQuotientContinuation_analyticOrderAt_ne_top K L hH s)
  have hz : analyticOrderAt H s = 0 ↔ (analyticOrderAt H s).toNat = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; rw [← hn, h]; rfl
  exact hz.symm.trans (hH.1 s (Set.mem_univ _)).analyticOrderAt_eq_zero

theorem numberFieldEntireFullQuotientContinuation_multiplicity_pos_iff (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (s : ℂ) :
    0 < fullQuotientZeroMultiplicity H s ↔ H s = 0 := by
  simpa only [Nat.pos_iff_ne_zero, not_not] using
    not_congr (numberFieldEntireFullQuotientContinuation_multiplicity_zero_iff K L hH s)

theorem numberFieldEntireFullQuotientContinuation_divisor_eq_nat (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    (V : Set ℂ) {s : ℂ} (hs : s ∈ V) :
    MeromorphicOn.divisor H V s = (fullQuotientZeroMultiplicity H s : ℤ) := by
  rw [(hH.1.mono (Set.subset_univ V)).meromorphicOn.divisor_apply hs,
    numberFieldEntireFullQuotientContinuation_order_eq_nat K L hH s]
  simp

theorem numberFieldEntireFullQuotientContinuation_finite_zeros_compact (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {V : Set ℂ} (hc : IsCompact V) : {s : ℂ | s ∈ V ∧ H s = 0}.Finite := by
  apply ((MeromorphicOn.divisor H V).finiteSupport hc).subset
  intro s hs
  rw [Function.mem_support, numberFieldEntireFullQuotientContinuation_divisor_eq_nat K L hH V hs.1]
  have hp := (numberFieldEntireFullQuotientContinuation_multiplicity_pos_iff K L hH s).mpr hs.2
  exact_mod_cast hp.ne'

theorem numberFieldEntireFullQuotientContinuation_countable_zeros (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) :
    {s : ℂ | H s = 0}.Countable := by
  apply ((HereditarilyLindelofSpace.isLindelof
    (MeromorphicOn.divisor H Set.univ).support).countable_of_isDiscrete
      (MeromorphicOn.divisor H Set.univ).discreteSupport).mono
  intro s hs
  rw [Function.mem_support,
    numberFieldEntireFullQuotientContinuation_divisor_eq_nat K L hH Set.univ (Set.mem_univ s)]
  have hp := (numberFieldEntireFullQuotientContinuation_multiplicity_pos_iff K L hH s).mpr hs
  exact_mod_cast hp.ne'

/-- Each actual zero in the closed critical strip has precisely its natural
multiplicity many labels. Trivial zeros outside the strip must not be included
in the Gaussian imaginary-height mass. -/
def fullQuotientZeroIndex (H : ℂ → ℂ) :=
  Σ s : {s : ℂ // 0 ≤ s.re ∧ s.re ≤ 1 ∧ H s = 0}, Fin (fullQuotientZeroMultiplicity H s)

def fullQuotientIndexedZero (H : ℂ → ℂ) (i : fullQuotientZeroIndex H) : ℂ := i.1

theorem fullQuotientIndexedZero_is_zero (H : ℂ → ℂ) (i : fullQuotientZeroIndex H) :
    H (fullQuotientIndexedZero H i) = 0 := i.1.property.2.2

theorem fullQuotientIndexedZero_strip (H : ℂ → ℂ) (i : fullQuotientZeroIndex H) :
    0 ≤ (fullQuotientIndexedZero H i).re ∧ (fullQuotientIndexedZero H i).re ≤ 1 :=
  ⟨i.1.property.1, i.1.property.2.1⟩

theorem numberFieldEntireFullQuotientContinuation_countable_zeroIndex (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) :
    Countable (fullQuotientZeroIndex H) := by
  have hc : {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ H s = 0}.Countable :=
    (numberFieldEntireFullQuotientContinuation_countable_zeros K L hH).mono
      (fun _ hs => hs.2.2)
  let : Countable {s : ℂ // 0 ≤ s.re ∧ s.re ≤ 1 ∧ H s = 0} := hc.to_subtype
  unfold fullQuotientZeroIndex
  infer_instance

/-- Jensen bounds actual natural zero multiplicities; it still requires the
boundary norm bound M, and does not supply a uniform family zero mass. -/
theorem numberFieldEntireFullQuotientContinuation_jensen_multiplicity_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) |R|, ‖H z‖ ≤ M) :
    (((∑ᶠ s : ℂ, if s ∈ closedBall (2 : ℂ) |r|
      then (fullQuotientZeroMultiplicity H s : ℤ) else 0) : ℤ) : ℝ) ≤
        Real.log (M / ‖H 2‖) / Real.log (R / r) := by
  have heq : (MeromorphicOn.divisor H (closedBall (2 : ℂ) |r|) : ℂ → ℤ) =
      fun s => if s ∈ closedBall (2 : ℂ) |r| then (fullQuotientZeroMultiplicity H s : ℤ) else 0 := by
    funext s
    by_cases hs : s ∈ closedBall (2 : ℂ) |r|
    · rw [if_pos hs, numberFieldEntireFullQuotientContinuation_divisor_eq_nat K L hH _ hs]
    · simp [hs]
  simpa only [heq] using (hH.1.mono (Set.subset_univ _)).sum_divisor_le hr hrR hM
    (numberFieldFullQuotientContinuation_ne_zero_two K L
      (numberFieldEntireFullQuotientContinuation_positive K L hH)) hb

end
end SimultaneousPrimitiveRoots
