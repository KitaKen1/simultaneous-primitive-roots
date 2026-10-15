module

public import SimultaneousPrimitiveRoots.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData

/-! Generalization of `SimultaneousPrimitiveRoots.ZetaQuotientMultiplicity` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField IsDedekindDomain Filter Metric
open scoped Topology
noncomputable section
open Classical

theorem numberFieldEntireFullQuotientContinuation_analyticOrderAt_ne_top (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (s : ℂ) :
    analyticOrderAt H s ≠ ⊤ := by
  have htwo : analyticOrderAt H (2 : ℂ) = 0 :=
    (hH.1 2 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr
      (numberFieldFullQuotientContinuation_ne_zero_two K L
        (numberFieldEntireFullQuotientContinuation_positive K L hH))
  exact hH.1.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ _) (by rw [htwo]; simp)

theorem numberFieldEntireFullQuotientContinuation_order_eq_nat (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (s : ℂ) :
    meromorphicOrderAt H s = ((fullQuotientZeroMultiplicity H s : ℕ) : WithTop ℤ) := by
  have hn := ENat.natCast_toNat
    (numberFieldEntireFullQuotientContinuation_analyticOrderAt_ne_top K L hH s)
  rw [(hH.1 s (Set.mem_univ _)).meromorphicOrderAt_eq, ← hn]
  simp [fullQuotientZeroMultiplicity]

theorem numberFieldEntireFullQuotientContinuation_multiplicity_zero_iff (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (s : ℂ) :
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
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (s : ℂ) :
    0 < fullQuotientZeroMultiplicity H s ↔ H s = 0 := by
  simpa only [Nat.pos_iff_ne_zero, not_not] using
    not_congr (numberFieldEntireFullQuotientContinuation_multiplicity_zero_iff K L hH s)

theorem numberFieldEntireFullQuotientContinuation_divisor_eq_nat (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    (V : Set ℂ) {s : ℂ} (hs : s ∈ V) :
    MeromorphicOn.divisor H V s = (fullQuotientZeroMultiplicity H s : ℤ) := by
  rw [(hH.1.mono (Set.subset_univ V)).meromorphicOn.divisor_apply hs,
    numberFieldEntireFullQuotientContinuation_order_eq_nat K L hH s]
  simp

theorem numberFieldEntireFullQuotientContinuation_finite_zeros_compact (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {V : Set ℂ} (hc : IsCompact V) : {s : ℂ | s ∈ V ∧ H s = 0}.Finite := by
  apply ((MeromorphicOn.divisor H V).finiteSupport hc).subset
  intro s hs
  rw [Function.mem_support, numberFieldEntireFullQuotientContinuation_divisor_eq_nat K L hH V hs.1]
  have hp := (numberFieldEntireFullQuotientContinuation_multiplicity_pos_iff K L hH s).mpr hs.2
  exact_mod_cast hp.ne'

theorem numberFieldEntireFullQuotientContinuation_countable_zeros (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) :
    {s : ℂ | H s = 0}.Countable := by
  apply ((HereditarilyLindelofSpace.isLindelof
    (MeromorphicOn.divisor H Set.univ).support).countable_of_isDiscrete
      (MeromorphicOn.divisor H Set.univ).discreteSupport).mono
  intro s hs
  rw [Function.mem_support,
    numberFieldEntireFullQuotientContinuation_divisor_eq_nat K L hH Set.univ (Set.mem_univ s)]
  have hp := (numberFieldEntireFullQuotientContinuation_multiplicity_pos_iff K L hH s).mpr hs
  exact_mod_cast hp.ne'

theorem numberFieldEntireFullQuotientContinuation_countable_zeroIndex (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) :
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
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
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
end SimultaneousPrimitiveRoots.Explicit
