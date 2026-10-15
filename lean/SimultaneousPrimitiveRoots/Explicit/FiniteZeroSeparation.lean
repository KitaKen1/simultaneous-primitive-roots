module

public import SimultaneousPrimitiveRoots.FiniteZeroSeparation
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.GaussianZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLogResidue
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientContourChoice

/-! Generalization of `SimultaneousPrimitiveRoots.FiniteZeroSeparation` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open Set Metric MeasureTheory Classical
noncomputable section

/-- Quantitatively avoid the heights of every actual zero in a specified compact
set. Zeros outside that set are not silently covered by this conclusion. -/
theorem numberFieldEntireFullQuotientContinuation_exists_separated_height
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {V : Set ℂ} (hV : IsCompact V) (N : ℝ) :
    ∃ T ε : ℝ, N < T ∧ T < N + 1 ∧ 0 < ε ∧
      ∀ ρ ∈ V, H ρ = 0 → ε ≤ |T - (|ρ.im|)| := by
  let F := (numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH hV).toFinset
  let S := F.image (fun ρ : ℂ => |ρ.im|)
  obtain ⟨T, hNT, hTN, hsep⟩ := exists_interval_separated_finset_gap
    (S := S) (show N < N + 1 by linarith)
  refine ⟨T, 1 / (4 * ((S.card : ℝ) + 1)), hNT, hTN, by positivity, ?_⟩
  intro ρ hρ hn
  have hm : |ρ.im| ∈ S := Finset.mem_image.mpr ⟨ρ,
    (numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH hV).mem_toFinset.mpr ⟨hρ, hn⟩, rfl⟩
  simpa only [add_sub_cancel_left] using hsep (|ρ.im|) hm

/-- The gap depends explicitly on the number of distinct actual zeros. Taking
an image of their heights can only reduce the number of forbidden intervals. -/
theorem numberFieldEntireFullQuotientContinuation_exists_height_card_gap
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {V : Set ℂ} (hV : IsCompact V) (N : ℝ) :
    let F := (numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH hV).toFinset
    ∃ T : ℝ, N < T ∧ T < N + 1 ∧
      ∀ ρ ∈ V, H ρ = 0 → 1 / (4 * ((F.card : ℝ) + 1)) ≤ |T - (|ρ.im|)| := by
  let F := (numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH hV).toFinset
  let S := F.image (fun ρ : ℂ => |ρ.im|)
  obtain ⟨T, hNT, hTN, hsep⟩ := exists_interval_separated_finset_gap
    (S := S) (show N < N + 1 by linarith)
  refine ⟨T, hNT, hTN, ?_⟩
  intro ρ hρ hn
  have hm : |ρ.im| ∈ S := Finset.mem_image.mpr ⟨ρ,
    (numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH hV).mem_toFinset.mpr ⟨hρ, hn⟩, rfl⟩
  have hcard : (S.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_image_le
  have hh : 1 / (4 * ((S.card : ℝ) + 1)) ≤ |T - (|ρ.im|)| := by
    simpa only [add_sub_cancel_left] using hsep (|ρ.im|) hm
  exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans hh

end
end SimultaneousPrimitiveRoots.Explicit
