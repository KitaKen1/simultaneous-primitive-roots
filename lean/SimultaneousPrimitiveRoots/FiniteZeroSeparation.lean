module

public import SimultaneousPrimitiveRoots.KummerQuotientContourChoice
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Set Metric MeasureTheory Classical
noncomputable section

/-- A finite family of short forbidden intervals cannot cover a longer interval.
This gives a quantitative gap, not just a point outside a countable set. -/
theorem exists_interval_separated_from_finset {S : Finset ℝ} {a b ε : ℝ}
    (hε : 0 ≤ ε) (hwidth : 2 * ε * (S.card : ℝ) < b - a) :
    ∃ t : ℝ, a < t ∧ t < b ∧ ∀ r ∈ S, ε ≤ |t - r| := by
  by_contra! hn
  have hsub : Ioo a b ⊆ ⋃ r ∈ S, Ioo (r - ε) (r + ε) := by
    intro t ht
    obtain ⟨r, hr, hrt⟩ := hn t ht.1 ht.2
    refine mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, ?_⟩⟩
    exact ⟨by linarith [(abs_lt.mp hrt).1], by linarith [(abs_lt.mp hrt).2]⟩
  have hm := (measure_mono hsub).trans
    (measure_biUnion_finset_le (μ := volume) S (fun r => Ioo (r - ε) (r + ε)))
  have heq : (∑ r ∈ S, volume (Ioo (r - ε) (r + ε))) =
      ENNReal.ofReal (2 * ε * (S.card : ℝ)) := by
    simp only [Real.volume_Ioo, show ∀ r : ℝ, r + ε - (r - ε) = 2 * ε by intro r; ring]
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
    congr 1
    ring
  rw [Real.volume_Ioo, heq] at hm
  have hp : 0 ≤ 2 * ε * (S.card : ℝ) := by positivity
  exact not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < b - a)).mpr hwidth) hm

/-- An explicit gap for any finite set, including the empty set. -/
theorem exists_interval_separated_finset_gap {S : Finset ℝ} {a b : ℝ} (hab : a < b) :
    ∃ t : ℝ, a < t ∧ t < b ∧
      ∀ r ∈ S, (b - a) / (4 * ((S.card : ℝ) + 1)) ≤ |t - r| := by
  have hd : 0 < 4 * ((S.card : ℝ) + 1) := by positivity
  apply exists_interval_separated_from_finset (by positivity)
  have heq : 2 * ((b - a) / (4 * ((S.card : ℝ) + 1))) * (S.card : ℝ) =
      (2 * (b - a) * (S.card : ℝ)) / (4 * ((S.card : ℝ) + 1)) := by ring
  rw [heq, div_lt_iff₀ hd]
  nlinarith

/-- Quantitatively avoid the heights of every actual zero in a specified compact
set. Zeros outside that set are not silently covered by this conclusion. -/
theorem numberFieldEntireFullQuotientContinuation_exists_separated_height
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
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
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
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

/-- The same height gap controls both horizontal edges in the complex plane. -/
theorem abs_height_difference_le_complex_distance (s ρ : ℂ) :
    |(|s.im|) - (|ρ.im|)| ≤ ‖s - ρ‖ := by
  exact (abs_abs_sub_abs_le_abs_sub s.im ρ.im).trans
    (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (s - ρ))

end
end SimultaneousPrimitiveRoots
