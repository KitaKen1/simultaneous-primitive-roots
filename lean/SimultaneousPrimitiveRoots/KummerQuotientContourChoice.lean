module

public import SimultaneousPrimitiveRoots.KummerQuotientLogResidue
public import PNTAnd.Rectangle
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Filter Metric
open scoped Topology
noncomputable section
open Classical

theorem exists_real_interval_avoiding_countable {S : Set ℝ} (hS : S.Countable)
    {a b : ℝ} (hab : a < b) : ∃ t, a < t ∧ t < b ∧ t ∉ S := by
  obtain ⟨t, htS, htab⟩ := (hS.dense_compl ℝ).exists_mem_open isOpen_Ioo
    (Set.nonempty_Ioo.mpr hab)
  exact ⟨t, htab.1, htab.2, htS⟩

/-- Choose a vertical line avoiding every actual zero, not only zeros in one finite box. -/
theorem numberFieldEntireFullQuotientContinuation_exists_zero_free_vertical
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {a b : ℝ} (hab : a < b) :
    ∃ σ : ℝ, a < σ ∧ σ < b ∧ ∀ s : ℂ, s.re = σ → H s ≠ 0 := by
  have hc := (numberFieldEntireFullQuotientContinuation_countable_zeros K L hH).image Complex.re
  obtain ⟨σ, ha, hb, hs⟩ := exists_real_interval_avoiding_countable hc hab
  refine ⟨σ, ha, hb, ?_⟩
  intro s hre hz
  exact hs ⟨s, hz, hre⟩

/-- Arbitrarily large symmetric horizontal edges avoid all actual zeros. -/
theorem numberFieldEntireFullQuotientContinuation_exists_zero_free_height
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (N : ℝ) :
    ∃ T : ℝ, N < T ∧ T < N + 1 ∧ ∀ s : ℂ, |s.im| = T → H s ≠ 0 := by
  have hc := (numberFieldEntireFullQuotientContinuation_countable_zeros K L hH).image
    (fun s : ℂ => |s.im|)
  obtain ⟨T, ha, hb, hs⟩ := exists_real_interval_avoiding_countable hc (a := N) (b := N + 1) (by linarith)
  refine ⟨T, ha, hb, ?_⟩
  intro s him hz
  exact hs ⟨s, hz, him⟩

/-- One fixed negative vertical line and arbitrarily high zero-free rectangles.
No quantitative logarithmic-derivative bound on the selected edges is asserted. -/
theorem numberFieldEntireFullQuotientContinuation_exists_zero_free_rectangles
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) :
    ∃ σ : ℝ, -1 < σ ∧ σ < -(1 / 2 : ℝ) ∧ ∀ N : ℝ, 0 ≤ N →
      ∃ T : ℝ, N < T ∧ T < N + 1 ∧
        ∀ s ∈ PNTAnd.RectangleBorder ((σ : ℂ) - Complex.I * T)
          ((2 : ℂ) + Complex.I * T), H s ≠ 0 := by
  obtain ⟨σ, hσl, hσr, hσ⟩ :=
    numberFieldEntireFullQuotientContinuation_exists_zero_free_vertical K L hH
      (show (-1 : ℝ) < -(1 / 2 : ℝ) by norm_num)
  refine ⟨σ, hσl, hσr, ?_⟩
  intro N hN
  obtain ⟨T, hNT, hT, hheight⟩ :=
    numberFieldEntireFullQuotientContinuation_exists_zero_free_height K L hH N
  have hT0 : 0 < T := hN.trans_lt hNT
  refine ⟨T, hNT, hT, ?_⟩
  intro s hs
  simp only [PNTAnd.RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
    Set.mem_singleton_iff, Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] at hs
  rcases hs with ((hs | hs) | hs) | hs
  · apply hheight s
    have him : s.im = -T := by simpa using hs.2
    rw [him, abs_neg, abs_of_pos hT0]
  · apply hσ s
    simpa using hs.1
  · apply hheight s
    have him : s.im = T := by simpa using hs.2
    rw [him, abs_of_pos hT0]
  · exact numberFieldEntireFullQuotientContinuation_boundary_ne_zero K L hH (by
      have hre : s.re = 2 := by simpa using hs.1
      rw [hre]
      norm_num)

end
end SimultaneousPrimitiveRoots
