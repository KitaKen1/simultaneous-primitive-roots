module

public import SimultaneousPrimitiveRoots.Hecke.DedekindEntire

/-!
# The value of the entire function `(s - 1) ζ_K(s)` at `s = 1`

By continuity and Mathlib's class number formula (`tendsto_sub_one_mul_dedekindZeta_nhdsGT`), the
entire continuation of `(s - 1) ζ_K(s)` takes the value `dedekindZeta_residue K > 0` at `s = 1`.
So `ζ_K` has a simple pole at `s = 1` with nonzero residue — the main term of the explicit formula.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Filter Topology

variable (K : Type*) [Field K] [NumberField K]

theorem dedekindZetaEntire_one :
    dedekindZetaEntire K 1 = (dedekindZeta_residue K : ℂ) := by
  have hcont : Continuous (dedekindZetaEntire K) := (differentiable_dedekindZetaEntire K).continuous
  have h1 : Tendsto (fun s : ℝ => dedekindZetaEntire K s) (𝓝[>] 1)
      (𝓝 (dedekindZetaEntire K 1)) := by
    have := (hcont.tendsto ((1 : ℝ) : ℂ)).comp
      ((Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ))))
    simp only [Complex.ofReal_one] at this
    exact this
  have h2 : Tendsto (fun s : ℝ => dedekindZetaEntire K s) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
    refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < (s : ℂ).re := by simpa using hs
    have hs0 : (s : ℂ) ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hs'
      linarith
    have hs1 : (s : ℂ) ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hs'
      linarith
    rw [dedekindZetaEntire_eq K hs0 hs1, dedekindZetaHecke_eq K hs']
  exact tendsto_nhds_unique h1 h2

theorem dedekindZetaEntire_one_ne_zero : dedekindZetaEntire K 1 ≠ 0 := by
  rw [dedekindZetaEntire_one]
  exact_mod_cast dedekindZeta_residue_ne_zero K

/-- **`ζ_K` has a simple pole at `1`**: the entire continuation of `(s - 1) ζ_K(s)` is nonzero at
`s = 1`, with value the class number formula residue. -/
theorem exists_entire_sub_one_mul_dedekindZeta_residue :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ s, 1 < s.re → F s = (s - 1) * dedekindZeta K s) ∧
      F 1 = (dedekindZeta_residue K : ℂ) :=
  ⟨dedekindZetaEntire K, differentiable_dedekindZetaEntire K, fun s hs => by
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hs
      linarith
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hs
      linarith
    rw [dedekindZetaEntire_eq K hs0 hs1, dedekindZetaHecke_eq K hs],
    dedekindZetaEntire_one K⟩

end SimultaneousPrimitiveRoots.Hecke

end
