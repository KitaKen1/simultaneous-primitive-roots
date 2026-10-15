module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostGeneralRows

/-!
# Actual positive majorant on unrestricted memory pairs

Both endpoint degrees fit a common certified cutoff. Positivity and absolute
domination therefore pass to the unchanged infinite counting kernel. Original
sqrt-factorial normalization preserves that domination.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

variable {P : Type*} {R : P → Type*}

theorem infinite_ghost_kernel_nonneg [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (hν : ∀ p, 0 ≤ ν p)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (x y : InfiniteMemory (Σ p, R p)) : 0 ≤ infiniteGhostKernel ν A D C x y := by
  rcases x with ⟨n, x⟩
  rcases y with ⟨m, y⟩
  exact finite_ghost_truncated_kernel_nonneg ν A D C hν hA hD hC (max n m)
    ⟨⟨n, by omega⟩, x⟩ ⟨⟨m, by omega⟩, y⟩

theorem infinite_ghost_kernel_abs_le [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A)
    (x y : InfiniteMemory (Σ p, R p)) :
    |infiniteGhostKernel ν A D C x y| ≤ infiniteGhostKernel ν A |D| |C| x y := by
  rcases x with ⟨n, x⟩
  rcases y with ⟨m, y⟩
  exact finite_ghost_truncated_kernel_abs_le ν A D C hν hA (max n m)
    ⟨⟨n, by omega⟩, x⟩ ⟨⟨m, by omega⟩, y⟩

theorem normalized_infinite_ghost_kernel_norm_majorant [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (hν : ∀ p, 0 < ν p) (A D C : ℝ) (hA : 0 ≤ A)
    (x y : InfiniteMemory (Σ p, R p)) :
    ‖normalizedInfiniteGhostKernel ν A D C x y‖ ≤
      (normalizedInfiniteGhostKernel ν A |D| |C| x y).re := by
  unfold normalizedInfiniteGhostKernel
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_eq_abs, Complex.ofReal_re, abs_div, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (infinite_ghost_kernel_abs_le ν A D C (fun p => (hν p).le) hA x y)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end SimultaneousPrimitiveRoots.Unconditional.Graph
