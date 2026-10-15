module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostTruncatedRows
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostTruncatedMaps
import Mathlib.Tactic.Ring

/-!
# Complex L2 bound for the complete finite ghost memory cutoff

All degrees up to N and all their admissible survivor sectors are included.
The actual full row and column conditions give a constant independent of N.
The original complex Fock row and factorial counting measure are retained.
The pure-ghost infinite-space completion is constructed in GhostContinuousOperator.
Unbounded row/joint interchanges, arithmetic coefficient bounds and tensor
products remain separate obligations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P : Type*} {R : P → Type*}

theorem finite_ghost_truncated_real_complex_row [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ) (N : ℕ)
    (g : FiniteMemory N (Σ p, R p) → ℂ)
    (hg : ∀ (n : Fin (N + 1)) (σ : Equiv.Perm (Fin n.val)) y,
      g ⟨n, y ∘ σ⟩ = g ⟨n, y⟩) (x : FiniteMemory N (Σ p, R p)) :
    finiteGhostTruncatedRow (fun p => (ν p : ℂ)) (A : ℂ) (D : ℂ) (C : ℂ) N g x =
      ∑ y : FiniteMemory N (Σ p, R p),
        ((finiteGhostTruncatedKernel ν A D C N x y : ℝ) : ℂ) * g y := by
  classical
  have hm (y : FiniteMemory N (Σ p, R p)) :=
    finite_ghost_truncated_kernel_map Complex.ofRealHom ν A D C N x y
  simp only [Function.comp_def, Complex.ofRealHom_eq_coe] at hm
  have h := finite_ghost_truncated_kernel_reproduces (fun p => (ν p : ℂ))
    (A : ℂ) (D : ℂ) (C : ℂ) N g hg x
  simp_rw [← hm] at h
  exact h.symm

/-- The complete signed finite kernel has a complex squared L2 bound independent of N. -/
theorem finite_ghost_truncated_projected_complex_sq_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) (N : ℕ)
    (g : FiniteMemory N (Σ p, R p) → ℂ) :
    (∑ x : FiniteMemory N (Σ p, R p),
      finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        ‖∑ y : FiniteMemory N (Σ p, R p),
          ((finiteGhostTruncatedKernel ν A D C N x y : ℝ) : ℂ) * g y‖ ^ 2) ≤
    Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) *
      ∑ y : FiniteMemory N (Σ p, R p),
        finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) y * ‖g y‖ ^ 2 := by
  classical
  let μ : FiniteMemory N (Σ p, R p) → ℝ :=
    finiteMemoryPointMass (fun z : Σ p, R p => ν z.1)
  have hμ (x) : 0 < μ x := finite_memory_point_mass_pos _ (fun z => hν z.1) x
  have hν0 : ∀ p, 0 ≤ ν p := fun p => (hν p).le
  have hrow (x : FiniteMemory N (Σ p, R p)) :
      (∑ y : FiniteMemory N (Σ p, R p),
        (finiteGhostTruncatedKernel ν A |D| |C| N x y / μ y) * μ y * v ^ y.1.val) ≤
      Real.exp (cmax * v * Mmax) * v ^ x.1.val := by
    simp_rw [div_mul_cancel₀ _ (hμ _).ne']
    have h := finite_ghost_truncated_kernel_weighted_row_le_uniform_exp
      ν A D C v cmax Mmax hν0 hA hv hbaseD hC hM N x
    rw [← Finset.sum_div] at h
    exact (div_le_iff₀ (pow_pos hv _)).mp h
  have hcol (y : FiniteMemory N (Σ p, R p)) :
      (∑ x : FiniteMemory N (Σ p, R p),
        (finiteGhostTruncatedKernel ν A |D| |C| N x y / μ y) * μ x * v ^ x.1.val) ≤
      Real.exp (dmax * v * Mmax) * v ^ y.1.val := by
    have h := finite_ghost_truncated_kernel_weighted_column_le_uniform_exp
      ν A D C v dmax Mmax hν0 hA hv hbaseC hD hM N y
    rw [← Finset.sum_div] at h
    have ht := (div_le_iff₀ (pow_pos hv y.1.val)).mp h
    calc
      _ = (∑ x : FiniteMemory N (Σ p, R p),
          μ x * finiteGhostTruncatedKernel ν A |D| |C| N x y * v ^ x.1.val) / μ y := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ _ := (div_le_iff₀ (hμ y)).mpr (by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using ht)
  have hB (x y : FiniteMemory N (Σ p, R p)) :
      ‖((finiteGhostTruncatedKernel ν A D C N x y / μ y : ℝ) : ℂ)‖ ≤
        finiteGhostTruncatedKernel ν A |D| |C| N x y / μ y := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (hμ y).le]
    exact div_le_div_of_nonneg_right
      (finite_ghost_truncated_kernel_abs_le ν A D C hν0 hA N x y) (hμ y).le
  have hs := finite_complex_weighted_schur
    (fun x y => ((finiteGhostTruncatedKernel ν A D C N x y / μ y : ℝ) : ℂ))
    (fun x y => finiteGhostTruncatedKernel ν A |D| |C| N x y / μ y)
    μ μ (fun x => v ^ x.1.val) (fun y => v ^ y.1.val)
    (Real.exp (cmax * v * Mmax)) (Real.exp (dmax * v * Mmax)) hB
    (fun x y => div_nonneg
      (finite_ghost_truncated_kernel_nonneg ν A |D| |C| hν0 hA
        (abs_nonneg D) (abs_nonneg C) N x y) (hμ y).le)
    (fun x => (hμ x).le) (fun y => (hμ y).le)
    (fun x => pow_pos hv x.1.val) (fun y => pow_pos hv y.1.val)
    (Real.exp_pos _).le (Real.exp_pos _).le hrow hcol g
  have hc (x y : FiniteMemory N (Σ p, R p)) :
      ((finiteGhostTruncatedKernel ν A D C N x y / μ y : ℝ) : ℂ) * (μ y : ℂ) =
        ((finiteGhostTruncatedKernel ν A D C N x y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (hμ y).ne']
  simp_rw [hc] at hs
  exact hs

/-- The uniform complete-cutoff estimate holds for the original complex symmetric Fock row. -/
theorem finite_ghost_truncated_actual_complex_sq_bound [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) (N : ℕ)
    (g : FiniteMemory N (Σ p, R p) → ℂ)
    (hg : ∀ (n : Fin (N + 1)) (σ : Equiv.Perm (Fin n.val)) y,
      g ⟨n, y ∘ σ⟩ = g ⟨n, y⟩) :
    (∑ x : FiniteMemory N (Σ p, R p),
      finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        ‖finiteGhostTruncatedRow (fun p => (ν p : ℂ)) (A : ℂ) (D : ℂ) (C : ℂ) N g x‖ ^ 2) ≤
    Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) *
      ∑ y : FiniteMemory N (Σ p, R p),
        finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) y * ‖g y‖ ^ 2 := by
  simp_rw [finite_ghost_truncated_real_complex_row ν A D C N g hg]
  exact finite_ghost_truncated_projected_complex_sq_bound ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM N g

end SimultaneousPrimitiveRoots.Unconditional.Graph
