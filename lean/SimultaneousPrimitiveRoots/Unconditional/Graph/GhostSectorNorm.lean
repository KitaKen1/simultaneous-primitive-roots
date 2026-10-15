module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostSectorRowBounds
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostKernelMaps
public import SimultaneousPrimitiveRoots.Unconditional.Graph.FiniteWeightedSchur
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complex L2 bound of an actual finite ghost sector

The row/column conditions are proved for the actual counting kernel. Positive
prime masses allow its conversion to the original factorial measured kernel.
The signed real kernel acts on complex tests, and its symmetric action equals
the original complex ghost row. This is one k/a/b sector, not the sum of all
sectors, a tensor product estimate, or an infinite Fock operator theorem.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P Z : Type*} {R : P → Type*} {k a b n : ℕ}

theorem factorial_memory_point_mass_pos (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (x : Fin n → Z) : 0 < factorialMemoryPointMass w x := by
  unfold factorialMemoryPointMass
  exact div_pos (Finset.prod_pos (fun i _ => hw (x i))) (by exact_mod_cast Nat.factorial_pos n)

/-- The real signed counting kernel represents the original complex row on symmetric tests. -/
theorem finite_ghost_sector_real_complex_row [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ)
    (g : (Fin (k + b) → Σ p, R p) → ℂ)
    (hg : ∀ (σ : Equiv.Perm (Fin (k + b))) y, g (y ∘ σ) = g y)
    (x : Fin (k + a) → Σ p, R p) :
    finiteGhostSectorRow (fun p => (ν p : ℂ)) (A : ℂ) (D : ℂ) (C : ℂ) g x =
      ∑ y : Fin (k + b) → Σ p, R p,
        ((finiteGhostSectorCountingKernel ν A D C x y : ℝ) : ℂ) * g y := by
  classical
  have hm (y : Fin (k + b) → Σ p, R p) :=
    finite_ghost_sector_counting_kernel_map Complex.ofRealHom ν A D C x y
  simp only [Function.comp_def, Complex.ofRealHom_eq_coe] at hm
  have h := finite_ghost_sector_counting_kernel_reproduces (fun p => (ν p : ℂ))
    (A : ℂ) (D : ℂ) (C : ℂ) g hg x
  simp_rw [← hm] at h
  exact h.symm

/-- The actual signed counting sector has a uniform complex squared L2 bound.
The positivity of the prime masses is explicit; all factorial masses are retained. -/
theorem finite_ghost_sector_projected_complex_sq_bound [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : (Fin (k + b) → Σ p, R p) → ℂ) :
    (∑ x : Fin (k + a) → Σ p, R p,
      factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        ‖∑ y : Fin (k + b) → Σ p, R p,
          ((finiteGhostSectorCountingKernel ν A D C x y : ℝ) : ℂ) * g y‖ ^ 2) ≤
    Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) *
      ∑ y : Fin (k + b) → Σ p, R p,
        factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) y * ‖g y‖ ^ 2 := by
  classical
  let μ : (Fin (k + a) → Σ p, R p) → ℝ :=
    factorialMemoryPointMass (fun z : Σ p, R p => ν z.1)
  let τ : (Fin (k + b) → Σ p, R p) → ℝ :=
    factorialMemoryPointMass (fun z : Σ p, R p => ν z.1)
  have hμ (x) : 0 < μ x := factorial_memory_point_mass_pos _ (fun z => hν z.1) x
  have hτ (y) : 0 < τ y := factorial_memory_point_mass_pos _ (fun z => hν z.1) y
  have hν0 : ∀ p, 0 ≤ ν p := fun p => (hν p).le
  have hrow (x : Fin (k + a) → Σ p, R p) :
      (∑ y : Fin (k + b) → Σ p, R p,
        (finiteGhostSectorCountingKernel ν A |D| |C| x y / τ y) * τ y * v ^ (k + b)) ≤
      Real.exp (cmax * v * Mmax) * v ^ (k + a) := by
    simp_rw [div_mul_cancel₀ _ (hτ _).ne']
    have h := finite_ghost_sector_counting_kernel_weighted_row_le_uniform_exp (b := b)
      ν A D C v cmax Mmax hν0 hA hv hbaseD hC hM x
    rw [← Finset.sum_div] at h
    exact (div_le_iff₀ (pow_pos hv _)).mp h
  have hcol (y : Fin (k + b) → Σ p, R p) :
      (∑ x : Fin (k + a) → Σ p, R p,
        (finiteGhostSectorCountingKernel ν A |D| |C| x y / τ y) * μ x * v ^ (k + a)) ≤
      Real.exp (dmax * v * Mmax) * v ^ (k + b) := by
    have h := finite_ghost_sector_counting_kernel_weighted_column_le_uniform_exp (a := a)
      ν A D C v dmax Mmax hν0 hA hv hbaseC hD hM y
    rw [← Finset.sum_div] at h
    have ht := (div_le_iff₀ (pow_pos hv (k + b))).mp h
    calc
      _ = (∑ x : Fin (k + a) → Σ p, R p,
          μ x * finiteGhostSectorCountingKernel ν A |D| |C| x y * v ^ (k + a)) / τ y := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ _ := (div_le_iff₀ (hτ y)).mpr (by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using ht)
  have hB (x : Fin (k + a) → Σ p, R p) (y : Fin (k + b) → Σ p, R p) :
      ‖((finiteGhostSectorCountingKernel ν A D C x y / τ y : ℝ) : ℂ)‖ ≤
        finiteGhostSectorCountingKernel ν A |D| |C| x y / τ y := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (hτ y).le,
      finite_ghost_sector_counting_kernel_abs ν A D C hν0 hA]
  have hs := finite_complex_weighted_schur
    (fun x y => ((finiteGhostSectorCountingKernel ν A D C x y / τ y : ℝ) : ℂ))
    (fun x y => finiteGhostSectorCountingKernel ν A |D| |C| x y / τ y)
    μ τ (fun _ => v ^ (k + a)) (fun _ => v ^ (k + b))
    (Real.exp (cmax * v * Mmax)) (Real.exp (dmax * v * Mmax)) hB
    (fun x y => div_nonneg
      (finite_ghost_sector_counting_kernel_nonneg ν A |D| |C| hν0 hA
        (abs_nonneg D) (abs_nonneg C) x y) (hτ y).le)
    (fun x => (hμ x).le) (fun y => (hτ y).le)
    (fun _ => pow_pos hv _) (fun _ => pow_pos hv _)
    (Real.exp_pos _).le (Real.exp_pos _).le hrow hcol g
  have hc (x : Fin (k + a) → Σ p, R p) (y : Fin (k + b) → Σ p, R p) :
      ((finiteGhostSectorCountingKernel ν A D C x y / τ y : ℝ) : ℂ) * (τ y : ℂ) =
        ((finiteGhostSectorCountingKernel ν A D C x y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (hτ y).ne']
  simp_rw [hc] at hs
  exact hs

/-- The uniform bound applies to the original complex finite ghost row on the symmetric Fock sector. -/
theorem finite_ghost_sector_actual_complex_sq_bound [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : (Fin (k + b) → Σ p, R p) → ℂ)
    (hg : ∀ (σ : Equiv.Perm (Fin (k + b))) y, g (y ∘ σ) = g y) :
    (∑ x : Fin (k + a) → Σ p, R p,
      factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        ‖finiteGhostSectorRow (fun p => (ν p : ℂ)) (A : ℂ) (D : ℂ) (C : ℂ) g x‖ ^ 2) ≤
    Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) *
      ∑ y : Fin (k + b) → Σ p, R p,
        factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) y * ‖g y‖ ^ 2 := by
  simp_rw [finite_ghost_sector_real_complex_row ν A D C g hg]
  exact finite_ghost_sector_projected_complex_sq_bound ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM g

end SimultaneousPrimitiveRoots.Unconditional.Graph
