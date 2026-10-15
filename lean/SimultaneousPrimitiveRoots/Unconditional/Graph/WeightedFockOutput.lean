module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostInfiniteSupportNorm
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Original factorial-weighted Fock output as an ell-two element

Multiplication by the square root of the original point mass identifies the
weighted square sum with the counting ell-two norm. The infinite-output
action of a finite-support input therefore belongs to the actual ell-two
space. WeightedFockInput and GhostContinuousOperator separately construct the
dense-domain continuous extension.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped ENNReal

variable {Z P : Type*} {R : P → Type*}

noncomputable def weightedMemoryCoordinates (w : Z → ℝ)
    (f : InfiniteMemory Z → ℂ) (x : InfiniteMemory Z) : ℂ :=
  (Real.sqrt (infiniteMemoryPointMass w x) : ℂ) * f x

theorem weighted_memory_coordinates_norm_sq (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (f : InfiniteMemory Z → ℂ) (x : InfiniteMemory Z) :
    ‖weightedMemoryCoordinates w f x‖ ^ 2 = infiniteMemoryPointMass w x * ‖f x‖ ^ 2 := by
  unfold weightedMemoryCoordinates
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (infinite_memory_point_mass_pos w hw x).le]

theorem infinite_ghost_finite_support_weighted_mem_lp [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) :
    Memℓp (weightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostFiniteSupportAction ν A D C g)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  have h := infinite_ghost_finite_support_sq_summable ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM g
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    weighted_memory_coordinates_norm_sq _ (fun z : Σ p, R p => hν z.1)] using h

noncomputable def infiniteGhostFiniteSupportLpOutput [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) :
    lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2 :=
  ⟨weightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostFiniteSupportAction ν A D C g),
    infinite_ghost_finite_support_weighted_mem_lp ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g⟩

theorem infinite_ghost_finite_support_lp_output_norm_sq_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) :
    ‖infiniteGhostFiniteSupportLpOutput ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g‖ ^ 2 ≤
    Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) *
      ∑ y ∈ g.support, infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) y * ‖g y‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (infiniteGhostFiniteSupportLpOutput ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  change ‖infiniteGhostFiniteSupportLpOutput ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM g‖ ^ 2 =
    ∑' x, ‖weightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostFiniteSupportAction ν A D C g) x‖ ^ 2 at h
  simp_rw [weighted_memory_coordinates_norm_sq _ (fun z : Σ p, R p => hν z.1)] at h
  rw [h]
  exact infinite_ghost_finite_support_tsum_sq_bound ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM g

end SimultaneousPrimitiveRoots.Unconditional.Graph
