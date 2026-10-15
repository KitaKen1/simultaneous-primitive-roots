module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostWeightedDomain
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Continuous completion of the pure ghost action in original weighted coordinates

The finite-support domain is dense after its proved square-root factorial
mass embedding. The original ghost action therefore has a unique bounded
continuous extension to counting ell-two in those coordinates, with the
same norm constant. Agreement with every finite-support input and the
original symmetric finite row is explicit. General-input single rows and the reversed bounded adjoint are certified
separately. Flat joint-sum interchange, arithmetic uniformity and full
conditional transference remain separate obligations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P : Type*} {R : P → Type*}

noncomputable def infiniteGhostContinuousOperator [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) :
    lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2 →L[ℂ]
      lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2 :=
  (infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM).extendOfNorm
      (weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1))

theorem infinite_ghost_continuous_operator_on_finite_support [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) :
    infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM
        (weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1) g) =
    infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g := by
  exact LinearMap.extendOfNorm_eq
    (f := infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM)
    (e := weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1))
    (weighted_memory_input_dense _ (fun z : Σ p, R p => hν z.1))
    ⟨_, infinite_ghost_weighted_domain_norm_bound ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM⟩ g

theorem infinite_ghost_continuous_operator_norm_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    ‖infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f‖ ≤
    Real.sqrt (Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax)) * ‖f‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le
    (f := infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM)
    (e := weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1))
    (weighted_memory_input_dense _ (fun z : Σ p, R p => hν z.1)) _
    (infinite_ghost_weighted_domain_norm_bound ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM) f

theorem infinite_ghost_continuous_operator_opnorm_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) :
    ‖infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM‖ ≤
    Real.sqrt (Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax)) := by
  apply ContinuousLinearMap.opNorm_le_bound
    (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM) (Real.sqrt_nonneg _)
  exact infinite_ghost_continuous_operator_norm_bound ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM

theorem infinite_ghost_continuous_operator_coordinates [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) (x : InfiniteMemory (Σ p, R p)) :
    infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM
        (weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1) g) x =
    weightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostFiniteSupportAction ν A D C g) x := by
  rw [infinite_ghost_continuous_operator_on_finite_support]
  rfl

theorem infinite_ghost_continuous_operator_unique [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (T : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2 →L[ℂ]
      lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (hT : T.toLinearMap.comp (weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1)) =
      infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
        hν hA hv hbaseD hbaseC hC hD hM) :
    infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM = T := by
  exact LinearMap.extendOfNorm_unique
    (f := infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM)
    (e := weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1))
    (weighted_memory_input_dense _ (fun z : Σ p, R p => hν z.1)) _
    (infinite_ghost_weighted_domain_norm_bound ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM) T hT

theorem infinite_ghost_continuous_operator_actual_row [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) (N : ℕ)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) (hs : ∀ y ∈ g.support, y.1 ≤ N)
    (hg : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) y, g ⟨n, y ∘ σ⟩ = g ⟨n, y⟩)
    (x : FiniteMemory N (Σ p, R p)) :
    infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM
        (weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1) g) (finiteMemoryToInfinite x) =
    (Real.sqrt (finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) x) : ℂ) *
      finiteGhostTruncatedRow (fun p => (ν p : ℂ)) (A : ℂ) (D : ℂ) (C : ℂ) N
        (fun y => g (finiteMemoryToInfinite y)) x := by
  rw [infinite_ghost_continuous_operator_coordinates]
  unfold weightedMemoryCoordinates
  rw [infinite_memory_point_mass_cutoff,
    infinite_ghost_finite_support_actual_row_cutoff ν A D C N g hs hg x]

end SimultaneousPrimitiveRoots.Unconditional.Graph
