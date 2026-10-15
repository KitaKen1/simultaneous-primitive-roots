module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostAbsoluteJoint
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostDegreeJoint
import Lean.Elab.Tactic.Omega

/-!
# Absolute summability before collapsing survivor sectors

At each memory pair the survivor sum is finite, and its sum of absolute
terms is exactly the positive-coefficient counting-kernel joint norm.
Nonnegative Tonelli and the bounded positive completion therefore certify
absolute summability over memory pairs and survivor counts together.
This permits the survivor expansion before any degree-sector reindexing.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ComplexInnerProductSpace

variable {P : Type*} {R : P → Type*}

noncomputable def infiniteGhostSurvivorJoint [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (f g : InfiniteMemory (Σ p, R p) → ℂ)
    (x y : InfiniteMemory (Σ p, R p)) (k : ℕ) : ℂ :=
  ((infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x : ℝ) : ℂ) *
    star (g x) * ((finiteGhostDegreeKernel ν A D C k x.1 y.1 x.2 y.2 : ℝ) : ℂ) * f y

theorem real_weighted_ghost_pair_norm (w a : ℝ) (hw : 0 ≤ w) (g f : ℂ) :
    ‖(w : ℂ) * star g * (a : ℂ) * f‖ = w * ‖g‖ * |a| * ‖f‖ := by
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]

theorem infinite_ghost_survivor_joint_outside [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (f g : InfiniteMemory (Σ p, R p) → ℂ)
    (x y : InfiniteMemory (Σ p, R p)) (k : ℕ)
    (hk : k ∉ Finset.range (min x.1 y.1 + 1)) :
    infiniteGhostSurvivorJoint ν A D C f g x y k = 0 := by
  have hnot : ¬ (k ≤ x.1 ∧ k ≤ y.1) := by
    intro h
    exact hk (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min h.1 h.2)))
  unfold infiniteGhostSurvivorJoint
  rw [finite_ghost_degree_kernel_inadmissible ν A D C k _ _ hnot]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul]

theorem infinite_ghost_survivor_joint_summable [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (f g : InfiniteMemory (Σ p, R p) → ℂ)
    (x y : InfiniteMemory (Σ p, R p)) :
    Summable (infiniteGhostSurvivorJoint ν A D C f g x y) :=
  summable_of_ne_finset_zero (s := Finset.range (min x.1 y.1 + 1))
    (infinite_ghost_survivor_joint_outside ν A D C f g x y)

theorem infinite_ghost_survivor_joint_norm_summable [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (f g : InfiniteMemory (Σ p, R p) → ℂ)
    (x y : InfiniteMemory (Σ p, R p)) :
    Summable (fun k => ‖infiniteGhostSurvivorJoint ν A D C f g x y k‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range (min x.1 y.1 + 1))
  intro k hk
  rw [infinite_ghost_survivor_joint_outside ν A D C f g x y k hk, norm_zero]

theorem infinite_ghost_survivor_joint_tsum [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (f g : InfiniteMemory (Σ p, R p) → ℂ)
    (x y : InfiniteMemory (Σ p, R p)) :
    (∑' k, infiniteGhostSurvivorJoint ν A D C f g x y k) =
    ((infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x : ℝ) : ℂ) *
      star (g x) * ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) * f y := by
  classical
  rw [tsum_eq_sum (s := Finset.range (min x.1 y.1 + 1))
    (infinite_ghost_survivor_joint_outside ν A D C f g x y)]
  unfold infiniteGhostSurvivorJoint infiniteGhostKernel
  simp only [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]

theorem infinite_ghost_survivor_absolute_total [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (hν : ∀ p, 0 < ν p) (A D C : ℝ) (hA : 0 ≤ A)
    (f g : InfiniteMemory (Σ p, R p) → ℂ) (x y : InfiniteMemory (Σ p, R p)) :
    (∑' k, ‖infiniteGhostSurvivorJoint ν A D C f g x y k‖) =
    ‖((infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x : ℝ) : ℂ) *
      star (g x) * ((infiniteGhostKernel ν A |D| |C| x y : ℝ) : ℂ) * f y‖ := by
  classical
  have hμ : 0 ≤ infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x :=
    (infinite_memory_point_mass_pos _ (fun z => hν z.1) x).le
  rw [tsum_eq_sum (s := Finset.range (min x.1 y.1 + 1)) (fun k hk => by
    rw [infinite_ghost_survivor_joint_outside ν A D C f g x y k hk, norm_zero])]
  simp only [infiniteGhostSurvivorJoint, real_weighted_ghost_pair_norm _ _ hμ]
  simp only [finite_ghost_degree_kernel_abs ν A D C (fun p => (hν p).le) hA]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [abs_of_nonneg (infinite_ghost_kernel_nonneg ν A |D| |C|
    (fun p => (hν p).le) hA (abs_nonneg _) (abs_nonneg _) x y)]
  rfl

section Bounded

variable [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)

include v cmax dmax Mmax hν hA hv hbaseD hbaseC hC hD hM

theorem infinite_ghost_expanded_joint_norm_summable
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    Summable (fun z : (InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p)) × ℕ =>
      ‖infiniteGhostSurvivorJoint ν A D C
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f)
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g)
        z.1.1 z.1.2 z.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro z
    exact infinite_ghost_survivor_joint_norm_summable ν A D C _ _ z.1 z.2
  · simpa only [infinite_ghost_survivor_absolute_total ν hν A D C hA] using
      infinite_ghost_original_joint_norm_summable ν A |D| |C| v cmax dmax Mmax
        hν hA hv (by simpa only [abs_abs] using hbaseD)
        (by simpa only [abs_abs] using hbaseC)
        (by simpa only [abs_abs] using hC) (by simpa only [abs_abs] using hD) hM f g

theorem infinite_ghost_expanded_flat_joint_pairing
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    (∑' z : (InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p)) × ℕ,
      infiniteGhostSurvivorJoint ν A D C
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f)
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g)
        z.1.1 z.1.2 z.2) =
    inner ℂ g (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f) := by
  rw [(infinite_ghost_expanded_joint_norm_summable ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f g).of_norm.tsum_prod]
  simp only [infinite_ghost_survivor_joint_tsum]
  exact infinite_ghost_original_flat_joint_pairing ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f g

theorem infinite_ghost_expanded_absolute_joint_bound
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    (∑' z : (InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p)) × ℕ,
      ‖infiniteGhostSurvivorJoint ν A D C
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f)
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g)
        z.1.1 z.1.2 z.2‖) ≤
    ‖g‖ * Real.sqrt (Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax)) * ‖f‖ := by
  rw [(infinite_ghost_expanded_joint_norm_summable ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f g).tsum_prod]
  simp only [infinite_ghost_survivor_absolute_total ν hν A D C hA]
  exact infinite_ghost_original_absolute_joint_bound ν A |D| |C| v cmax dmax Mmax
    hν hA hv (by simpa only [abs_abs] using hbaseD)
    (by simpa only [abs_abs] using hbaseC)
    (by simpa only [abs_abs] using hC) (by simpa only [abs_abs] using hD) hM f g

end Bounded

end SimultaneousPrimitiveRoots.Unconditional.Graph
