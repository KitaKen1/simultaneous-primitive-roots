module

public import SimultaneousPrimitiveRoots.ComplexPlaceHaar
public import SimultaneousPrimitiveRoots.FiniteLogNormSheet
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

def artinComplexLogNorm (z : ℂˣ) : ℝ := 2 * Real.log ‖(z : ℂ)‖

theorem artinComplexLogNorm_mul (z v : ℂˣ) :
    artinComplexLogNorm (z * v) = artinComplexLogNorm z + artinComplexLogNorm v := by
  simp only [artinComplexLogNorm, Units.val_mul, norm_mul]
  rw [Real.log_mul (norm_ne_zero_iff.mpr z.ne_zero) (norm_ne_zero_iff.mpr v.ne_zero)]
  ring

theorem artinComplexLogNorm_polar (x : ℝ) (θ : Circle) :
    artinComplexLogNorm (artinComplexPolarUnit (Multiplicative.ofAdd x, θ)) = x := by
  rw [artinComplexLogNorm, artinComplexPolarUnit_norm, toAdd_ofAdd, Real.log_exp]
  ring

theorem artinComplexUnitAngle_polar (x : ℝ) (θ : Circle) :
    artinComplexUnitAngle (artinComplexPolarUnit (Multiplicative.ofAdd x, θ)) = θ :=
  congrArg Prod.snd (artinComplexPolarUnit_left_inv (Multiplicative.ofAdd x, θ))

theorem artinComplexLogNorm_exp (z : ℂˣ) :
    Real.exp (artinComplexLogNorm z) = ‖(z : ℂ)‖ ^ 2 := by
  rw [artinComplexLogNorm, two_mul, Real.exp_add,
    Real.exp_log (norm_pos_iff.mpr z.ne_zero), ← pow_two]

theorem artinComplexLogNorm_continuous : Continuous artinComplexLogNorm :=
  continuous_const.mul (Units.continuous_val.norm.log
    (fun z => norm_ne_zero_iff.mpr z.ne_zero))

/-- The actual product-norm-one subgroup of r=n+1 complex multiplicative groups. -/
def artinComplexNormKernel (n : ℕ) : Subgroup (Fin (n + 1) → ℂˣ) where
  carrier := {z | (∏ i, ‖(z i : ℂ)‖ ^ 2) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro z v hz hv
    simp only [Set.mem_ofPred_eq] at hz hv ⊢
    simp only [Pi.mul_apply, Units.val_mul, norm_mul, mul_pow, Finset.prod_mul_distrib, hz, hv,
      one_mul]
  inv_mem' := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, inv_pow, Finset.prod_inv_distrib, hz,
      inv_one]

theorem artinComplexNormKernel_isClosed (n : ℕ) :
    IsClosed (artinComplexNormKernel n : Set (Fin (n + 1) → ℂˣ)) := by
  apply isClosed_eq _ continuous_const
  exact continuous_finsetProd _ (fun i _ =>
    ((Units.continuous_val.comp (continuous_apply i)).norm.pow 2))

theorem artinComplexNormKernel_log_sum {n : ℕ} (z : artinComplexNormKernel n) :
    (∑ i, artinComplexLogNorm (z.1 i)) = 0 := by
  apply Real.exp_injective
  rw [Real.exp_sum]
  simp_rw [artinComplexLogNorm_exp]
  exact z.2.trans (Real.exp_zero.symm)

/-- Actual complex points on a log-norm sheet; angle coordinates are independent. -/
def artinComplexNormPoint (n : ℕ) (w : ℝ)
    (p : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle)) : Fin (n + 1) → ℂˣ :=
  fun i => artinComplexPolarUnit
    (Multiplicative.ofAdd (Fin.cons (α := fun _ => ℝ) (w - ∑ j, Multiplicative.toAdd p.1 j)
      (Multiplicative.toAdd p.1) i), p.2 i)

theorem artinComplexNormPoint_norm_sq (n : ℕ) (w : ℝ)
    (p : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle)) (i : Fin (n + 1)) :
    ‖(artinComplexNormPoint n w p i : ℂ)‖ ^ 2 =
      Real.exp (artinFiniteLogNormSheetEquiv n (w, Multiplicative.toAdd p.1) i) := by
  rw [artinComplexNormPoint, artinComplexPolarUnit_norm_sq, toAdd_ofAdd,
    artinFiniteLogNormSheet_coordinates]

theorem artinComplexNormPoint_product (n : ℕ) (w : ℝ)
    (p : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle)) :
    (∏ i, ‖(artinComplexNormPoint n w p i : ℂ)‖ ^ 2) = Real.exp w := by
  simp_rw [artinComplexNormPoint_norm_sq]
  rw [← Real.exp_sum, artinFiniteLogNormSheet_total]

theorem artinComplexNormPoint_mul (n : ℕ) (w v : ℝ)
    (p q : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle)) :
    artinComplexNormPoint n (w + v) (p * q) =
      artinComplexNormPoint n w p * artinComplexNormPoint n v q := by
  funext i
  unfold artinComplexNormPoint
  simp only [Pi.mul_apply]
  rw [← artinComplexPolarUnit_mul]
  congr 1
  apply Prod.ext
  · change Fin.cons (α := fun _ => ℝ)
      (w + v - ∑ j, (Multiplicative.toAdd p.1 j + Multiplicative.toAdd q.1 j))
      (fun j => Multiplicative.toAdd p.1 j + Multiplicative.toAdd q.1 j) i =
      Fin.cons (α := fun _ => ℝ)
        (w - ∑ j, Multiplicative.toAdd p.1 j) (Multiplicative.toAdd p.1) i +
        Fin.cons (α := fun _ => ℝ)
          (v - ∑ j, Multiplicative.toAdd q.1 j) (Multiplicative.toAdd q.1) i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Finset.sum_add_distrib]
      ring
    · simp
  · rfl

theorem artinComplexNormPoint_continuous (n : ℕ) (w : ℝ) :
    Continuous (artinComplexNormPoint n w) := by
  have hx : Continuous (fun p : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle) =>
      Multiplicative.toAdd p.1) := continuous_toAdd.comp continuous_fst
  have hsum : Continuous (fun p : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle) =>
      ∑ j, Multiplicative.toAdd p.1 j) :=
    continuous_finsetSum _ (fun j _ => (continuous_apply j).comp hx)
  apply continuous_pi
  intro i
  unfold artinComplexNormPoint
  apply artinComplexPolarUnit_continuous.comp
  apply Continuous.prodMk
  · apply continuous_ofAdd.comp
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const.sub hsum
    · exact (continuous_apply j).comp hx
  · exact (continuous_apply i).comp continuous_snd

def artinComplexNormKernelPoint (n : ℕ)
    (p : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle)) : artinComplexNormKernel n :=
  ⟨artinComplexNormPoint n 0 p, by
    change (∏ i, ‖(artinComplexNormPoint n 0 p i : ℂ)‖ ^ 2) = 1
    rw [artinComplexNormPoint_product, Real.exp_zero]⟩

def artinComplexNormKernelInverse (n : ℕ) (z : artinComplexNormKernel n) :
    Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle) :=
  (Multiplicative.ofAdd (fun j => artinComplexLogNorm (z.1 j.succ)),
    fun i => artinComplexUnitAngle (z.1 i))

theorem artinComplexNormKernelPoint_left_inv (n : ℕ)
    (p : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle)) :
    artinComplexNormKernelInverse n (artinComplexNormKernelPoint n p) = p := by
  apply Prod.ext
  · change Multiplicative.ofAdd (fun j => artinComplexLogNorm
      (artinComplexNormPoint n 0 p j.succ)) = p.1
    change (fun j => artinComplexLogNorm (artinComplexNormPoint n 0 p j.succ)) =
      Multiplicative.toAdd p.1
    funext j
    simp only [artinComplexNormPoint, Fin.cons_succ, artinComplexLogNorm_polar]
  · funext i
    exact artinComplexUnitAngle_polar _ _

theorem artinComplexNormKernelPoint_right_inv (n : ℕ) (z : artinComplexNormKernel n) :
    artinComplexNormKernelPoint n (artinComplexNormKernelInverse n z) = z := by
  apply Subtype.ext
  funext i
  have hs := artinComplexNormKernel_log_sum z
  rw [Fin.sum_univ_succ] at hs
  have h0 : (0 : ℝ) - ∑ j : Fin n, artinComplexLogNorm (z.1 j.succ) =
      artinComplexLogNorm (z.1 0) := by linarith
  change artinComplexNormPoint n 0 (artinComplexNormKernelInverse n z) i = z.1 i
  refine Fin.cases ?_ (fun j => ?_) i
  · change artinComplexPolarUnit (Multiplicative.ofAdd
      (0 - ∑ j : Fin n, artinComplexLogNorm (z.1 j.succ)), artinComplexUnitAngle (z.1 0)) = _
    rw [h0]
    exact artinComplexPolarUnit_right_inv _
  · exact artinComplexPolarUnit_right_inv _

/-- The actual norm-one subgroup has r-1 real log coordinates and r compact angles. -/
def artinComplexNormKernelCoordinates (n : ℕ) :
    (Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle)) ≃ₜ* artinComplexNormKernel n where
  toFun := artinComplexNormKernelPoint n
  invFun := artinComplexNormKernelInverse n
  left_inv := artinComplexNormKernelPoint_left_inv n
  right_inv := artinComplexNormKernelPoint_right_inv n
  map_mul' p q := by
    apply Subtype.ext
    change artinComplexNormPoint n 0 (p * q) =
      artinComplexNormPoint n 0 p * artinComplexNormPoint n 0 q
    simpa only [zero_add] using artinComplexNormPoint_mul n 0 0 p q
  continuous_toFun := (artinComplexNormPoint_continuous n 0).subtype_mk _
  continuous_invFun :=
    (continuous_ofAdd.comp (continuous_pi (fun j => artinComplexLogNorm_continuous.comp
      ((continuous_apply j.succ).comp continuous_subtype_val)))).prodMk
        (continuous_pi (fun i => artinComplexUnitAngle_continuous.comp
          ((continuous_apply i).comp continuous_subtype_val)))

def artinComplexNormSection (n : ℕ) (u : ℝ) : Fin (n + 1) → ℂˣ :=
  artinComplexNormPoint n (Real.log u) 1

theorem artinComplexNormSection_product (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (∏ i, ‖(artinComplexNormSection n u i : ℂ)‖ ^ 2) = u := by
  rw [artinComplexNormSection, artinComplexNormPoint_product, Real.exp_log hu]

theorem artinComplexNormSection_mul (n : ℕ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    artinComplexNormSection n (u * v) = artinComplexNormSection n u * artinComplexNormSection n v := by
  rw [artinComplexNormSection, Real.log_mul hu.ne' hv.ne']
  simpa only [one_mul, artinComplexNormSection] using
    artinComplexNormPoint_mul n (Real.log u) (Real.log v) 1 1

theorem artinComplexNormPoint_transport (n : ℕ) (u : ℝ)
    (p : Multiplicative (Fin n → ℝ) × (Fin (n + 1) → Circle)) :
    artinComplexNormPoint n (Real.log u) p =
      artinComplexNormSection n u * (artinComplexNormKernelCoordinates n p : Fin (n + 1) → ℂˣ) := by
  change artinComplexNormPoint n (Real.log u) p =
    artinComplexNormPoint n (Real.log u) 1 * artinComplexNormPoint n 0 p
  simpa only [add_zero, one_mul] using artinComplexNormPoint_mul n (Real.log u) 0 1 p

end
end SimultaneousPrimitiveRoots
