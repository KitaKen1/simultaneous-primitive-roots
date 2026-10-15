module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Leaves
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The frame operator of an almost orthonormal family

Source: `verification/stage7-sources/S-03.tex`, lines 241–256 (`[S-03:0241–0256]`),
(eq:ideal-frame) and (eq:ideal-gram-bound).

`gramFrameBound : GramFrameBound` (`Comparison/Leaves.lean`): if finitely many functions `φ_i` of
`L²(X, w)`, `w ≥ 0`, have `‖φ_i‖ ≤ 1` and `|⟨φ_i, φ_j⟩| ≤ ε` for `i ≠ j`, then
`‖∑_i φ_i ⟨φ_i, f⟩‖ ≤ (1 + N ε) ‖f‖`.

Proof. Put `c_i = ⟨φ_i, f⟩` and `F = ∑_i c_i φ_i`.

* `Gram.wNormSq_comb_le`: `‖F‖² = ∑_{i,j} conj(c_i) c_j ⟨φ_i, φ_j⟩ ≤ (1 + N ε) ∑_i |c_i|²`, for
  arbitrary coefficients `c` (the Schur test on the Gram matrix: the row `i` contributes at most
  `|c_i| (|c_i| + ε ∑_j |c_j|)`, and `(∑_j |c_j|)² ≤ N ∑_j |c_j|²`).
* `Gram.wInner_frame_eq`: `∑_i |c_i|² = ⟨F, f⟩`, which is at most `‖F‖ ‖f‖`
  (`Gram.norm_wInner_sq_le`).
* `Gram.sqrt_le_of_frame`: `A ≤ κ S` and `S² ≤ A B` give `√A ≤ κ √B`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Gram

variable {X : Type*} [Fintype X] {ι : Type*} [Fintype ι]

/-- Cauchy–Schwarz for the inner product of `L²(X, w)`, `w ≥ 0`. -/
theorem norm_wInner_sq_le {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (a b : X → ℂ) :
    ‖wInner w a b‖ ^ 2 ≤ wNormSq w a * wNormSq w b := by
  have h1 : ‖wInner w a b‖ ≤ ∑ x, (Real.sqrt (w x) * ‖a x‖) * (Real.sqrt (w x) * ‖b x‖) := by
    unfold wInner
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg (hw x), Complex.norm_conj]
    calc w x * (‖a x‖ * ‖b x‖)
        = (Real.sqrt (w x) * Real.sqrt (w x)) * (‖a x‖ * ‖b x‖) := by
          rw [Real.mul_self_sqrt (hw x)]
      _ = (Real.sqrt (w x) * ‖a x‖) * (Real.sqrt (w x) * ‖b x‖) := by ring
  have h2 : (∑ x, (Real.sqrt (w x) * ‖a x‖) * (Real.sqrt (w x) * ‖b x‖)) ^ 2 ≤
      (∑ x, (Real.sqrt (w x) * ‖a x‖) ^ 2) * ∑ x, (Real.sqrt (w x) * ‖b x‖) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have h3 : ∀ d : X → ℂ, ∑ x, (Real.sqrt (w x) * ‖d x‖) ^ 2 = ∑ x, w x * ‖d x‖ ^ 2 :=
    fun d => Finset.sum_congr rfl fun x _ => by rw [mul_pow, Real.sq_sqrt (hw x)]
  rw [h3 a, h3 b] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- The inner product is conjugate-linear in the first argument. -/
theorem wInner_sum_left (w : X → ℝ) (φ : ι → X → ℂ) (c : ι → ℂ) (g : X → ℂ) :
    wInner w (fun x => ∑ i, φ i x * c i) g = ∑ i, conj (c i) * wInner w (φ i) g := by
  have h : ∀ x : X, (w x : ℂ) * (conj (∑ i, φ i x * c i) * g x) =
      ∑ i, conj (c i) * ((w x : ℂ) * (conj (φ i x) * g x)) := by
    intro x
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    ring
  unfold wInner
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- The inner product is linear in the second argument. -/
theorem wInner_sum_right (w : X → ℝ) (g : X → ℂ) (φ : ι → X → ℂ) (c : ι → ℂ) :
    wInner w g (fun x => ∑ i, φ i x * c i) = ∑ i, c i * wInner w g (φ i) := by
  have h : ∀ x : X, (w x : ℂ) * (conj (g x) * ∑ i, φ i x * c i) =
      ∑ i, c i * ((w x : ℂ) * (conj (g x) * φ i x)) := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold wInner
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- `‖∑_i c_i φ_i‖² = ∑_{i,j} conj(c_i) c_j ⟨φ_i, φ_j⟩`. -/
theorem wNormSq_comb_eq (w : X → ℝ) (φ : ι → X → ℂ) (c : ι → ℂ) :
    ((wNormSq w (fun x => ∑ i, φ i x * c i) : ℝ) : ℂ) =
      ∑ i, conj (c i) * ∑ j, c j * wInner w (φ i) (φ j) := by
  rw [← wInner_self, wInner_sum_left w φ c]
  exact Finset.sum_congr rfl fun i _ => by rw [wInner_sum_right w (φ i) φ c]

/-- **The Gram matrix bound** (eq:ideal-gram-bound): for arbitrary coefficients,
`‖∑_i c_i φ_i‖² ≤ (1 + N ε) ∑_i |c_i|²`. -/
theorem wNormSq_comb_le {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (φ : ι → X → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i, wNormSq w (φ i) ≤ 1)
    (hoff : ∀ i j, i ≠ j → ‖wInner w (φ i) (φ j)‖ ≤ ε) (c : ι → ℂ) :
    wNormSq w (fun x => ∑ i, φ i x * c i) ≤
      (1 + (Fintype.card ι : ℝ) * ε) * ∑ i, ‖c i‖ ^ 2 := by
  classical
  -- the norm of the double sum
  have hnorm : wNormSq w (fun x => ∑ i, φ i x * c i) ≤
      ∑ i, ‖c i‖ * ∑ j, ‖c j‖ * ‖wInner w (φ i) (φ j)‖ := by
    have h0 : wNormSq w (fun x => ∑ i, φ i x * c i) =
        ‖((wNormSq w (fun x => ∑ i, φ i x * c i) : ℝ) : ℂ)‖ :=
      (Complex.norm_of_nonneg (wNormSq_nonneg hw _)).symm
    rw [h0, wNormSq_comb_eq]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_conj]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  -- one row of the Gram matrix
  have hrow : ∀ i : ι, ∑ j, ‖c j‖ * ‖wInner w (φ i) (φ j)‖ ≤ ‖c i‖ + ε * ∑ j, ‖c j‖ := by
    intro i
    have hsingle : ∑ j, (if j = i then ‖c j‖ else 0) = ‖c i‖ := by
      rw [Finset.sum_eq_single i]
      · exact if_pos rfl
      · intro j _ hji
        exact if_neg hji
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hpt : ∀ j : ι, ‖c j‖ * ‖wInner w (φ i) (φ j)‖ ≤
        (if j = i then ‖c j‖ else 0) + ε * ‖c j‖ := by
      intro j
      by_cases hji : j = i
      · rw [if_pos hji, hji, wInner_self, Complex.norm_of_nonneg (wNormSq_nonneg hw _)]
        have h1 : ‖c i‖ * wNormSq w (φ i) ≤ ‖c i‖ * 1 :=
          mul_le_mul_of_nonneg_left (hdiag i) (norm_nonneg _)
        have h2 : 0 ≤ ε * ‖c i‖ := mul_nonneg hε (norm_nonneg _)
        linarith
      · rw [if_neg hji, zero_add, mul_comm ε]
        exact mul_le_mul_of_nonneg_left (hoff i j (Ne.symm hji)) (norm_nonneg _)
    calc ∑ j, ‖c j‖ * ‖wInner w (φ i) (φ j)‖
        ≤ ∑ j, ((if j = i then ‖c j‖ else 0) + ε * ‖c j‖) := Finset.sum_le_sum fun j _ => hpt j
      _ = ‖c i‖ + ε * ∑ j, ‖c j‖ := by
          rw [Finset.sum_add_distrib, hsingle, Finset.mul_sum]
  -- Cauchy–Schwarz for the `ℓ¹` norm of the coefficients
  have hT : (∑ j, ‖c j‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ j, ‖c j‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun j => ‖c j‖)
    rw [Finset.card_univ] at h
    exact h
  calc wNormSq w (fun x => ∑ i, φ i x * c i)
      ≤ ∑ i, ‖c i‖ * ∑ j, ‖c j‖ * ‖wInner w (φ i) (φ j)‖ := hnorm
    _ ≤ ∑ i, ‖c i‖ * (‖c i‖ + ε * ∑ j, ‖c j‖) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (norm_nonneg _)
    _ = ∑ i, ‖c i‖ ^ 2 + ε * (∑ j, ‖c j‖) ^ 2 := by
        have h : ∀ i : ι, ‖c i‖ * (‖c i‖ + ε * ∑ j, ‖c j‖) =
            ‖c i‖ ^ 2 + (ε * ∑ j, ‖c j‖) * ‖c i‖ := fun i => by ring
        rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    _ ≤ ∑ i, ‖c i‖ ^ 2 + ε * ((Fintype.card ι : ℝ) * ∑ j, ‖c j‖ ^ 2) := by
        have h := mul_le_mul_of_nonneg_left hT hε
        linarith
    _ = (1 + (Fintype.card ι : ℝ) * ε) * ∑ i, ‖c i‖ ^ 2 := by ring

/-- `⟨∑_i φ_i ⟨φ_i, f⟩, f⟩ = ∑_i |⟨φ_i, f⟩|²`. -/
theorem wInner_frame_eq (w : X → ℝ) (φ : ι → X → ℂ) (f : X → ℂ) :
    wInner w (fun x => ∑ i, φ i x * wInner w (φ i) f) f =
      ((∑ i, ‖wInner w (φ i) f‖ ^ 2 : ℝ) : ℂ) := by
  rw [wInner_sum_left w φ (fun i => wInner w (φ i) f) f, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Complex.conj_mul', Complex.ofReal_pow]

/-- The endgame: `A ≤ κ S` and `S² ≤ A B` give `√A ≤ κ √B`. -/
theorem sqrt_le_of_frame {A B S κ : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hS0 : 0 ≤ S) (hκ : 0 ≤ κ)
    (hA : A ≤ κ * S) (hS : S ^ 2 ≤ A * B) : Real.sqrt A ≤ κ * Real.sqrt B := by
  have hkey : A ≤ κ ^ 2 * B := by
    rcases hA0.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact mul_nonneg (sq_nonneg _) hB0
    · have h2 : A * A ≤ A * (κ ^ 2 * B) := by
        calc A * A ≤ (κ * S) * (κ * S) := mul_le_mul hA hA hA0 (mul_nonneg hκ hS0)
          _ = κ ^ 2 * S ^ 2 := by ring
          _ ≤ κ ^ 2 * (A * B) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
          _ = A * (κ ^ 2 * B) := by ring
      exact le_of_mul_le_mul_left h2 hpos
  calc Real.sqrt A ≤ Real.sqrt (κ ^ 2 * B) := Real.sqrt_le_sqrt hkey
    _ = κ * Real.sqrt B := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ]

end Gram

/-- **The frame operator of an almost orthonormal family** (eq:ideal-frame),
(eq:ideal-gram-bound) [S-03:0241–0256]. -/
theorem gramFrameBound : GramFrameBound := by
  intro X _ w hw ι _ φ ε hε hdiag hoff f
  have hκ : (0 : ℝ) ≤ 1 + (Fintype.card ι : ℝ) * ε :=
    add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hε)
  have hS0 : (0 : ℝ) ≤ ∑ i, ‖wInner w (φ i) f‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA := Gram.wNormSq_comb_le hw φ hε hdiag hoff (fun i => wInner w (φ i) f)
  have hS : (∑ i, ‖wInner w (φ i) f‖ ^ 2) ^ 2 ≤
      wNormSq w (fun x => ∑ i, φ i x * wInner w (φ i) f) * wNormSq w f := by
    have h := Gram.norm_wInner_sq_le hw (fun x => ∑ i, φ i x * wInner w (φ i) f) f
    rw [Gram.wInner_frame_eq w φ f, Complex.norm_of_nonneg hS0] at h
    exact h
  exact Gram.sqrt_le_of_frame (wNormSq_nonneg hw _) (wNormSq_nonneg hw _) hS0 hκ hA hS

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
