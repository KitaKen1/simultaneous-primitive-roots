module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.MinorArcTools
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.FrameCells
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Hilbert
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Denominators at most `Q`: the tools

Source: `verification/stage7-sources/S-03.tex`, lines 339–412 (`[S-03:0339–0412]`).

* `Major.gap`, `Major.defect_eq_gap` — the left side of (eq:ideal-comparison) is
  `E conj(f(X_B)) g(X_A) Δ(X_A, X_B)` with the pointwise defect
  `Δ = (X_A X_B)^{iζ} e(α X_A X_B) - E_D 𝒦_A 𝒦_B (D_A D_B)^{iζ} e(α D_A D_B)`.
* `Major.norm_sum_le_of_pointwise` — "pairing it with the tests costs at most the same bound times
  `‖f‖₂ ‖g‖₂`, since their spaces are independent" [S-03:0387–0389], and
  `E[1_ℰ |f(X_B) g(X_A)|] ≤ ℙ(ℰ)^{1/2} ‖f‖₂ ‖g‖₂` [S-03:0361–0367].
* `Major.discarded_mass_le` — (eq:ideal-discarded-mass): the discarded cells have total
  probability at most `N_Λ ξ`.
* `Major.slowPhase`, `Major.norm_slowPhase_sub_le` — the multiplier `M(v) = exp(iζv) e(β e^v)`
  in the log variable [S-03:0372–0378]: `|M(log D) - M(log X)| ≤ |ζ| τ + 2π |β| X · 2τ` when
  `|log D - log X| ≤ τ ≤ 1`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Major

/-! ### The pointwise defect -/

section Algebra

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

/-- The pointwise defect `Δ(X_A, X_B)`. -/
def gap (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ α ζ : ℝ) (xA : AuxList big A)
    (xB : AuxList big Bs) : ℂ :=
  dilPhase ζ α (tupleProd A xA * tupleProd Bs xB) -
    ∑ dA : AuxList big A, ∑ dB : AuxList big Bs,
      ((auxWeight big A dA * auxWeight big Bs dB : ℝ) : ℂ) *
        (cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
          cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
          dilPhase ζ α (tupleProd A dA * tupleProd Bs dB))

theorem defect_eq_gap (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ)
    (hA1 : ∑ t : AuxList big A, auxWeight big A t = 1)
    (hB1 : ∑ t : AuxList big Bs, auxWeight big Bs t = 1) (f : AuxList big Bs → ℂ)
    (g : AuxList big A → ℂ) (α ζ : ℝ) :
    comparisonDefect big A Bs Q h ξ f g α ζ =
      ∑ xA : AuxList big A, ∑ xB : AuxList big Bs,
        ((auxWeight big A xA * auxWeight big Bs xB : ℝ) : ℂ) * (conj (f xB) * g xA) *
          gap big A Bs Q h ξ α ζ xA xB := by
  unfold comparisonDefect
  refine Finset.sum_congr rfl fun xA _ => Finset.sum_congr rfl fun xB _ => ?_
  have h1 : (∑ dA : AuxList big A, ∑ dB : AuxList big Bs,
        ((auxWeight big A xA * auxWeight big Bs xB * auxWeight big A dA *
          auxWeight big Bs dB : ℝ) : ℂ) * (conj (f xB) * g xA) *
          (dilPhase ζ α (tupleProd A xA * tupleProd Bs xB) -
            cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
              cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
              dilPhase ζ α (tupleProd A dA * tupleProd Bs dB))) =
      (∑ dA : AuxList big A, ∑ dB : AuxList big Bs,
        ((auxWeight big A xA * auxWeight big Bs xB * auxWeight big A dA *
          auxWeight big Bs dB : ℝ) : ℂ) *
          ((conj (f xB) * g xA) * dilPhase ζ α (tupleProd A xA * tupleProd Bs xB))) -
      ∑ dA : AuxList big A, ∑ dB : AuxList big Bs,
        ((auxWeight big A xA * auxWeight big Bs xB : ℝ) : ℂ) * (conj (f xB) * g xA) *
          (((auxWeight big A dA * auxWeight big Bs dB : ℝ) : ℂ) *
            (cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
              cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
              dilPhase ζ α (tupleProd A dA * tupleProd Bs dB))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun dA _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun dB _ => ?_
    push_cast
    ring
  rw [h1, Minor.sum_weights_const (auxWeight big A) (auxWeight big Bs) hA1 hB1]
  unfold gap
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun dA _ => (Finset.mul_sum _ _ _).symm

end Algebra

/-! ### From a pointwise bound to the bilinear bound -/

/-- `|E conj(f) g Δ| ≤ (ℙ(ℰ_A)^{1/2} + ℙ(ℰ_B)^{1/2} + ε) ‖f‖ ‖g‖` when
`|Δ| ≤ 1_{ℰ_A} + 1_{ℰ_B} + ε` pointwise, for independent variables. -/
theorem norm_sum_le_of_pointwise {X Y : Type} [Fintype X] [Fintype Y] (wA : X → ℝ) (wB : Y → ℝ)
    (hwA : ∀ x, 0 ≤ wA x) (hwB : ∀ y, 0 ≤ wB y) (hA1 : ∑ x, wA x = 1) (hB1 : ∑ y, wB y = 1)
    (f : Y → ℂ) (g : X → ℂ) (Δ : X → Y → ℂ) (a : X → ℝ) (b : Y → ℝ) {ε pA pB : ℝ}
    (ha : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (hb : ∀ y, 0 ≤ b y ∧ b y ≤ 1) (hε : 0 ≤ ε)
    (hpA : ∑ x, wA x * a x ≤ pA) (hpB : ∑ y, wB y * b y ≤ pB)
    (hΔ : ∀ x y, g x ≠ 0 → f y ≠ 0 → ‖Δ x y‖ ≤ a x + b y + ε) :
    ‖∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (conj (f y) * g x) * Δ x y‖ ≤
      (Real.sqrt pA + Real.sqrt pB + ε) * (wNorm wB f * wNorm wA g) := by
  -- Cauchy's inequality for the four marginal sums
  have hSG : ∑ x, wA x * (‖g x‖ * 1) ≤ wNorm wA g := by
    have h : ∑ x, wA x * (‖g x‖ * 1) ≤ Real.sqrt (∑ x, wA x * ‖g x‖ ^ 2) *
        Real.sqrt (∑ x, wA x * (1 : ℝ) ^ 2) :=
      IdealConstruction.sum_weight_mul_le wA hwA (fun x => ‖g x‖) (fun _ => 1)
        (fun _ => norm_nonneg _) (fun _ => zero_le_one)
    have h1 : ∑ x, wA x * (1 : ℝ) ^ 2 = 1 :=
      (Finset.sum_congr rfl fun x _ => by ring).trans hA1
    have h2 : Real.sqrt (∑ x, wA x * (1 : ℝ) ^ 2) = 1 := by rw [h1, Real.sqrt_one]
    exact h.trans (le_of_eq (by rw [h2, mul_one]; rfl))
  have hSF : ∑ y, wB y * (‖f y‖ * 1) ≤ wNorm wB f := by
    have h : ∑ y, wB y * (‖f y‖ * 1) ≤ Real.sqrt (∑ y, wB y * ‖f y‖ ^ 2) *
        Real.sqrt (∑ y, wB y * (1 : ℝ) ^ 2) :=
      IdealConstruction.sum_weight_mul_le wB hwB (fun y => ‖f y‖) (fun _ => 1)
        (fun _ => norm_nonneg _) (fun _ => zero_le_one)
    have h1 : ∑ y, wB y * (1 : ℝ) ^ 2 = 1 :=
      (Finset.sum_congr rfl fun y _ => by ring).trans hB1
    have h2 : Real.sqrt (∑ y, wB y * (1 : ℝ) ^ 2) = 1 := by rw [h1, Real.sqrt_one]
    exact h.trans (le_of_eq (by rw [h2, mul_one]; rfl))
  have hSGa : ∑ x, wA x * (‖g x‖ * a x) ≤ wNorm wA g * Real.sqrt pA := by
    have h : ∑ x, wA x * (‖g x‖ * a x) ≤ Real.sqrt (∑ x, wA x * ‖g x‖ ^ 2) *
        Real.sqrt (∑ x, wA x * a x ^ 2) :=
      IdealConstruction.sum_weight_mul_le wA hwA (fun x => ‖g x‖) a
        (fun _ => norm_nonneg _) (fun x => (ha x).1)
    have h1 : ∑ x, wA x * a x ^ 2 ≤ pA :=
      (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg (ha x).1 (sub_nonneg.mpr (ha x).2)]) (hwA x)).trans hpA
    exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _))
  have hSFb : ∑ y, wB y * (‖f y‖ * b y) ≤ wNorm wB f * Real.sqrt pB := by
    have h : ∑ y, wB y * (‖f y‖ * b y) ≤ Real.sqrt (∑ y, wB y * ‖f y‖ ^ 2) *
        Real.sqrt (∑ y, wB y * b y ^ 2) :=
      IdealConstruction.sum_weight_mul_le wB hwB (fun y => ‖f y‖) b
        (fun _ => norm_nonneg _) (fun y => (hb y).1)
    have h1 : ∑ y, wB y * b y ^ 2 ≤ pB :=
      (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg (hb y).1 (sub_nonneg.mpr (hb y).2)]) (hwB y)).trans hpB
    exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _))
  have h0F : 0 ≤ ∑ y, wB y * (‖f y‖ * 1) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hwB y) (mul_nonneg (norm_nonneg _) zero_le_one)
  have h0Fb : 0 ≤ ∑ y, wB y * (‖f y‖ * b y) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hwB y) (mul_nonneg (norm_nonneg _) (hb y).1)
  -- the double sum of the pointwise bounds is a combination of products of marginal sums
  have hid : ∑ x, ∑ y, wA x * wB y * (‖f y‖ * ‖g x‖) * (a x + b y + ε) =
      (∑ x, wA x * (‖g x‖ * a x)) * (∑ y, wB y * (‖f y‖ * 1)) +
        (∑ x, wA x * (‖g x‖ * 1)) * (∑ y, wB y * (‖f y‖ * b y)) +
        ε * ((∑ x, wA x * (‖g x‖ * 1)) * (∑ y, wB y * (‖f y‖ * 1))) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hstep : ‖∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (conj (f y) * g x) * Δ x y‖ ≤
      ∑ x, ∑ y, wA x * wB y * (‖f y‖ * ‖g x‖) * (a x + b y + ε) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_of_nonneg (mul_nonneg (hwA x) (hwB y)),
      Complex.norm_conj]
    by_cases hg0 : g x = 0
    · have h0 : wA x * wB y * (‖f y‖ * ‖g x‖) = 0 := by
        rw [hg0, norm_zero, mul_zero, mul_zero]
      exact le_of_eq (by rw [h0, zero_mul, zero_mul])
    by_cases hf0 : f y = 0
    · have h0 : wA x * wB y * (‖f y‖ * ‖g x‖) = 0 := by
        rw [hf0, norm_zero, zero_mul, mul_zero]
      exact le_of_eq (by rw [h0, zero_mul, zero_mul])
    exact mul_le_mul_of_nonneg_left (hΔ x y hg0 hf0)
      (mul_nonneg (mul_nonneg (hwA x) (hwB y)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hNf := wNorm_nonneg wB f
  have hNg := wNorm_nonneg wA g
  have hpAs := Real.sqrt_nonneg pA
  have t1 : (∑ x, wA x * (‖g x‖ * a x)) * (∑ y, wB y * (‖f y‖ * 1)) ≤
      wNorm wA g * Real.sqrt pA * wNorm wB f :=
    mul_le_mul hSGa hSF h0F (mul_nonneg hNg hpAs)
  have t2 : (∑ x, wA x * (‖g x‖ * 1)) * (∑ y, wB y * (‖f y‖ * b y)) ≤
      wNorm wA g * (wNorm wB f * Real.sqrt pB) :=
    mul_le_mul hSG hSFb h0Fb hNg
  have t3 : ε * ((∑ x, wA x * (‖g x‖ * 1)) * (∑ y, wB y * (‖f y‖ * 1))) ≤
      ε * (wNorm wA g * wNorm wB f) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hSG hSF h0F hNg) hε
  rw [hid] at hstep
  have hfin : wNorm wA g * Real.sqrt pA * wNorm wB f +
      wNorm wA g * (wNorm wB f * Real.sqrt pB) + ε * (wNorm wA g * wNorm wB f) =
      (Real.sqrt pA + Real.sqrt pB + ε) * (wNorm wB f * wNorm wA g) := by ring
  linarith

/-! ### The discarded cells -/

section Cells

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] {J : ℕ}

/-- **(eq:ideal-discarded-mass)** [S-03:0352–0358]: the cells of mass less than `ξ` have total
probability at most `N_Λ ξ`. -/
theorem discarded_mass_le (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) (h ξ : ℝ)
    (hξ : 0 ≤ ξ) :
    ∑ t : AuxList 𝔊.big Λ, auxWeight 𝔊.big Λ t *
        (if cellMass 𝔊.big Λ h (logCell h (tupleProd Λ t)) < ξ then (1 : ℝ) else 0) ≤
      (cellCount 𝔊.big Λ h : ℝ) * ξ := by
  have hcell : ∀ k : ℤ, ∑ t : AuxList 𝔊.big Λ,
      Frame.cellWeight (auxWeight 𝔊.big Λ) (fun t : AuxList 𝔊.big Λ => logCell h (tupleProd Λ t))
        k t * (if cellMass 𝔊.big Λ h (logCell h (tupleProd Λ t)) < ξ then (1 : ℝ) else 0) ≤
      ξ := by
    intro k
    by_cases hk : cellMass 𝔊.big Λ h k < ξ
    · have h1 : ∑ t : AuxList 𝔊.big Λ,
          Frame.cellWeight (auxWeight 𝔊.big Λ)
            (fun t : AuxList 𝔊.big Λ => logCell h (tupleProd Λ t)) k t *
            (if cellMass 𝔊.big Λ h (logCell h (tupleProd Λ t)) < ξ then (1 : ℝ) else 0) ≤
          cellMass 𝔊.big Λ h k := by
        refine Finset.sum_le_sum fun t _ => ?_
        by_cases hc : logCell h (tupleProd Λ t) = k
        · have h2 : Frame.cellWeight (auxWeight 𝔊.big Λ)
              (fun t : AuxList 𝔊.big Λ => logCell h (tupleProd Λ t)) k t =
              auxWeight 𝔊.big Λ t := if_pos hc
          have h3 : (if logCell h (tupleProd Λ t) = k then auxWeight 𝔊.big Λ t else 0) =
              auxWeight 𝔊.big Λ t := if_pos hc
          rw [h2, h3]
          refine mul_le_of_le_one_right (tupleWeight_nonneg 𝔊 Λ t) ?_
          by_cases hm : cellMass 𝔊.big Λ h (logCell h (tupleProd Λ t)) < ξ
          · exact le_of_eq (if_pos hm)
          · rw [if_neg hm]
            exact zero_le_one
        · have h2 : Frame.cellWeight (auxWeight 𝔊.big Λ)
              (fun t : AuxList 𝔊.big Λ => logCell h (tupleProd Λ t)) k t = 0 :=
            if_neg hc
          rw [h2, zero_mul]
          exact (if_neg hc).ge
      exact h1.trans hk.le
    · refine le_trans (le_of_eq (Finset.sum_eq_zero fun t _ => ?_)) hξ
      by_cases hc : logCell h (tupleProd Λ t) = k
      · rw [hc, if_neg hk, mul_zero]
      · have h2 : Frame.cellWeight (auxWeight 𝔊.big Λ)
            (fun t : AuxList 𝔊.big Λ => logCell h (tupleProd Λ t)) k t = 0 :=
          if_neg hc
        rw [h2, zero_mul]
  rw [Frame.sum_weight_eq (auxWeight 𝔊.big Λ)
    (fun t : AuxList 𝔊.big Λ => logCell h (tupleProd Λ t))
    (fun t => if cellMass 𝔊.big Λ h (logCell h (tupleProd Λ t)) < ξ then (1 : ℝ) else 0)]
  refine (Finset.sum_le_sum fun k _ => hcell k).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

end Cells

/-! ### The multiplier in the log variable -/

/-- `M(log n) = n^{iζ} e(β n)`, "the remaining scalar multiplier in the log variable"
[S-03:0372–0375]. -/
def slowPhase (ζ β : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ ((ζ : ℂ) * Complex.I) * expUnit (β * (n : ℝ))

theorem slowPhase_eq_exp (ζ β : ℝ) {n : ℕ} (hn : 0 < n) :
    slowPhase ζ β n = Complex.exp (Complex.I *
      ((ζ * Real.log (n : ℝ) + 2 * Real.pi * (β * (n : ℝ)) : ℝ) : ℂ)) := by
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]
  unfold slowPhase expUnit
  rw [Complex.cpow_def_of_ne_zero hn0, hlog, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_exp_I_sub_le (s t : ℝ) :
    ‖Complex.exp (Complex.I * (s : ℂ)) - Complex.exp (Complex.I * (t : ℂ))‖ ≤ |s - t| := by
  have h0 : Complex.I * (s : ℂ) = Complex.I * (t : ℂ) + Complex.I * ((s - t : ℝ) : ℂ) := by
    push_cast
    ring
  have h1 : Complex.exp (Complex.I * (s : ℂ)) - Complex.exp (Complex.I * (t : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) *
        (Complex.exp (Complex.I * ((s - t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, ← h0]
  have h2 : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I t
  rw [h1, norm_mul, h2, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq (Real.norm_eq_abs _))

/-- **The replacement of the log-variable multiplier** [S-03:0376–0381]: "on the enlarged product
range its derivative has magnitude `O(L^{C₄} + S)`". -/
theorem norm_slowPhase_sub_le (ζ β : ℝ) {D X : ℕ} (hD : 0 < D) (hX : 0 < X) {τ : ℝ}
    (hτ1 : τ ≤ 1) (hlog : |Real.log (D : ℝ) - Real.log (X : ℝ)| ≤ τ) :
    ‖slowPhase ζ β D - slowPhase ζ β X‖ ≤
      |ζ| * τ + 2 * Real.pi * (|β| * ((X : ℝ) * (2 * τ))) := by
  have hXr : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hDX : |(D : ℝ) - (X : ℝ)| ≤ (X : ℝ) * (2 * τ) := by
    have h1 : (X : ℝ) * Real.exp (Real.log (D : ℝ) - Real.log (X : ℝ)) = (D : ℝ) := by
      rw [Real.exp_sub, Real.exp_log hDr, Real.exp_log hXr]
      have h : (X : ℝ) * ((D : ℝ) / (X : ℝ)) = (D : ℝ) * ((X : ℝ)⁻¹ * (X : ℝ)) := by ring
      rw [h, inv_mul_cancel₀ hXr.ne', mul_one]
    have h2 : |Real.exp (Real.log (D : ℝ) - Real.log (X : ℝ)) - 1| ≤
        2 * |Real.log (D : ℝ) - Real.log (X : ℝ)| := Real.abs_exp_sub_one_le (hlog.trans hτ1)
    have h3 : (D : ℝ) - (X : ℝ) =
        (X : ℝ) * (Real.exp (Real.log (D : ℝ) - Real.log (X : ℝ)) - 1) := by
      rw [mul_sub, mul_one, h1]
    rw [h3, abs_mul, abs_of_pos hXr]
    exact mul_le_mul_of_nonneg_left (h2.trans (by linarith)) hXr.le
  have hθ : ζ * Real.log (D : ℝ) + 2 * Real.pi * (β * (D : ℝ)) -
      (ζ * Real.log (X : ℝ) + 2 * Real.pi * (β * (X : ℝ))) =
      ζ * (Real.log (D : ℝ) - Real.log (X : ℝ)) +
        2 * Real.pi * (β * ((D : ℝ) - (X : ℝ))) := by ring
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h4 := norm_add_le (ζ * (Real.log (D : ℝ) - Real.log (X : ℝ)))
    (2 * Real.pi * (β * ((D : ℝ) - (X : ℝ))))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul ζ (Real.log (D : ℝ) - Real.log (X : ℝ)),
    abs_mul (2 * Real.pi) (β * ((D : ℝ) - (X : ℝ))), abs_of_nonneg hpi,
    abs_mul β ((D : ℝ) - (X : ℝ))] at h4
  rw [slowPhase_eq_exp ζ β hD, slowPhase_eq_exp ζ β hX]
  refine (norm_exp_I_sub_le _ _).trans ?_
  rw [hθ]
  exact h4.trans (add_le_add (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDX (abs_nonneg _)) hpi))

end Major

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
