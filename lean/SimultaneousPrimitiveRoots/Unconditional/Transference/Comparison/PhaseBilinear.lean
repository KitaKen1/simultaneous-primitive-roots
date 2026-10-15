module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Collapse
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.IntegerBilinear
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The probability-space bilinear bound (eq:ideal-probability-bilinear)

Source: `verification/stage7-sources/S-03.tex`, lines 163–174 (`[S-03:0163–0174]`).

`probabilityBilinear_of : CollapseBound → IntegerBilinear → ProbabilityBilinear`.

"For two independent selected products of sizes `U, V`, combining (eq:ideal-collapse) and
(eq:integer-bilinear) shows that the probability-space bilinear form with phase `e(α P_A P_B)` has
norm at most `C L^κ (1/V + 1/r + log(2r)/U + r log(2r)/(UV))^{1/2}`. The same assertion holds with
the phase multiplied by `(P_A P_B)^{iζ}` for any real `ζ`, since this factor separates between the
two tests and preserves their norms."

* `Phase.twist` — the test `G` multiplied by `P_A^{iζ}`; it has the same support and a norm at
  most that of `G` ("this factor separates between the two tests and preserves their norms").
* `Phase.phaseForm_eq` — the form is `∑_{n,k} a_n b_k e(α n k)` with the collapsed coefficients
  `a_n = E[G P_A^{iζ} 1_{P_A = n}]`, `b_k = E[F P_B^{iζ} 1_{P_B = k}]`.
* `Phase.root_bound` — the arithmetic: with `‖a‖² ≤ L^κ/(c₁U) ‖G‖²`, `‖b‖² ≤ L^κ/(c₁V) ‖F‖²`,
  `[U + (1 + V/r)(U + r log 2r)] / (UV) = 2/V + 1/r + log(2r)/U + r log(2r)/(UV)`.

The constant is `C = 2 K / c₁`, `K` the constant of Lemma 4.2 for intervals of length `c₂ U`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Phase

/-! ### Elementary facts -/

/-- `|D^{iζ}| ≤ 1` for a natural number `D`. -/
theorem norm_natCast_cpow_le_one (D : ℕ) (ζ : ℝ) : ‖(D : ℂ) ^ ((ζ : ℂ) * Complex.I)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos D with h0 | hpos
  · rw [h0, Nat.cast_zero]
    by_cases hw : (ζ : ℂ) * Complex.I = 0
    · rw [hw, Complex.cpow_zero, norm_one]
    · rw [Complex.zero_cpow hw, norm_zero]
      exact zero_le_one
  · have hre : ((ζ : ℂ) * Complex.I).re = 0 := by simp
    rw [Complex.norm_natCast_cpow_of_pos hpos]
    exact le_of_eq (by rw [hre, Real.rpow_zero])

/-- `(nk)^{iζ} e(α n k) = n^{iζ} k^{iζ} e(α n k)`. -/
theorem dilPhase_mul_eq (ζ α : ℝ) (n k : ℕ) :
    dilPhase ζ α (n * k) =
      (n : ℂ) ^ ((ζ : ℂ) * Complex.I) * (k : ℂ) ^ ((ζ : ℂ) * Complex.I) *
        expUnit (α * (n : ℝ) * (k : ℝ)) := by
  have h1 : ((n * k : ℕ) : ℂ) = (n : ℂ) * (k : ℂ) := Nat.cast_mul n k
  have h2 : α * ((n * k : ℕ) : ℝ) = α * (n : ℝ) * (k : ℝ) := by
    rw [Nat.cast_mul, mul_assoc]
  unfold dilPhase
  rw [h1, h2, Complex.natCast_mul_natCast_cpow]

/-- A sum over a finite type, grouped by the values of a function. -/
theorem sum_fiber {X : Type} [Fintype X] (p : X → ℕ) (Ψ : X → ℂ) (g : ℕ → ℂ) :
    ∑ x, Ψ x * g (p x) =
      ∑ k ∈ Finset.univ.image p, (∑ x, if p x = k then Ψ x else 0) * g k := by
  have h1 : ∀ k : ℕ, (∑ x, if p x = k then Ψ x else 0) * g k =
      ∑ x, if p x = k then Ψ x * g k else 0 := by
    intro k
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hc : p x = k
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, zero_mul]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem p (Finset.mem_univ x))]

/-- **The arithmetic of (eq:ideal-probability-bilinear)**. -/
theorem root_bound {E c₁ U V R ℓ : ℝ} (hE : 0 ≤ E) (hc₁ : 0 < c₁) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hR : 1 ≤ R) (hℓ : 0 ≤ ℓ) :
    Real.sqrt (E / (c₁ * U)) * Real.sqrt (E / (c₁ * V)) *
        Real.sqrt (U + (1 + V / R) * (U + R * ℓ)) ≤
      2 / c₁ * E * Real.sqrt (1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) := by
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  have hR0 : 0 < R := by linarith
  have hUV : 0 < U * V := mul_pos hU0 hV0
  have h1 : 1 / V * (U * V) = U := by
    have h : 1 / V * (U * V) = U * (V⁻¹ * V) := by ring
    rw [h, inv_mul_cancel₀ hV0.ne', mul_one]
  have h3 : ℓ / U * (U * V) = ℓ * V := by
    have h : ℓ / U * (U * V) = ℓ * V * (U⁻¹ * U) := by ring
    rw [h, inv_mul_cancel₀ hU0.ne', mul_one]
  have h4 : R * ℓ / (U * V) * (U * V) = R * ℓ := by
    have h : R * ℓ / (U * V) * (U * V) = R * ℓ * ((U * V)⁻¹ * (U * V)) := by ring
    rw [h, inv_mul_cancel₀ hUV.ne', mul_one]
  have hSig : (1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) * (U * V) =
      U + 1 / R * (U * V) + ℓ * V + R * ℓ := by
    rw [add_mul, add_mul, add_mul, h1, h3, h4]
  have hW : U + (1 + V / R) * (U + R * ℓ) = 2 * U + R * ℓ + 1 / R * (U * V) + V * ℓ := by
    have h : U + (1 + V / R) * (U + R * ℓ) =
        2 * U + R * ℓ + 1 / R * (U * V) + V * ℓ * (R⁻¹ * R) := by ring
    rw [h, inv_mul_cancel₀ hR0.ne', mul_one]
  have hnn1 : 0 ≤ 1 / R * (U * V) := mul_nonneg (div_nonneg zero_le_one hR0.le) hUV.le
  have hnn2 : 0 ≤ ℓ * V := mul_nonneg hℓ hV0.le
  have hnn3 : 0 ≤ R * ℓ := mul_nonneg hR0.le hℓ
  have hW4 : U + (1 + V / R) * (U + R * ℓ) ≤
      4 * ((1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) * (U * V)) := by
    rw [hW, hSig]
    nlinarith [hnn1, hnn2, hnn3, hU0.le]
  have hkey : E / (c₁ * U) * (E / (c₁ * V)) * (U + (1 + V / R) * (U + R * ℓ)) ≤
      (2 / c₁ * E) ^ 2 * (1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) := by
    have e1 : E / (c₁ * U) * (E / (c₁ * V)) * (U + (1 + V / R) * (U + R * ℓ)) =
        (E / c₁) ^ 2 * (U * V)⁻¹ * (U + (1 + V / R) * (U + R * ℓ)) := by ring
    have e2 : (2 / c₁ * E) ^ 2 * (1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) =
        (E / c₁) ^ 2 * (U * V)⁻¹ *
          (4 * ((1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) * (U * V))) := by
      have h : (E / c₁) ^ 2 * (U * V)⁻¹ *
            (4 * ((1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) * (U * V))) =
          (2 / c₁ * E) ^ 2 * (1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) *
            ((U * V)⁻¹ * (U * V)) := by ring
      rw [h, inv_mul_cancel₀ hUV.ne', mul_one]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hW4 (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hUV.le))
  have hE1 : 0 ≤ E / (c₁ * U) := div_nonneg hE (mul_pos hc₁ hU0).le
  have hE2 : 0 ≤ E / (c₁ * V) := div_nonneg hE (mul_pos hc₁ hV0).le
  have hc : 0 ≤ 2 / c₁ * E := mul_nonneg (div_nonneg zero_le_two hc₁.le) hE
  calc Real.sqrt (E / (c₁ * U)) * Real.sqrt (E / (c₁ * V)) *
        Real.sqrt (U + (1 + V / R) * (U + R * ℓ))
      = Real.sqrt (E / (c₁ * U) * (E / (c₁ * V)) * (U + (1 + V / R) * (U + R * ℓ))) := by
        rw [Real.sqrt_mul (mul_nonneg hE1 hE2), Real.sqrt_mul hE1]
    _ ≤ Real.sqrt ((2 / c₁ * E) ^ 2 * (1 / V + 1 / R + ℓ / U + R * ℓ / (U * V))) :=
        Real.sqrt_le_sqrt hkey
    _ = 2 / c₁ * E * Real.sqrt (1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

/-! ### The twisted tests and the collapsed form -/

section Tuples

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {big : B → Finset ℕ}

omit [DecidableEq B] in
/-- The test `F` multiplied by `P_Λ^{iζ}`. -/
def twist (ζ : ℝ) (Λ : B → Finset (Fin J)) (F : AuxList big Λ → ℂ) (t : AuxList big Λ) : ℂ :=
  F t * ((tupleProd Λ t : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I)

omit [DecidableEq B] in
theorem norm_twist_le (ζ : ℝ) (Λ : B → Finset (Fin J)) (F : AuxList big Λ → ℂ)
    (t : AuxList big Λ) : ‖twist ζ Λ F t‖ ≤ ‖F t‖ := by
  unfold twist
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_natCast_cpow_le_one _ ζ) (norm_nonneg _)).trans
    (le_of_eq (mul_one _))

omit [DecidableEq B] in
theorem twist_eq_zero (ζ : ℝ) (Λ : B → Finset (Fin J)) {F : AuxList big Λ → ℂ}
    {t : AuxList big Λ} (h : F t = 0) : twist ζ Λ F t = 0 := by
  unfold twist
  rw [h, zero_mul]

/-- A collapsed coefficient vanishes when the test vanishes on the fiber. -/
theorem fiberCoeff_eq_zero (big : B → Finset ℕ) (Λ : B → Finset (Fin J))
    (F : AuxList big Λ → ℂ) (n : ℕ) (h : ∀ t, tupleProd Λ t = n → F t = 0) :
    fiberCoeff big Λ F n = 0 := by
  unfold fiberCoeff
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases hc : tupleProd Λ t = n
  · rw [if_pos hc, h t hc, mul_zero]
  · exact if_neg hc

/-- **The form is the integer bilinear form of the collapsed coefficients.** -/
theorem phaseForm_eq (big : B → Finset ℕ) (A Bs : B → Finset (Fin J))
    (F : AuxList big Bs → ℂ) (G : AuxList big A → ℂ) (α ζ : ℝ) :
    phaseForm big A Bs F G α ζ =
      ∑ n ∈ Finset.univ.image (fun t : AuxList big A => tupleProd A t),
        ∑ k ∈ Finset.univ.image (fun t : AuxList big Bs => tupleProd Bs t),
          fiberCoeff big A (twist ζ A G) n * fiberCoeff big Bs (twist ζ Bs F) k *
            expUnit (α * (n : ℝ) * (k : ℝ)) := by
  have hterm : ∀ (xA : AuxList big A) (xB : AuxList big Bs),
      ((auxWeight big A xA * auxWeight big Bs xB : ℝ) : ℂ) * (F xB * G xA) *
          dilPhase ζ α (tupleProd A xA * tupleProd Bs xB) =
        ((auxWeight big A xA : ℂ) * twist ζ A G xA) *
          (((auxWeight big Bs xB : ℂ) * twist ζ Bs F xB) *
            expUnit (α * ((tupleProd A xA : ℕ) : ℝ) * ((tupleProd Bs xB : ℕ) : ℝ))) := by
    intro xA xB
    rw [dilPhase_mul_eq]
    unfold twist
    push_cast
    ring
  have hB : ∀ xA : AuxList big A,
      ∑ xB : AuxList big Bs, ((auxWeight big Bs xB : ℂ) * twist ζ Bs F xB) *
          expUnit (α * ((tupleProd A xA : ℕ) : ℝ) * ((tupleProd Bs xB : ℕ) : ℝ)) =
        ∑ k ∈ Finset.univ.image (fun t : AuxList big Bs => tupleProd Bs t),
          fiberCoeff big Bs (twist ζ Bs F) k *
            expUnit (α * ((tupleProd A xA : ℕ) : ℝ) * (k : ℝ)) := fun xA =>
    sum_fiber (fun t : AuxList big Bs => tupleProd Bs t)
      (fun xB => (auxWeight big Bs xB : ℂ) * twist ζ Bs F xB)
      (fun k => expUnit (α * ((tupleProd A xA : ℕ) : ℝ) * (k : ℝ)))
  have hA : ∑ xA : AuxList big A, ((auxWeight big A xA : ℂ) * twist ζ A G xA) *
        ∑ k ∈ Finset.univ.image (fun t : AuxList big Bs => tupleProd Bs t),
          fiberCoeff big Bs (twist ζ Bs F) k *
            expUnit (α * ((tupleProd A xA : ℕ) : ℝ) * (k : ℝ)) =
      ∑ n ∈ Finset.univ.image (fun t : AuxList big A => tupleProd A t),
        fiberCoeff big A (twist ζ A G) n *
          ∑ k ∈ Finset.univ.image (fun t : AuxList big Bs => tupleProd Bs t),
            fiberCoeff big Bs (twist ζ Bs F) k * expUnit (α * (n : ℝ) * (k : ℝ)) :=
    sum_fiber (fun t : AuxList big A => tupleProd A t)
      (fun xA => (auxWeight big A xA : ℂ) * twist ζ A G xA)
      (fun n => ∑ k ∈ Finset.univ.image (fun t : AuxList big Bs => tupleProd Bs t),
        fiberCoeff big Bs (twist ζ Bs F) k * expUnit (α * (n : ℝ) * (k : ℝ)))
  unfold phaseForm
  calc ∑ xA : AuxList big A, ∑ xB : AuxList big Bs,
        ((auxWeight big A xA * auxWeight big Bs xB : ℝ) : ℂ) * (F xB * G xA) *
          dilPhase ζ α (tupleProd A xA * tupleProd Bs xB)
      = ∑ xA : AuxList big A, ((auxWeight big A xA : ℂ) * twist ζ A G xA) *
          ∑ k ∈ Finset.univ.image (fun t : AuxList big Bs => tupleProd Bs t),
            fiberCoeff big Bs (twist ζ Bs F) k *
              expUnit (α * ((tupleProd A xA : ℕ) : ℝ) * (k : ℝ)) := by
        refine Finset.sum_congr rfl fun xA _ => ?_
        rw [← hB xA, Finset.mul_sum]
        exact Finset.sum_congr rfl fun xB _ => hterm xA xB
    _ = ∑ n ∈ Finset.univ.image (fun t : AuxList big A => tupleProd A t),
          fiberCoeff big A (twist ζ A G) n *
            ∑ k ∈ Finset.univ.image (fun t : AuxList big Bs => tupleProd Bs t),
              fiberCoeff big Bs (twist ζ Bs F) k * expUnit (α * (n : ℝ) * (k : ℝ)) := hA
    _ = ∑ n ∈ Finset.univ.image (fun t : AuxList big A => tupleProd A t),
          ∑ k ∈ Finset.univ.image (fun t : AuxList big Bs => tupleProd Bs t),
            fiberCoeff big A (twist ζ A G) n * fiberCoeff big Bs (twist ζ Bs F) k *
              expUnit (α * (n : ℝ) * (k : ℝ)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm

/-- The sum over all the values of the two products is the sum over the values in the two
windows, when the coefficients vanish outside the windows. -/
theorem sum_window (sA sB : Finset ℕ) (a b : ℕ → ℂ) (e : ℕ → ℕ → ℂ) (pA pB : ℕ → Prop)
    [DecidablePred pA] [DecidablePred pB] (ha : ∀ n, ¬pA n → a n = 0)
    (hb : ∀ k, ¬pB k → b k = 0) :
    ∑ n ∈ sA, ∑ k ∈ sB, a n * b k * e n k =
      ∑ n ∈ sA.filter pA, ∑ k ∈ sB.filter pB, a n * b k * e n k := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : pA n
  · rw [if_pos hn, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : pB k
    · rw [if_pos hk]
    · rw [if_neg hk, hb k hk, mul_zero, zero_mul]
  · rw [if_neg hn]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [ha n hn, zero_mul, zero_mul]

end Tuples

end Phase

/-! ### The bound -/

/-- **The probability-space bilinear bound (eq:ideal-probability-bilinear)** [S-03:0163–0174],
from the collapse (eq:ideal-collapse) and Lemma 4.2. -/
theorem probabilityBilinear_of (hcolS : CollapseBound) (hbilS : IntegerBilinear) :
    ProbabilityBilinear := by
  intro P m c₁ c₂ hc₁ hc₁₂
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  obtain ⟨K₀, hK₀, hbil⟩ := hbilS c₂ hc₂
  obtain ⟨x₁, hcol⟩ := hcolS P m
  refine ⟨2 * K₀ / c₁, div_pos (mul_pos zero_lt_two hK₀) hc₁, max x₁ (Real.exp 1), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 J A Bs hA hBs hAm hBm U V hU hV F G hF hG α ζ β u r hr hcop hα hβ
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL0 : 0 < Real.log x := by linarith
  have hE : 0 ≤ Real.log x ^ atomExponent P m := Real.rpow_nonneg hL0.le _
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
  have hℓ : 0 ≤ Real.log (2 * (r : ℝ)) := Real.log_nonneg (by linarith)
  -- the collapsed coefficients vanish outside the windows
  have ha0 : ∀ n : ℕ, ¬(c₁ * U ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₂ * U) →
      fiberCoeff 𝔊.big A (Phase.twist ζ A G) n = 0 := by
    intro n hn
    refine Phase.fiberCoeff_eq_zero 𝔊.big A _ n fun t ht => ?_
    by_contra hne
    have hGt : G t ≠ 0 := fun h0 => hne (Phase.twist_eq_zero ζ A h0)
    have h1 := hG t hGt
    rw [ht] at h1
    exact hn h1
  have hb0 : ∀ k : ℕ, ¬(c₁ * V ≤ (k : ℝ) ∧ (k : ℝ) ≤ c₂ * V) →
      fiberCoeff 𝔊.big Bs (Phase.twist ζ Bs F) k = 0 := by
    intro k hk
    refine Phase.fiberCoeff_eq_zero 𝔊.big Bs _ k fun t ht => ?_
    by_contra hne
    have hFt : F t ≠ 0 := fun h0 => hne (Phase.twist_eq_zero ζ Bs h0)
    have h1 := hF t hFt
    rw [ht] at h1
    exact hk h1
  -- Lemma 4.2 on the windows
  have hsA : ∀ n ∈ (Finset.univ.image (fun t : AuxList 𝔊.big A => tupleProd A t)).filter
      (fun n : ℕ => c₁ * U ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₂ * U),
      ⌊c₁ * U⌋₊ ≤ n ∧ (n : ℝ) ≤ (⌊c₁ * U⌋₊ : ℝ) + c₂ * U := by
    intro n hn
    have h1 := (Finset.mem_filter.mp hn).2
    exact ⟨Nat.floor_le_of_le h1.1, by linarith [h1.2, Nat.cast_nonneg (α := ℝ) ⌊c₁ * U⌋₊]⟩
  have hsB : ∀ k ∈ (Finset.univ.image (fun t : AuxList 𝔊.big Bs => tupleProd Bs t)).filter
      (fun k : ℕ => c₁ * V ≤ (k : ℝ) ∧ (k : ℝ) ≤ c₂ * V),
      ⌊c₁ * V⌋₊ ≤ k ∧ (k : ℝ) ≤ (⌊c₁ * V⌋₊ : ℝ) + c₂ * V := by
    intro k hk
    have h1 := (Finset.mem_filter.mp hk).2
    exact ⟨Nat.floor_le_of_le h1.1, by linarith [h1.2, Nat.cast_nonneg (α := ℝ) ⌊c₁ * V⌋₊]⟩
  have hint := hbil U V hU hV _ _ ⌊c₁ * U⌋₊ ⌊c₁ * V⌋₊ hsA hsB
    (fiberCoeff 𝔊.big A (Phase.twist ζ A G)) (fiberCoeff 𝔊.big Bs (Phase.twist ζ Bs F))
    α β u r hr hcop hα hβ
  -- the collapse of the two tests
  have hcolA : Real.sqrt (∑ n ∈ (Finset.univ.image
        (fun t : AuxList 𝔊.big A => tupleProd A t)).filter
        (fun n : ℕ => c₁ * U ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₂ * U),
        ‖fiberCoeff 𝔊.big A (Phase.twist ζ A G) n‖ ^ 2) ≤
      Real.sqrt (Real.log x ^ atomExponent P m / (c₁ * U)) * tupleNorm 𝔊.big A G := by
    have h1 := hcol x hx₁ S B 𝔊 J A hA hAm (c₁ * U) (mul_pos hc₁ hU0) (Phase.twist ζ A G)
      (fun t ht => (hG t fun h0 => ht (Phase.twist_eq_zero ζ A h0)).1)
      ((Finset.univ.image (fun t : AuxList 𝔊.big A => tupleProd A t)).filter
        (fun n : ℕ => c₁ * U ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₂ * U))
    have h2 : wNormSq (auxWeight 𝔊.big A) (Phase.twist ζ A G) ≤
        wNormSq (auxWeight 𝔊.big A) G :=
      Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (Phase.norm_twist_le ζ A G t) 2)
        (tupleWeight_nonneg 𝔊 A t)
    have h3 : 0 ≤ Real.log x ^ atomExponent P m / (c₁ * U) :=
      div_nonneg hE (mul_pos hc₁ hU0).le
    have h4 := h1.trans (mul_le_mul_of_nonneg_left h2 h3)
    have h5 := Real.sqrt_le_sqrt h4
    rw [Real.sqrt_mul h3] at h5
    exact h5
  have hcolB : Real.sqrt (∑ k ∈ (Finset.univ.image
        (fun t : AuxList 𝔊.big Bs => tupleProd Bs t)).filter
        (fun k : ℕ => c₁ * V ≤ (k : ℝ) ∧ (k : ℝ) ≤ c₂ * V),
        ‖fiberCoeff 𝔊.big Bs (Phase.twist ζ Bs F) k‖ ^ 2) ≤
      Real.sqrt (Real.log x ^ atomExponent P m / (c₁ * V)) * tupleNorm 𝔊.big Bs F := by
    have h1 := hcol x hx₁ S B 𝔊 J Bs hBs hBm (c₁ * V) (mul_pos hc₁ hV0) (Phase.twist ζ Bs F)
      (fun t ht => (hF t fun h0 => ht (Phase.twist_eq_zero ζ Bs h0)).1)
      ((Finset.univ.image (fun t : AuxList 𝔊.big Bs => tupleProd Bs t)).filter
        (fun k : ℕ => c₁ * V ≤ (k : ℝ) ∧ (k : ℝ) ≤ c₂ * V))
    have h2 : wNormSq (auxWeight 𝔊.big Bs) (Phase.twist ζ Bs F) ≤
        wNormSq (auxWeight 𝔊.big Bs) F :=
      Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (Phase.norm_twist_le ζ Bs F t) 2)
        (tupleWeight_nonneg 𝔊 Bs t)
    have h3 : 0 ≤ Real.log x ^ atomExponent P m / (c₁ * V) :=
      div_nonneg hE (mul_pos hc₁ hV0).le
    have h4 := h1.trans (mul_le_mul_of_nonneg_left h2 h3)
    have h5 := Real.sqrt_le_sqrt h4
    rw [Real.sqrt_mul h3] at h5
    exact h5
  have hroot := Phase.root_bound hE hc₁ hU hV hR1 hℓ
  rw [Phase.phaseForm_eq, Phase.sum_window _ _ _ _ _
    (fun n : ℕ => c₁ * U ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₂ * U)
    (fun k : ℕ => c₁ * V ≤ (k : ℝ) ∧ (k : ℝ) ≤ c₂ * V) ha0 hb0]
  refine hint.trans ?_
  calc K₀ * Real.sqrt (∑ n ∈ (Finset.univ.image
          (fun t : AuxList 𝔊.big A => tupleProd A t)).filter
          (fun n : ℕ => c₁ * U ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₂ * U),
          ‖fiberCoeff 𝔊.big A (Phase.twist ζ A G) n‖ ^ 2) *
        Real.sqrt (∑ k ∈ (Finset.univ.image
          (fun t : AuxList 𝔊.big Bs => tupleProd Bs t)).filter
          (fun k : ℕ => c₁ * V ≤ (k : ℝ) ∧ (k : ℝ) ≤ c₂ * V),
          ‖fiberCoeff 𝔊.big Bs (Phase.twist ζ Bs F) k‖ ^ 2) *
        Real.sqrt (U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * Real.log (2 * (r : ℝ))))
      ≤ K₀ * (Real.sqrt (Real.log x ^ atomExponent P m / (c₁ * U)) * tupleNorm 𝔊.big A G) *
          (Real.sqrt (Real.log x ^ atomExponent P m / (c₁ * V)) * tupleNorm 𝔊.big Bs F) *
          Real.sqrt (U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * Real.log (2 * (r : ℝ)))) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hcolA hK₀.le) hcolB (Real.sqrt_nonneg _)
          (mul_nonneg hK₀.le (mul_nonneg (Real.sqrt_nonneg _) (wNorm_nonneg _ _)))
    _ = K₀ * (Real.sqrt (Real.log x ^ atomExponent P m / (c₁ * U)) *
          Real.sqrt (Real.log x ^ atomExponent P m / (c₁ * V)) *
          Real.sqrt (U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * Real.log (2 * (r : ℝ))))) *
          (tupleNorm 𝔊.big Bs F * tupleNorm 𝔊.big A G) := by ring
    _ ≤ K₀ * (2 / c₁ * Real.log x ^ atomExponent P m *
          Real.sqrt (1 / V + 1 / (r : ℝ) + Real.log (2 * (r : ℝ)) / U +
            (r : ℝ) * Real.log (2 * (r : ℝ)) / (U * V))) *
          (tupleNorm 𝔊.big Bs F * tupleNorm 𝔊.big A G) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot hK₀.le)
          (mul_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _))
    _ = 2 * K₀ / c₁ * Real.log x ^ atomExponent P m *
          Real.sqrt (1 / V + 1 / (r : ℝ) + Real.log (2 * (r : ℝ)) / U +
            (r : ℝ) * Real.log (2 * (r : ℝ)) / (U * V)) *
          (tupleNorm 𝔊.big Bs F * tupleNorm 𝔊.big A G) := by ring

/-- **The probability-space bilinear bound (eq:ideal-probability-bilinear)**
[S-03:0163–0174]. -/
theorem probabilityBilinear : ProbabilityBilinear :=
  probabilityBilinear_of collapseBound integerBilinear

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
