module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Statements
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# [S] Lemma 4.3 from its intermediate statements

Source: `verification/stage7-sources/S-03.tex`, lines 294–314 and 414–437.

`comparisonKernelLemma_of_statements` proves `ComparisonKernelLemma` from the four statements
`ScaleLowerBound`, `DyadicSummation`, `MinorArcBound`, `MajorArcBound` of
`Comparison/Statements.lean`. The steps proved here:

* `exists_dirichletData` — (eq:ideal-dirichlet) [S-03:0304–0314]: "Dirichlet approximation with
  maximum denominator `⌊Z/S⌋` gives a reduced fraction satisfying `α = u/r + β`, `1 ≤ r ≤ Z/S`,
  `|β| ≤ r⁻²`, `|β| Z ≤ 2S/r`", for `Z ≥ S > 0` (Mathlib:
  `Real.exists_rat_abs_sub_le_and_den_le`, which returns a rational number, so the fraction is
  reduced).
* `dyadicContract_of_arcs` — on one pair of dyads, the two cases `r ≤ Q` and `r > Q` of the
  approximation. "Here `Z/S → ∞`" [S-03:0312]: a nonzero test `g` on the dyad `[2^a, 2^{a+1})`
  gives a tuple with `2^{a+1} > X_A ≥ L^{s_*+1}` (`ScaleLowerBound`), so `Z = 2^a 2^b ≥ S` as soon
  as `L ≥ 2`; if `g = 0` the left side vanishes.
* `comparisonContract_of_statements` — "a noncircular choice of parameters" [S-03:0414–0437]:
  the exponents `B₀ = dyadExponent`, `q_* = s_* = arcExponent`, `h_* = cellExponent`,
  `x_* = massExponent` satisfy the inequalities of (eq:ideal-parameter-order) required by
  `DyadicSummation`, `MinorArcBound` and `MajorArcBound`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### The exponents [S-03:0414–0437] -/

/-- `κ ≥ 0`. -/
theorem atomExponent_nonneg (P : GroupParams) (m : ℕ) : 0 ≤ atomExponent P m := by
  unfold atomExponent
  have h1 : (0 : ℝ) ≤ Real.log (m.factorial : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr (Nat.factorial_pos m))
  have h2 : (0 : ℝ) ≤ Real.log (max 1 P.vMinus⁻¹) := Real.log_nonneg (le_max_left _ _)
  exact mul_nonneg P.C₀_pos.le (add_nonneg h1 (mul_nonneg (Nat.cast_nonneg _) h2))

theorem d_pos (P : GroupParams) : 0 < P.d := by
  linarith [P.a_pos, P.a_lt_b, P.b_lt_c, P.c_lt_d]

/-- "`B₀ > A₀ + 2(d+1) + 10`" [S-03:0423]. -/
theorem dyadExponent_gt (P : GroupParams) (A₀ : ℝ) :
    A₀ + 2 * (P.d + 1) + 10 < dyadExponent P A₀ := by
  unfold dyadExponent
  linarith

theorem dyadExponent_pos (P : GroupParams) {A₀ : ℝ} (hA₀ : 0 < A₀) : 0 < dyadExponent P A₀ := by
  have h := dyadExponent_gt P A₀
  have hd := d_pos P
  linarith

/-- "`q_*, s_* > 2(B₀ + κ + 10) + d + 1`" [S-03:0424]. -/
theorem arcExponent_gt (P : GroupParams) (m : ℕ) (A₀ : ℝ) :
    2 * (dyadExponent P A₀ + atomExponent P m + 10) + P.d + 1 < arcExponent P m A₀ := by
  unfold arcExponent
  linarith

theorem arcExponent_nonneg (P : GroupParams) (m : ℕ) {A₀ : ℝ} (hA₀ : 0 < A₀) :
    0 ≤ arcExponent P m A₀ := by
  have h := arcExponent_gt P m A₀
  have hB := dyadExponent_pos P hA₀
  have hκ := atomExponent_nonneg P m
  have hd := d_pos P
  linarith

/-- "`h_* > 4 q_* + max(s_*, C₄) + B₀ + 10`" [S-03:0425], with `s_* = q_*`. -/
theorem cellExponent_gt (P : GroupParams) (m : ℕ) (A₀ C₄ : ℝ) :
    4 * arcExponent P m A₀ + max (arcExponent P m A₀) C₄ + dyadExponent P A₀ + 10 <
      cellExponent P m A₀ C₄ := by
  unfold cellExponent
  linarith

theorem cellExponent_nonneg (P : GroupParams) (m : ℕ) {A₀ C₄ : ℝ} (hA₀ : 0 < A₀)
    (hC₄ : 0 ≤ C₄) : 0 ≤ cellExponent P m A₀ C₄ := by
  have h := cellExponent_gt P m A₀ C₄
  have hB := dyadExponent_pos P hA₀
  have hq := arcExponent_nonneg P m hA₀
  have hmax : C₄ ≤ max (arcExponent P m A₀) C₄ := le_max_right _ _
  linarith

/-- "`x_* > 2 B₀ + d + 1 + h_* + 10`" [S-03:0426]. -/
theorem massExponent_gt (P : GroupParams) (m : ℕ) (A₀ C₄ : ℝ) :
    2 * dyadExponent P A₀ + P.d + 1 + cellExponent P m A₀ C₄ + 10 < massExponent P m A₀ C₄ := by
  unfold massExponent
  linarith

theorem massExponent_nonneg (P : GroupParams) (m : ℕ) {A₀ C₄ : ℝ} (hA₀ : 0 < A₀)
    (hC₄ : 0 ≤ C₄) : 0 ≤ massExponent P m A₀ C₄ := by
  have h := massExponent_gt P m A₀ C₄
  have hB := dyadExponent_pos P hA₀
  have hh := cellExponent_nonneg P m hA₀ hC₄
  have hd := d_pos P
  linarith

/-! ### The Dirichlet approximation (eq:ideal-dirichlet) [S-03:0304–0314] -/

/-- **(eq:ideal-dirichlet)**: for `Z ≥ S > 0`, "Dirichlet approximation with maximum denominator
`⌊Z/S⌋` gives a reduced fraction satisfying `α = u/r + β`, `1 ≤ r ≤ Z/S`, `|β| ≤ r⁻²`,
`|β| Z ≤ 2S/r`". -/
theorem exists_dirichletData (α : ℝ) {Z S : ℝ} (hS : 0 < S) (hZ : S ≤ Z) :
    ∃ (u : ℤ) (r : ℕ) (β : ℝ), DirichletData α Z S u r β := by
  have hZ0 : 0 ≤ Z := hS.le.trans hZ
  have hZS : 1 ≤ Z / S := (one_le_div hS).mpr hZ
  have hn : 0 < ⌊Z / S⌋₊ := Nat.floor_pos.mpr hZS
  obtain ⟨q, hq, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hn
  have hr0 : 0 < q.den := q.den_pos
  have hr : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hr0
  have hrn : (q.den : ℝ) ≤ (⌊Z / S⌋₊ : ℝ) := by exact_mod_cast hden
  have hnle : (⌊Z / S⌋₊ : ℝ) ≤ Z / S := Nat.floor_le (le_trans zero_le_one hZS)
  have hnlt : Z / S < (⌊Z / S⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn1 : (0 : ℝ) < (⌊Z / S⌋₊ : ℝ) + 1 := by positivity
  have hZlt : Z < ((⌊Z / S⌋₊ : ℝ) + 1) * S := (div_lt_iff₀ hS).mp hnlt
  refine ⟨q.num, q.den, α - (q : ℝ), hr0, Rat.isCoprime_num_den q, ?_, hrn.trans hnle, ?_, ?_⟩
  · rw [Rat.cast_def]
    ring
  · calc |α - (q : ℝ)| ≤ 1 / (((⌊Z / S⌋₊ : ℝ) + 1) * (q.den : ℝ)) := hq
      _ ≤ 1 / ((q.den : ℝ) * (q.den : ℝ)) :=
          one_div_le_one_div_of_le (mul_pos hr hr)
            (mul_le_mul_of_nonneg_right (by linarith) hr.le)
      _ = ((q.den : ℝ) ^ 2)⁻¹ := by rw [one_div, sq]
  · have h1 : |α - (q : ℝ)| * Z ≤ 1 / (((⌊Z / S⌋₊ : ℝ) + 1) * (q.den : ℝ)) * Z :=
      mul_le_mul_of_nonneg_right hq hZ0
    have h2 : 1 / (((⌊Z / S⌋₊ : ℝ) + 1) * (q.den : ℝ)) * Z ≤ S / (q.den : ℝ) := by
      rw [one_div_mul_eq_div, div_le_div_iff₀ (mul_pos hn1 hr) hr]
      have h4 : Z * (q.den : ℝ) ≤ ((⌊Z / S⌋₊ : ℝ) + 1) * S * (q.den : ℝ) :=
        mul_le_mul_of_nonneg_right hZlt.le hr.le
      linarith
    have h3 : S / (q.den : ℝ) ≤ 2 * S / (q.den : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hr.le
    exact h1.trans (h2.trans h3)

/-! ### One pair of dyads -/

section Defect

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

/-- The left side of (eq:ideal-comparison) vanishes when the test `g` vanishes. -/
theorem comparisonDefect_eq_zero_of_right (big : B → Finset ℕ) (A Bs : B → Finset (Fin J))
    (Q h ξ : ℝ) (f : AuxList big Bs → ℂ) {g : AuxList big A → ℂ} (hg : ∀ t, g t = 0)
    (α ζ : ℝ) : comparisonDefect big A Bs Q h ξ f g α ζ = 0 := by
  unfold comparisonDefect
  refine Finset.sum_eq_zero fun xA _ => Finset.sum_eq_zero fun xB _ =>
    Finset.sum_eq_zero fun dA _ => Finset.sum_eq_zero fun dB _ => ?_
  rw [hg xA, mul_zero, mul_zero, zero_mul]

end Defect

/-- **One pair of dyads** [S-03:0304–0314]: the estimates for `r > Q` and for `r ≤ Q`, applied to
the Dirichlet approximation of `α` with maximum denominator `⌊Z/S⌋`, `Z = 2^a 2^b`,
`S = L^{s_*}`, give the estimate on the pair of dyads. -/
theorem dyadicContract_of_arcs (hscale : ScaleLowerBound) {P : GroupParams} {m : ℕ}
    {B₀ C₄ qs ss hs xs : ℝ} (hminor : MinorArcContract P m B₀ qs ss hs xs)
    (hmajor : MajorArcContract P m B₀ C₄ qs ss hs xs) : DyadicContract P m B₀ C₄ qs hs xs := by
  obtain ⟨x₁, h₁⟩ := hminor
  obtain ⟨x₂, h₂⟩ := hmajor
  obtain ⟨x₃, h₃⟩ := hscale P (ss + 1)
  refine ⟨max (max x₁ x₂) (max x₃ (Real.exp 2)), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 hint J A Bs hA hBs hAm hBm a b f g hf hg α ζ hζ
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx₂ : x₂ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx₃ : x₃ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxe : Real.exp 2 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hL2 : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL0 : 0 < Real.log x := by linarith
  by_cases hg0 : ∀ t, g t = 0
  · rw [comparisonDefect_eq_zero_of_right 𝔊.big A Bs _ _ _ f hg0 α ζ, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hL0.le _)
      (mul_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _))
  · obtain ⟨tA, htA⟩ := not_forall.mp hg0
    have ha : Nat.log 2 (tupleProd A tA) = a := hg tA htA
    have hP : Real.log x ^ (ss + 1) ≤ (tupleProd A tA : ℝ) := (h₃ x hx₃ S B 𝔊).2 J A hA tA
    have hlt : tupleProd A tA < 2 ^ (Nat.log 2 (tupleProd A tA) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    rw [ha] at hlt
    have hlt' : (tupleProd A tA : ℝ) < (2 : ℝ) ^ (a + 1) := by exact_mod_cast hlt
    rw [pow_succ] at hlt'
    have hS : 0 < Real.log x ^ ss := Real.rpow_pos_of_pos hL0 _
    have hS1 : Real.log x ^ (ss + 1) = Real.log x ^ ss * Real.log x :=
      Real.rpow_add_one hL0.ne' ss
    have hSU : Real.log x ^ ss ≤ (2 : ℝ) ^ a := by
      have h4 : Real.log x ^ ss * 2 ≤ Real.log x ^ ss * Real.log x :=
        mul_le_mul_of_nonneg_left hL2 hS.le
      linarith
    have hV1 : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
    have hU0 : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
    have hZ : Real.log x ^ ss ≤ (2 : ℝ) ^ a * (2 : ℝ) ^ b :=
      hSU.trans (le_mul_of_one_le_right hU0.le hV1)
    obtain ⟨u, r, β, hdata⟩ := exists_dirichletData α hS hZ
    by_cases hr : (r : ℝ) ≤ Real.log x ^ qs
    · exact h₂ x hx₂ S B 𝔊 hint J A Bs hA hBs hAm hBm a b f g hf hg α ζ β u r hζ hdata hr
    · exact h₁ x hx₁ S B 𝔊 hint J A Bs hA hBs hAm hBm a b f g hf hg α ζ β u r hdata
        (not_le.mp hr)

/-! ### The lemma -/

/-- **(eq:ideal-comparison) with the explicit exponents of (eq:ideal-parameter-order)**
[S-03:0414–0437]: `Q = L^{q_*}`, `h = L^{-h_*}`, `ξ = L^{-x_*}` with `q_* = arcExponent`,
`h_* = cellExponent`, `x_* = massExponent`; the proof uses `B₀ = dyadExponent` and
`S = L^{s_*}`, `s_* = q_*`. "None of these choices involves `J`." -/
theorem comparisonContract_of_statements (hscale : ScaleLowerBound) (hdy : DyadicSummation)
    (hminor : MinorArcBound) (hmajor : MajorArcBound) (P : GroupParams) (m : ℕ) (A₀ C₄ : ℝ)
    (hA₀ : 0 < A₀) (hC₄ : 0 ≤ C₄) :
    ComparisonContract P m A₀ C₄ (arcExponent P m A₀) (cellExponent P m A₀ C₄)
      (massExponent P m A₀ C₄) := by
  have hB := dyadExponent_pos P hA₀
  have hq := arcExponent_gt P m A₀
  have hq0 := arcExponent_nonneg P m hA₀
  have hh := cellExponent_gt P m A₀ C₄
  have hh0 := cellExponent_nonneg P m hA₀ hC₄
  have hx := massExponent_gt P m A₀ C₄
  have hx0 := massExponent_nonneg P m hA₀ hC₄
  refine hdy P m A₀ C₄ (arcExponent P m A₀) (cellExponent P m A₀ C₄) (massExponent P m A₀ C₄)
    (dyadExponent P A₀) (dyadExponent_gt P A₀) ?_
  exact dyadicContract_of_arcs hscale
    (hminor P m (dyadExponent P A₀) (arcExponent P m A₀) (arcExponent P m A₀)
      (cellExponent P m A₀ C₄) (massExponent P m A₀ C₄) hB hq hq hh0 hx0)
    (hmajor P m (dyadExponent P A₀) C₄ (arcExponent P m A₀) (arcExponent P m A₀)
      (cellExponent P m A₀ C₄) (massExponent P m A₀ C₄) hB hC₄ hq0 hh hx)

/-- **[S] Lemma 4.3 (comparison kernel) from its intermediate statements** [S-03:0270–0437]. -/
theorem comparisonKernelLemma_of_statements (hscale : ScaleLowerBound) (hdy : DyadicSummation)
    (hminor : MinorArcBound) (hmajor : MajorArcBound) : ComparisonKernelLemma := by
  intro P m A₀ C₄ hA₀ hC₄
  exact ⟨arcExponent P m A₀, cellExponent P m A₀ C₄, massExponent P m A₀ C₄,
    arcExponent_nonneg P m hA₀, cellExponent_nonneg P m hA₀ hC₄,
    massExponent_nonneg P m hA₀ hC₄,
    comparisonContract_of_statements hscale hdy hminor hmajor P m A₀ C₄ hA₀ hC₄⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
