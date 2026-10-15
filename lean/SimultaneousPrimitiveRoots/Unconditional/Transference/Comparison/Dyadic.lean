module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Scales
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The dyadic summation

Source: `verification/stage7-sources/S-03.tex`, lines 295–302 (`[S-03:0295–0302]`).

`dyadicSummation : DyadicSummation`. "Split the tests according to dyads `X_A ∈ [U, 2U)` and
`X_B ∈ [V, 2V)`. Each selected product lies between `exp(L^c)` and `exp(m C₀ T L^d)`; thus for
sufficiently large `x` there are at most `L^{d+1}` dyads for each product. We prove a bound
`L^{-B₀}` on each pair of dyads, with `B₀ > A₀ + 2(d+1) + 10`. Summing the bounds proves the
lemma, even using the crude bound of the original test norm for every dyadic restriction."

* `Dyadic.piece`, `Dyadic.dyads` — the restriction of a test to the dyad `Nat.log 2 P_Λ = a`, and
  the finite set of the dyads met by the tuples of type `Λ`.
* `Dyadic.defect_eq_sum_pieces` — the left side of (eq:ideal-comparison) is sesquilinear in the
  two tests, so it is the sum over the pairs of dyads.
* `Dyadic.card_dyads_le_rpow` — there are at most `L^{d+1}` dyads as soon as
  `L ≥ (2 m C₀ / log 2 + 1)²`: the dyad index is at most `log P_Λ / log 2 ≤ m C₀ T L^d / log 2`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Dyadic

/-! ### The left side of (eq:ideal-comparison) is sesquilinear -/

section Algebra

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

theorem defect_eq_zero_of_left (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ)
    {f : AuxList big Bs → ℂ} (hf : ∀ t, f t = 0) (g : AuxList big A → ℂ) (α ζ : ℝ) :
    comparisonDefect big A Bs Q h ξ f g α ζ = 0 := by
  unfold comparisonDefect
  refine Finset.sum_eq_zero fun xA _ => Finset.sum_eq_zero fun xB _ =>
    Finset.sum_eq_zero fun dA _ => Finset.sum_eq_zero fun dB _ => ?_
  rw [hf xB, map_zero, zero_mul, mul_zero, zero_mul]

theorem defect_add_right (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ)
    (f : AuxList big Bs → ℂ) (g₁ g₂ : AuxList big A → ℂ) (α ζ : ℝ) :
    comparisonDefect big A Bs Q h ξ f (fun t => g₁ t + g₂ t) α ζ =
      comparisonDefect big A Bs Q h ξ f g₁ α ζ + comparisonDefect big A Bs Q h ξ f g₂ α ζ := by
  unfold comparisonDefect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun xA _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun xB _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun dA _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun dB _ => ?_
  ring

theorem defect_add_left (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ)
    (f₁ f₂ : AuxList big Bs → ℂ) (g : AuxList big A → ℂ) (α ζ : ℝ) :
    comparisonDefect big A Bs Q h ξ (fun t => f₁ t + f₂ t) g α ζ =
      comparisonDefect big A Bs Q h ξ f₁ g α ζ + comparisonDefect big A Bs Q h ξ f₂ g α ζ := by
  unfold comparisonDefect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun xA _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun xB _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun dA _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun dB _ => ?_
  rw [map_add (starRingEnd ℂ) (f₁ xB) (f₂ xB)]
  ring

theorem defect_sum_right {ι : Type} (s : Finset ι) (big : B → Finset ℕ)
    (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ) (f : AuxList big Bs → ℂ)
    (G : ι → AuxList big A → ℂ) (α ζ : ℝ) :
    comparisonDefect big A Bs Q h ξ f (fun t => ∑ i ∈ s, G i t) α ζ =
      ∑ i ∈ s, comparisonDefect big A Bs Q h ξ f (G i) α ζ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact comparisonDefect_eq_zero_of_right big A Bs Q h ξ f (fun t => Finset.sum_empty) α ζ
  | insert i s hi ih =>
    have hfun : (fun t => ∑ j ∈ insert i s, G j t) = fun t => G i t + ∑ j ∈ s, G j t :=
      funext fun t => Finset.sum_insert hi
    rw [hfun, defect_add_right big A Bs Q h ξ f (G i) (fun t => ∑ j ∈ s, G j t) α ζ,
      Finset.sum_insert hi, ih]

theorem defect_sum_left {ι : Type} (s : Finset ι) (big : B → Finset ℕ)
    (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ) (F : ι → AuxList big Bs → ℂ)
    (g : AuxList big A → ℂ) (α ζ : ℝ) :
    comparisonDefect big A Bs Q h ξ (fun t => ∑ i ∈ s, F i t) g α ζ =
      ∑ i ∈ s, comparisonDefect big A Bs Q h ξ (F i) g α ζ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact defect_eq_zero_of_left big A Bs Q h ξ (fun t => Finset.sum_empty) g α ζ
  | insert i s hi ih =>
    have hfun : (fun t => ∑ j ∈ insert i s, F j t) = fun t => F i t + ∑ j ∈ s, F j t :=
      funext fun t => Finset.sum_insert hi
    rw [hfun, defect_add_left big A Bs Q h ξ (F i) (fun t => ∑ j ∈ s, F j t) g α ζ,
      Finset.sum_insert hi, ih]

/-- A double sum of terms of norm at most `C`. -/
theorem norm_double_sum_le {ι κ : Type} (s : Finset ι) (t : Finset κ) (D : ι → κ → ℂ) (C : ℝ)
    (h : ∀ a ∈ s, ∀ b ∈ t, ‖D a b‖ ≤ C) :
    ‖∑ a ∈ s, ∑ b ∈ t, D a b‖ ≤ (s.card : ℝ) * ((t.card : ℝ) * C) := by
  calc ‖∑ a ∈ s, ∑ b ∈ t, D a b‖ ≤ ∑ a ∈ s, ‖∑ b ∈ t, D a b‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ s, ∑ b ∈ t, C :=
        Finset.sum_le_sum fun a ha => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b hb => h a ha b hb)
    _ = (s.card : ℝ) * ((t.card : ℝ) * C) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]

/-! ### Dyadic pieces -/

/-- The restriction of a test to the dyad `P_Λ ∈ [2^a, 2^{a+1})`. -/
def piece {big : B → Finset ℕ} (Λ : B → Finset (Fin J)) (F : AuxList big Λ → ℂ) (a : ℕ)
    (t : AuxList big Λ) : ℂ :=
  if Nat.log 2 (tupleProd Λ t) = a then F t else 0

/-- The dyads met by the products of the tuples of type `Λ`. -/
def dyads (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) : Finset ℕ :=
  Finset.univ.image fun t : AuxList big Λ => Nat.log 2 (tupleProd Λ t)

theorem sum_piece (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (F : AuxList big Λ → ℂ)
    (t : AuxList big Λ) : ∑ a ∈ dyads big Λ, piece Λ F a t = F t := by
  have hmem : Nat.log 2 (tupleProd Λ t) ∈ dyads big Λ := by
    unfold dyads
    exact Finset.mem_image_of_mem (fun t : AuxList big Λ => Nat.log 2 (tupleProd Λ t))
      (Finset.mem_univ t)
  unfold piece
  rw [Finset.sum_ite_eq, if_pos hmem]

omit [DecidableEq B] in
theorem norm_piece_le {big : B → Finset ℕ} (Λ : B → Finset (Fin J)) (F : AuxList big Λ → ℂ)
    (a : ℕ) (t : AuxList big Λ) : ‖piece Λ F a t‖ ≤ ‖F t‖ := by
  unfold piece
  by_cases hc : Nat.log 2 (tupleProd Λ t) = a
  · rw [if_pos hc]
  · rw [if_neg hc, norm_zero]
    exact norm_nonneg _

omit [DecidableEq B] in
theorem dyadSupported_piece (big : B → Finset ℕ) (Λ : B → Finset (Fin J))
    (F : AuxList big Λ → ℂ) (a : ℕ) : DyadSupported big Λ a (piece Λ F a) := by
  intro t ht
  by_contra hne
  apply ht
  unfold piece
  exact if_neg hne

/-- The left side of (eq:ideal-comparison) is the sum over the pairs of dyads. -/
theorem defect_eq_sum_pieces (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ)
    (f : AuxList big Bs → ℂ) (g : AuxList big A → ℂ) (α ζ : ℝ) :
    comparisonDefect big A Bs Q h ξ f g α ζ =
      ∑ a ∈ dyads big A, ∑ b ∈ dyads big Bs,
        comparisonDefect big A Bs Q h ξ (piece Bs f b) (piece A g a) α ζ := by
  have hg : (fun t => ∑ a ∈ dyads big A, piece A g a t) = g :=
    funext fun t => sum_piece big A g t
  have hf : (fun t => ∑ b ∈ dyads big Bs, piece Bs f b t) = f :=
    funext fun t => sum_piece big Bs f t
  calc comparisonDefect big A Bs Q h ξ f g α ζ
      = comparisonDefect big A Bs Q h ξ f (fun t => ∑ a ∈ dyads big A, piece A g a t) α ζ := by
        rw [hg]
    _ = ∑ a ∈ dyads big A, comparisonDefect big A Bs Q h ξ f (piece A g a) α ζ :=
        defect_sum_right (dyads big A) big A Bs Q h ξ f (piece A g) α ζ
    _ = ∑ a ∈ dyads big A, ∑ b ∈ dyads big Bs,
          comparisonDefect big A Bs Q h ξ (piece Bs f b) (piece A g a) α ζ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        calc comparisonDefect big A Bs Q h ξ f (piece A g a) α ζ
            = comparisonDefect big A Bs Q h ξ (fun t => ∑ b ∈ dyads big Bs, piece Bs f b t)
                (piece A g a) α ζ := by rw [hf]
          _ = ∑ b ∈ dyads big Bs,
                comparisonDefect big A Bs Q h ξ (piece Bs f b) (piece A g a) α ζ :=
              defect_sum_left (dyads big Bs) big A Bs Q h ξ (piece Bs f) (piece A g a) α ζ

end Algebra

/-! ### Norms of the pieces and the number of dyads -/

section Groups

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] {J : ℕ}

theorem tupleNorm_piece_le (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J))
    (F : AuxList 𝔊.big Λ → ℂ) (a : ℕ) :
    tupleNorm 𝔊.big Λ (piece Λ F a) ≤ tupleNorm 𝔊.big Λ F := by
  unfold tupleNorm wNorm
  refine Real.sqrt_le_sqrt ?_
  unfold wNormSq
  exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_piece_le Λ F a t) 2) (tupleWeight_nonneg 𝔊 Λ t)

/-- The number of dyads is at most `log P_Λ / log 2 + 1 ≤ m C₀ T L^d / log 2 + 1`. -/
theorem card_dyads_le (𝔊 : PrimeGroups P x S B) (hL : 1 ≤ Real.log x) (Λ : B → Finset (Fin J))
    {m : ℕ} (hΛ : ∀ g, (Λ g).card ≤ m) :
    ((dyads 𝔊.big Λ).card : ℝ) ≤
      (m : ℝ) * P.C₀ * Real.log (Real.log x) * Real.log x ^ P.d / Real.log 2 + 1 := by
  have hL0 : 0 ≤ Real.log x := le_trans zero_le_one hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hU0 : 0 ≤ (m : ℝ) * P.C₀ * Real.log (Real.log x) * Real.log x ^ P.d :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) P.C₀_pos.le) (Real.log_nonneg hL))
      (Real.rpow_nonneg hL0 _)
  have hsub : dyads 𝔊.big Λ ⊆ Finset.range
      (⌊(m : ℝ) * P.C₀ * Real.log (Real.log x) * Real.log x ^ P.d / Real.log 2⌋₊ + 1) := by
    intro a ha
    unfold dyads at ha
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_range, Nat.lt_add_one_iff]
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hlog2]
    have hpos : 0 < tupleProd Λ t := tupleProd_pos 𝔊 Λ t
    have h1 : 2 ^ Nat.log 2 (tupleProd Λ t) ≤ tupleProd Λ t := Nat.pow_log_le_self 2 hpos.ne'
    have h2 : (2 : ℝ) ^ Nat.log 2 (tupleProd Λ t) ≤ ((tupleProd Λ t : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 (tupleProd Λ t)) ≤
        Real.log ((tupleProd Λ t : ℕ) : ℝ) := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    exact h3.trans (log_tupleProd_le_const 𝔊 hL0 Λ hΛ t)
  have hcard : (dyads 𝔊.big Λ).card ≤
      ⌊(m : ℝ) * P.C₀ * Real.log (Real.log x) * Real.log x ^ P.d / Real.log 2⌋₊ + 1 := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_range] at h
  have hfl : (⌊(m : ℝ) * P.C₀ * Real.log (Real.log x) * Real.log x ^ P.d / Real.log 2⌋₊ : ℝ) ≤
      (m : ℝ) * P.C₀ * Real.log (Real.log x) * Real.log x ^ P.d / Real.log 2 :=
    Nat.floor_le (div_nonneg hU0 hlog2.le)
  have hcard' : ((dyads 𝔊.big Λ).card : ℝ) ≤
      (⌊(m : ℝ) * P.C₀ * Real.log (Real.log x) * Real.log x ^ P.d / Real.log 2⌋₊ : ℝ) + 1 := by
    exact_mod_cast hcard
  linarith

/-- "For sufficiently large `x` there are at most `L^{d+1}` dyads for each product"
[S-03:0297–0298]: as soon as `L ≥ (2 m C₀ / log 2 + 1)²`. -/
theorem card_dyads_le_rpow (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) {m : ℕ}
    (hΛ : ∀ g, (Λ g).card ≤ m)
    (hL : (2 * ((m : ℝ) * P.C₀ / Real.log 2) + 1) ^ 2 ≤ Real.log x) :
    ((dyads 𝔊.big Λ).card : ℝ) ≤ Real.log x ^ (P.d + 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 ≤ (m : ℝ) * P.C₀ / Real.log 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) P.C₀_pos.le) hlog2.le
  have hL1 : 1 ≤ Real.log x := by nlinarith [mul_nonneg hc0 hc0]
  have hL0 : 0 < Real.log x := by linarith
  have hT : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have hLd : 1 ≤ Real.log x ^ P.d := Real.one_le_rpow hL1 (d_pos P).le
  have h1 := card_dyads_le 𝔊 hL1 Λ hΛ
  have h2 : (m : ℝ) * P.C₀ / Real.log 2 * Real.log (Real.log x) + 1 ≤ Real.log x :=
    mul_log_add_one_le hc0 hL
  have h3 : Real.log x ^ (P.d + 1) = Real.log x ^ P.d * Real.log x :=
    Real.rpow_add_one hL0.ne' P.d
  have h5 : (m : ℝ) * P.C₀ * Real.log (Real.log x) * Real.log x ^ P.d / Real.log 2 =
      (m : ℝ) * P.C₀ / Real.log 2 * Real.log (Real.log x) * Real.log x ^ P.d := by ring
  have h6 : Real.log x ^ P.d * ((m : ℝ) * P.C₀ / Real.log 2 * Real.log (Real.log x) + 1) ≤
      Real.log x ^ P.d * Real.log x :=
    mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one hLd)
  rw [h3]
  rw [h5] at h1
  nlinarith [h6, hLd, h1]

end Groups

end Dyadic

/-! ### The dyadic summation -/

/-- **The dyadic summation** [S-03:0295–0302]. -/
theorem dyadicSummation : DyadicSummation := by
  intro P m A₀ C₄ qs hs xs B₀ hB₀ hdy
  obtain ⟨x₁, h₁⟩ := hdy
  refine ⟨max x₁ (Real.exp ((2 * ((m : ℝ) * P.C₀ / Real.log 2) + 1) ^ 2)), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 hint J A Bs hA hBs hAm hBm f g α ζ hζ
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp ((2 * ((m : ℝ) * P.C₀ / Real.log 2) + 1) ^ 2) ≤ x :=
    (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hLc : (2 * ((m : ℝ) * P.C₀ / Real.log 2) + 1) ^ 2 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr hxe
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 ≤ (m : ℝ) * P.C₀ / Real.log 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) P.C₀_pos.le) hlog2.le
  have hL1 : 1 ≤ Real.log x := by nlinarith [mul_nonneg hc0 hc0]
  have hL0 : 0 < Real.log x := by linarith
  have hX : 0 ≤ tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g :=
    mul_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _)
  have hB0 : 0 ≤ Real.log x ^ (-B₀) := Real.rpow_nonneg hL0.le _
  have hLd0 : 0 ≤ Real.log x ^ (P.d + 1) := Real.rpow_nonneg hL0.le _
  have hcA : ((Dyadic.dyads 𝔊.big A).card : ℝ) ≤ Real.log x ^ (P.d + 1) :=
    Dyadic.card_dyads_le_rpow 𝔊 A hAm hLc
  have hcB : ((Dyadic.dyads 𝔊.big Bs).card : ℝ) ≤ Real.log x ^ (P.d + 1) :=
    Dyadic.card_dyads_le_rpow 𝔊 Bs hBm hLc
  have hpow : Real.log x ^ (P.d + 1) * Real.log x ^ (P.d + 1) * Real.log x ^ (-B₀) ≤
      Real.log x ^ (-A₀) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hterm : ∀ a ∈ Dyadic.dyads 𝔊.big A, ∀ b ∈ Dyadic.dyads 𝔊.big Bs,
      ‖comparisonDefect 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
          (Dyadic.piece Bs f b) (Dyadic.piece A g a) α ζ‖ ≤
        Real.log x ^ (-B₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g) := by
    intro a _ b _
    refine (h₁ x hx₁ S B 𝔊 hint J A Bs hA hBs hAm hBm a b (Dyadic.piece Bs f b)
      (Dyadic.piece A g a) (Dyadic.dyadSupported_piece 𝔊.big Bs f b)
      (Dyadic.dyadSupported_piece 𝔊.big A g a) α ζ hζ).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB0
    exact mul_le_mul (Dyadic.tupleNorm_piece_le 𝔊 Bs f b) (Dyadic.tupleNorm_piece_le 𝔊 A g a)
      (wNorm_nonneg _ _) (wNorm_nonneg _ _)
  have hsum : ‖∑ a ∈ Dyadic.dyads 𝔊.big A, ∑ b ∈ Dyadic.dyads 𝔊.big Bs,
      comparisonDefect 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
        (Dyadic.piece Bs f b) (Dyadic.piece A g a) α ζ‖ ≤
      ((Dyadic.dyads 𝔊.big A).card : ℝ) * (((Dyadic.dyads 𝔊.big Bs).card : ℝ) *
        (Real.log x ^ (-B₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g))) :=
    Dyadic.norm_double_sum_le _ _ _ _ hterm
  rw [Dyadic.defect_eq_sum_pieces]
  calc ‖∑ a ∈ Dyadic.dyads 𝔊.big A, ∑ b ∈ Dyadic.dyads 𝔊.big Bs,
        comparisonDefect 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
          (Dyadic.piece Bs f b) (Dyadic.piece A g a) α ζ‖
      ≤ ((Dyadic.dyads 𝔊.big A).card : ℝ) * (((Dyadic.dyads 𝔊.big Bs).card : ℝ) *
          (Real.log x ^ (-B₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g))) := hsum
    _ ≤ Real.log x ^ (P.d + 1) * (Real.log x ^ (P.d + 1) *
          (Real.log x ^ (-B₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g))) :=
        mul_le_mul hcA (mul_le_mul_of_nonneg_right hcB (mul_nonneg hB0 hX))
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB0 hX)) hLd0
    _ = Real.log x ^ (P.d + 1) * Real.log x ^ (P.d + 1) * Real.log x ^ (-B₀) *
          (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g) := by ring
    _ ≤ Real.log x ^ (-A₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g) :=
        mul_le_mul_of_nonneg_right hpow hX

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
