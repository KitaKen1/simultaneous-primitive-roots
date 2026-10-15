module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Dyadic
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Denominators larger than `Q`: the tools

Source: `verification/stage7-sources/S-03.tex`, lines 316–337 (`[S-03:0316–0337]`).

* `Minor.defect_eq_sub` — the left side of (eq:ideal-comparison) is the raw bilinear form minus
  the bilinear form of the two tests after kernel integration: "for the comparison term, move the
  two separate kernel integrations onto the two tests".
* `Minor.kernelIntX_eq_zero` — "the resulting tests on `D_A, D_B` are supported in `[U/2, 4U]`
  and `[V/2, 4V]` for large `x`, by the log localization" (here `[U/4, 8U]`, for every `h ≤ 1`).
* `Minor.sigma_sqrt_le` — (eq:ideal-minor-error):
  `(1/V + 1/r + log(2r)/U + r log(2r)/(UV))^{1/2} ≤ 2 L^{-(B₀+κ+10)}` when `r > Q`, `r ≤ UV/S`,
  `log(2r) ≤ L^{d+1}`, `U, V ≥ L^{q_*+d+2}/2` and `q_*, s_* > 2(B₀+κ+10) + d + 1`.
* `Minor.final_le` — the absolute constant is absorbed: `10 K L^{-B₀-10} ≤ L^{-B₀}` for
  `L ≥ max(2, 10K)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Minor

/-! ### Sums -/

theorem sum_comm₄ {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (H : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b c d = ∑ c, ∑ d, ∑ a, ∑ b, H a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, H a b c d
      = ∑ a, ∑ c, ∑ b, ∑ d, H a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, H a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, H a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, H a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem mul_sum_mul_sum {α β : Type} [Fintype α] [Fintype β] (c φ : ℂ) (γ : α → ℂ)
    (β' : β → ℂ) :
    c * ((∑ b, β' b) * (∑ a, γ a)) * φ = ∑ a, ∑ b, c * (β' b * γ a) * φ := by
  rw [mul_comm (∑ b, β' b), Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem sum_weights_const {α β : Type} [Fintype α] [Fintype β] (u : α → ℝ) (v : β → ℝ)
    (hu : ∑ a, u a = 1) (hv : ∑ b, v b = 1) (p : ℝ) (z : ℂ) :
    ∑ a, ∑ b, ((p * u a * v b : ℝ) : ℂ) * z = (p : ℂ) * z := by
  have h : ∀ a, ∑ b, ((p * u a * v b : ℝ) : ℂ) * z = ((p * u a : ℝ) : ℂ) * z := fun a => by
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.mul_sum, hv, mul_one]
  rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.sum_mul, ← Complex.ofReal_sum,
    ← Finset.mul_sum, hu, mul_one]

/-! ### The two bilinear forms -/

section Algebra

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

/-- **The comparison defect is the raw form minus the form of the integrated tests**
[S-03:0317–0319]. -/
theorem defect_eq_sub (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ)
    (hA1 : ∑ t : AuxList big A, auxWeight big A t = 1)
    (hB1 : ∑ t : AuxList big Bs, auxWeight big Bs t = 1) (f : AuxList big Bs → ℂ)
    (g : AuxList big A → ℂ) (α ζ : ℝ) :
    comparisonDefect big A Bs Q h ξ f g α ζ =
      phaseForm big A Bs (fun t => conj (f t)) g α ζ -
        phaseForm big A Bs (kernelIntX big Bs Q h ξ (fun t => conj (f t)))
          (kernelIntX big A Q h ξ g) α ζ := by
  have h1 : comparisonDefect big A Bs Q h ξ f g α ζ =
      (∑ xA : AuxList big A, ∑ xB : AuxList big Bs, ∑ dA : AuxList big A,
        ∑ dB : AuxList big Bs,
          ((auxWeight big A xA * auxWeight big Bs xB * auxWeight big A dA *
            auxWeight big Bs dB : ℝ) : ℂ) *
            ((conj (f xB) * g xA) * dilPhase ζ α (tupleProd A xA * tupleProd Bs xB))) -
      ∑ xA : AuxList big A, ∑ xB : AuxList big Bs, ∑ dA : AuxList big A,
        ∑ dB : AuxList big Bs,
          ((auxWeight big A xA * auxWeight big Bs xB * auxWeight big A dA *
            auxWeight big Bs dB : ℝ) : ℂ) *
            ((conj (f xB) * g xA) *
              (cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
                cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
                dilPhase ζ α (tupleProd A dA * tupleProd Bs dB))) := by
    unfold comparisonDefect
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun xA _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun xB _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun dA _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun dB _ => ?_
    ring
  have h2 : (∑ xA : AuxList big A, ∑ xB : AuxList big Bs, ∑ dA : AuxList big A,
        ∑ dB : AuxList big Bs,
          ((auxWeight big A xA * auxWeight big Bs xB * auxWeight big A dA *
            auxWeight big Bs dB : ℝ) : ℂ) *
            ((conj (f xB) * g xA) * dilPhase ζ α (tupleProd A xA * tupleProd Bs xB))) =
      phaseForm big A Bs (fun t => conj (f t)) g α ζ :=
    Finset.sum_congr rfl fun xA _ => Finset.sum_congr rfl fun xB _ =>
      (sum_weights_const (auxWeight big A) (auxWeight big Bs) hA1 hB1
        (auxWeight big A xA * auxWeight big Bs xB)
        ((conj (f xB) * g xA) * dilPhase ζ α (tupleProd A xA * tupleProd Bs xB))).trans
        (mul_assoc _ _ _).symm
  have h3 : (∑ xA : AuxList big A, ∑ xB : AuxList big Bs, ∑ dA : AuxList big A,
        ∑ dB : AuxList big Bs,
          ((auxWeight big A xA * auxWeight big Bs xB * auxWeight big A dA *
            auxWeight big Bs dB : ℝ) : ℂ) *
            ((conj (f xB) * g xA) *
              (cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
                cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
                dilPhase ζ α (tupleProd A dA * tupleProd Bs dB)))) =
      phaseForm big A Bs (kernelIntX big Bs Q h ξ (fun t => conj (f t)))
        (kernelIntX big A Q h ξ g) α ζ := by
    rw [sum_comm₄]
    refine Finset.sum_congr rfl fun dA _ => Finset.sum_congr rfl fun dB _ => ?_
    refine Eq.trans ?_ (mul_sum_mul_sum
      ((auxWeight big A dA * auxWeight big Bs dB : ℝ) : ℂ)
      (dilPhase ζ α (tupleProd A dA * tupleProd Bs dB))
      (fun xA : AuxList big A => ((auxWeight big A xA : ℝ) : ℂ) *
        (cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) * g xA))
      (fun xB : AuxList big Bs => ((auxWeight big Bs xB : ℝ) : ℂ) *
        (cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) * conj (f xB)))).symm
    refine Finset.sum_congr rfl fun xA _ => Finset.sum_congr rfl fun xB _ => ?_
    push_cast
    ring
  rw [h1, h2, h3]

theorem tupleNorm_conj (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (f : AuxList big Λ → ℂ) :
    tupleNorm big Λ (fun t => conj (f t)) = tupleNorm big Λ f := by
  unfold tupleNorm wNorm wNormSq
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun t _ => ?_)
  simp only [Complex.norm_conj]

end Algebra

/-! ### The supports -/

section Supports

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] {J : ℕ}

omit [DecidableEq B] in
/-- A tuple of the dyad `a` has its product in `[2^a, 2^{a+1})`. -/
theorem dyad_bounds (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) {a : ℕ}
    {t : AuxList 𝔊.big Λ} (h : Nat.log 2 (tupleProd Λ t) = a) :
    (2 : ℝ) ^ a ≤ ((tupleProd Λ t : ℕ) : ℝ) ∧ ((tupleProd Λ t : ℕ) : ℝ) < 2 * (2 : ℝ) ^ a := by
  have hpos := tupleProd_pos 𝔊 Λ t
  have h1 : 2 ^ Nat.log 2 (tupleProd Λ t) ≤ tupleProd Λ t := Nat.pow_log_le_self 2 hpos.ne'
  have h2 : tupleProd Λ t < 2 ^ (Nat.log 2 (tupleProd Λ t) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  rw [h] at h1 h2
  have h3 : (2 : ℝ) ^ a ≤ ((tupleProd Λ t : ℕ) : ℝ) := by exact_mod_cast h1
  have h4 : ((tupleProd Λ t : ℕ) : ℝ) < (2 : ℝ) ^ (a + 1) := by exact_mod_cast h2
  rw [pow_succ] at h4
  exact ⟨h3, by linarith⟩

/-- **The log localization** [S-03:0321–0322]: after kernel integration, a test of the dyad `a`
vanishes outside `[2^a/4, 8·2^a]`, for every cell width `h ≤ 1`. -/
theorem kernelIntX_eq_zero (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) {Q h ξ : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) {a : ℕ} {G : AuxList 𝔊.big Λ → ℂ}
    (hG : DyadSupported 𝔊.big Λ a G) (d : AuxList 𝔊.big Λ)
    (hd : ¬(1 / 4 * (2 : ℝ) ^ a ≤ ((tupleProd Λ d : ℕ) : ℝ) ∧
      ((tupleProd Λ d : ℕ) : ℝ) ≤ 8 * (2 : ℝ) ^ a)) :
    kernelIntX 𝔊.big Λ Q h ξ G d = 0 := by
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hGy : G y = 0
  · rw [hGy, mul_zero, mul_zero]
  · by_cases hc : logCell h (tupleProd Λ d) = logCell h (tupleProd Λ y)
    · exfalso
      apply hd
      obtain ⟨hy1, hy2⟩ := dyad_bounds 𝔊 Λ (hG y hGy)
      have hdpos : (0 : ℝ) < ((tupleProd Λ d : ℕ) : ℝ) := by
        exact_mod_cast tupleProd_pos 𝔊 Λ d
      have hypos : (0 : ℝ) < ((tupleProd Λ y : ℕ) : ℝ) := by
        exact_mod_cast tupleProd_pos 𝔊 Λ y
      unfold logCell at hc
      have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hc
      rw [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh] at h1
      obtain ⟨h2, h3⟩ := abs_lt.mp h1
      have he : Real.exp 1 < 3 := Real.exp_one_lt_three
      -- `P d < e · P y` and `P y < e · P d`
      have h4 : ((tupleProd Λ d : ℕ) : ℝ) < ((tupleProd Λ y : ℕ) : ℝ) * Real.exp 1 := by
        have h5 : Real.log ((tupleProd Λ d : ℕ) : ℝ) <
            Real.log ((tupleProd Λ y : ℕ) : ℝ) + 1 := by linarith
        have h6 := (Real.log_lt_iff_lt_exp hdpos).mp h5
        rwa [Real.exp_add, Real.exp_log hypos] at h6
      have h7 : ((tupleProd Λ y : ℕ) : ℝ) < ((tupleProd Λ d : ℕ) : ℝ) * Real.exp 1 := by
        have h5 : Real.log ((tupleProd Λ y : ℕ) : ℝ) <
            Real.log ((tupleProd Λ d : ℕ) : ℝ) + 1 := by linarith
        have h6 := (Real.log_lt_iff_lt_exp hypos).mp h5
        rwa [Real.exp_add, Real.exp_log hdpos] at h6
      have h8 : ((tupleProd Λ y : ℕ) : ℝ) * Real.exp 1 ≤ ((tupleProd Λ y : ℕ) : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left he.le hypos.le
      have h9 : ((tupleProd Λ d : ℕ) : ℝ) * Real.exp 1 ≤ ((tupleProd Λ d : ℕ) : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left he.le hdpos.le
      constructor <;> linarith
    · rw [cellKernel_eq_zero_of_logCell_ne hc, zero_mul, mul_zero]

end Supports

/-! ### The arithmetic of (eq:ideal-minor-error) -/

/-- **(eq:ideal-minor-error)**. -/
theorem sigma_sqrt_le {L qs ss d w U V R ℓ : ℝ} (hL : 2 ≤ L) (hd : 0 < d)
    (hq : 2 * w + d + 1 < qs) (hs : 2 * w + d + 1 < ss)
    (hU : L ^ (qs + d + 2) ≤ 2 * U) (hV : L ^ (qs + d + 2) ≤ 2 * V) (hR : L ^ qs < R)
    (hRle : R ≤ U * V / L ^ ss) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ L ^ (d + 1)) :
    Real.sqrt (1 / V + 1 / R + ℓ / U + R * ℓ / (U * V)) ≤ 2 * L ^ (-w) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hA : 0 < L ^ qs := Real.rpow_pos_of_pos hL0 _
  have hD : 0 < L ^ (d + 1) := Real.rpow_pos_of_pos hL0 _
  have hD1 : 1 ≤ L ^ (d + 1) := Real.one_le_rpow hL1 (by linarith)
  have hS : 0 < L ^ ss := Real.rpow_pos_of_pos hL0 _
  have hy : 0 < L ^ (-qs) := Real.rpow_pos_of_pos hL0 _
  have hz : 0 < L ^ (-ss) := Real.rpow_pos_of_pos hL0 _
  have hyA : L ^ (-qs) * L ^ qs = 1 := by
    rw [← Real.rpow_add hL0, neg_add_cancel, Real.rpow_zero]
  have hzS : L ^ (-ss) * L ^ ss = 1 := by
    rw [← Real.rpow_add hL0, neg_add_cancel, Real.rpow_zero]
  have hE : L ^ (qs + d + 2) = L ^ qs * L ^ (d + 1) * L := by
    have h1 : qs + d + 2 = qs + (d + 1) + 1 := by ring
    rw [h1, Real.rpow_add_one hL0.ne', Real.rpow_add hL0]
  have hAD : 0 < L ^ qs * L ^ (d + 1) := mul_pos hA hD
  -- `U, V ≥ L^{q_*} L^{d+1}`
  have hU' : L ^ qs * L ^ (d + 1) ≤ U := by
    have h1 : L ^ qs * L ^ (d + 1) * 2 ≤ L ^ qs * L ^ (d + 1) * L :=
      mul_le_mul_of_nonneg_left hL hAD.le
    linarith
  have hV' : L ^ qs * L ^ (d + 1) ≤ V := by
    have h1 : L ^ qs * L ^ (d + 1) * 2 ≤ L ^ qs * L ^ (d + 1) * L :=
      mul_le_mul_of_nonneg_left hL hAD.le
    linarith
  have hAU : L ^ qs ≤ U := by
    have h1 : L ^ qs * 1 ≤ L ^ qs * L ^ (d + 1) := mul_le_mul_of_nonneg_left hD1 hA.le
    linarith
  have hAV : L ^ qs ≤ V := by
    have h1 : L ^ qs * 1 ≤ L ^ qs * L ^ (d + 1) := mul_le_mul_of_nonneg_left hD1 hA.le
    linarith
  have hU0 : 0 < U := lt_of_lt_of_le hA hAU
  have hV0 : 0 < V := lt_of_lt_of_le hA hAV
  have hR0 : 0 < R := lt_trans hA hR
  have hUV : 0 < U * V := mul_pos hU0 hV0
  -- the four terms
  have t1 : 1 / V ≤ L ^ (-qs) := by
    rw [div_le_iff₀ hV0]
    have h1 : L ^ (-qs) * L ^ qs ≤ L ^ (-qs) * V := mul_le_mul_of_nonneg_left hAV hy.le
    linarith
  have t2 : 1 / R ≤ L ^ (-qs) := by
    rw [div_le_iff₀ hR0]
    have h1 : L ^ (-qs) * L ^ qs ≤ L ^ (-qs) * R := mul_le_mul_of_nonneg_left hR.le hy.le
    linarith
  have t3 : ℓ / U ≤ L ^ (-qs) := by
    rw [div_le_iff₀ hU0]
    have h1 : L ^ (-qs) * (L ^ qs * L ^ (d + 1)) ≤ L ^ (-qs) * U :=
      mul_le_mul_of_nonneg_left hU' hy.le
    have h2 : L ^ (-qs) * (L ^ qs * L ^ (d + 1)) = L ^ (d + 1) := by
      rw [← mul_assoc, hyA, one_mul]
    linarith
  have t4 : R * ℓ / (U * V) ≤ L ^ (d + 1) * L ^ (-ss) := by
    rw [div_le_iff₀ hUV]
    have h1 : R * L ^ ss ≤ U * V := (le_div_iff₀ hS).mp hRle
    have h2 : R = R * L ^ ss * L ^ (-ss) := by
      rw [mul_assoc, mul_comm (L ^ ss), hzS, mul_one]
    have h3 : R ≤ U * V * L ^ (-ss) := by
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 hz.le
    have h4 : R * ℓ ≤ U * V * L ^ (-ss) * L ^ (d + 1) :=
      mul_le_mul h3 hℓ hℓ0 (mul_nonneg hUV.le hz.le)
    linarith
  -- the exponents
  have e1 : L ^ (-qs) ≤ L ^ (-(2 * w)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have e2 : L ^ (d + 1) * L ^ (-ss) ≤ L ^ (-(2 * w)) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have e3 : L ^ (-(2 * w)) = L ^ (-w) * L ^ (-w) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hw0 : 0 ≤ L ^ (-w) := Real.rpow_nonneg hL0.le _
  have hsum : 1 / V + 1 / R + ℓ / U + R * ℓ / (U * V) ≤ (2 * L ^ (-w)) ^ 2 := by
    have h1 : (2 * L ^ (-w)) ^ 2 = 4 * (L ^ (-w) * L ^ (-w)) := by ring
    rw [h1, ← e3]
    linarith
  exact (Real.sqrt_le_sqrt hsum).trans
    (le_of_eq (Real.sqrt_sq (mul_nonneg zero_le_two hw0)))

/-- The absolute constant is absorbed by the margin of the exponents. -/
theorem final_le {L K κ B₀ : ℝ} (hL : 2 ≤ L) (hK : 0 < K) (hLK : 10 * K ≤ L) :
    5 * (K * L ^ κ * (2 * L ^ (-(B₀ + κ + 10)))) ≤ L ^ (-B₀) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have h1 : L ^ κ * L ^ (-(B₀ + κ + 10)) = L ^ (-B₀) * L ^ (-(10 : ℝ)) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    ring
  have h2 : L ^ (-(10 : ℝ)) ≤ L ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h3 : L ^ (-(1 : ℝ)) = L⁻¹ := Real.rpow_neg_one L
  have h4 : 10 * K * L⁻¹ ≤ 1 := by
    have h5 : 10 * K * L⁻¹ ≤ L * L⁻¹ := mul_le_mul_of_nonneg_right hLK (inv_nonneg.mpr hL0.le)
    rwa [mul_inv_cancel₀ hL0.ne'] at h5
  have hB : 0 ≤ L ^ (-B₀) := Real.rpow_nonneg hL0.le _
  have h6 : 5 * (K * L ^ κ * (2 * L ^ (-(B₀ + κ + 10)))) =
      L ^ (-B₀) * (10 * K * L ^ (-(10 : ℝ))) := by
    have h7 : 5 * (K * L ^ κ * (2 * L ^ (-(B₀ + κ + 10)))) =
        10 * K * (L ^ κ * L ^ (-(B₀ + κ + 10))) := by ring
    rw [h7, h1]
    ring
  rw [h6]
  have h8 : 10 * K * L ^ (-(10 : ℝ)) ≤ 1 := by
    have h9 : 10 * K * L ^ (-(10 : ℝ)) ≤ 10 * K * L⁻¹ := by
      rw [← h3]
      exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num) hK.le)
    linarith
  calc L ^ (-B₀) * (10 * K * L ^ (-(10 : ℝ))) ≤ L ^ (-B₀) * 1 :=
        mul_le_mul_of_nonneg_left h8 hB
    _ = L ^ (-B₀) := mul_one _

end Minor

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
