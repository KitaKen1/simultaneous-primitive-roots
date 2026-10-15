module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.TailRestrict
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostAbsoluteProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.BoundaryNormProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Scalars
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Memory truncation and its tail: proof of `MemoryTail`

Source: `verification/stage7-sources/S-02.tex`, lines 796–822 (`[S-02:0796–0822]`).

"We now restrict the total memory size to `B = ⌈L²⌉` before and after every operation, writing the
projections implicitly. This is not an assumption on the original moment. At most `(ℓ + m)|ℬ|N`
particles can be supplied by stores. Thus a path violating this restriction has at least
`B - O((ℓ + m)sN)` ghost births. Multiply every ghost birth by two in the absolute path sum and
use the preceding bounds. The total omitted mass, even with the distinct-birth indicator, is at
most `2^{-B + O((ℓ + m)sN)} L^{O(N)} = exp(-Ω(L²)) = o(L^{-AN})` for every fixed `A`."

The proof has three parts.

* (`TailRestrict.lean`, `tail_sum_fits_eq`) The path integral at the cutoff `B` is the part of the
  path integral at a cutoff `Bc ≥ B` over the histories whose total memory is at most `B` before
  and after every operation (`History.Fits`), with the same weights and the same births.
* (`TailGrowth.lean`, `tail_sum_notFits_le`; `TailAbsSum.lean`, `tail_absSum_le`) A history which
  does not fit `B` has more than `B - N M|ℬ|` ghost births (`M = J + ℓ`), and the absolute path sum
  with doubled ghost births is at most `‖𝟏_∅‖² R_g^{N+1} R_e^N`, where `R_g`, `R_e` are the row
  bounds of the visit operations with doubled births and of the absolute edges.
* (this file) `memoryTail_core` puts the two together, and `tail_scalar_exponent`,
  `tail_scalar_final` are the scalar estimate
  `2^{N M|ℬ|} / 2^{B+1} · 2 · L^{C_v(N+1) + C_a N} ≤ L^{-AN}` for large `x`.

The inputs are the row halves of `ghostAbsolute` (with doubled births) and `memoryAbsolute`, and
`boundaryNorm`; the hypothesis `Admissible` is used through `memoryAbsolute` only.

One deviation from the text: the number of particles which the stores of one edge supply to one
big group is bounded by `M = J + ℓ` (all local choices) instead of `ℓ + m` (the choices with
nonvanishing coefficient). Since `J` is fixed before `x₀`, the estimate is the same.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open Filter
open scoped BigOperators

noncomputable section

/-! ### The omitted mass -/

section Core

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {b Bc : ℕ}

open _root_.Classical in
/-- **The truncation error is the omitted mass** (eq:memory-tail) [S-02:0803–0811], for a general
family: for `b ≤ Bc`, the path integrals with the distinct-birth rule at the cutoffs `Bc` and `b`
differ by at most `2^{N M|ℬ|} / 2^{b+1} · ‖𝟏_∅‖² R_g^{N+1} R_e^N`, where `R_g` is a row bound of
the visit operations with doubled ghost births and `R_e` a row bound of the absolute edges, both
at the cutoff `Bc`. -/
theorem memoryTail_core (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (θ : ℝ) {v Rg Re : ℝ}
    (hv : 1 ≤ v) (hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s) (hRg : 0 ≤ Rg)
    (hRe : 0 ≤ Re)
    (hG : ∀ i, i ≤ D.n → RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) =>
        (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c|) ghostTgt Rg)
    (hE : ∀ i, i < D.n → RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖) (edgeFullTgt D i) Re) :
    ‖distinctSum D Bc θ - distinctSum D b θ‖ ≤
      (2 : ℝ) ^ (D.n * ((J + ℓ) * Fintype.card B)) / 2 ^ (b + 1) *
        (wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) * (Rg ^ (D.n + 1) * Re ^ D.n)) := by
  -- the difference is the sum over the histories at the cutoff `Bc` which do not fit `b`
  have e : distinctSum D Bc θ - distinctSum D b θ =
      ∑ h : History D Bc, ((if Graph.PerformedBirthsDistinct h.birth then h.weight θ else 0) -
        (if h.Fits b then
          (if Graph.PerformedBirthsDistinct h.birth then h.weight θ else 0) else 0)) := by
    rw [Finset.sum_sub_distrib, tail_sum_fits_eq hb D θ]
    rfl
  have hterm : ∀ h : History D Bc,
      ‖(if Graph.PerformedBirthsDistinct h.birth then h.weight θ else 0) -
        (if h.Fits b then
          (if Graph.PerformedBirthsDistinct h.birth then h.weight θ else 0) else 0)‖ ≤
        (if h.Fits b then 0 else ‖h.weight θ‖) := by
    intro h
    split_ifs <;> simp
  rw [e]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun h _ => hterm h).trans
    (tail_sum_notFits_le D Bc θ b hv hm hRg hRe hG hE))

end Core

/-! ### Scalars -/

/-- The last step of (eq:memory-tail): if
`κ log 2 + (C_v (N + 1) + C_a N + A N) log L ≤ B log 2`, then
`2^κ / 2^{B+1} · K · (L^{C_v})^{N+1} (L^{C_a})^N ≤ L^{-AN}` for `K ≤ 2`. -/
theorem tail_scalar_final {L Cv Ca A K : ℝ} {n Bn kap : ℕ} (hL : 0 < L) (hK : K ≤ 2)
    (h : (kap : ℝ) * Real.log 2 + (Cv * ((n : ℝ) + 1) + Ca * n + A * n) * Real.log L ≤
      (Bn : ℝ) * Real.log 2) :
    (2 : ℝ) ^ kap / 2 ^ (Bn + 1) * (K * ((L ^ Cv) ^ (n + 1) * (L ^ Ca) ^ n)) ≤
      L ^ (-(A * (n : ℝ))) := by
  have e2 : ∀ j : ℕ, (2 : ℝ) ^ j = Real.exp ((j : ℝ) * Real.log 2) := fun j => by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have eL : ∀ (y : ℝ) (j : ℕ), (L ^ y) ^ j = Real.exp ((j : ℝ) * (Real.log L * y)) :=
    fun y j => by rw [Real.exp_nat_mul, ← Real.rpow_def_of_pos hL]
  have hP0 : 0 ≤ (L ^ Cv) ^ (n + 1) * (L ^ Ca) ^ n :=
    mul_nonneg (pow_nonneg (Real.rpow_nonneg hL.le _) _) (pow_nonneg (Real.rpow_nonneg hL.le _) _)
  have hBpos : (0 : ℝ) < 2 ^ Bn := pow_pos two_pos Bn
  have hc0 : (0 : ℝ) ≤ 2 ^ kap / 2 ^ (Bn + 1) :=
    div_nonneg (pow_nonneg zero_le_two _) (pow_nonneg zero_le_two _)
  have h1 : (2 : ℝ) ^ kap / 2 ^ (Bn + 1) * (K * ((L ^ Cv) ^ (n + 1) * (L ^ Ca) ^ n)) ≤
      (2 : ℝ) ^ kap / 2 ^ (Bn + 1) * (2 * ((L ^ Cv) ^ (n + 1) * (L ^ Ca) ^ n)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hP0) hc0
  have h2 : (2 : ℝ) ^ kap / 2 ^ (Bn + 1) * (2 * ((L ^ Cv) ^ (n + 1) * (L ^ Ca) ^ n)) =
      (2 : ℝ) ^ kap * ((L ^ Cv) ^ (n + 1) * (L ^ Ca) ^ n) / 2 ^ Bn := by
    rw [pow_succ (2 : ℝ) Bn, div_mul_eq_mul_div,
      div_eq_div_iff (mul_ne_zero hBpos.ne' two_ne_zero) hBpos.ne']
    ring
  refine h1.trans (le_of_eq_of_le h2 ?_)
  rw [div_le_iff₀ hBpos, e2 kap, e2 Bn, eL Cv (n + 1), eL Ca n, Real.rpow_def_of_pos hL,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  push_cast
  linarith

/-- The exponent inequality behind `exp(-Ω(L²)) = o(L^{-AN})` [S-02:0809–0811]: with
`N ≤ 2 (L^{13/25} + 1)`, `|ℬ| ≤ C₀ log L`, `B ≥ L²` and `log L ≤ L^{12/25}`, the quantity
`N M|ℬ| log 2 + (C_v (N + 1) + C_a N + A N) log L` is at most `5 K L ≤ L² / 2 ≤ B log 2`
as soon as `L ≥ 10 K`, `K = M |C₀| + |C_v| + |C_a| + |A|`. -/
theorem tail_scalar_exponent {L C₀ Cv Ca A : ℝ} {n Bn M cB : ℕ} (hL1 : 1 ≤ L)
    (hLK : 10 * ((M : ℝ) * |C₀| + |Cv| + |Ca| + |A|) ≤ L)
    (hT : Real.log L ≤ L ^ ((12 : ℝ) / 25))
    (hn : (n : ℝ) ≤ 2 * (L ^ ((13 : ℝ) / 25) + 1))
    (hcB : (cB : ℝ) ≤ C₀ * Real.log L) (hBn : L ^ 2 ≤ (Bn : ℝ)) :
    ((n * (M * cB) : ℕ) : ℝ) * Real.log 2 +
        (Cv * ((n : ℝ) + 1) + Ca * n + A * n) * Real.log L ≤ (Bn : ℝ) * Real.log 2 := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hT0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hy1 : (1 : ℝ) ≤ L ^ ((13 : ℝ) / 25) := Real.one_le_rpow hL1 (by norm_num)
  have hyz : L ^ ((13 : ℝ) / 25) * L ^ ((12 : ℝ) / 25) = L := by
    rw [← Real.rpow_add hL0, show (13 : ℝ) / 25 + 12 / 25 = 1 by norm_num, Real.rpow_one]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
    linarith
  have hlog2' : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (two_pos : (0 : ℝ) < 2)
    have e : (1 : ℝ) - 2⁻¹ = 1 / 2 := by norm_num
    linarith
  -- `(N + 1) log L ≤ 5 L`
  have hnT : ((n : ℝ) + 1) * Real.log L ≤ 5 * L := by
    have h1 : (n : ℝ) + 1 ≤ 5 * L ^ ((13 : ℝ) / 25) := by linarith
    calc ((n : ℝ) + 1) * Real.log L ≤ 5 * L ^ ((13 : ℝ) / 25) * Real.log L :=
          mul_le_mul_of_nonneg_right h1 hT0
      _ ≤ 5 * L ^ ((13 : ℝ) / 25) * L ^ ((12 : ℝ) / 25) :=
          mul_le_mul_of_nonneg_left hT (by linarith)
      _ = 5 * L := by rw [mul_assoc, hyz]
  have hnT0 : 0 ≤ ((n : ℝ) + 1) * Real.log L := mul_nonneg (by linarith) hT0
  have hnT'0 : 0 ≤ (n : ℝ) * Real.log L := mul_nonneg hn0 hT0
  have hnT' : (n : ℝ) * Real.log L ≤ ((n : ℝ) + 1) * Real.log L :=
    mul_le_mul_of_nonneg_right (by linarith) hT0
  -- the stores
  have hkap : ((n * (M * cB) : ℕ) : ℝ) * Real.log 2 ≤
      (M : ℝ) * |C₀| * (((n : ℝ) + 1) * Real.log L) := by
    have h1 : ((n * (M * cB) : ℕ) : ℝ) = (n : ℝ) * ((M : ℝ) * (cB : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_mul]
    have h2 : (n : ℝ) * ((M : ℝ) * (cB : ℝ)) ≤ (n : ℝ) * ((M : ℝ) * (C₀ * Real.log L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcB hM0) hn0
    have h3 : (n : ℝ) * ((M : ℝ) * (C₀ * Real.log L)) =
        (M : ℝ) * C₀ * ((n : ℝ) * Real.log L) := by ring
    have h4 : (M : ℝ) * C₀ * ((n : ℝ) * Real.log L) ≤
        (M : ℝ) * |C₀| * ((n : ℝ) * Real.log L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self C₀) hM0) hnT'0
    have h5 : (M : ℝ) * |C₀| * ((n : ℝ) * Real.log L) ≤
        (M : ℝ) * |C₀| * (((n : ℝ) + 1) * Real.log L) :=
      mul_le_mul_of_nonneg_left hnT' (mul_nonneg hM0 (abs_nonneg C₀))
    have h6 : ((n * (M * cB) : ℕ) : ℝ) * Real.log 2 ≤ ((n * (M * cB) : ℕ) : ℝ) :=
      mul_le_of_le_one_right (Nat.cast_nonneg _) hlog2
    calc ((n * (M * cB) : ℕ) : ℝ) * Real.log 2 ≤ ((n * (M * cB) : ℕ) : ℝ) := h6
      _ = (n : ℝ) * ((M : ℝ) * (cB : ℝ)) := h1
      _ ≤ (n : ℝ) * ((M : ℝ) * (C₀ * Real.log L)) := h2
      _ = (M : ℝ) * C₀ * ((n : ℝ) * Real.log L) := h3
      _ ≤ (M : ℝ) * |C₀| * ((n : ℝ) * Real.log L) := h4
      _ ≤ (M : ℝ) * |C₀| * (((n : ℝ) + 1) * Real.log L) := h5
  -- the powers of `L`
  have hrest : (Cv * ((n : ℝ) + 1) + Ca * n + A * n) * Real.log L ≤
      (|Cv| + |Ca| + |A|) * (((n : ℝ) + 1) * Real.log L) := by
    have h1 : Cv * (((n : ℝ) + 1) * Real.log L) ≤ |Cv| * (((n : ℝ) + 1) * Real.log L) :=
      mul_le_mul_of_nonneg_right (le_abs_self Cv) hnT0
    have h2 : Ca * ((n : ℝ) * Real.log L) ≤ |Ca| * (((n : ℝ) + 1) * Real.log L) :=
      (mul_le_mul_of_nonneg_right (le_abs_self Ca) hnT'0).trans
        (mul_le_mul_of_nonneg_left hnT' (abs_nonneg Ca))
    have h3 : A * ((n : ℝ) * Real.log L) ≤ |A| * (((n : ℝ) + 1) * Real.log L) :=
      (mul_le_mul_of_nonneg_right (le_abs_self A) hnT'0).trans
        (mul_le_mul_of_nonneg_left hnT' (abs_nonneg A))
    have e1 : (Cv * ((n : ℝ) + 1) + Ca * n + A * n) * Real.log L =
        Cv * (((n : ℝ) + 1) * Real.log L) + Ca * ((n : ℝ) * Real.log L) +
          A * ((n : ℝ) * Real.log L) := by ring
    have e2 : (|Cv| + |Ca| + |A|) * (((n : ℝ) + 1) * Real.log L) =
        |Cv| * (((n : ℝ) + 1) * Real.log L) + |Ca| * (((n : ℝ) + 1) * Real.log L) +
          |A| * (((n : ℝ) + 1) * Real.log L) := by ring
    rw [e1, e2]
    exact add_le_add (add_le_add h1 h2) h3
  -- the sum
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (M : ℝ) * |C₀| + |Cv| + |Ca| + |A| := ⟨_, rfl⟩
  rw [← hKdef] at hLK
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    positivity
  have hsum : ((n * (M * cB) : ℕ) : ℝ) * Real.log 2 +
      (Cv * ((n : ℝ) + 1) + Ca * n + A * n) * Real.log L ≤ K * (5 * L) := by
    have e : K * (((n : ℝ) + 1) * Real.log L) =
        (M : ℝ) * |C₀| * (((n : ℝ) + 1) * Real.log L) +
          (|Cv| + |Ca| + |A|) * (((n : ℝ) + 1) * Real.log L) := by
      rw [hKdef]
      ring
    calc ((n * (M * cB) : ℕ) : ℝ) * Real.log 2 +
          (Cv * ((n : ℝ) + 1) + Ca * n + A * n) * Real.log L
        ≤ (M : ℝ) * |C₀| * (((n : ℝ) + 1) * Real.log L) +
          (|Cv| + |Ca| + |A|) * (((n : ℝ) + 1) * Real.log L) := add_le_add hkap hrest
      _ = K * (((n : ℝ) + 1) * Real.log L) := e.symm
      _ ≤ K * (5 * L) := mul_le_mul_of_nonneg_left hnT hK0
  have hfin : K * (5 * L) ≤ L ^ 2 * (1 / 2) := by
    have h1 : 10 * K * L ≤ L * L := mul_le_mul_of_nonneg_right hLK hL0.le
    have e1 : K * (5 * L) = 1 / 2 * (10 * K * L) := by ring
    have e2 : L ^ 2 * (1 / 2) = 1 / 2 * (L * L) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  calc ((n * (M * cB) : ℕ) : ℝ) * Real.log 2 +
        (Cv * ((n : ℝ) + 1) + Ca * n + A * n) * Real.log L ≤ K * (5 * L) := hsum
    _ ≤ L ^ 2 * (1 / 2) := hfin
    _ ≤ (Bn : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_right hBn (by norm_num)
    _ ≤ (Bn : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2' (Nat.cast_nonneg _)

/-! ### The truncation estimate -/

/-- **The truncation estimate for fixed constants** (eq:memory-truncation), (eq:memory-tail)
[S-02:0796–0811]. The threshold `x₀` depends on `P, m, C₁, J, C₂, A`: it is the maximum of the
thresholds of `ghostAbsolute` (for `J`), `memoryAbsolute` (for `J, C₂`), `boundaryNorm` (for `J`),
of the positivity of the measure, and of the scalar conditions `log x ≥ 1`,
`log x ≥ 10 ((J + ℓ) C₀ + |C_v| + |C_a| + |A|)`, `log log x ≤ (log x)^{12/25}`. -/
theorem memoryTailBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ A : ℝ) :
    MemoryTailBound P m C₁ J C₂ A := by
  obtain ⟨Cv, hCv⟩ := ghostAbsolute P
  obtain ⟨Ca, hCa⟩ := memoryAbsolute P m C₁
  obtain ⟨x₁, hx₁⟩ := hCv J
  obtain ⟨x₂, hx₂⟩ := hCa J C₂
  obtain ⟨x₃, hx₃⟩ := boundaryNorm P J
  obtain ⟨x₄, hx₄⟩ := eventually_atTop.mp ((eventually_memMeasure_nonneg P).and
    ((eventually_log_ge 1).and
      ((eventually_log_ge (10 * (((J + P.ℓ : ℕ) : ℝ) * |P.C₀| + |Cv| + |Ca| + |A|))).and
        (eventually_loglog_le ((12 : ℝ) / 25) 1 (by norm_num) one_pos))))
  refine ⟨max (max x₁ x₂) (max x₃ x₄), fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm θ Bc hBc => ?_⟩
  have hxa : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : x₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxd : x₄ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hnn, hL1, hLK, hT⟩ := hx₄ x hxd
  have hL0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hG := hx₁ x hxa S B 𝔊 N 𝔉 ζ k Bc
  have hE := hx₂ x hxb S B 𝔊 N 𝔉 ζ k hadm Bc
  have hW : wNormSq (memMeasure 𝔊 J Bc) (emptyVec 𝔊.toGroupFamily J P.ℓ Bc) ≤ 2 :=
    hx₃ x hxc S B 𝔊 Bc
  -- the omitted mass
  have hcore : ‖distinctSum (memData 𝔊 𝔉 k ζ) Bc θ -
        distinctSum (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ‖ ≤
      (2 : ℝ) ^ (Graph.sourceMemoryLength (Real.log x) * ((J + P.ℓ) * Fintype.card B)) /
          2 ^ (memCutoff (Real.log x) + 1) *
        (wNormSq (memMeasure 𝔊 J Bc) (emptyVec 𝔊.toGroupFamily J P.ℓ Bc) *
          ((Real.log x ^ Cv) ^ (Graph.sourceMemoryLength (Real.log x) + 1) *
            (Real.log x ^ Ca) ^ Graph.sourceMemoryLength (Real.log x))) :=
    memoryTail_core hBc (memData 𝔊 𝔉 k ζ) θ (one_lt_memV P).le
      (fun s => hnn S B 𝔊 J Bc s) (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
      (fun i hi => (hG i hi).1) (fun i hi => (hE θ i hi).1)
  -- the scalars
  have hT' : Real.log (Real.log x) ≤ Real.log x ^ ((12 : ℝ) / 25) :=
    hT.trans (le_of_eq (one_mul _))
  have hn : (Graph.sourceMemoryLength (Real.log x) : ℝ) ≤
      2 * (Real.log x ^ ((13 : ℝ) / 25) + 1) :=
    Graph.source_memory_length_upper (Real.log x) hL0.le
  have hBn : Real.log x ^ 2 ≤ (memCutoff (Real.log x) : ℝ) := Nat.le_ceil _
  have hexp := tail_scalar_exponent (Cv := Cv) (Ca := Ca) (A := A)
    (n := Graph.sourceMemoryLength (Real.log x)) (M := J + P.ℓ) hL1 hLK hT' hn
    𝔊.card_big_le hBn
  exact hcore.trans (tail_scalar_final hL0 hW hexp)

/-- **Memory truncation and its tail, (eq:memory-truncation), (eq:memory-tail)**
[S-02:0796–0822], proved: for all sufficiently large `x` and every cutoff `Bc ≥ B = ⌈L²⌉`, the
path integrals with the distinct-birth rule at the cutoffs `Bc` and `B` differ by at most
`L^{-AN}`, uniformly in the cutoff, the prime groups, the admissible pattern family, `k`, `ζ` and
`θ`. -/
theorem memoryTail : MemoryTail :=
  fun P m C₁ J C₂ A => memoryTailBound P m C₁ J C₂ A

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
