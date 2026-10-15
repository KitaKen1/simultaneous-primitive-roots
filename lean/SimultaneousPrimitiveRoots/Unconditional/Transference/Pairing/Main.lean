module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing.Blocks
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# [S] Corollary 3.11 (endpoint pairing): `endpointPairing : EndpointPairing`

Source: `verification/stage7-sources/S-02.tex`, lines 1266–1339 (`[S-02:1266–1339]`).

For every choice of the constants of Theorem 3.5, the moment bound (the conclusion of
Theorem 3.5) implies `|⟨f, 𝒜 g⟩| ≤ M X L^{-E + 2C₃}` with

`M = √12 · exp(10 |C₂| + 30 J C₀ + |C_sup| + 20 |C₃|)`

and the threshold `x₀ = max(x₁, e)`, where `x₁` is the threshold of the moment bound.

The operator part is `Pairing.pairMarkFree_pow_le` (`Blocks.lean`), with `R = ⌈L^{13/25}⌉`:

`|⟨f, 𝒜 g⟩|^{2R} ≤ (3‖g‖²)^R ‖f‖^{2(R-1)} (H + 1) sup|f_n|² ∑_{n ∈ I} ⟨u_n, (𝒜 𝒜*)^R u_n⟩`.

This file inserts the hypotheses:

* `‖f‖², ‖g‖² ≤ X L^{2C₃}`;
* `∑_{n ∈ I} ⟨u_n, (𝒜 𝒜*)^R u_n⟩ ≤ |I ∩ ℤ| L^{-2RE} ≤ 2X L^{-2RE}` (the moment bound, and
  `card_intWindow_le`);
* `H + 1 ≤ 2 L^{C₂} exp(3 J C₀ T L^d)` (`stepBound_add_one_le`: "`D` has `Js` factors, all at most
  `exp(L^d)`", `log H = O_J(T L^d)`, [S-02:1286–1290]) and `sup |f_n|² ≤ exp(2 C_sup √L)`;
* `4 L^{C₂} exp(3 J C₀ T L^d) exp(2 C_sup √L) L^{-2C₃} ≤ (4 e^{2c})^R` (`loss_le`):
  "`(O(H) sup|f_n|²)^{1/(2R)} = exp(O_J((T L^d + √L)/L^{0.52})) = O(1)`" and "the extra factor
  `L^{-C₃/R}` is bounded for fixed `C₃`" [S-02:1321–1338]. It uses `d < 0.47`, `T ≤ 20 L^{1/20}`
  and `R ≥ L^{13/25}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Pairing

/-! ### The window, the moment bound and the maximal displacement -/

theorem rpow_sq_eq {L : ℝ} (hL : 0 < L) (a : ℝ) : (L ^ a) ^ 2 = L ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  congr 1
  push_cast
  ring

/-- The algebra of the final substitution: with `Y = X ℓ` bounding `‖f‖²` and `‖g‖²`. -/
theorem assemble_identity (R' : ℕ) (X ℓ κ D : ℝ) :
    (3 * (X * ℓ)) ^ (R' + 1) * ((X * ℓ) ^ R' * (X * κ ^ (R' + 1) * (D ^ (R' + 1) * ℓ))) =
      (3 * D * X ^ 2 * ℓ ^ 2 * κ) ^ (R' + 1) := by
  ring

/-- `|I ∩ ℤ| ≤ 2X` for `I = [X, 2X)`, `X ≥ 1`. -/
theorem card_intWindow_le {X : ℝ} (hX : 1 ≤ X) : ((intWindow X).card : ℝ) ≤ 2 * X := by
  have hle : ⌈X⌉ ≤ ⌈2 * X⌉ := Int.ceil_mono (by linarith)
  have h1 : (((intWindow X).card : ℤ) : ℝ) = ((⌈2 * X⌉ - ⌈X⌉ : ℤ) : ℝ) := by
    unfold intWindow
    rw [Int.card_Ico_of_le _ _ hle]
  have h2 : ((intWindow X).card : ℝ) = (⌈2 * X⌉ : ℝ) - (⌈X⌉ : ℝ) := by
    rw [← Int.cast_natCast, h1, Int.cast_sub]
  rw [h2]
  linarith [Int.ceil_lt_add_one (2 * X), Int.le_ceil X]

section Groups

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B]

/-- The moment bound, without the normalization by `|I ∩ ℤ|`. -/
theorem sum_physMoment_le [DecidableEq S] [DecidableEq B] (𝔊 : PrimeGroups P x S B) {J : ℕ}
    {N : Type} [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ) (k : ℤ) (ζ : ℝ) (X : ℝ) {Bd : ℝ}
    {R : ℕ} (hR : transferR (Real.log x) = R) (h : averagedMoment 𝔊 𝔉 k ζ X ≤ Bd) :
    ∑ n ∈ intWindow X, physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ R n ≤
      ((intWindow X).card : ℝ) * Bd := by
  subst hR
  unfold averagedMoment at h
  rcases Nat.eq_zero_or_pos (intWindow X).card with h0 | hpos
  · have hempty : intWindow X = ∅ := Finset.card_eq_zero.mp h0
    have hsum : ∑ n ∈ intWindow X,
        physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (transferR (Real.log x)) n = 0 := by
      rw [hempty]
      exact Finset.sum_empty
    have hc : ((intWindow X).card : ℝ) = 0 := by
      rw [h0]
      exact Nat.cast_zero
    rw [hsum, hc, zero_mul]
  · exact (inv_mul_le_iff₀ (Nat.cast_pos.mpr hpos)).mp h

/-- All group primes are at most `exp(L^d)` (for `L ≥ 1`). -/
theorem maxPrime_le (𝔊 : PrimeGroups P x S B) (hL : 1 ≤ Real.log x) :
    (maxPrime 𝔊.toGroupFamily : ℝ) ≤ Real.exp (Real.log x ^ P.d) := by
  have hexp1 : (1 : ℝ) ≤ Real.exp (Real.log x ^ P.d) :=
    Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hbd : Real.exp (Real.log x ^ P.b) ≤ Real.exp (Real.log x ^ P.d) :=
    Real.exp_le_exp.mpr
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith [P.b_lt_c, P.c_lt_d]))
  have hall : ∀ p ∈ 𝔊.toGroupFamily.allPrimes, (p : ℝ) ≤ Real.exp (Real.log x ^ P.d) := by
    intro p hp
    unfold GroupFamily.allPrimes at hp
    rcases Finset.mem_union.mp hp with h | h
    · obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp h
      exact (𝔊.small_le g p hg).trans hbd
    · obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp h
      exact 𝔊.big_le g p hg
  have hsup : 𝔊.toGroupFamily.allPrimes.sup id ≤ ⌊Real.exp (Real.log x ^ P.d)⌋₊ :=
    Finset.sup_le fun p hp => Nat.le_floor (hall p hp)
  unfold maxPrime
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le hexp1 ((Nat.cast_le.mpr hsup).trans (Nat.floor_le (Real.exp_pos _).le))

/-- **`log H = O_J(T L^d)`** [S-02:1286–1290], in the form
`H + 1 ≤ 2 L^{C₂} exp(3 J C₀ T L^d)`. -/
theorem stepBound_add_one_le (𝔊 : PrimeGroups P x S B) (hL : 1 ≤ Real.log x) (J : ℕ) {C₂ : ℝ}
    {k : ℤ} (hk0 : k ≠ 0) (hk : |(k : ℝ)| ≤ Real.log x ^ C₂) :
    (stepBound 𝔊.toGroupFamily J k : ℝ) + 1 ≤
      2 * (Real.log x ^ C₂ *
        Real.exp (3 * (J * P.C₀) * (Real.log (Real.log x) * Real.log x ^ P.d))) := by
  have hL0 : 0 < Real.log x := by linarith
  have hT0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  have hd0 : 0 ≤ Real.log x ^ P.d := Real.rpow_nonneg hL0.le _
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hcount : ((J * Fintype.card S + 2 * J * Fintype.card B : ℕ) : ℝ) ≤
      3 * (J * P.C₀) * Real.log (Real.log x) := by
    have h1 := mul_le_mul_of_nonneg_left 𝔊.card_small_le hJ
    have h2 := mul_le_mul_of_nonneg_left 𝔊.card_big_le hJ
    push_cast
    linarith
  have hdil : (dilBound 𝔊.toGroupFamily J : ℝ) ≤
      Real.exp (3 * (J * P.C₀) * (Real.log (Real.log x) * Real.log x ^ P.d)) := by
    unfold dilBound
    rw [Nat.cast_pow]
    calc (maxPrime 𝔊.toGroupFamily : ℝ) ^ (J * Fintype.card S + 2 * J * Fintype.card B)
        ≤ Real.exp (Real.log x ^ P.d) ^ (J * Fintype.card S + 2 * J * Fintype.card B) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (maxPrime_le 𝔊 hL) _
      _ = Real.exp (((J * Fintype.card S + 2 * J * Fintype.card B : ℕ) : ℝ) *
            Real.log x ^ P.d) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (3 * (J * P.C₀) * (Real.log (Real.log x) * Real.log x ^ P.d)) :=
          Real.exp_le_exp.mpr (by
            calc ((J * Fintype.card S + 2 * J * Fintype.card B : ℕ) : ℝ) * Real.log x ^ P.d
                ≤ (3 * (J * P.C₀) * Real.log (Real.log x)) * Real.log x ^ P.d :=
                  mul_le_mul_of_nonneg_right hcount hd0
              _ = 3 * (J * P.C₀) * (Real.log (Real.log x) * Real.log x ^ P.d) := by ring)
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have h : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    exact_mod_cast h
  have hkabs : (k.natAbs : ℝ) = |(k : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hE1 : 1 ≤ Real.exp (3 * (J * P.C₀) * (Real.log (Real.log x) * Real.log x ^ P.d)) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hJ P.C₀_pos.le))
      (mul_nonneg hT0 hd0))
  have hkL : 0 ≤ Real.log x ^ C₂ := (abs_nonneg _).trans hk
  have hstep : (stepBound 𝔊.toGroupFamily J k : ℝ) ≤ Real.log x ^ C₂ *
      Real.exp (3 * (J * P.C₀) * (Real.log (Real.log x) * Real.log x ^ P.d)) := by
    unfold stepBound
    rw [Nat.cast_mul, hkabs]
    exact mul_le_mul hk hdil (Nat.cast_nonneg _) hkL
  have hY1 : 1 ≤ Real.log x ^ C₂ *
      Real.exp (3 * (J * P.C₀) * (Real.log (Real.log x) * Real.log x ^ P.d)) := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ Real.log x ^ C₂ *
          Real.exp (3 * (J * P.C₀) * (Real.log (Real.log x) * Real.log x ^ P.d)) :=
          mul_le_mul (hk1.trans hk) hE1 zero_le_one hkL
  linarith

end Groups

/-! ### The losses are bounded -/

/-- The exponent of the constant of Corollary 3.11: `M = √12 · exp(pairingConst)`. -/
def pairingConst (P : GroupParams) (J : ℕ) (C₂ C₃ Csup : ℝ) : ℝ :=
  10 * |C₂| + 30 * (J * P.C₀) + |Csup| + 20 * |C₃|

/-- **The losses are bounded** [S-02:1321–1338]: with `R = ⌈L^{13/25}⌉` and `L ≥ 1`,

`4 L^{C₂} exp(3 J C₀ T L^d) exp(2 C_sup √L) ≤ (4 e^{2c})^R L^{2C₃}`,

`c = pairingConst`. The left side bounds `2 (H + 1) sup|f_n|²`. -/
theorem loss_le (P : GroupParams) (J : ℕ) (C₂ C₃ Csup : ℝ) {L : ℝ} (hL : 1 ≤ L) :
    2 * (2 * (L ^ C₂ * Real.exp (3 * (J * P.C₀) * (Real.log L * L ^ P.d)))) *
        Real.exp (Csup * Real.sqrt L) ^ 2 ≤
      (4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup)) ^ transferR L * L ^ (2 * C₃) := by
  have hL0 : 0 < L := by linarith
  have hT0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hpow : L ^ ((13 : ℝ) / 25) ≤ (transferR L : ℝ) := Nat.le_ceil _
  have hρ1 : (1 : ℝ) ≤ (transferR L : ℝ) := (Real.one_le_rpow hL (by norm_num)).trans hpow
  have hR1 : 1 ≤ transferR L := by exact_mod_cast hρ1
  have hlog : Real.log L ≤ 20 * L ^ ((1 : ℝ) / 20) := by
    have h1 : Real.log L ≤ L ^ ((1 : ℝ) / 20) / (1 / 20) :=
      Real.log_le_rpow_div hL0.le (by norm_num)
    have h3 : L ^ ((1 : ℝ) / 20) / (1 / 20) = 20 * L ^ ((1 : ℝ) / 20) := by ring
    linarith
  have hT : Real.log L ≤ 20 * (transferR L : ℝ) := by
    have h2 : L ^ ((1 : ℝ) / 20) ≤ L ^ ((13 : ℝ) / 25) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    linarith
  have hd0 : 0 ≤ L ^ P.d := Real.rpow_nonneg hL0.le _
  have hTd : Real.log L * L ^ P.d ≤ 20 * (transferR L : ℝ) := by
    have h2 : L ^ ((1 : ℝ) / 20) * L ^ P.d ≤ L ^ ((13 : ℝ) / 25) := by
      rw [← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL (by linarith [P.d_lt])
    calc Real.log L * L ^ P.d ≤ (20 * L ^ ((1 : ℝ) / 20)) * L ^ P.d :=
          mul_le_mul_of_nonneg_right hlog hd0
      _ = 20 * (L ^ ((1 : ℝ) / 20) * L ^ P.d) := by ring
      _ ≤ 20 * (transferR L : ℝ) := by linarith
  have hsq : Real.sqrt L ≤ (transferR L : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)).trans hpow
  have hsq0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hJC : 0 ≤ (J : ℝ) * P.C₀ := mul_nonneg (Nat.cast_nonneg _) P.C₀_pos.le
  have hρ0 : (0 : ℝ) ≤ (transferR L : ℝ) := Nat.cast_nonneg _
  have ha : Real.log L * C₂ ≤ 20 * (transferR L : ℝ) * |C₂| :=
    (mul_le_mul_of_nonneg_left (le_abs_self C₂) hT0).trans
      (mul_le_mul_of_nonneg_right hT (abs_nonneg C₂))
  have hb : 3 * (J * P.C₀) * (Real.log L * L ^ P.d) ≤
      3 * (J * P.C₀) * (20 * (transferR L : ℝ)) :=
    mul_le_mul_of_nonneg_left hTd (mul_nonneg (by norm_num) hJC)
  have he : Csup * Real.sqrt L ≤ |Csup| * (transferR L : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self Csup) hsq0).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg Csup))
  have hf : Real.log L * -C₃ ≤ 20 * (transferR L : ℝ) * |C₃| :=
    (mul_le_mul_of_nonneg_left (neg_le_abs C₃) hT0).trans
      (mul_le_mul_of_nonneg_right hT (abs_nonneg C₃))
  have hexpo : Real.log L * C₂ + 3 * (J * P.C₀) * (Real.log L * L ^ P.d) +
        2 * (Csup * Real.sqrt L) ≤
      (transferR L : ℝ) * (2 * pairingConst P J C₂ C₃ Csup) + Real.log L * (2 * C₃) := by
    unfold pairingConst
    linarith
  have e1 : L ^ C₂ = Real.exp (Real.log L * C₂) := Real.rpow_def_of_pos hL0 C₂
  have e2 : L ^ (2 * C₃) = Real.exp (Real.log L * (2 * C₃)) := Real.rpow_def_of_pos hL0 _
  have e3 : Real.exp (Csup * Real.sqrt L) ^ 2 = Real.exp (2 * (Csup * Real.sqrt L)) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have e4 : Real.exp (2 * pairingConst P J C₂ C₃ Csup) ^ transferR L =
      Real.exp ((transferR L : ℝ) * (2 * pairingConst P J C₂ C₃ Csup)) :=
    (Real.exp_nat_mul _ _).symm
  have hmain : L ^ C₂ * Real.exp (3 * (J * P.C₀) * (Real.log L * L ^ P.d)) *
        Real.exp (Csup * Real.sqrt L) ^ 2 ≤
      Real.exp (2 * pairingConst P J C₂ C₃ Csup) ^ transferR L * L ^ (2 * C₃) := by
    rw [e1, e2, e3, e4, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hexpo
  have h4 : (4 : ℝ) ≤ 4 ^ transferR L := by
    calc (4 : ℝ) = 4 ^ 1 := (pow_one _).symm
      _ ≤ 4 ^ transferR L := pow_le_pow_right₀ (by norm_num) hR1
  calc 2 * (2 * (L ^ C₂ * Real.exp (3 * (J * P.C₀) * (Real.log L * L ^ P.d)))) *
        Real.exp (Csup * Real.sqrt L) ^ 2
      = 4 * (L ^ C₂ * Real.exp (3 * (J * P.C₀) * (Real.log L * L ^ P.d)) *
          Real.exp (Csup * Real.sqrt L) ^ 2) := by ring
    _ ≤ 4 ^ transferR L *
          (Real.exp (2 * pairingConst P J C₂ C₃ Csup) ^ transferR L * L ^ (2 * C₃)) :=
        mul_le_mul h4 hmain
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.exp_pos _).le) (sq_nonneg _))
          (pow_nonneg (by norm_num) _)
    _ = (4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup)) ^ transferR L * L ^ (2 * C₃) := by
        rw [mul_pow]
        ring

/-! ### The pairing bound for one `x` -/

/-- **Corollary 3.11 for one value of `x`** with `log x ≥ 1`: the moment bound for the window
`[X, 2X)` gives the pairing bound, with `M = √12 · exp(pairingConst)`. -/
theorem pairing_bound_of_moment (P : GroupParams) (E : ℝ) {m : ℕ} {C₁ : ℝ} (J : ℕ)
    (C₂ γ C₃ Csup : ℝ) (hγ : 0 < γ) {x : ℝ} (hL : 1 ≤ Real.log x) (hx1 : 1 ≤ x)
    {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔊 : PrimeGroups P x S B) {N : Type} [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ) (ζ : ℝ)
    (k : ℤ) (hadm : Admissible (Real.log x) m C₁ C₂ 𝔉 k) {X : ℝ} (hX : x ^ γ ≤ X)
    (fn : ℤ → ℂ) (g : PState intPos 𝔊.toGroupFamily J P.ℓ → ℂ)
    (hEnd : EndpointHyp 𝔊 J X C₃ Csup fn g)
    (hmom : averagedMoment 𝔊 𝔉 k ζ X ≤
      Real.log x ^ (-(E * (Graph.sourceMemoryLength (Real.log x) : ℝ)))) :
    ‖pairMarkFree intPos 𝔊.toGroupFamily J P.ℓ (intWindow X) fn
        (physOp intPos 𝔊.toGroupFamily P.q 𝔉 k ζ g)‖ ≤
      Real.sqrt 12 * Real.exp (pairingConst P J C₂ C₃ Csup) * X *
        Real.log x ^ (-E + 2 * C₃) := by
  obtain ⟨hsup, hfnorm, hgL2, hgnorm⟩ := hEnd
  have hL0 : 0 < Real.log x := by linarith
  have hX1 : 1 ≤ X := (Real.one_le_rpow hx1 hγ.le).trans hX
  have hX0 : 0 < X := by linarith
  have hR1 : 1 ≤ transferR (Real.log x) :=
    Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hL0 _)
  obtain ⟨R', hR'⟩ : ∃ R' : ℕ, transferR (Real.log x) = R' + 1 :=
    ⟨transferR (Real.log x) - 1, (Nat.sub_add_cancel hR1).symm⟩
  -- the operator inequality
  have hop := pairMarkFree_pow_le (q := P.q) 𝔉 k ζ (intWindow X) fn hgL2 hsup R'
  -- the norms of the endpoints
  have hsq_le : ∀ {t : ℝ}, 0 ≤ t → Real.sqrt t ≤ Real.sqrt X * Real.log x ^ C₃ →
      t ≤ X * Real.log x ^ (2 * C₃) := by
    intro t ht h
    have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg t) h 2
    rwa [Real.sq_sqrt ht, mul_pow, Real.sq_sqrt hX0.le, rpow_sq_eq hL0] at h1
  have hF0 : 0 ≤ markFreeNormSq intPos 𝔊.toGroupFamily J P.ℓ (intWindow X) fn := by
    rw [← gsq_markVec (𝔭 := intPos) (intWindow X) fn]
    exact gsq_nonneg (𝔭 := intPos) (intWindow X) (posSupp_markVec (𝔭 := intPos) (intWindow X) fn)
  have hG0 : 0 ≤ physNormSq intPos 𝔊.toGroupFamily J P.ℓ g := physNormSq_nonneg g
  have hF := hsq_le hF0 hfnorm
  have hG := hsq_le hG0 hgnorm
  have hℓ0 : 0 < Real.log x ^ (2 * C₃) := Real.rpow_pos_of_pos hL0 _
  have hκ0 : 0 < Real.log x ^ (-(2 * E)) := Real.rpow_pos_of_pos hL0 _
  have hY0 : 0 ≤ X * Real.log x ^ (2 * C₃) := (mul_pos hX0 hℓ0).le
  -- the moment bound
  have hκ : Real.log x ^ (-(E * (Graph.sourceMemoryLength (Real.log x) : ℝ))) =
      (Real.log x ^ (-(2 * E))) ^ (R' + 1) := by
    rw [sourceMemoryLength_eq_two_mul, hR', ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    push_cast
    ring
  have hsum0 : 0 ≤ ∑ n ∈ intWindow X,
      physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (R' + 1) n :=
    Finset.sum_nonneg fun n _ => physMoment_nonneg 𝔊.toGroupFamily P.q 𝔉 k ζ (R' + 1) n
  have hsumle : ∑ n ∈ intWindow X, physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (R' + 1) n ≤
      2 * X * (Real.log x ^ (-(2 * E))) ^ (R' + 1) :=
    calc ∑ n ∈ intWindow X, physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (R' + 1) n
        ≤ ((intWindow X).card : ℝ) *
            Real.log x ^ (-(E * (Graph.sourceMemoryLength (Real.log x) : ℝ))) :=
          sum_physMoment_le 𝔊 𝔉 k ζ X hR' hmom
      _ = ((intWindow X).card : ℝ) * (Real.log x ^ (-(2 * E))) ^ (R' + 1) := by rw [hκ]
      _ ≤ 2 * X * (Real.log x ^ (-(2 * E))) ^ (R' + 1) :=
          mul_le_mul_of_nonneg_right (card_intWindow_le hX1) (pow_nonneg hκ0.le _)
  -- the maximal displacement and the supremum of the coefficients
  have hH := stepBound_add_one_le 𝔊 hL J hadm.2.2.1 hadm.2.2.2
  have hloss := loss_le P J C₂ C₃ Csup hL
  rw [hR'] at hloss
  have hH0 : (0 : ℝ) ≤ (stepBound 𝔊.toGroupFamily J k : ℝ) + 1 := by positivity
  have hs0 : 0 ≤ Real.exp (Csup * Real.sqrt (Real.log x)) ^ 2 := sq_nonneg _
  have hV0 : 0 ≤ ((stepBound 𝔊.toGroupFamily J k : ℝ) + 1) *
      Real.exp (Csup * Real.sqrt (Real.log x)) ^ 2 *
      ∑ n ∈ intWindow X, physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (R' + 1) n :=
    mul_nonneg (mul_nonneg hH0 hs0) hsum0
  have hV : ((stepBound 𝔊.toGroupFamily J k : ℝ) + 1) *
        Real.exp (Csup * Real.sqrt (Real.log x)) ^ 2 *
        ∑ n ∈ intWindow X, physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (R' + 1) n ≤
      X * (Real.log x ^ (-(2 * E))) ^ (R' + 1) *
        ((4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup)) ^ (R' + 1) *
          Real.log x ^ (2 * C₃)) := by
    calc ((stepBound 𝔊.toGroupFamily J k : ℝ) + 1) *
          Real.exp (Csup * Real.sqrt (Real.log x)) ^ 2 *
          ∑ n ∈ intWindow X, physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (R' + 1) n
        ≤ (2 * (Real.log x ^ C₂ * Real.exp (3 * (J * P.C₀) *
              (Real.log (Real.log x) * Real.log x ^ P.d)))) *
            Real.exp (Csup * Real.sqrt (Real.log x)) ^ 2 *
            (2 * X * (Real.log x ^ (-(2 * E))) ^ (R' + 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hH hs0) hsumle hsum0
            (mul_nonneg (hH0.trans hH) hs0)
      _ = (2 * (2 * (Real.log x ^ C₂ * Real.exp (3 * (J * P.C₀) *
              (Real.log (Real.log x) * Real.log x ^ P.d)))) *
            Real.exp (Csup * Real.sqrt (Real.log x)) ^ 2) *
            (X * (Real.log x ^ (-(2 * E))) ^ (R' + 1)) := by ring
      _ ≤ ((4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup)) ^ (R' + 1) *
            Real.log x ^ (2 * C₃)) * (X * (Real.log x ^ (-(2 * E))) ^ (R' + 1)) :=
          mul_le_mul_of_nonneg_right hloss (mul_nonneg hX0.le (pow_nonneg hκ0.le _))
      _ = X * (Real.log x ^ (-(2 * E))) ^ (R' + 1) *
            ((4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup)) ^ (R' + 1) *
              Real.log x ^ (2 * C₃)) := by ring
  -- assembling
  have hchain : (‖pairMarkFree intPos 𝔊.toGroupFamily J P.ℓ (intWindow X) fn
        (physOp intPos 𝔊.toGroupFamily P.q 𝔉 k ζ g)‖ ^ 2) ^ (R' + 1) ≤
      (3 * (4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup)) * X ^ 2 *
        (Real.log x ^ (2 * C₃)) ^ 2 * Real.log x ^ (-(2 * E))) ^ (R' + 1) := by
    calc (‖pairMarkFree intPos 𝔊.toGroupFamily J P.ℓ (intWindow X) fn
          (physOp intPos 𝔊.toGroupFamily P.q 𝔉 k ζ g)‖ ^ 2) ^ (R' + 1)
        ≤ (3 * physNormSq intPos 𝔊.toGroupFamily J P.ℓ g) ^ (R' + 1) *
            (markFreeNormSq intPos 𝔊.toGroupFamily J P.ℓ (intWindow X) fn ^ R' *
              (((stepBound 𝔊.toGroupFamily J k : ℝ) + 1) *
                Real.exp (Csup * Real.sqrt (Real.log x)) ^ 2 *
                ∑ n ∈ intWindow X,
                  physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (R' + 1) n)) := hop
      _ ≤ (3 * (X * Real.log x ^ (2 * C₃))) ^ (R' + 1) *
            ((X * Real.log x ^ (2 * C₃)) ^ R' *
              (X * (Real.log x ^ (-(2 * E))) ^ (R' + 1) *
                ((4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup)) ^ (R' + 1) *
                  Real.log x ^ (2 * C₃)))) :=
          mul_le_mul
            (pow_le_pow_left₀ (mul_nonneg (by norm_num) hG0)
              (mul_le_mul_of_nonneg_left hG (by norm_num)) _)
            (mul_le_mul (pow_le_pow_left₀ hF0 hF _) hV hV0 (pow_nonneg hY0 _))
            (mul_nonneg (pow_nonneg hF0 _) hV0)
            (pow_nonneg (mul_nonneg (by norm_num) hY0) _)
      _ = (3 * (4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup)) * X ^ 2 *
            (Real.log x ^ (2 * C₃)) ^ 2 * Real.log x ^ (-(2 * E))) ^ (R' + 1) :=
          assemble_identity R' X (Real.log x ^ (2 * C₃)) (Real.log x ^ (-(2 * E)))
            (4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup))
  have hM2 : (Real.sqrt 12 * Real.exp (pairingConst P J C₂ C₃ Csup)) ^ 2 =
      12 * Real.exp (2 * pairingConst P J C₂ C₃ Csup) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12), ← Real.exp_nat_mul]
    norm_num
  have hL2 : (Real.log x ^ (-E + 2 * C₃)) ^ 2 =
      (Real.log x ^ (2 * C₃)) ^ 2 * Real.log x ^ (-(2 * E)) := by
    rw [rpow_sq_eq hL0, rpow_sq_eq hL0, ← Real.rpow_add hL0]
    congr 1
    ring
  have htarget : (Real.sqrt 12 * Real.exp (pairingConst P J C₂ C₃ Csup) * X *
        Real.log x ^ (-E + 2 * C₃)) ^ 2 =
      3 * (4 * Real.exp (2 * pairingConst P J C₂ C₃ Csup)) * X ^ 2 *
        (Real.log x ^ (2 * C₃)) ^ 2 * Real.log x ^ (-(2 * E)) := by
    rw [mul_pow, mul_pow, hM2, hL2]
    ring
  have htarget0 : 0 ≤ Real.sqrt 12 * Real.exp (pairingConst P J C₂ C₃ Csup) * X *
      Real.log x ^ (-E + 2 * C₃) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) hX0.le)
      (Real.rpow_nonneg hL0.le _)
  have hp2 : ‖pairMarkFree intPos 𝔊.toGroupFamily J P.ℓ (intWindow X) fn
        (physOp intPos 𝔊.toGroupFamily P.q 𝔉 k ζ g)‖ ^ 2 ≤
      (Real.sqrt 12 * Real.exp (pairingConst P J C₂ C₃ Csup) * X *
        Real.log x ^ (-E + 2 * C₃)) ^ 2 := by
    rw [htarget]
    refine (pow_le_pow_iff_left₀ (sq_nonneg _) ?_ (Nat.succ_ne_zero R')).mp hchain
    rw [← htarget]
    exact sq_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) htarget0 two_ne_zero).mp hp2

end Pairing

/-! ### Corollary 3.11 -/

/-- **[S] Corollary 3.11 (endpoint pairing)** [S-02:1266–1339]: for every choice of the constants
of Theorem 3.5, the moment bound implies the pairing bound, with the constant
`M = √12 · exp(10 |C₂| + 30 J C₀ + |C_sup| + 20 |C₃|)` and the threshold `x₀ = max(x₁, e)`, where
`x₁` is the threshold of the moment bound. -/
theorem endpointPairing : EndpointPairing := by
  intro P E Eid m C₁ J C₂ γ _ hγ hM C₃ Csup
  obtain ⟨x₁, hx₁⟩ := hM
  refine ⟨Real.sqrt 12 * Real.exp (Pairing.pairingConst P J C₂ C₃ Csup),
    max x₁ (Real.exp 1), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm hideal X hX1 hX2 fn g hEnd
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hxe
  have hL : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h
  exact Pairing.pairing_bound_of_moment P E J C₂ γ C₃ Csup hγ hL hx1 𝔊 𝔉 ζ k hadm hX1 fn g
    hEnd (hx₁ x hxx₁ S B 𝔊 N 𝔉 ζ k hadm hideal X hX1 hX2)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
