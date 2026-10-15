module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourcePrimeGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Scalar estimates for the assembly of [S] Theorem 3.5

Source: `verification/stage7-sources/S-02.tex`, lines 1020–1258 (`[S-02:1020–1258]`).

Everything here is about real numbers: `L = log x`, `T = log L`, `N`, `P_* = exp(L^c)`.

* `eventually_log_ge`, `eventually_memLength_ge`, `eventually_loglog_le`, `eventually_rpow_ge` —
  "for all sufficiently large `x`": `L`, `N` and `L^c` exceed any constant and `T ≤ ε L^c`
  ("`log P_* = L^c ≫ T`", [S-02:1169]).
* `clean_half`, `dirty_half` — the two halves of (eq:whole-edge-contraction) [S-02:1021–1037]
  from (eq:transference-parameter-choice) and (eq:dirty-J-gain) [S-02:0889–0892].
* `exists_slot_threshold` — "finally choose the fixed integer `J` so large that …"
  [S-02:1025–1031].
* `scalar_low`, `scalar_high`, `scalar_total` — the sums over small and over large rank
  [S-02:1157–1170, 1219–1235], per rank, with the cost `A_*^{2r}` of (eq:rank-coefficient-count).
* `moment_scalar` — the last step of the proof [S-02:1242–1252].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open Filter

noncomputable section

/-! ### Sufficiently large `x` -/

theorem eventually_log_ge (K : ℝ) : ∀ᶠ x : ℝ in atTop, K ≤ Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_ge_atTop K)

/-- `N ≥ L^{0.52}` tends to infinity. -/
theorem eventually_memLength_ge (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K ≤ (Graph.sourceMemoryLength (Real.log x) : ℝ) := by
  have h1 : Tendsto (fun L : ℝ => L ^ ((13 : ℝ) / 25)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h2 := (h1.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop K)
  filter_upwards [h2] with x hx
  have h3 : Real.log x ^ ((13 : ℝ) / 25) ≤ (Nat.ceil (Real.log x ^ ((13 : ℝ) / 25)) : ℝ) :=
    Nat.le_ceil _
  have h4 : (Graph.sourceMemoryLength (Real.log x) : ℝ) =
      2 * (Nat.ceil (Real.log x ^ ((13 : ℝ) / 25)) : ℝ) := by
    unfold Graph.sourceMemoryLength
    push_cast
    ring
  have h5 : (0 : ℝ) ≤ (Nat.ceil (Real.log x ^ ((13 : ℝ) / 25)) : ℝ) := Nat.cast_nonneg _
  have hx' : K ≤ Real.log x ^ ((13 : ℝ) / 25) := hx
  linarith

/-- `L^c` tends to infinity. -/
theorem eventually_rpow_ge (c K : ℝ) (hc : 0 < c) : ∀ᶠ x : ℝ in atTop, K ≤ Real.log x ^ c :=
  ((tendsto_rpow_atTop hc).comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop K)

/-- `T ≤ ε L^c` for large `x`: "`log P_* = L^c ≫ T`" [S-02:1169]. -/
theorem eventually_loglog_le (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ≤ ε * Real.log x ^ c := by
  have h := (isLittleO_log_rpow_atTop hc).def hε
  have h' := Real.tendsto_log_atTop.eventually h
  filter_upwards [h', eventually_log_ge 1] with x hx h1
  have hpos : 0 ≤ Real.log x ^ c := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos] at hx
  exact (le_abs_self _).trans hx

/-! ### Powers of `L` -/

theorem rpow_neg_two_le {L : ℝ} (hL : 4 ≤ L) : L ^ (-2 : ℝ) ≤ 1 / 16 := by
  have hL0 : 0 < L := by linarith
  have h16 : (16 : ℝ) ≤ L ^ 2 := by nlinarith
  rw [Real.rpow_neg hL0.le, Real.rpow_two, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h16

/-- The clean half of (eq:whole-edge-contraction): `2 L^{-E_id + C_s} ≤ ½ L^{-G}` when
`E_id ≥ G + C_s + 2` (eq:transference-parameter-choice) and `L ≥ 4`. -/
theorem clean_half {L G Cs Eid : ℝ} (hL : 4 ≤ L) (h : G + Cs + 2 ≤ Eid) :
    2 * L ^ (-Eid + Cs) ≤ 1 / 2 * L ^ (-G) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have h1 : L ^ (-Eid + Cs) ≤ L ^ (-G + (-2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have e : L ^ (-G + (-2 : ℝ)) = L ^ (-G) * L ^ (-2 : ℝ) := Real.rpow_add hL0 _ _
  rw [e] at h1
  have h2 := rpow_neg_two_le hL
  have h3 : 0 ≤ L ^ (-G) := Real.rpow_nonneg hL0.le _
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

/-- The dirty half of (eq:whole-edge-contraction), i.e. (eq:dirty-J-gain) with the choice of `J`
[S-02:0889–0892, 1025–1031]: if `B ≤ 2L²`, `𝒟 = C^{s}` with `s ≥ c₀ T` and
`(c₀/2) log C ≥ C_d + G + 3`, then `2 L^{C_d} (B/𝒟)^{1/2} ≤ ½ L^{-G}` for `L ≥ 4`. -/
theorem dirty_half {L G Cd c₀ : ℝ} (hL : 4 ≤ L) {Bcut C s : ℕ}
    (hB : (Bcut : ℝ) ≤ 2 * L ^ 2) (hC : 1 ≤ C) (hs : c₀ * Real.log L ≤ (s : ℝ))
    (hJ : Cd + G + 3 ≤ c₀ / 2 * Real.log (C : ℝ)) :
    2 * L ^ Cd * Real.sqrt ((Bcut : ℝ) / ((C ^ s : ℕ) : ℝ)) ≤ 1 / 2 * L ^ (-G) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hC1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hC0 : (0 : ℝ) < (C : ℝ) := by linarith
  have hlogC : 0 ≤ Real.log (C : ℝ) := Real.log_nonneg hC1
  set y : ℝ := c₀ * Real.log (C : ℝ) with hy
  -- `𝒟 ≥ L^{c₀ log C}`
  have hD : L ^ y ≤ ((C ^ s : ℕ) : ℝ) := by
    have e1 : ((C ^ s : ℕ) : ℝ) = (C : ℝ) ^ (s : ℝ) := by
      rw [Nat.cast_pow, Real.rpow_natCast]
    have e2 : L ^ y = (C : ℝ) ^ (c₀ * Real.log L) := by
      rw [Real.rpow_def_of_pos hL0, Real.rpow_def_of_pos hC0, hy]
      congr 1
      ring
    rw [e1, e2]
    exact Real.rpow_le_rpow_of_exponent_le hC1 hs
  have hDpos : (0 : ℝ) < ((C ^ s : ℕ) : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 _) hD
  -- the target for the square root
  have hy6 : 2 * Cd + 2 * G + 6 ≤ y := by rw [hy]; linarith
  have hgoal : Real.sqrt ((Bcut : ℝ) / ((C ^ s : ℕ) : ℝ)) ≤ 1 / 4 * L ^ (-G - Cd) := by
    rw [Real.sqrt_le_iff]
    refine ⟨mul_nonneg (by norm_num) (Real.rpow_nonneg hL0.le _), ?_⟩
    rw [div_le_iff₀ hDpos]
    have e3 : (1 / 4 * L ^ (-G - Cd)) ^ 2 = 1 / 16 * L ^ (-2 * G - 2 * Cd) := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ (-G - Cd)) 2, ← Real.rpow_mul hL0.le]
      norm_num
      ring_nf
    rw [e3]
    have h6 : L ^ (2 : ℝ) * L ^ (4 : ℝ) ≤ L ^ (-2 * G - 2 * Cd) * L ^ y := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h4 : (32 : ℝ) ≤ L ^ (4 : ℝ) := by
      have : L ^ (4 : ℝ) = L ^ 4 := by
        rw [← Real.rpow_natCast]
        norm_num
      rw [this]
      have h16 : (16 : ℝ) ≤ L ^ 2 := by nlinarith
      have e4 : L ^ 4 = L ^ 2 * L ^ 2 := by ring
      rw [e4]
      nlinarith
    have h2 : L ^ (2 : ℝ) = L ^ 2 := Real.rpow_two L
    have hL2 : (0 : ℝ) ≤ L ^ (2 : ℝ) := Real.rpow_nonneg hL0.le _
    have hnn : 0 ≤ L ^ (-2 * G - 2 * Cd) := Real.rpow_nonneg hL0.le _
    calc (Bcut : ℝ) ≤ 2 * L ^ 2 := hB
      _ = 2 * L ^ (2 : ℝ) := by rw [h2]
      _ ≤ 1 / 16 * (L ^ (2 : ℝ) * L ^ (4 : ℝ)) := by
          have h32 := mul_le_mul_of_nonneg_left h4 hL2
          linarith
      _ ≤ 1 / 16 * (L ^ (-2 * G - 2 * Cd) * L ^ y) :=
          mul_le_mul_of_nonneg_left h6 (by norm_num)
      _ ≤ 1 / 16 * (L ^ (-2 * G - 2 * Cd) * ((C ^ s : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hnn) (by norm_num)
      _ = 1 / 16 * L ^ (-2 * G - 2 * Cd) * ((C ^ s : ℕ) : ℝ) := by ring
  have hCd : 0 ≤ L ^ Cd := Real.rpow_nonneg hL0.le _
  have e4 : L ^ Cd * L ^ (-G - Cd) = L ^ (-G) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  calc 2 * L ^ Cd * Real.sqrt ((Bcut : ℝ) / ((C ^ s : ℕ) : ℝ))
      ≤ 2 * L ^ Cd * (1 / 4 * L ^ (-G - Cd)) :=
        mul_le_mul_of_nonneg_left hgoal (mul_nonneg (by norm_num) hCd)
    _ = 1 / 2 * (L ^ Cd * L ^ (-G - Cd)) := by ring
    _ = 1 / 2 * L ^ (-G) := by rw [e4]

/-- "Finally choose the fixed integer `J` so large that …; for example it suffices that
`(c₀/2) log C(J + ℓ, ℓ) > C_a + G + 3`" [S-02:1025–1031]: since `ℓ ≥ 1`, `C(J + ℓ, ℓ) ≥ J + 1`
tends to infinity with `J`. -/
theorem exists_slot_threshold (c₀ K : ℝ) (hc₀ : 0 < c₀) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → K ≤ c₀ / 2 * Real.log (((J + ℓ).choose ℓ : ℕ) : ℝ) := by
  refine ⟨Nat.ceil (Real.exp (2 * K / c₀)), fun J hJ => ?_⟩
  have h1 : J + 1 ≤ (J + ℓ).choose ℓ := by
    calc J + 1 = (J + 1).choose J := (Nat.choose_succ_self_right J).symm
      _ ≤ (J + ℓ).choose J := Nat.choose_le_choose J (by omega)
      _ = (J + ℓ).choose ℓ := Nat.choose_symm_add
  have h2 : Real.exp (2 * K / c₀) ≤ (((J + ℓ).choose ℓ : ℕ) : ℝ) := by
    calc Real.exp (2 * K / c₀) ≤ (Nat.ceil (Real.exp (2 * K / c₀)) : ℝ) := Nat.le_ceil _
      _ ≤ (J : ℝ) := by exact_mod_cast hJ
      _ ≤ ((J + 1 : ℕ) : ℝ) := by push_cast; linarith
      _ ≤ (((J + ℓ).choose ℓ : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 : 2 * K / c₀ ≤ Real.log (((J + ℓ).choose ℓ : ℕ) : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at this
  have h4 : 2 * K ≤ c₀ * Real.log (((J + ℓ).choose ℓ : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left h3 hc₀.le
    rwa [mul_div_cancel₀ _ hc₀.ne'] at this
  linarith

/-! ### The sums over the rank -/

/-- **Small rank, one rank** [S-02:1219–1235]: the bound (eq:low-rank-path-bound) of a collection
of rank `r`, times the number `A_*^{2r} ≤ L^{6r}` of (eq:rank-coefficient-count), is at most
`L^{-(E+7)N}` when `r (6 + 2G + 2C_a) ≤ N` ("`r₀/N = o(1)`") and `G = E + 2 C_v + 9`
(eq:transference-parameter-choice). Here `a = min(N, 2r)` bounds the number of affected edges. -/
theorem scalar_low {L E Cv Ca G A : ℝ} (hL : 2 ≤ L) (hCv : 0 ≤ Cv) (hCa : 0 ≤ Ca) (hE : 0 ≤ E)
    (hG : G = E + 2 * Cv + 9) {n r : ℕ} (hn : 1 ≤ n) (hA0 : 0 ≤ A) (hA : A ≤ L ^ (3 : ℝ))
    (hr : (r : ℝ) * (6 + 2 * G + 2 * Ca) ≤ n) :
    A ^ (2 * r) * (2 * (L ^ Cv) ^ (n + 1) * (L ^ (-G)) ^ (n - min n (2 * r)) *
        (L ^ Ca) ^ min n (2 * r)) ≤ L ^ (-((E + 7) * (n : ℝ))) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have ha1 : min n (2 * r) ≤ n := min_le_left _ _
  have ha2 : min n (2 * r) ≤ 2 * r := min_le_right _ _
  set a : ℕ := min n (2 * r) with ha
  have ha1' : (a : ℝ) ≤ n := by exact_mod_cast ha1
  have ha2' : (a : ℝ) ≤ 2 * r := by exact_mod_cast ha2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have e1 : A ^ (2 * r) ≤ L ^ ((6 : ℝ) * r) := by
    calc A ^ (2 * r) ≤ (L ^ (3 : ℝ)) ^ (2 * r) := pow_le_pow_left₀ hA0 hA _
      _ = L ^ ((3 : ℝ) * ((2 * r : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      _ = L ^ ((6 : ℝ) * r) := by
          congr 1
          push_cast
          ring
  have e2 : (L ^ Cv) ^ (n + 1) = L ^ (Cv * ((n : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    push_cast
    ring
  have e3 : (L ^ (-G)) ^ (n - a) = L ^ (-G * ((n : ℝ) - a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, Nat.cast_sub ha1]
  have e4 : (L ^ Ca) ^ a = L ^ (Ca * (a : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  have e5 : (2 : ℝ) ≤ L ^ (n : ℝ) := by
    calc (2 : ℝ) ≤ L := hL
      _ = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hn'
  have hX : 0 ≤ L ^ (Cv * ((n : ℝ) + 1)) := Real.rpow_nonneg hL0.le _
  have hY : 0 ≤ L ^ (-G * ((n : ℝ) - a)) := Real.rpow_nonneg hL0.le _
  have hZ : 0 ≤ L ^ (Ca * (a : ℝ)) := Real.rpow_nonneg hL0.le _
  have hin : 2 * L ^ (Cv * ((n : ℝ) + 1)) * L ^ (-G * ((n : ℝ) - a)) * L ^ (Ca * (a : ℝ)) ≤
      L ^ (n : ℝ) * L ^ (Cv * ((n : ℝ) + 1)) * L ^ (-G * ((n : ℝ) - a)) * L ^ (Ca * (a : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e5 hX) hY) hZ
  have hin0 : 0 ≤ 2 * L ^ (Cv * ((n : ℝ) + 1)) * L ^ (-G * ((n : ℝ) - a)) *
      L ^ (Ca * (a : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hX) hY) hZ
  have hGnn : 0 ≤ G + Ca := by rw [hG]; linarith [hE]
  have h1 : (G + Ca) * (a : ℝ) ≤ (G + Ca) * (2 * r) := mul_le_mul_of_nonneg_left ha2' hGnn
  have h2 : Cv * 1 ≤ Cv * (n : ℝ) := mul_le_mul_of_nonneg_left hn' hCv
  rw [e2, e3, e4]
  calc A ^ (2 * r) * (2 * L ^ (Cv * ((n : ℝ) + 1)) * L ^ (-G * ((n : ℝ) - a)) *
        L ^ (Ca * (a : ℝ)))
      ≤ L ^ ((6 : ℝ) * r) * (L ^ (n : ℝ) * L ^ (Cv * ((n : ℝ) + 1)) *
          L ^ (-G * ((n : ℝ) - a)) * L ^ (Ca * (a : ℝ))) :=
        mul_le_mul e1 hin hin0 (Real.rpow_nonneg hL0.le _)
    _ = L ^ ((6 : ℝ) * r + ((n : ℝ) + Cv * ((n : ℝ) + 1) + -G * ((n : ℝ) - a) +
          Ca * (a : ℝ))) := by
        rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0]
    _ ≤ L ^ (-((E + 7) * (n : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
        subst hG
        nlinarith

/-- **Large rank, one rank** [S-02:1157–1170]: the bound (eq:high-rank-path-bound) of a collection
of rank `r ≥ r₀`, times the number `A_*^{2r} ≤ L^{6r}` of (eq:rank-coefficient-count), is at most
`L^{-(E+7)N}` when `L^6 C ≤ P_*^{1/2}`, `r₀ ≥ C'' N T / log P_*` (eq:rank-threshold) and
`C'' = 2(2 C_h + E + 7)` ("increasing `C''` beats the fixed exponent `C_h + E`"). -/
theorem scalar_high {L E Ch Cp c C'' A : ℝ} (hL : 2 ≤ L) {n r r₀ : ℕ}
    (hn : 1 ≤ n) (hA0 : 0 ≤ A) (hA : A ≤ L ^ (3 : ℝ)) (hCp : 0 < Cp)
    (hϱ : L ^ (6 : ℝ) * Cp ≤ Real.exp (L ^ c / 2))
    (hr₀ : C'' * (n : ℝ) * Real.log L ≤ L ^ c * (r₀ : ℝ))
    (hC'' : C'' = 2 * (2 * max Ch 0 + E + 7)) (hr : r₀ ≤ r) :
    A ^ (2 * r) * (L ^ (Ch * ((n : ℝ) + 1)) * (Cp / Real.exp (L ^ c)) ^ r) ≤
      L ^ (-((E + 7) * (n : ℝ))) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hT : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLc : 0 ≤ L ^ c := Real.rpow_nonneg hL0.le _
  have hexp : 0 < Real.exp (L ^ c) := Real.exp_pos _
  -- one factor
  have hA2 : A ^ 2 ≤ L ^ (6 : ℝ) := by
    calc A ^ 2 ≤ (L ^ (3 : ℝ)) ^ 2 := pow_le_pow_left₀ hA0 hA 2
      _ = L ^ (6 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
          norm_num
  have hone : A ^ 2 * (Cp / Real.exp (L ^ c)) ≤ Real.exp (-(L ^ c / 2)) := by
    have h1 : A ^ 2 * (Cp / Real.exp (L ^ c)) ≤ L ^ (6 : ℝ) * Cp / Real.exp (L ^ c) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hA2 (div_nonneg hCp.le hexp.le)
    have h2 : L ^ (6 : ℝ) * Cp / Real.exp (L ^ c) ≤ Real.exp (L ^ c / 2) / Real.exp (L ^ c) :=
      div_le_div_of_nonneg_right hϱ hexp.le
    have h3 : Real.exp (L ^ c / 2) / Real.exp (L ^ c) = Real.exp (-(L ^ c / 2)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    linarith
  have hone0 : 0 ≤ A ^ 2 * (Cp / Real.exp (L ^ c)) :=
    mul_nonneg (sq_nonneg A) (div_nonneg hCp.le hexp.le)
  have hpow : A ^ (2 * r) * (Cp / Real.exp (L ^ c)) ^ r ≤
      Real.exp (-(L ^ c * (r₀ : ℝ) / 2)) := by
    calc A ^ (2 * r) * (Cp / Real.exp (L ^ c)) ^ r
        = (A ^ 2 * (Cp / Real.exp (L ^ c))) ^ r := by rw [pow_mul, mul_pow]
      _ ≤ Real.exp (-(L ^ c / 2)) ^ r := pow_le_pow_left₀ hone0 hone r
      _ ≤ Real.exp (-(L ^ c / 2)) ^ r₀ :=
          pow_le_pow_of_le_one (Real.exp_pos _).le
            (Real.exp_le_one_iff.mpr (by linarith)) hr
      _ = Real.exp (-(L ^ c * (r₀ : ℝ) / 2)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hCh : L ^ (Ch * ((n : ℝ) + 1)) = Real.exp (Real.log L * (Ch * ((n : ℝ) + 1))) :=
    Real.rpow_def_of_pos hL0 _
  have htarget : L ^ (-((E + 7) * (n : ℝ))) = Real.exp (Real.log L * (-((E + 7) * (n : ℝ)))) :=
    Real.rpow_def_of_pos hL0 _
  have hmax0 : 0 ≤ max Ch 0 := le_max_right _ _
  have hmax1 : Ch ≤ max Ch 0 := le_max_left _ _
  calc A ^ (2 * r) * (L ^ (Ch * ((n : ℝ) + 1)) * (Cp / Real.exp (L ^ c)) ^ r)
      = L ^ (Ch * ((n : ℝ) + 1)) * (A ^ (2 * r) * (Cp / Real.exp (L ^ c)) ^ r) := by ring
    _ ≤ L ^ (Ch * ((n : ℝ) + 1)) * Real.exp (-(L ^ c * (r₀ : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hL0.le _)
    _ = Real.exp (Real.log L * (Ch * ((n : ℝ) + 1)) + -(L ^ c * (r₀ : ℝ) / 2)) := by
        rw [hCh, ← Real.exp_add]
    _ ≤ Real.exp (Real.log L * (-((E + 7) * (n : ℝ)))) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : Real.log L * (Ch * ((n : ℝ) + 1)) ≤
            Real.log L * (max Ch 0 * (2 * (n : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hT
          calc Ch * ((n : ℝ) + 1) ≤ max Ch 0 * ((n : ℝ) + 1) :=
                mul_le_mul_of_nonneg_right hmax1 (by linarith)
            _ ≤ max Ch 0 * (2 * (n : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hmax0
        subst hC''
        nlinarith
    _ = L ^ (-((E + 7) * (n : ℝ))) := htarget.symm

/-- The sum over the ranks `r ≤ A_*`: `(A_* + 1) L^{-(E+7)N} ≤ ½ L^{-EN}`. -/
theorem scalar_total {L E A : ℝ} (hL : 2 ≤ L) {n : ℕ} (hn : 1 ≤ n) (hA0 : 0 ≤ A)
    (hA : A ≤ L ^ (3 : ℝ)) :
    (A + 1) * L ^ (-((E + 7) * (n : ℝ))) ≤ 1 / 2 * L ^ (-(E * (n : ℝ))) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (1 : ℝ) ≤ L ^ (3 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have h4 : A + 1 ≤ L ^ (4 : ℝ) := by
    have e : L ^ (4 : ℝ) = L ^ (3 : ℝ) * L := by
      rw [show (4 : ℝ) = 3 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
    rw [e]
    nlinarith
  have hW : 0 ≤ L ^ (-((E + 7) * (n : ℝ))) := Real.rpow_nonneg hL0.le _
  have h5 : L ^ (4 : ℝ) * L ^ (-((E + 7) * (n : ℝ))) ≤ L ^ (-(E * (n : ℝ)) + (-1 : ℝ)) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)
  have h6 : L ^ (-(E * (n : ℝ)) + (-1 : ℝ)) = L ^ (-(E * (n : ℝ))) * L⁻¹ := by
    rw [Real.rpow_add hL0, Real.rpow_neg_one]
  have h7 : L⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hL
  have h8 : 0 ≤ L ^ (-(E * (n : ℝ))) := Real.rpow_nonneg hL0.le _
  calc (A + 1) * L ^ (-((E + 7) * (n : ℝ)))
      ≤ L ^ (4 : ℝ) * L ^ (-((E + 7) * (n : ℝ))) := mul_le_mul_of_nonneg_right h4 hW
    _ ≤ L ^ (-(E * (n : ℝ))) * L⁻¹ := by rw [← h6]; exact h5
    _ ≤ L ^ (-(E * (n : ℝ))) * (1 / 2) := mul_le_mul_of_nonneg_left h7 h8
    _ = 1 / 2 * L ^ (-(E * (n : ℝ))) := by ring

/-- The last step [S-02:1242–1252]: "restore the tail; multiply by the baseline, which is at most
one; … finally restore the uniform residue-replacement error": if the three errors are
`½ L^{-EN}`, `L^{-(E+1)N}` and `L^{-(E+1)N}`, their sum is at most `L^{-EN}` (`L ≥ 4`,
`N ≥ 1`). -/
theorem moment_scalar {L E : ℝ} (hL : 4 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    1 / 2 * L ^ (-(E * (n : ℝ))) + L ^ (-((E + 1) * (n : ℝ))) + L ^ (-((E + 1) * (n : ℝ))) ≤
      L ^ (-(E * (n : ℝ))) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : L ^ (-((E + 1) * (n : ℝ))) = L ^ (-(E * (n : ℝ))) * L ^ (-(n : ℝ)) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have h1 : L ^ (-(n : ℝ)) ≤ L ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h2 : L ^ (-1 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg_one, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hL
  have h3 : 0 ≤ L ^ (-(E * (n : ℝ))) := Real.rpow_nonneg hL0.le _
  have h4 : L ^ (-(E * (n : ℝ))) * L ^ (-(n : ℝ)) ≤ L ^ (-(E * (n : ℝ))) * (1 / 4) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) h3
  rw [e]
  linarith

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
