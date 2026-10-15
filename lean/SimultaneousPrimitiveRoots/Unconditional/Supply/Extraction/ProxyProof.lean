module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProxyBoxBound
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoreGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The Type II step (ext:proxy-replacement)

`proxyLink d H b hH hb hq hq1 : ProxyLink d H b q` (`[P-07:0249–0315]`, with the class of
`[PUB-tex:0503–0516]`), for `0 < H`, `b.Coprime H`, `0 < q < 1` and every number of slots: the
field `proxy` of `ExtractionOpenLeaves d H b q q₀`.

Fix `ε, Φ, γ`. With `z = x^γ`, `P = 1_{prime > z}` and `a` the proxy coefficient:

* `Proxy.convPow_sub_convPow`: `P^{*j} - a^{*j} = (P - a) * β_j` for the companion coefficient
  `β_j` ("Telescope one variable `m` at a time and write `n` for the product of the other `j - 1`
  variables"; the `j` steps are collected in one coefficient), so the difference of the two tuple
  sums is `∑_{m, n} 1_{mn ≡ b (H)} Φ((mn-1)/x) F_x(mn-1) (P - a)(m) β_j(n)`
  (`Proxy.shiftSum_antidiagonal`).
* Both coefficients vanish below `m₀ = ⌊z⌋ + 1`, and the pairs are split into the boxes
  `[m₀ 2^a, m₀ 2^{a+1}) × [m₀ 2^c, m₀ 2^{c+1})`, `a, c < ⌈3L⌉` (`Proxy.sum_sum_boxes`). A box
  that meets the support of the cutoff has `x/κ ≤ H_m H_n ≤ κ x`, `κ = max(R + 1, 4/r)`
  (`Proxy.cutoff_eq_zero_of_irrelevant`), and `H_m, H_n > x^γ`, so it has the scales of
  Theorem 3.1 with `δ = γ`.
* `Proxy.box_relevant_le`: each such box is `O(x L^{-4})`, by Theorem 3.1 in the form
  `markedTypeII_twisted` (the class is carried by characters modulo `H`), with `F` the normalized
  clipped statistic, coefficients bounded by `L^{B+1}` and the saving `D_* = B + 8`; here
  `B = ⌈A⌉ + 4` for the exponent `A` of the divisor moment of order `2⌊2/γ⌋`. These exponents
  depend on `γ` only, so `K₀` is chosen before `K`, the bands, `j` and `η`
  (`[P-07:0300–0304]`: "We then choose `K` sufficiently large for that target, simultaneously for
  all `2 ≤ j ≤ 2/γ` … independent of the particular fixed band exponents").

Deviation from the manuscript: the cutoff `Φ((mn-1)/x)` is not separated by Fourier inversion
(`[P-07:0283–0291]`) but by cutting each dyad of `m` into `O(L^{B+4})` short blocks on which it
is, up to `O(L^{-(B+4)})`, a function of `n` alone (`Proxy.abs_cutoff_sub_le`); Theorem 3.1 allows
"an arbitrary interval in `[H_m, 2H_m]`", and is used with `v = 0` only.

All four hypotheses are used: `0 < H` and `b.Coprime H` for the characters modulo `H`
(`Proxy.abs_bilinear_le`), `0 < q < 1` for Theorem 3.1.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

namespace Proxy

/-- `W = exp(L^{0.24}) ≤ x^γ` for large `x`. -/
theorem eventually_roughCutoff_le {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, roughCutoff x ≤ x ^ γ := by
  have hγ2 : (0 : ℝ) < γ ^ 2 := pow_pos hγ 2
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 1 ((γ ^ 2)⁻¹ + 1)),
    eventually_gt_atTop (0 : ℝ)] with x hLx hx0
  have hL1 : 1 ≤ Real.log x := (le_max_left _ _).trans hLx
  have hL2 : (γ ^ 2)⁻¹ + 1 ≤ Real.log x := (le_max_right _ _).trans hLx
  have hLγ : 1 < γ ^ 2 * Real.log x := by
    have h1 : γ ^ 2 * (γ ^ 2)⁻¹ < γ ^ 2 * Real.log x :=
      mul_lt_mul_of_pos_left (by linarith) hγ2
    rwa [mul_inv_cancel₀ hγ2.ne'] at h1
  have h1 := TwoSidedProof.rpow_lt_mul hγ hL1 hLγ
  have h2 : Real.log x ^ (0.24 : ℝ) ≤ Real.log x ^ (0.46 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  unfold roughCutoff
  rw [Real.rpow_def_of_pos hx0]
  exact Real.exp_le_exp.mpr (by linarith)

/-- `L^E ≤ x^γ` for large `x`. -/
theorem eventually_log_pow_le (E : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ E ≤ x ^ γ := by
  have h := (isLittleO_log_rpow_rpow_atTop ((E : ℕ) : ℝ) hγ).def (show (0 : ℝ) < 1 from one_pos)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hL0 : 0 ≤ Real.log x := (Real.log_pos hx1).le
  have hx0 : 0 ≤ x := by linarith
  have hx' : ‖Real.log x ^ ((E : ℕ) : ℝ)‖ ≤ 1 * ‖x ^ γ‖ := hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0 _), Real.norm_of_nonneg (Real.rpow_nonneg hx0 _),
    one_mul, Real.rpow_natCast] at hx'
  exact hx'

/-- `x² ≤ 2^{⌈3L⌉}`: the dyads `a < ⌈3L⌉` cover the support of the cutoff. -/
theorem sq_le_two_pow {x : ℝ} (hx0 : 0 < x) (hL0 : 0 ≤ Real.log x) :
    x * x ≤ (2 : ℝ) ^ ⌈3 * Real.log x⌉₊ := by
  have h1 : (2 : ℝ) ^ ⌈3 * Real.log x⌉₊ = (2 : ℝ) ^ ((⌈3 * Real.log x⌉₊ : ℕ) : ℝ) :=
    (Real.rpow_natCast 2 _).symm
  have h2 : (2 : ℝ) ^ (3 * Real.log x) ≤ (2 : ℝ) ^ ((⌈3 * Real.log x⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
  have h3 : (2 : ℝ) ^ (3 * Real.log x) = Real.exp (Real.log 2 * (3 * Real.log x)) :=
    Real.rpow_def_of_pos two_pos _
  have hlog2 := Real.log_two_gt_d9
  have h4 : Real.log x + Real.log x ≤ Real.log 2 * (3 * Real.log x) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3 * Real.log 2 - 2 by linarith) hL0]
  rw [h1]
  refine le_trans ?_ h2
  rw [h3]
  calc x * x = Real.exp (Real.log x + Real.log x) := by rw [Real.exp_add, Real.exp_log hx0]
    _ ≤ Real.exp (Real.log 2 * (3 * Real.log x)) := Real.exp_le_exp.mpr h4

end Proxy

open Proxy in
/-- **The Type II step** (`[P-07:0249–0315]`): Theorem 3.1 in coefficient form, Lemma 5.2, the
bounded statistic and Mertens' product theorem give the replacement of the prime variables by the
proxy coefficients, with the class `u + 1 ≡ b (mod H)`. -/
theorem proxyLink (d H b : ℕ) (hH : 0 < H) (hb : b.Coprime H) {q : ℝ} (hq : 0 < q)
    (hq1 : q < 1) : ProxyLink d H b q := by
  intro hII h52 hSlot hCore hM2 ε hε Φ hΦ γ hγ _hγ1
  -- the cutoff: support, bound, Lipschitz constant
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨r, hr0, hr⟩ := hΦ.exists_lower
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ.exists_bound
  have hBΦ' : ∀ t, |Φ t| ≤ BΦ := fun t => by
    rw [abs_of_nonneg (hΦ.nonneg t)]
    exact hBΦ t
  obtain ⟨LipN, hLipN⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hΦ.compact hΦ.smooth
      (ENat.one_le_iff_ne_zero_withTop.mp
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  have hLip : ∀ s t : ℝ, |Φ s - Φ t| ≤ (LipN : ℝ) * |s - t| := fun s t => by
    have h := hLipN.dist_le_mul s t
    rwa [Real.dist_eq, Real.dist_eq] at h
  -- the comparison constant of the scales
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = max (R + 1) (4 / r) := ⟨_, rfl⟩
  have hκR : R + 1 ≤ κ := by
    rw [hκdef]
    exact le_max_left _ _
  have hκr : 4 / r ≤ κ := by
    rw [hκdef]
    exact le_max_right _ _
  have hκ1 : 1 ≤ κ := by linarith
  have hκ0 : 0 < κ := by linarith
  -- the divisor moment and the exponents: they depend on `γ` only
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = ⌊2 / γ⌋₊ := ⟨_, rfl⟩
  obtain ⟨Cτ, Aτ, hCτ, hτ⟩ := (divisorMoments (J * 2)).1
  obtain ⟨An, hAn⟩ : ∃ An : ℕ, An = ⌈Aτ⌉₊ := ⟨_, rfl⟩
  have hAτ : Aτ ≤ (An : ℝ) := by
    rw [hAn]
    exact Nat.le_ceil Aτ
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = An + 4 := ⟨_, rfl⟩
  -- Theorem 3.1 with the class carried by characters: `K₀` is chosen here
  obtain ⟨K₀, hK₀⟩ := markedTypeII_twisted hII h52 hH γ ((B + 1 : ℕ) : ℝ)
    ((B + 4 + 4 : ℕ) : ℝ) q κ hγ (by positivity) (by positivity) hq hq1 hκ1
  refine ⟨K₀, fun K hK 𝔞 j hj2 hjγ η hη => ?_⟩
  obtain ⟨M, x₀, hM⟩ := hK₀ K hK 𝔞
  obtain ⟨Bs₀, hBs₀⟩ := hSlot ε hε (4 * κ) (by positivity)
  obtain ⟨BF, hBF0, hBF⟩ := hCore ε hε (4 * κ) (by positivity) K
  obtain ⟨Bs, hBsdef⟩ : ∃ Bs : ℝ, Bs = max Bs₀ 1 := ⟨_, rfl⟩
  have hBs : 0 < Bs := by
    rw [hBsdef]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hBs₀le : Bs₀ ≤ Bs := by
    rw [hBsdef]
    exact le_max_left _ _
  have hjJ : j ≤ J := by
    rw [hJdef]
    exact Nat.le_floor hjγ
  obtain ⟨j', hj'⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  have hj'1 : 1 ≤ j' := by omega
  -- the constant of one box
  obtain ⟨Cbox, hCbox⟩ : ∃ Cbox : ℝ, Cbox = 3 * Bs * |M| * κ + 4 * (LipN : ℝ) * BF * κ ^ 2 +
      2 * BΦ * BF * (J : ℝ) ^ 2 * Cτ * 2 ^ An * κ := ⟨_, rfl⟩
  have hCbox0 : 0 ≤ Cbox := by
    rw [hCbox]
    positivity
  filter_upwards [eventually_ge_atTop x₀, hBs₀, hBF 𝔞, eventually_proxyKappa_le_one hM2 hγ,
    eventually_band_notMem_slot hε, eventually_log_pow_le (B + 4) hγ,
    eventually_roughCutoff_le hγ,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (max BΦ (max γ⁻¹ (16 * Cbox / η)))),
    eventually_ge_atTop (max 1 (max (4 * κ) (R + 2)))]
    with x hx₀ hxs hxF hxκ hxband hxpow hxrough hxL hxbig S hS
  -- the size of `x`
  have hL1 : 1 ≤ Real.log x := (le_max_left _ _).trans hxL
  have hLBΦ : BΦ ≤ Real.log x := ((le_max_left _ _).trans (le_max_right _ _)).trans hxL
  have hLγ : γ⁻¹ ≤ Real.log x :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hxL
  have hLη : 16 * Cbox / η ≤ Real.log x :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hxL
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hxbig
  have hx4κ : 4 * κ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hxbig
  have hxR : R + 2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hxbig
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hz1 : 1 ≤ x ^ γ := Real.one_le_rpow hx1 hγ.le
  have hF : CoeffFacts x γ := ⟨hz1, hxrough, hxκ⟩
  have hγL : 1 ≤ γ * Real.log x := by
    have h := mul_le_mul_of_nonneg_left hLγ hγ.le
    rwa [mul_inv_cancel₀ hγ.ne'] at h
  -- the statistic and the core on the range `u ≤ 4κx`
  obtain ⟨hmass, hcount⟩ := hxs S hS
  have hslot : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ 4 * κ * x →
      |(slotCount S u : ℝ) - slotMass S| ≤ Bs := by
    intro u hu1 hu2
    have h1 := hcount u hu1 hu2
    have h2 : (0 : ℝ) ≤ (slotCount S u : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ slotMass S := by
      unfold slotMass
      exact Finset.sum_nonneg fun 𝔩 _ => by positivity
    rw [abs_le]
    constructor <;> linarith
  have hcoreb : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ 4 * κ * x → |centeredCore q 𝔞 x S u| ≤ BF :=
    fun u hu1 hu2 => hxF S hS u hu1 hu2
  -- the normalized clipped statistic satisfies the hypotheses of Theorem 3.1
  have hFnorm : ∀ h : ℕ, ‖((clipCore Bs S h : ℝ) : ℂ)‖ ≤ 1 := fun h => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_clipCore_le Bs S h
  have hFinv : BandInvariant 𝔞 x (fun h => ((clipCore Bs S h : ℝ) : ℂ)) :=
    bandInvariant_clipCore Bs hS.prime (fun i p hp i' => hxband K 𝔞 i p hp d S hS i')
  have hLC1 : 1 ≤ Real.log x ^ ((B + 1 : ℕ) : ℝ) := Real.one_le_rpow hL1 (Nat.cast_nonneg _)
  have hv0 : |(0 : ℝ)| ≤ Real.log x ^ ((B + 1 : ℕ) : ℝ) := by
    rw [abs_zero]
    exact le_trans zero_le_one hLC1
  -- the dyadic grid
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀ : ℕ, m₀ = ⌊x ^ γ⌋₊ + 1 := ⟨_, rfl⟩
  have hm₀z : x ^ γ < (m₀ : ℝ) := by
    rw [hm₀def]
    push_cast
    exact Nat.lt_floor_add_one _
  have hm₀1 : 1 ≤ m₀ := by
    rw [hm₀def]
    exact Nat.succ_pos _
  obtain ⟨A₁, hA₁def⟩ : ∃ A₁ : ℕ, A₁ = ⌈3 * Real.log x⌉₊ := ⟨_, rfl⟩
  have hN : ⌊R * x⌋₊ + 1 < m₀ * 2 ^ A₁ := by
    have h5 : x * x ≤ (2 : ℝ) ^ A₁ := by
      rw [hA₁def]
      exact sq_le_two_pow hx0 hL0.le
    have h6 : R * x + 2 ≤ x * x := by
      have h := mul_le_mul_of_nonneg_right hxR hx0.le
      linarith
    have h7 : ((⌊R * x⌋₊ + 1 : ℕ) : ℝ) < ((m₀ * 2 ^ A₁ : ℕ) : ℝ) := by
      push_cast
      have h8 : (⌊R * x⌋₊ : ℝ) ≤ R * x := Nat.floor_le (mul_nonneg hR0.le hx0.le)
      have h9 : (2 : ℝ) ^ A₁ ≤ (m₀ : ℝ) * 2 ^ A₁ :=
        le_mul_of_one_le_left (pow_nonneg zero_le_two _) (Nat.one_le_cast.mpr hm₀1)
      linarith
    exact_mod_cast h7
  -- the summand of the double sum
  obtain ⟨tt, htt⟩ : ∃ tt : ℕ → ℕ → ℝ, tt = fun m n =>
      Φ (((m * n - 1 : ℕ) : ℝ) / x) *
        (clsInd H b (m * n) * centeredCore q 𝔞 x S (m * n - 1) * diffCoeff x γ m) *
          beta x γ j n := ⟨_, rfl⟩
  have httmn : ∀ m n : ℕ, tt m n = Φ (((m * n - 1 : ℕ) : ℝ) / x) *
      (clsInd H b (m * n) * centeredCore q 𝔞 x S (m * n - 1) * diffCoeff x γ m) *
        beta x γ j n := by
    intro m n
    rw [htt]
  -- the difference of the two tuple sums as a double sum over `m, n`
  have hstep1 : shiftSum Φ x (fun v => v ≡ b [MOD H])
      (fun u => centeredCore q 𝔞 x S u *
        (convPow j (primeCoeff (x ^ γ)) (u + 1) - convPow j (proxyCoeff x γ) (u + 1))) =
      ∑ m ∈ Finset.Ico 1 (m₀ * 2 ^ A₁), ∑ n ∈ Finset.Ico 1 (m₀ * 2 ^ A₁), tt m n := by
    have hconv : ∀ u : ℕ, centeredCore q 𝔞 x S u *
        (convPow j (primeCoeff (x ^ γ)) (u + 1) - convPow j (proxyCoeff x γ) (u + 1)) =
        centeredCore q 𝔞 x S u *
          ∑ p ∈ (u + 1).divisorsAntidiagonal, diffCoeff x γ p.1 * beta x γ j p.2 := by
      intro u
      rw [convPow_sub_convPow]
      rfl
    rw [shiftSum_congr Φ x _ hconv,
      shiftSum_antidiagonal hR hx0 (fun v => v ≡ b [MOD H]) (centeredCore q 𝔞 x S)
        (fun m n => diffCoeff x γ m * beta x γ j n) hN]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [httmn]
    unfold clsInd
    by_cases hc : m * n ≡ b [MOD H]
    · rw [if_pos hc, if_pos hc]
      ring
    · rw [if_neg hc, if_neg hc]
      ring
  -- only `m, n ≥ m₀` contribute
  have hsubI : Finset.Ico m₀ (m₀ * 2 ^ A₁) ⊆ Finset.Ico 1 (m₀ * 2 ^ A₁) := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hm
    exact Finset.mem_Ico.mpr ⟨hm₀1.trans h1, h2⟩
  have hsmall : ∀ m : ℕ, m ∈ Finset.Ico 1 (m₀ * 2 ^ A₁) → m ∉ Finset.Ico m₀ (m₀ * 2 ^ A₁) →
      ¬x ^ γ < (m : ℝ) := by
    intro m hm hnot hlt
    apply hnot
    refine Finset.mem_Ico.mpr ⟨?_, (Finset.mem_Ico.mp hm).2⟩
    rw [hm₀def]
    exact Nat.succ_le_of_lt ((Nat.floor_lt (le_trans zero_le_one hz1)).mpr hlt)
  have hstep2 : ∑ m ∈ Finset.Ico m₀ (m₀ * 2 ^ A₁), ∑ n ∈ Finset.Ico m₀ (m₀ * 2 ^ A₁), tt m n =
      ∑ m ∈ Finset.Ico 1 (m₀ * 2 ^ A₁), ∑ n ∈ Finset.Ico 1 (m₀ * 2 ^ A₁), tt m n := by
    refine (Finset.sum_congr rfl fun m _ => Finset.sum_subset hsubI fun n hn hnot => ?_).trans
      (Finset.sum_subset hsubI fun m hm hnot => Finset.sum_eq_zero fun n _ => ?_)
    · have hβ0 : beta x γ j n = 0 := by
        by_contra hne
        rw [hj'] at hne
        exact hsmall n hn hnot (beta_lt hj'1 hne)
      rw [httmn, hβ0, mul_zero]
    · rw [httmn, diffCoeff_eq_zero (hsmall m hm hnot), mul_zero, mul_zero, zero_mul]
  -- one box
  have hbox : ∀ a c : ℕ, |∑ m ∈ Finset.Ico (m₀ * 2 ^ a) (m₀ * 2 ^ (a + 1)),
      ∑ n ∈ Finset.Ico (m₀ * 2 ^ c) (m₀ * 2 ^ (c + 1)), tt m n| ≤
        Cbox * (x * (Real.log x ^ 4)⁻¹) := by
    intro a c
    have hpa : m₀ * 2 ^ (a + 1) = 2 * (m₀ * 2 ^ a) := by ring
    have hpc : m₀ * 2 ^ (c + 1) = 2 * (m₀ * 2 ^ c) := by ring
    rw [hpa, hpc]
    obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : ℕ, A₀ = m₀ * 2 ^ a := ⟨_, rfl⟩
    obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℕ, C₀ = m₀ * 2 ^ c := ⟨_, rfl⟩
    rw [← hA₀def, ← hC₀def]
    have hA₀m : m₀ ≤ A₀ := by
      rw [hA₀def]
      exact Nat.le_mul_of_pos_right m₀ (pow_pos two_pos a)
    have hC₀m : m₀ ≤ C₀ := by
      rw [hC₀def]
      exact Nat.le_mul_of_pos_right m₀ (pow_pos two_pos c)
    have hA₀z : x ^ γ < (A₀ : ℝ) := lt_of_lt_of_le hm₀z (Nat.cast_le.mpr hA₀m)
    have hC₀z : x ^ γ < (C₀ : ℝ) := lt_of_lt_of_le hm₀z (Nat.cast_le.mpr hC₀m)
    have hX0 : 0 ≤ Cbox * (x * (Real.log x ^ 4)⁻¹) :=
      mul_nonneg hCbox0 (mul_nonneg hx0.le (inv_nonneg.mpr (pow_nonneg hL0.le 4)))
    simp only [httmn]
    by_cases hrel : x / κ ≤ (A₀ : ℝ) * (C₀ : ℝ) ∧ (A₀ : ℝ) * (C₀ : ℝ) ≤ κ * x
    · -- the scales of Theorem 3.1
      have hsc : TypeIIScales γ κ x (A₀ : ℝ) (C₀ : ℝ) := ⟨hA₀z.le, hC₀z.le, hrel.1, hrel.2⟩
      have h := box_relevant_le hH hb 𝔞 S Φ hF hx1 hL1 hκ1 (j := j) hjJ hB hA₀z hC₀z hrel.2 hBs
        hBF0 hslot hcoreb hBΦ' hLBΦ (NNReal.coe_nonneg LipN) hLip hxpow hγL hx4κ hCτ.le hAτ hτ
        (fun lo hi hlo hhi lam β hβ => hM x hx₀ _ _ hsc _ hFnorm hFinv 0 hv0 lo hi hlo hhi
          (roughDyad_primeMinusRough hlo hhi
            (lt_of_le_of_lt hxrough (lt_of_lt_of_le hA₀z hlo))
            (lt_of_le_of_lt hz1 (lt_of_lt_of_le hA₀z hlo))
            (fun m hm => hxκ m (lt_of_lt_of_le hA₀z (hlo.trans hm))) hLC1) lam β hβ)
      rw [hCbox]
      exact h
    · -- the box does not meet the support of the cutoff
      have hzero : ∑ m ∈ Finset.Ico A₀ (2 * A₀), ∑ n ∈ Finset.Ico C₀ (2 * C₀),
          Φ (((m * n - 1 : ℕ) : ℝ) / x) *
            (clsInd H b (m * n) * centeredCore q 𝔞 x S (m * n - 1) * diffCoeff x γ m) *
              beta x γ j n = 0 := by
        refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun n hn => ?_
        rw [cutoff_eq_zero_of_irrelevant hr0 hr hR hκR hκr hx1 (hm₀1.trans hA₀m)
          (hm₀1.trans hC₀m) hrel hm hn, zero_mul, zero_mul]
      rw [hzero, abs_zero]
      exact hX0
  -- the sum over the boxes
  rw [hstep1, ← hstep2, sum_sum_boxes]
  have hsum := abs_sum_sum_le_const (I := Finset.range A₁) (J := Finset.range A₁)
    (f := fun a c => ∑ m ∈ Finset.Ico (m₀ * 2 ^ a) (m₀ * 2 ^ (a + 1)),
      ∑ n ∈ Finset.Ico (m₀ * 2 ^ c) (m₀ * 2 ^ (c + 1)), tt m n)
    (fun a _ c _ => hbox a c)
  rw [Finset.card_range] at hsum
  have hA₁ : (A₁ : ℝ) ≤ 4 * Real.log x := by
    rw [hA₁def]
    have h := (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hL0.le :
      (0 : ℝ) ≤ 3 * Real.log x)).le
    linarith
  exact hsum.trans (final_sum_arith (Nat.cast_nonneg _) hA₁ hCbox0 hx0.le hL1 hη hLη)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
