module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExtractionErrorBounds
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SlotMass
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SlotMassAll

/-!
# The coefficient error of the extraction

`ExtractionErrorBound d` (`[P-06:0692–0703]`): `∑_{w ≤ a₂ Y} |𝒰_err(w)|² ≤ M Y L^{-A}` for every
`A > 0`: "The square exceptions have relative count at most `L^{O(1)} exp(-L^{.27})` on the
relevant dyads. … the extra terms have a square of a prime at least `x^ε` dividing `w`, a relative
count `O(x^{-ε})`. … Indeed their squared coefficient norm is at most
`Y L^{O(1)} (exp(-L^{.27}) + x^{-ε})`."

* `extractionError_of_slotMass d : SlotMassBounded (d + 1) → ExtractedCoefficientIdentity d →
  MertensReciprocal → PartialMarkedBound → ExtractionErrorBound d`, for every number of slots; the
  bound `C_x = O(1)` is used for the constant part and for the centering.
* `extractionError d`: the field `extractionError` of `EndpointOpenLeaves d`, for every `d`, with
  `slotMassBounded (d + 1)` (`EndpointProof/SlotMassAll.lean`).
* `extractionError_zero`: the case of one slot, with `slotMassBounded_one` only.

The proof, with `N = ⌊a₂ Y⌋`, `W = exp(L^{.27})` and the pieces of
`EndpointProof/ExtractionErrorBounds.lean`:

* `𝒰_err(w) = 0` unless the square of a prime `p ∈ 𝒫_{g_s} ∪ ⋃_i S_i` divides `w`
  (`errEndpoint_eq_zero_of_not_sq`), and all these primes are `≥ W` (`x^ε ≥ exp(2 L^{.46})`);
* there are at most `(N/W)(1 + log N) ≤ a₂ Y · 3L · exp(-L^{.27})` such `w ≤ N`
  (`card_filter_sq_dvd_le`; `N ≤ x²` by `a₂_mul_scale_le_sq`);
* `|𝒰_err(w)| ≤ K L^E` on `1 ≤ w ≤ x²` (`norm_errEndpoint_le`);
* `L^{2E + 1 + A} exp(-L^{.27}) ≤ 1` for large `x` (`eventually_rpow_mul_exp_neg_le_one`).

So `M = 3 a₂ K²`, with `K = C_W ((2/ε)^{d+1} + B_s) + 16/v₋ + 4 B_s/v₋` and
`E = Dψ 0 + max(C₁, C) + 2`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- `L^b exp(-L^{.27}) ≤ 1` for large `x`. -/
theorem eventually_rpow_mul_exp_neg_le_one (b : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ b * Real.exp (-(Real.log x ^ (0.27 : ℝ))) ≤ 1 := by
  have h1 : Tendsto (fun t : ℝ => t ^ (b / 0.27) * Real.exp (-1 * t)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b / 0.27) 1 one_pos
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ (0.27 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.27)).comp Real.tendsto_log_atTop
  have h3 : Tendsto (fun x : ℝ => (Real.log x ^ (0.27 : ℝ)) ^ (b / 0.27) *
      Real.exp (-1 * Real.log x ^ (0.27 : ℝ))) atTop (𝓝 0) := h1.comp h2
  have h4 : ∀ᶠ x : ℝ in atTop, (Real.log x ^ (0.27 : ℝ)) ^ (b / 0.27) *
      Real.exp (-1 * Real.log x ^ (0.27 : ℝ)) < 1 :=
    h3.eventually (eventually_lt_nhds one_pos)
  filter_upwards [h4, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hL0 : 0 ≤ Real.log x := (Real.log_pos hx1).le
  have hpow : (Real.log x ^ (0.27 : ℝ)) ^ (b / 0.27) = Real.log x ^ b := by
    rw [← Real.rpow_mul hL0, mul_div_cancel₀ b (by norm_num : (0.27 : ℝ) ≠ 0)]
  rw [hpow, neg_one_mul] at hx
  exact hx.le

/-- **The coefficient error of the extraction** (`[P-06:0692–0703]`), for `d + 1` slots with
`C_x = O(1)`. -/
theorem extractionError_of_slotMass (d : ℕ) (hS : SlotMassBounded (d + 1)) :
    ExtractedCoefficientIdentity d → MertensReciprocal → PartialMarkedBound →
      ExtractionErrorBound d := by
  intro hEI hM hPM D A _
  obtain ⟨CW, hCW⟩ := Extraction.arrayWeightBounded_all hM D.q D.q_pos D.q_lt_one D.K
  obtain ⟨Bs, xs, hBs⟩ := hS D.ε D.ε_pos
  obtain ⟨C₁, x₁, hC₁⟩ := hPM D.P D.q₀ D.q₀_pos D.q₀_lt_one D.m'
  obtain ⟨C, xc, hC⟩ := coefficientBound d hM hPM D
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = CW * ((2 / D.ε) ^ (d + 1) + Bs) + 16 * D.P.vlo⁻¹ +
      4 * Bs * D.P.vlo⁻¹ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = D.Dψ 0 + max C₁ C + 2 := ⟨_, rfl⟩
  -- the thresholds
  have hpowL : ∀ r : ℝ, 0 < r → ∀ b : ℝ, ∀ᶠ x : ℝ in atTop, b < Real.log x ^ r :=
    fun r hr b => ((tendsto_rpow_atTop hr).comp Real.tendsto_log_atTop).eventually_gt_atTop b
  have hLLo : ∀ᶠ x : ℝ in atTop, ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ (0.19 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.19)).def one_pos)
  have hev : ∀ᶠ x : ℝ in atTop,
      (∀ n, |markedWeight D.q D.𝔞 x n| ≤ CW) ∧
      Real.log x ^ (2 * E + 1 + A) * Real.exp (-(Real.log x ^ (0.27 : ℝ))) ≤ 1 ∧
      2 < Real.log x ^ (0.07 : ℝ) ∧ 2 / D.ε < Real.log x ^ (0.54 : ℝ) ∧
      |D.c₂| < Real.log x ^ (0.25 : ℝ) ∧ 2 < Real.log x ^ (0.1 : ℝ) ∧
      ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ (0.19 : ℝ)‖ ∧
      2 * Real.log D.a₂ ≤ Real.log x ∧ 1 ≤ Real.log x ∧ 1 < x := by
    filter_upwards [hCW D.𝔞, eventually_rpow_mul_exp_neg_le_one (2 * E + 1 + A),
      hpowL 0.07 (by norm_num) 2, hpowL 0.54 (by norm_num) (2 / D.ε),
      hpowL 0.25 (by norm_num) |D.c₂|, hpowL 0.1 (by norm_num) 2, hLLo,
      Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log D.a₂),
      Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ)]
      with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨3 * D.a₂ * K ^ 2, max x₀ (max xs (max x₁ xc)), ?_⟩
  intro x hx c hc i₀
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hxs : xs ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxx₁ : x₁ ≤ x :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hxc : xc ≤ x :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  obtain ⟨hW, hlimx, h07, h54, hc₂, h10, hLLn, ha₂, hL1, hx1⟩ := hx₀ x hxx₀
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hY : 0 < c.Y := lt_of_lt_of_le (mul_pos hx0 (Real.exp_pos _)) hc.scale_ge
  have ha₂pos : 0 < D.a₂ := lt_of_lt_of_le D.a₁_pos D.a₁_le_a₂
  have hLL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have hp19 : 0 ≤ Real.log x ^ (0.19 : ℝ) := Real.rpow_nonneg hL0.le _
  have hLL : Real.log (Real.log x) ≤ Real.log x ^ (0.19 : ℝ) := by
    have h := hLLn
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0, abs_of_nonneg hp19] at h
    exact h
  have haY : D.a₂ * c.Y ≤ x ^ (2 : ℝ) :=
    a₂_mul_scale_le_sq D hx1 hLL hc₂.le h10.le ha₂ hL1 hc.scale_le
  -- the bounds for the factors
  have hBsx : slotMass c.S ≤ Bs := hBs x hxs c.S hc.slots
  have hact : ∀ n, ‖c.𝔊.activeWeight D.q₀ c.t c.test n‖ ≤ Real.log x ^ C₁ := by
    intro n
    have h := hC₁ x hxx₁ c.𝔊 hc.groups c.t (fun g => (hc.marks g).2) c.test hc.test_le ∅ n
    rw [partialWeight_empty] at h
    exact h
  have hcoef := hC x hxc c hc i₀
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊D.a₂ * c.Y⌋₊ := ⟨_, rfl⟩
  rw [← hN]
  have hNle : (N : ℝ) ≤ D.a₂ * c.Y := by
    rw [hN]
    exact Nat.floor_le (mul_pos ha₂pos hY).le
  have hNx : (N : ℝ) ≤ x ^ (2 : ℝ) := hNle.trans haY
  -- the pointwise bound on `1 ≤ w ≤ N`
  have hpt : ∀ w ∈ Finset.Icc 1 N, ‖c.errEndpoint D x i₀ w‖ ≤ K * Real.log x ^ E := by
    intro w hw
    obtain ⟨hw1, hwN⟩ := Finset.mem_Icc.mp hw
    rw [hK, hE]
    exact norm_errEndpoint_le D hc i₀ hx1 hL1 hW hBsx hact hcoef hw1
      ((Nat.cast_le.mpr hwN).trans hNx)
  -- the primes whose squares matter are at least `exp(L^{.27})`
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = c.smallGroup i₀ ∪ Finset.univ.biUnion c.S := ⟨_, rfl⟩
  have hTge : ∀ p ∈ T, Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ (p : ℝ) := by
    intro p hp
    rw [hT] at hp
    rcases Finset.mem_union.mp hp with h | h
    · exact (hc.groups.small_range i₀ p h).1
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
      have h1 := slot_prime_gt D hL1 h54 hx0 hc i hi
      have h3 : Real.log x ^ (0.27 : ℝ) ≤ Real.log x ^ (0.46 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have h4 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
      have h2 : Real.exp (Real.log x ^ (0.27 : ℝ)) ≤
          Real.exp (2 * Real.log x ^ (0.46 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      linarith
  -- the error vanishes away from the squares
  have hzero : ∀ w ∈ Finset.Icc 1 N, ‖c.errEndpoint D x i₀ w‖ ^ 2 ≠ 0 →
      ∃ p ∈ T, p ^ 2 ∣ w := by
    intro w hw hne
    by_contra hno
    have hw0 : 0 < w := Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hw).1
    have h0 : c.errEndpoint D x i₀ w = 0 := by
      refine errEndpoint_eq_zero_of_not_sq hEI D hL1 h07 h54 hx0 hc i₀ hw0 ?_ ?_
      · intro p hp hdvd
        refine hno ⟨p, ?_, hdvd⟩
        rw [hT]
        exact Finset.mem_union_left _ hp
      · intro i l hl hdvd
        refine hno ⟨l, ?_, hdvd⟩
        rw [hT]
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hl⟩)
    apply hne
    rw [h0, norm_zero]
    norm_num
  classical
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ,
      F = (Finset.Icc 1 N).filter (fun w => ∃ p ∈ T, p ^ 2 ∣ w) := ⟨_, rfl⟩
  have hsum : ∑ w ∈ Finset.Icc 1 N, ‖c.errEndpoint D x i₀ w‖ ^ 2 =
      ∑ w ∈ F, ‖c.errEndpoint D x i₀ w‖ ^ 2 := by
    rw [hF]
    exact (Finset.sum_filter_of_ne hzero).symm
  have hcard : (F.card : ℝ) ≤
      (N : ℝ) / Real.exp (Real.log x ^ (0.27 : ℝ)) * (1 + Real.log N) :=
    card_filter_sq_dvd_le (Real.exp_pos _) hTge N F (fun w hw => by
      rw [hF] at hw
      exact ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩)
  have hsq : ∀ w ∈ F, ‖c.errEndpoint D x i₀ w‖ ^ 2 ≤ (K * Real.log x ^ E) ^ 2 := by
    intro w hw
    rw [hF] at hw
    exact pow_le_pow_left₀ (norm_nonneg _) (hpt w (Finset.mem_filter.mp hw).1) 2
  -- the sizes
  have hlogN : Real.log (N : ℝ) ≤ 2 * Real.log x := by
    by_cases hN0 : N = 0
    · rw [hN0, Nat.cast_zero, Real.log_zero]
      linarith
    · have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
      have h1 := Real.log_le_log hNpos hNx
      rw [Real.log_rpow hx0] at h1
      exact h1
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = Real.exp (Real.log x ^ (0.27 : ℝ)) := ⟨_, rfl⟩
  rw [← hWdef] at hcard
  have hWpos : 0 < W := by
    rw [hWdef]
    exact Real.exp_pos _
  have hlim' : Real.log x ^ (2 * E + 1 + A) * W⁻¹ ≤ 1 := by
    rw [hWdef, ← Real.exp_neg]
    exact hlimx
  have hpow : Real.log x * (Real.log x ^ E) ^ 2 =
      Real.log x ^ (-A) * Real.log x ^ (2 * E + 1 + A) := by
    have e1 : Real.log x ^ (-A) * Real.log x ^ (2 * E + 1 + A) =
        Real.log x ^ (1 + (E + E)) := by
      rw [← Real.rpow_add hL0]
      congr 1
      ring
    rw [e1, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one, pow_two]
  have hKL0 : 0 ≤ (K * Real.log x ^ E) ^ 2 := sq_nonneg _
  have hPA0 : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0.le _
  have hcoef0 : 0 ≤ 3 * D.a₂ * K ^ 2 * c.Y :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha₂pos.le) (sq_nonneg K)) hY.le
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hlen : (N : ℝ) / W * (1 + Real.log N) ≤ D.a₂ * c.Y / W * (3 * Real.log x) :=
    mul_le_mul (div_le_div_of_nonneg_right hNle hWpos.le) (by linarith) (by linarith)
      (div_nonneg (mul_pos ha₂pos hY).le hWpos.le)
  calc ∑ w ∈ Finset.Icc 1 N, ‖c.errEndpoint D x i₀ w‖ ^ 2
      = ∑ w ∈ F, ‖c.errEndpoint D x i₀ w‖ ^ 2 := hsum
    _ ≤ ∑ _w ∈ F, (K * Real.log x ^ E) ^ 2 := Finset.sum_le_sum hsq
    _ = (F.card : ℝ) * (K * Real.log x ^ E) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) / W * (1 + Real.log N) * (K * Real.log x ^ E) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard hKL0
    _ ≤ D.a₂ * c.Y / W * (3 * Real.log x) * (K * Real.log x ^ E) ^ 2 :=
        mul_le_mul_of_nonneg_right hlen hKL0
    _ = 3 * D.a₂ * K ^ 2 * c.Y * W⁻¹ * (Real.log x * (Real.log x ^ E) ^ 2) := by ring
    _ = 3 * D.a₂ * K ^ 2 * c.Y * W⁻¹ *
          (Real.log x ^ (-A) * Real.log x ^ (2 * E + 1 + A)) := by rw [hpow]
    _ = 3 * D.a₂ * K ^ 2 * c.Y *
          (Real.log x ^ (-A) * (Real.log x ^ (2 * E + 1 + A) * W⁻¹)) := by ring
    _ ≤ 3 * D.a₂ * K ^ 2 * c.Y * (Real.log x ^ (-A) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlim' hPA0) hcoef0
    _ = 3 * D.a₂ * K ^ 2 * c.Y * Real.log x ^ (-A) := by rw [mul_one]

/-- **The field `extractionError` of `EndpointOpenLeaves 0`** (one slot): the coefficient error
of the extraction, `[P-06:0692–0703]`. -/
theorem extractionError_zero : ExtractedCoefficientIdentity 0 → MertensReciprocal →
    PartialMarkedBound → ExtractionErrorBound 0 :=
  extractionError_of_slotMass 0 slotMassBounded_one

/-- **The field `extractionError` of `EndpointOpenLeaves d`**, for every number of slots: the
coefficient error of the extraction, `[P-06:0692–0703]`. -/
theorem extractionError (d : ℕ) : ExtractedCoefficientIdentity d → MertensReciprocal →
    PartialMarkedBound → ExtractionErrorBound d :=
  extractionError_of_slotMass d (slotMassBounded (d + 1))

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
