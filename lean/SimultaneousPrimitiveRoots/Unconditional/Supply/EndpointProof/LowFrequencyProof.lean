module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.LowFrequencyTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.DivisorModelProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.LowMainTermProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExtractionErrorBounds
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.PartialWeight

/-!
# The low-frequency step

`lowFrequency d : DivisorModel → LowMainTerm → SlotMassBounded (d + 1) → LowFrequencyBound (d + 1)`
(`[P-06:0646–0679]`): "For every fixed `B' > 0`, we claim uniformly for `|t| ≤ L^{B'}` that the
normalized sum in (cor:SM) saves any prescribed log power."

With `Φ(w) = ψ_1(w/Y) w^{i(t+σ)} e(hw/k)`, `H = H_marks`, and
`T(m) = ∑_{a₁ Y/m ≤ n ≤ a₂ Y/m} Φ(m n) H(n)` (`scaleSum`):

* `Y · (the normalized sum) = ∑_𝔩 T(l_𝔩) - C_x T(1)`: "In a tuple term put `w = l n`. All long
  primes lie outside the marked groups, so `H_marks(l n) = H_marks(n)`" (`hMarks_congr`; the slot
  primes exceed `exp(2 L^{.46})`, `slot_prime_gt`).
* "Apply Lemma `lem:divisor-model` on the scales `Y/l` and `Y`": the model `H_0 = ∑_{d' ∣ n} A_{d'}`
  with precision `2(N + |D_0|)`; "Cauchy and (cor:model-error)" (`norm_sum_mul_le_of_dyadic`, with
  `λ = L^{N + |D_0|}`) give the error `≤ (Y/m) C_E L^{-N}` at the scale `m`.
* "For a fixed divisor `d'`, all primes in `l d'` exceed `k` for large `x`, so `gcd(l d', k) = 1`"
  (the marked primes are `≥ exp(L^{.1}) > L^{C_6} ≥ k`), and (cor:low-main-term) gives
  `∑_v Φ(m d' v) = (Y/(m d')) G + O(L^{C})` (`norm_scaleSum_sub_main_le`).
* "`∑_𝔩 1 ≤ x^{1-ε} C_x`, `∑_{d'} |A_{d'}| ≤ exp(O(L^{.47})) L^{C_8}`. The summed errors in
  (cor:low-main-term) are therefore `O(x^{-ε+o(1)})`, since `Y ≥ x^{1-o(1)}`"
  (`card_slotTuples_le`, `eventually_rpow_neg_mul_exp_mul_rpow_le_one`).
* "The main term depends on `l` only through `1/l`. Its tuple sum is exactly `C_x` times the main
  term for the subtracted constant. They cancel" (`norm_sum_scale_sub_le`).

The constant is `M = |B_s| (2 e^{c₁} |M_L| + 2 C_E)`, `C_E = (2^{⌈a₂/a₁⌉+1} |M_E| a₁ + a₂)/2`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-! ### Slot tuples -/

/-- A tuple of distinct slot primes: its entries, and the size of its product. -/
theorem slotTuple_facts {d : ℕ} {ε x : ℝ} {S : Fin d → Finset ℕ} (hS : SlotsAdmissible ε x S)
    {𝔩 : Fin d → ℕ} (h𝔩 : 𝔩 ∈ slotTuples S) :
    (∀ i, 𝔩 i ∈ S i) ∧ 0 < ∏ i, 𝔩 i ∧ ((∏ i, 𝔩 i : ℕ) : ℝ) ≤ x ^ (1 - ε) := by
  have hmem : ∀ i, 𝔩 i ∈ S i := by
    unfold slotTuples at h𝔩
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp h𝔩).1
  refine ⟨hmem, Finset.prod_pos fun i _ => (hS.prime i _ (hmem i)).pos, ?_⟩
  rw [Nat.cast_prod]
  calc ∏ i, ((𝔩 i : ℕ) : ℝ) ≤ ∏ i, (((S i).sup id : ℕ) : ℝ) :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
          (fun i _ => Nat.cast_le.mpr (Finset.le_sup (f := id) (hmem i)))
    _ ≤ x ^ (1 - ε) := hS.upper

/-- `∑_𝔩 1 ≤ x^{1-ε} C_x` (`[P-06:0669]`). -/
theorem card_slotTuples_le {d : ℕ} {ε x : ℝ} {S : Fin d → Finset ℕ}
    (hS : SlotsAdmissible ε x S) : ((slotTuples S).card : ℝ) ≤ x ^ (1 - ε) * slotMass S := by
  unfold slotMass
  rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun 𝔩 h𝔩 => ?_
  obtain ⟨-, hpos, hle⟩ := slotTuple_facts hS h𝔩
  have hpos' : (0 : ℝ) < ((∏ i, 𝔩 i : ℕ) : ℝ) := Nat.cast_pos.mpr hpos
  rw [Nat.cast_one, mul_one_div, le_div_iff₀ hpos', one_mul]
  exact hle

/-! ### The statement -/

/-- **The low-frequency step** (`[P-06:0646–0679]`), for any number `d + 1` of slots: from the
truncated divisor model, (cor:low-main-term) and `C_x = O(1)`. -/
theorem lowFrequency (d : ℕ) :
    DivisorModel → LowMainTerm → SlotMassBounded (d + 1) → LowFrequencyBound (d + 1) := by
  intro hDM hLM hSM D B' N _ hN
  obtain ⟨Csupp, C₈, hmodel⟩ :=
    hDM D.q D.q₀ D.q_pos D.q_lt_one D.q₀_pos D.q₀_lt_one D.K D.𝔞 D.P D.m'
  have hD0 : 0 ≤ |D.Dψ 0| := abs_nonneg _
  obtain ⟨ME, xE, hE⟩ := hmodel (2 * (N + |D.Dψ 0|)) (by linarith)
  obtain ⟨CL, ML, xL, hLMx⟩ :=
    hLM D.a₁ D.a₂ D.a₁_pos D.a₁_le_a₂ (D.Dψ 0) (D.Dψ 1) D.Cσ D.C₆ B'
  obtain ⟨Bs, xs, hBs⟩ := hSM D.ε D.ε_pos
  obtain ⟨CE, hCE⟩ : ∃ CE : ℝ,
      CE = (2 ^ (⌈D.a₂ / D.a₁⌉₊ + 1) * |ME| * D.a₁ + D.a₂) / 2 := ⟨_, rfl⟩
  have hCE0 : 0 ≤ CE := by
    have ha₂ : 0 < D.a₂ := lt_of_lt_of_le D.a₁_pos D.a₁_le_a₂
    have h1 : 0 ≤ (2 : ℝ) ^ (⌈D.a₂ / D.a₁⌉₊ + 1) * |ME| * D.a₁ :=
      mul_nonneg (mul_nonneg (pow_nonneg zero_le_two _) (abs_nonneg _)) D.a₁_pos.le
    rw [hCE]
    linarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hae : 0 < D.a₁ * Real.exp (-D.c₁) := mul_pos D.a₁_pos (Real.exp_pos _)
  -- the thresholds
  have hpowL : ∀ r : ℝ, 0 < r → ∀ b : ℝ, ∀ᶠ x : ℝ in atTop, b ≤ Real.log x ^ r :=
    fun r hr b => ((tendsto_rpow_atTop hr).comp Real.tendsto_log_atTop).eventually_ge_atTop b
  have hC6pos : 0 < 1 / (|D.C₆| + 1) := by
    have h := abs_nonneg D.C₆
    exact one_div_pos.mpr (by linarith)
  have hLLo : ∀ᶠ x : ℝ in atTop, ‖Real.log (Real.log x)‖ ≤
      1 / (|D.C₆| + 1) * ‖Real.log x ^ (1 / 10 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).def hC6pos)
  have h54 : ∀ᶠ x : ℝ in atTop, 2 / D.ε < Real.log x ^ (0.54 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.54)).comp
      Real.tendsto_log_atTop).eventually_gt_atTop _
  have hxε : ∀ᶠ x : ℝ in atTop, 1 / (D.a₁ * Real.exp (-D.c₁)) ≤ x ^ D.ε :=
    (tendsto_rpow_atTop D.ε_pos).eventually_ge_atTop _
  have hev : ∀ᶠ x : ℝ in atTop,
      (Real.exp 1 ≤ Real.log x ∧ 2 ≤ Real.log x ^ (0.26 : ℝ) ∧
        2 / D.ε < Real.log x ^ (0.54 : ℝ) ∧
        ‖Real.log (Real.log x)‖ ≤ 1 / (|D.C₆| + 1) * ‖Real.log x ^ (1 / 10 : ℝ)‖) ∧
      (1 / (D.a₁ * Real.exp (-D.c₁)) ≤ x ^ D.ε ∧ 1 / (D.a₁ * Real.exp (-D.c₁)) ≤ x ∧
        1 < x) ∧
      (x ^ (-D.ε) * Real.exp (Csupp * Real.log x ^ (0.47 : ℝ)) *
          Real.log x ^ (C₈ + CL + N) ≤ 1 ∧
        x ^ (-(1 : ℝ)) * Real.exp (Csupp * Real.log x ^ (0.47 : ℝ)) *
          Real.log x ^ (C₈ + CL + N) ≤ 1) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
      hpowL 0.26 (by norm_num) 2, h54, hLLo, hxε,
      eventually_ge_atTop (1 / (D.a₁ * Real.exp (-D.c₁))), eventually_gt_atTop (1 : ℝ),
      eventually_rpow_neg_mul_exp_mul_rpow_le_one D.ε_pos Csupp (C₈ + CL + N),
      eventually_rpow_neg_mul_exp_mul_rpow_le_one one_pos Csupp (C₈ + CL + N)]
      with x a1 a2 a3 a4 a5 a6 a7 a8 a9
    exact ⟨⟨a1, a2, a3, a4⟩, ⟨a5, a6, a7⟩, a8, a9⟩
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.mp hev
  refine ⟨|Bs| * (2 * Real.exp D.c₁ * |ML| + 2 * CE), max (max xE xL) (max xs x₃), ?_⟩
  intro x hx c hc k hk hkL h τ hτ
  have hxE : xE ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxL : xL ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxs : xs ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxx₃ : x₃ ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨⟨hLe, h26, h54x, hLLn⟩, ⟨hxεx, hxa, hx1⟩, hu, hu'⟩ := hx₃ x hxx₃
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL1 : 1 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hL0).mpr hLe
  have hLL0 : 0 ≤ Real.log (Real.log x) := by linarith
  have h46 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
  -- the scale
  have hYlow : x * Real.exp (-D.c₁) ≤ c.Y := by
    have h39 : 0 ≤ Real.log x ^ (0.39 : ℝ) := Real.rpow_nonneg hL0.le _
    exact le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hx0.le)
      hc.scale_ge
  have hxe0 : 0 < x * Real.exp (-D.c₁) := mul_pos hx0 (Real.exp_pos _)
  have hY : 0 < c.Y := lt_of_lt_of_le hxe0 hYlow
  have hWpos : 0 < D.a₁ * c.Y := mul_pos D.a₁_pos hY
  have haY : D.a₁ * Real.exp (-D.c₁) * x ≤ D.a₁ * c.Y := by
    have h1 := mul_le_mul_of_nonneg_left hYlow D.a₁_pos.le
    linarith
  have h1Y : ((1 : ℕ) : ℝ) ≤ D.a₁ * c.Y := by
    have h1 : 1 ≤ D.a₁ * Real.exp (-D.c₁) * x := (div_le_iff₀' hae).mp hxa
    rw [Nat.cast_one]
    linarith
  have hlY : ∀ 𝔩 ∈ slotTuples c.S, ((∏ i, 𝔩 i : ℕ) : ℝ) ≤ D.a₁ * c.Y := by
    intro 𝔩 h𝔩
    have h1 := (slotTuple_facts hc.slots h𝔩).2.2
    have h2 : 1 ≤ D.a₁ * Real.exp (-D.c₁) * x ^ D.ε := (div_le_iff₀' hae).mp hxεx
    have h3 : x ^ D.ε * x ^ (1 - D.ε) = x := by
      have e : D.ε + (1 - D.ε) = 1 := by ring
      rw [← Real.rpow_add hx0, e, Real.rpow_one]
    have h4 : 0 ≤ x ^ (1 - D.ε) := Real.rpow_nonneg hx0.le _
    calc ((∏ i, 𝔩 i : ℕ) : ℝ) ≤ x ^ (1 - D.ε) := h1
      _ = 1 * x ^ (1 - D.ε) := (one_mul _).symm
      _ ≤ D.a₁ * Real.exp (-D.c₁) * x ^ D.ε * x ^ (1 - D.ε) :=
          mul_le_mul_of_nonneg_right h2 h4
      _ = D.a₁ * Real.exp (-D.c₁) * (x ^ D.ε * x ^ (1 - D.ε)) := by ring
      _ = D.a₁ * Real.exp (-D.c₁) * x := by rw [h3]
      _ ≤ D.a₁ * c.Y := haY
  -- the cutoff
  have hψ0 : ∀ u : ℝ, ‖c.ψ₁ u‖ ≤ Real.log x ^ D.Dψ 0 := fun u => by
    have h1 := hc.cutoff_deriv 0 u
    rw [iteratedDeriv_zero] at h1
    exact h1
  have hψ1 : ∀ u : ℝ, ‖deriv c.ψ₁ u‖ ≤ Real.log x ^ D.Dψ 1 := fun u => by
    have h1 := hc.cutoff_deriv 1 u
    rw [iteratedDeriv_one] at h1
    exact h1
  -- the divisor model
  obtain ⟨A, hAmodel, hAerr⟩ := hE x hxE c.𝔊 hc.groups c.t (fun g => (hc.marks g).2) c.test
    hc.test_le ∅
  obtain ⟨Emax, hEmax⟩ : ∃ Emax : ℕ,
      Emax = ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊ := ⟨_, rfl⟩
  obtain ⟨Xe, hXe⟩ : ∃ Xe : ℝ, Xe = Real.exp (Csupp * Real.log x ^ (0.47 : ℝ)) := ⟨_, rfl⟩
  have hXe0 : 0 < Xe := by
    rw [hXe]
    exact Real.exp_pos _
  have hA : ∀ e : ℕ, A e ≠ 0 → e ∈ Finset.Icc 1 Emax := fun e he => by
    rw [hEmax]
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_of_lt (hAmodel.size e he).1, Nat.le_floor (hAmodel.size e he).2⟩
  have hA1 : ∑ e ∈ Finset.Icc 1 Emax, ‖A e‖ ≤ Xe * Real.log x ^ C₈ := by
    have hm := hAmodel.mass
    rw [← hEmax] at hm
    have hpt : ∀ e ∈ Finset.Icc 1 Emax, ‖A e‖ ≤ ‖A e‖ / (e : ℝ) * Xe := by
      intro e he
      have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
      have he2 : e ≤ Emax := (Finset.mem_Icc.mp he).2
      have hepos : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.mpr (by omega)
      have hele : (e : ℝ) ≤ Xe := by
        rw [hEmax] at he2
        rw [hXe]
        exact (Nat.cast_le.mpr he2).trans (Nat.floor_le (Real.exp_pos _).le)
      calc ‖A e‖ = ‖A e‖ / (e : ℝ) * (e : ℝ) := (div_mul_cancel₀ _ hepos.ne').symm
        _ ≤ ‖A e‖ / (e : ℝ) * Xe :=
            mul_le_mul_of_nonneg_left hele (div_nonneg (norm_nonneg _) hepos.le)
    calc ∑ e ∈ Finset.Icc 1 Emax, ‖A e‖
        ≤ ∑ e ∈ Finset.Icc 1 Emax, ‖A e‖ / (e : ℝ) * Xe := Finset.sum_le_sum hpt
      _ = (∑ e ∈ Finset.Icc 1 Emax, ‖A e‖ / (e : ℝ)) * Xe := (Finset.sum_mul _ _ _).symm
      _ ≤ Real.log x ^ C₈ * Xe := mul_le_mul_of_nonneg_right hm hXe0.le
      _ = Xe * Real.log x ^ C₈ := mul_comm _ _
  -- the marked primes and the slot primes
  have hC6 : Real.log x ^ D.C₆ < Real.exp (Real.log x ^ (1 / 10 : ℝ)) := by
    have hp : 0 < Real.log x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
    have h5 := hLLn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0, abs_of_pos hp] at h5
    have hc0 := abs_nonneg D.C₆
    have hc1 : 0 < |D.C₆| + 1 := by linarith
    have h7 : Real.log (Real.log x) ≤ Real.log x ^ (1 / 10 : ℝ) / (|D.C₆| + 1) := by
      rw [← one_div_mul_eq_div]
      exact h5
    have h6 : Real.log (Real.log x) * (|D.C₆| + 1) ≤ Real.log x ^ (1 / 10 : ℝ) :=
      (le_div_iff₀ hc1).mp h7
    have h8 : Real.log (Real.log x) * D.C₆ ≤ Real.log (Real.log x) * |D.C₆| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hLL0
    rw [Real.rpow_def_of_pos hL0]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hge10 : ∀ p ∈ markPrimes D.𝔞 x c.𝔊,
      Real.exp (Real.log x ^ (1 / 10 : ℝ)) ≤ (p : ℝ) := by
    intro p hp
    rcases (mem_markPrimes_iff D.𝔞 x c.𝔊).mp hp with ⟨i, hi⟩ | ⟨g, hg⟩
    · refine le_trans (Real.exp_le_exp.mpr ?_) (mem_bandPrimes.mp hi).2.1
      exact Real.rpow_le_rpow_of_exponent_le hL1 (D.𝔞.gt_tenth i).le
    · rcases g with i | j
      · refine le_trans (Real.exp_le_exp.mpr ?_) (hc.groups.small_range i p hg).1
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      · refine le_trans (Real.exp_le_exp.mpr ?_) (hc.groups.big_range j p hg).1
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hbig : ∀ p ∈ markPrimes D.𝔞 x c.𝔊, Real.log x ^ D.C₆ < (p : ℝ) := fun p hp =>
    lt_of_lt_of_le hC6 (hge10 p hp)
  have hslot : ∀ 𝔩 ∈ slotTuples c.S, ∀ p : ℕ, p.Prime → p ∣ ∏ i, 𝔩 i →
      Real.exp (2 * Real.log x ^ (0.46 : ℝ)) < (p : ℝ) := by
    intro 𝔩 h𝔩 p hp hdvd
    obtain ⟨hmem, -, -⟩ := slotTuple_facts hc.slots h𝔩
    obtain ⟨i, -, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime 𝔩).mp hdvd
    have e : p = 𝔩 i := (Nat.prime_dvd_prime_iff_eq hp (hc.slots.prime i _ (hmem i))).mp hpi
    rw [e]
    exact slot_prime_gt D hL1 h54x hx0 hc i (hmem i)
  have hslotbig : ∀ 𝔩 ∈ slotTuples c.S, ∀ p : ℕ, p.Prime → p ∣ ∏ i, 𝔩 i →
      Real.log x ^ D.C₆ < (p : ℝ) := by
    intro 𝔩 h𝔩 p hp hdvd
    have h1 := hslot 𝔩 h𝔩 p hp hdvd
    have h3 : Real.log x ^ (1 / 10 : ℝ) ≤ Real.log x ^ (0.46 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h2 : Real.exp (Real.log x ^ (1 / 10 : ℝ)) ≤
        Real.exp (2 * Real.log x ^ (0.46 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    linarith
  -- the weight, the marked weight and the sums at one scale
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℕ → ℂ, ∀ w : ℕ, Φ w = c.ψ₁ ((w : ℝ) / c.Y) *
      (w : ℂ) ^ (((τ + c.σ : ℝ) : ℂ) * Complex.I) * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) :=
    ⟨fun w => c.ψ₁ ((w : ℝ) / c.Y) * (w : ℂ) ^ (((τ + c.σ : ℝ) : ℂ) * Complex.I) *
      addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)), fun _ => rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ → ℂ, ∀ n, H n = hMarks D.q D.q₀ D.𝔞 x c.𝔊 c.t c.test ∅ n :=
    ⟨fun n => hMarks D.q D.q₀ D.𝔞 x c.𝔊 c.t c.test ∅ n, fun _ => rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → ℂ, ∀ m, T m = scaleSum Φ H D.a₁ D.a₂ c.Y m :=
    ⟨fun m => scaleSum Φ H D.a₁ D.a₂ c.Y m, fun _ => rfl⟩
  have hΦsupp : ∀ w : ℕ, Φ w ≠ 0 → D.a₁ * c.Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ D.a₂ * c.Y := by
    intro w hw
    have hψ : c.ψ₁ ((w : ℝ) / c.Y) ≠ 0 := by
      intro h0
      rw [hΦdef w, h0, zero_mul, zero_mul] at hw
      exact hw rfl
    have hmem : (w : ℝ) / c.Y ∈ Set.Icc D.a₁ D.a₂ := hc.cutoff_support hψ
    exact ⟨(le_div_iff₀ hY).mp hmem.1, (div_le_iff₀ hY).mp hmem.2⟩
  have hΦnorm : ∀ w : ℕ, 0 < w → ‖Φ w‖ ≤ Real.log x ^ D.Dψ 0 := by
    intro w hw
    rw [hΦdef w, norm_mul, norm_mul, norm_natCast_cpow_mul_I hw, norm_addChar, mul_one,
      mul_one]
    exact hψ0 _
  have hHmul : ∀ 𝔩 ∈ slotTuples c.S, ∀ n : ℕ, H ((∏ i, 𝔩 i) * n) = H n := by
    intro 𝔩 h𝔩 n
    rw [hHdef, hHdef]
    refine hMarks_congr D.q D.q₀ D.𝔞 x c.𝔊 c.t c.test ∅ fun p hp => ?_
    have hpp : p.Prime := prime_of_mem_markPrimes D.𝔞 hc.groups hp
    constructor
    · intro hdvd
      rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h1 | h1
      · have h2 := hslot 𝔩 h𝔩 p hpp h1
        have h3 := le_exp_of_mem_markPrimes D.𝔞 hc.groups hL1 h26 hp
        have h4 : Real.exp (Real.log x ^ (0.46 : ℝ)) ≤
            Real.exp (2 * Real.log x ^ (0.46 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
        linarith
      · exact h1
    · intro hdvd
      exact Dvd.dvd.mul_left hdvd _
  -- the polynomial is `Y⁻¹ (∑_𝔩 T(l) - C_x T(1))`
  have hsE : ∀ w, c.endpoint D x w ≠ 0 → w ∈ natIcc (D.a₁ * c.Y) (D.a₂ * c.Y) := by
    intro w hw
    have hψ : c.ψ₁ ((w : ℝ) / c.Y) ≠ 0 := fun h' => hw (c.endpoint_eq_zero D x h')
    have hmem : (w : ℝ) / c.Y ∈ Set.Icc D.a₁ D.a₂ := hc.cutoff_support hψ
    exact (mem_natIcc_of_pos hWpos).mpr ⟨(le_div_iff₀ hY).mp hmem.1, (div_le_iff₀ hY).mp hmem.2⟩
  have hsummand : ∀ w ∈ natIcc (D.a₁ * c.Y) (D.a₂ * c.Y),
      c.endpoint D x w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
          (w : ℂ) ^ ((τ : ℂ) * Complex.I) =
        (slotCount c.S w : ℂ) * (Φ w * H w) - ((slotMass c.S : ℝ) : ℂ) * (Φ w * H w) := by
    intro w hw
    have hw0 : w ≠ 0 := ne_zero_of_mem_natIcc hWpos hw
    have hpow : (w : ℂ) ^ (((τ + c.σ : ℝ) : ℂ) * Complex.I) =
        (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) := by
      rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hw0)]
      congr 1
      push_cast
      ring
    rw [c.endpoint_eq_hMarks D x w, hΦdef w, hHdef w, hpow]
    push_cast
    ring
  have hT1eq : T 1 = ∑ w ∈ natIcc (D.a₁ * c.Y) (D.a₂ * c.Y), Φ w * H w := by
    rw [hTdef 1]
    unfold scaleSum
    rw [Nat.cast_one, div_one, div_one]
    exact Finset.sum_congr rfl fun n _ => by rw [one_mul]
  have htuple : ∑ w ∈ natIcc (D.a₁ * c.Y) (D.a₂ * c.Y), (slotCount c.S w : ℂ) * (Φ w * H w) =
      ∑ 𝔩 ∈ slotTuples c.S, T (∏ i, 𝔩 i) := by
    have h1 := sum_card_filter_dvd_mul (slotTuples c.S)
      (fun 𝔩 : Fin (d + 1) → ℕ => ∏ i, 𝔩 i)
      (fun 𝔩 h𝔩 => (slotTuple_facts hc.slots h𝔩).2.1) hWpos (R₂ := D.a₂ * c.Y)
      (fun w => Φ w * H w)
    calc ∑ w ∈ natIcc (D.a₁ * c.Y) (D.a₂ * c.Y), (slotCount c.S w : ℂ) * (Φ w * H w)
        = ∑ 𝔩 ∈ slotTuples c.S,
            ∑ n ∈ natIcc (D.a₁ * c.Y / ((∏ i, 𝔩 i : ℕ) : ℝ))
              (D.a₂ * c.Y / ((∏ i, 𝔩 i : ℕ) : ℝ)),
              Φ ((∏ i, 𝔩 i) * n) * H ((∏ i, 𝔩 i) * n) := h1
      _ = ∑ 𝔩 ∈ slotTuples c.S, T (∏ i, 𝔩 i) := Finset.sum_congr rfl fun 𝔩 h𝔩 => by
          rw [hTdef]
          unfold scaleSum
          exact Finset.sum_congr rfl fun n _ => by rw [hHmul 𝔩 h𝔩 n]
  have hpoly : endpointPolynomial (c.endpoint D x) c.Y h k τ = (c.Y : ℂ)⁻¹ *
      (∑ 𝔩 ∈ slotTuples c.S, T (∏ i, 𝔩 i) - ((slotMass c.S : ℝ) : ℂ) * T 1) := by
    rw [endpointPolynomial_eq_sum hsE c.Y h k τ, Finset.sum_congr rfl hsummand,
      Finset.sum_sub_distrib, ← Finset.mul_sum, htuple, hT1eq]
  -- the parameters of the error terms
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ, G =
      ((k : ℂ)⁻¹ * ∑ a ∈ Finset.range k, addChar ((h : ℝ) * (a : ℝ) / (k : ℝ))) *
        ∫ z in D.a₁..D.a₂, c.ψ₁ z *
          ((c.Y * z : ℝ) : ℂ) ^ (((τ + c.σ : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Real.log x ^ (N + |D.Dψ 0|) := ⟨_, rfl⟩
  obtain ⟨BE, hBE⟩ : ∃ BE : ℝ, BE = |ME| * Real.log x ^ (-(2 * (N + |D.Dψ 0|))) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.log x ^ (-(N + |D.Dψ 0|)) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by
    rw [hlam]
    exact Real.rpow_pos_of_pos hL0 _
  have hBE0 : 0 ≤ BE := by
    rw [hBE]
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hL0.le _)
  have hPb0 : 0 ≤ Real.log x ^ D.Dψ 0 := Real.rpow_nonneg hL0.le _
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ,
      ρ₀ = (∑ e ∈ Finset.Icc 1 Emax, ‖A e‖) * (|ML| * Real.log x ^ CL) := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = Real.log x ^ D.Dψ 0 *
      (lam * (2 ^ (⌈D.a₂ / D.a₁⌉₊ + 1) * (BE * (D.a₁ * c.Y))) + D.a₂ * c.Y * lam⁻¹) / 2 :=
    ⟨_, rfl⟩
  have hρ₀0 : 0 ≤ ρ₀ := by
    rw [hρ₀]
    exact mul_nonneg (Finset.sum_nonneg fun e _ => norm_nonneg _)
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hL0.le _))
  have hdyE : ∀ R' : ℝ, 1 ≤ R' →
      ∑ n ∈ natIcc R' (2 * R'), ‖H n - divisorSum A n‖ ^ 2 ≤ BE * R' := by
    intro R' hR'
    have h1 := hAerr R' hR'
    have h2 : ∑ n ∈ natIcc R' (2 * R'), ‖H n - divisorSum A n‖ ^ 2 =
        ∑ n ∈ natIcc R' (2 * R'),
          ‖hMarks D.q D.q₀ D.𝔞 x c.𝔊 c.t c.test ∅ n - divisorSum A n‖ ^ 2 :=
      Finset.sum_congr rfl fun n _ => by rw [hHdef n]
    have h3 : ME * R' * Real.log x ^ (-(2 * (N + |D.Dψ 0|))) ≤
        |ME| * R' * Real.log x ^ (-(2 * (N + |D.Dψ 0|))) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self ME) (by linarith))
        (Real.rpow_nonneg hL0.le _)
    have e : BE * R' = |ME| * R' * Real.log x ^ (-(2 * (N + |D.Dψ 0|))) := by
      rw [hBE]
      ring
    rw [h2, e]
    exact h1.trans h3
  -- one scale
  have hscale : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ D.a₁ * c.Y →
      (∀ p : ℕ, p.Prime → p ∣ m → Real.log x ^ D.C₆ < (p : ℝ)) →
      ‖T m - (c.Y : ℂ) / (m : ℂ) * (G * ∑ e ∈ Finset.Icc 1 Emax, A e / (e : ℂ))‖ ≤
        ρ₀ + ρ₁ / (m : ℝ) := by
    intro m hm hmY hmp
    rw [hTdef m, hρ₀, hρ₁]
    refine norm_scaleSum_sub_main_le D.a₁_pos hY hΦsupp A hA hm ?_ ?_
    · intro e _ hAe
      have he0 : 0 < e := (hAmodel.size e hAe).1
      have hcop : (m * e).Coprime k := by
        refine Nat.coprime_of_dvd fun p hp hpme hpk => ?_
        have hple : (p : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (Nat.le_of_dvd hk hpk)
        have hgt : Real.log x ^ D.C₆ < (p : ℝ) := by
          rcases (Nat.Prime.dvd_mul hp).mp hpme with h1 | h1
          · exact hmp p hp h1
          · exact hbig p (hAmodel.primes_mem e hAe p hp h1)
        linarith
      have hlm := hLMx x hxL c.Y hY c.ψ₁ hc.cutoff_smooth hc.cutoff_support hψ0 hψ1 c.σ τ
        hc.twist hτ k hk hkL h (m * e) (Nat.mul_pos hm he0) hcop
      have hfin : ∑ᶠ v : ℕ, Φ (m * e * v) =
          ∑ᶠ v : ℕ, c.ψ₁ (((m * e * v : ℕ) : ℝ) / c.Y) *
            ((m * e * v : ℕ) : ℂ) ^ (((τ + c.σ : ℝ) : ℂ) * Complex.I) *
              addChar ((h : ℝ) * ((m * e * v : ℕ) : ℝ) / (k : ℝ)) :=
        finsum_congr fun v => hΦdef (m * e * v)
      rw [hfin, hGdef, ← mul_assoc]
      exact hlm.trans
        (mul_le_mul_of_nonneg_right (le_abs_self ML) (Real.rpow_nonneg hL0.le _))
    · exact norm_sum_mul_le_of_dyadic (E := fun n => H n - divisorSum A n) D.a₁_pos
        D.a₁_le_a₂ hY hm hmY hBE0 hPb0 hlam0 hdyE hΦnorm
  have hT1b : ‖T 1 - (c.Y : ℂ) / ((1 : ℕ) : ℂ) *
      (G * ∑ e ∈ Finset.Icc 1 Emax, A e / (e : ℂ))‖ ≤ ρ₀ + ρ₁ / ((1 : ℕ) : ℝ) :=
    hscale 1 Nat.one_pos h1Y fun p hp h1 => absurd (Nat.dvd_one.mp h1) hp.ne_one
  have hcomb : ‖∑ 𝔩 ∈ slotTuples c.S, T (∏ i, 𝔩 i) - ((slotMass c.S : ℝ) : ℂ) * T 1‖ ≤
      (((slotTuples c.S).card : ℝ) + slotMass c.S) * ρ₀ + 2 * slotMass c.S * ρ₁ :=
    norm_sum_scale_sub_le (Cx := slotMass c.S) (ρ₀ := ρ₀) (ρ₁ := ρ₁) (slotTuples c.S)
      (fun 𝔩 : Fin (d + 1) → ℕ => ∏ i, 𝔩 i) T c.Y
      (G * ∑ e ∈ Finset.Icc 1 Emax, A e / (e : ℂ)) rfl (slotMass_nonneg c.S) hT1b
      fun 𝔩 h𝔩 => hscale (∏ i, 𝔩 i) (slotTuple_facts hc.slots h𝔩).2.1 (hlY 𝔩 h𝔩)
        (hslotbig 𝔩 h𝔩)
  -- the size of the two error terms
  have hCx0 : 0 ≤ slotMass c.S := slotMass_nonneg c.S
  have hLN0 : 0 < Real.log x ^ (-N) := Real.rpow_pos_of_pos hL0 _
  have hsplitN : Real.log x ^ (C₈ + CL + N) =
      Real.log x ^ C₈ * Real.log x ^ CL * Real.log x ^ N := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0]
  have hNinv : Real.log x ^ N * Real.log x ^ (-N) = 1 := by
    rw [← Real.rpow_add hL0, add_neg_cancel, Real.rpow_zero]
  have hu1 : ∀ y : ℝ, y * Xe * Real.log x ^ (C₈ + CL + N) ≤ 1 →
      y * Xe * (Real.log x ^ C₈ * Real.log x ^ CL) ≤ Real.log x ^ (-N) := by
    intro y hy
    rw [hsplitN] at hy
    have h2 := mul_le_mul_of_nonneg_right hy hLN0.le
    have e : y * Xe * (Real.log x ^ C₈ * Real.log x ^ CL * Real.log x ^ N) *
          Real.log x ^ (-N) =
        y * Xe * (Real.log x ^ C₈ * Real.log x ^ CL) *
          (Real.log x ^ N * Real.log x ^ (-N)) := by ring
    rw [e, hNinv, mul_one, one_mul] at h2
    exact h2
  rw [← hXe] at hu hu'
  have hxinv1 : x⁻¹ * x ^ (1 - D.ε) = x ^ (-D.ε) := by
    have e : (1 - D.ε : ℝ) = 1 + -D.ε := by ring
    rw [e, Real.rpow_add hx0, Real.rpow_one, ← mul_assoc, inv_mul_cancel₀ hx0.ne', one_mul]
  have hxinv2 : x⁻¹ = x ^ (-(1 : ℝ)) := (Real.rpow_neg_one x).symm
  have hYinv : c.Y⁻¹ ≤ Real.exp D.c₁ * x⁻¹ := by
    have e : (x * Real.exp (-D.c₁))⁻¹ = Real.exp D.c₁ * x⁻¹ := by
      rw [mul_inv, ← Real.exp_neg, neg_neg]
      exact mul_comm _ _
    rw [← e]
    exact inv_anti₀ hxe0 hYlow
  have hP1 : c.Y⁻¹ * ((((slotTuples c.S).card : ℝ) + slotMass c.S) * ρ₀) ≤
      slotMass c.S * (Real.exp D.c₁ * |ML|) * (2 * Real.log x ^ (-N)) := by
    have hcard := card_slotTuples_le hc.slots
    have hX1 : 0 ≤ x ^ (1 - D.ε) := Real.rpow_nonneg hx0.le _
    have h1 : ((slotTuples c.S).card : ℝ) + slotMass c.S ≤
        slotMass c.S * (x ^ (1 - D.ε) + 1) := by linarith
    have h2 : ρ₀ ≤ Xe * Real.log x ^ C₈ * (|ML| * Real.log x ^ CL) := by
      rw [hρ₀]
      exact mul_le_mul_of_nonneg_right hA1
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hL0.le _))
    have h3 : 0 ≤ x ^ (1 - D.ε) + 1 := by linarith
    have h4 := hu1 (x ^ (-D.ε)) hu
    have h5 := hu1 (x ^ (-(1 : ℝ))) hu'
    calc c.Y⁻¹ * ((((slotTuples c.S).card : ℝ) + slotMass c.S) * ρ₀)
        ≤ Real.exp D.c₁ * x⁻¹ * (slotMass c.S * (x ^ (1 - D.ε) + 1) *
            (Xe * Real.log x ^ C₈ * (|ML| * Real.log x ^ CL))) :=
          mul_le_mul hYinv (mul_le_mul h1 h2 hρ₀0 (mul_nonneg hCx0 h3))
            (mul_nonneg (add_nonneg (Nat.cast_nonneg _) hCx0) hρ₀0)
            (mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hx0.le))
      _ = slotMass c.S * (Real.exp D.c₁ * |ML|) *
            (x⁻¹ * x ^ (1 - D.ε) * Xe * (Real.log x ^ C₈ * Real.log x ^ CL) +
              x⁻¹ * Xe * (Real.log x ^ C₈ * Real.log x ^ CL)) := by ring
      _ = slotMass c.S * (Real.exp D.c₁ * |ML|) *
            (x ^ (-D.ε) * Xe * (Real.log x ^ C₈ * Real.log x ^ CL) +
              x ^ (-(1 : ℝ)) * Xe * (Real.log x ^ C₈ * Real.log x ^ CL)) := by
          rw [hxinv1, hxinv2]
      _ ≤ slotMass c.S * (Real.exp D.c₁ * |ML|) * (2 * Real.log x ^ (-N)) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg hCx0 (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)))
  have hlamBE : lam * BE = |ME| * q := by
    have e : Real.log x ^ (N + |D.Dψ 0|) * (|ME| * Real.log x ^ (-(2 * (N + |D.Dψ 0|)))) =
        |ME| * (Real.log x ^ (N + |D.Dψ 0|) * Real.log x ^ (-(2 * (N + |D.Dψ 0|)))) := by
      ring
    have e2 : N + |D.Dψ 0| + -(2 * (N + |D.Dψ 0|)) = -(N + |D.Dψ 0|) := by ring
    rw [hlam, hBE, hq, e, ← Real.rpow_add hL0, e2]
  have hlaminv : lam⁻¹ = q := by
    rw [hlam, hq]
    exact (Real.rpow_neg hL0.le _).symm
  have hρ₁eq : ρ₁ = c.Y * (Real.log x ^ D.Dψ 0 * q * CE) := by
    have e1 : lam * (2 ^ (⌈D.a₂ / D.a₁⌉₊ + 1) * (BE * (D.a₁ * c.Y))) =
        2 ^ (⌈D.a₂ / D.a₁⌉₊ + 1) * (lam * BE) * (D.a₁ * c.Y) := by ring
    rw [hρ₁, e1, hlamBE, hlaminv, hCE]
    ring
  have hPbq : Real.log x ^ D.Dψ 0 * q ≤ Real.log x ^ (-N) := by
    rw [hq, ← Real.rpow_add hL0]
    refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
    have h1 := le_abs_self (D.Dψ 0)
    linarith
  have hP2 : c.Y⁻¹ * (2 * slotMass c.S * ρ₁) ≤
      slotMass c.S * (2 * CE * Real.log x ^ (-N)) := by
    have e : c.Y⁻¹ * (2 * slotMass c.S * (c.Y * (Real.log x ^ D.Dψ 0 * q * CE))) =
        slotMass c.S * (2 * CE * (Real.log x ^ D.Dψ 0 * q)) * (c.Y⁻¹ * c.Y) := by ring
    rw [hρ₁eq, e, inv_mul_cancel₀ hY.ne', mul_one]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hPbq (mul_nonneg zero_le_two hCE0)) hCx0
  -- the conclusion
  have hCxB : slotMass c.S ≤ |Bs| := (hBs x hxs c.S hc.slots).trans (le_abs_self Bs)
  have hfac0 : 0 ≤ (2 * Real.exp D.c₁ * |ML| + 2 * CE) * Real.log x ^ (-N) :=
    mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Real.exp_pos _).le)
      (abs_nonneg _)) (mul_nonneg zero_le_two hCE0)) hLN0.le
  rw [hpoly, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hY.le]
  calc c.Y⁻¹ * ‖∑ 𝔩 ∈ slotTuples c.S, T (∏ i, 𝔩 i) - ((slotMass c.S : ℝ) : ℂ) * T 1‖
      ≤ c.Y⁻¹ * ((((slotTuples c.S).card : ℝ) + slotMass c.S) * ρ₀ +
          2 * slotMass c.S * ρ₁) := mul_le_mul_of_nonneg_left hcomb (inv_nonneg.mpr hY.le)
    _ = c.Y⁻¹ * ((((slotTuples c.S).card : ℝ) + slotMass c.S) * ρ₀) +
          c.Y⁻¹ * (2 * slotMass c.S * ρ₁) := mul_add _ _ _
    _ ≤ slotMass c.S * (Real.exp D.c₁ * |ML|) * (2 * Real.log x ^ (-N)) +
          slotMass c.S * (2 * CE * Real.log x ^ (-N)) := add_le_add hP1 hP2
    _ = slotMass c.S * ((2 * Real.exp D.c₁ * |ML| + 2 * CE) * Real.log x ^ (-N)) := by ring
    _ ≤ |Bs| * ((2 * Real.exp D.c₁ * |ML| + 2 * CE) * Real.log x ^ (-N)) :=
        mul_le_mul_of_nonneg_right hCxB hfac0
    _ = |Bs| * (2 * Real.exp D.c₁ * |ML| + 2 * CE) * Real.log x ^ (-N) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
