module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements

/-!
# (cor:endpoint-squares)

`endpointSquaresLink d : EndpointSquaresLink d` (`[P-06:0402–0410]`): "The endpoint sequences have
smooth cutoffs at `Y`, fixed log-power twists, and the form of their respective invariant cores
times `W_𝐭^𝐛`, with `|𝐛| ≤ 1` … Fixed divisor moments give
`∑_w |𝒰(w)|² + ∑_w |𝒱(w)|² ≪ Y L^{C_5}`."

* Both sequences vanish outside `a₁ Y ≤ w ≤ a₂ Y` (`cutoff_range`), so the two sums are finite sums
  over `1 ≤ w ≤ ⌊a₂ Y⌋` (`finsum_normSq_le_sum`).
* First endpoint: `|w^{iσ}| = 1`, `|F_x(w)| ≤ B` by `CorePowerBounded d` with the power `κ = 3`
  (`w ≤ a₂ Y ≤ a₂ x² ≤ x³`), `|W_𝐭^𝐛(w)| ≤ L^{C_m}` by `MarkedBound`, `|ψ| ≤ L^{D₀}`. The sum is at
  most `a₂ Y B² L^{2D₀ + 2C_m} ≤ Y L^{2D₀ + 2C_m + 1}` once `L ≥ a₂ B²`.
* Second endpoint: `|G(v)| ≤ L^C τ(v_*)^C ≤ L^C τ(v)^k` with `k = ⌈C⌉₊` (`norm_core_le`:
  `v_* ∣ v` and `τ(v_*) ≥ 1`), and the divisor moment of order `2k` on `v ≤ a₂ Y`, with
  `1 ≤ log(2 a₂ Y) ≤ 3L`.

The exponent is `C₅ = max(2D₀ + 2C_m + 1, 2D₀ + 2C + 2C_m + max(A, 0) + 1)` with `A` the exponent
of the divisor moment of order `2⌈C⌉₊`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open Filter
open scoped Topology

/-! ### The free part and the growth of the second endpoint -/

/-- `n_* ≥ 1`. -/
theorem freePart_pos (P : Finset ℕ) (n : ℕ) : 0 < freePart P n := by
  unfold freePart
  exact Finset.prod_pos fun p hp =>
    pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1) _

/-- `n_* ∣ n` for `n ≥ 1`. -/
theorem freePart_dvd (P : Finset ℕ) {n : ℕ} (hn : n ≠ 0) : freePart P n ∣ n := by
  have h : freePart P n ∣ freePart ∅ n := by
    unfold freePart
    exact Finset.prod_dvd_prod_of_subset _ _ _ fun p hp =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, Finset.notMem_empty p⟩
  rwa [freePart_empty hn] at h

/-- `|G(v)| ≤ L^C τ(v)^k` with `k = ⌈C⌉₊`, for `v ≥ 1` and `L ≥ 0`: `τ(v_*) ≥ 1` and
`τ(v_*) ≤ τ(v)`. The exponent `C` may have any sign. -/
theorem norm_core_le {𝔊 : ActiveGroups} {x C : ℝ} {G : ℕ → ℂ} (hG : CoreAdmissible 𝔊 x C G)
    (hL : 0 ≤ Real.log x) {v : ℕ} (hv : 0 < v) :
    ‖G v‖ ≤ Real.log x ^ C * (v.divisors.card : ℝ) ^ ⌈C⌉₊ := by
  have h1 : (1 : ℝ) ≤ ((freePart 𝔊.allPrimes v).divisors.card : ℝ) :=
    Nat.one_le_cast.mpr (Finset.one_le_card.mpr
      ⟨1, Nat.one_mem_divisors.mpr (freePart_pos 𝔊.allPrimes v).ne'⟩)
  have h2 : ((freePart 𝔊.allPrimes v).divisors.card : ℝ) ≤ (v.divisors.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card
      (Nat.divisors_subset_of_dvd hv.ne' (freePart_dvd 𝔊.allPrimes hv.ne')))
  have h3 : ((freePart 𝔊.allPrimes v).divisors.card : ℝ) ^ C ≤
      (v.divisors.card : ℝ) ^ ⌈C⌉₊ :=
    calc ((freePart 𝔊.allPrimes v).divisors.card : ℝ) ^ C
        ≤ ((freePart 𝔊.allPrimes v).divisors.card : ℝ) ^ ((⌈C⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil C)
      _ = ((freePart 𝔊.allPrimes v).divisors.card : ℝ) ^ ⌈C⌉₊ := Real.rpow_natCast _ _
      _ ≤ (v.divisors.card : ℝ) ^ ⌈C⌉₊ := pow_le_pow_left₀ (zero_le_one.trans h1) h2 _
  exact (hG.growth v hv).trans (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hL C))

/-! ### Sequences cut off at the scale `Y` -/

/-- A cutoff supported in `[a₁, a₂] ⊂ (0, ∞)` at the scale `Y > 0` vanishes outside
`1 ≤ w ≤ ⌊a₂ Y⌋`. -/
theorem cutoff_range {ψ : ℝ → ℂ} {a₁ a₂ Y : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y)
    (hψ : Function.support ψ ⊆ Set.Icc a₁ a₂) {w : ℕ} (hw : ψ ((w : ℝ) / Y) ≠ 0) :
    1 ≤ w ∧ w ≤ ⌊a₂ * Y⌋₊ := by
  have h : (w : ℝ) / Y ∈ Set.Icc a₁ a₂ := hψ hw
  have hle : (w : ℝ) ≤ a₂ * Y := (div_le_iff₀ hY).mp h.2
  have hge : a₁ * Y ≤ (w : ℝ) := (le_div_iff₀ hY).mp h.1
  have hpos : (0 : ℝ) < (w : ℝ) := lt_of_lt_of_le (mul_pos ha₁ hY) hge
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hpos
    exact lt_irrefl _ hpos
  exact ⟨Nat.one_le_iff_ne_zero.mpr hw0, Nat.le_floor hle⟩

/-- The sum of the squares of a sequence that vanishes outside `1 ≤ w ≤ N` is a finite sum, and
it is bounded termwise. -/
theorem finsum_normSq_le_sum {f : ℕ → ℂ} {N : ℕ} {T : ℕ → ℝ}
    (hsupp : ∀ w, f w ≠ 0 → 1 ≤ w ∧ w ≤ N)
    (hT : ∀ w, 1 ≤ w → w ≤ N → ‖f w‖ ^ 2 ≤ T w) :
    ∑ᶠ w : ℕ, ‖f w‖ ^ 2 ≤ ∑ w ∈ Finset.Icc 1 N, T w := by
  have hsub : Function.support (fun w : ℕ => ‖f w‖ ^ 2) ⊆
      ((Finset.Icc 1 N : Finset ℕ) : Set ℕ) := by
    intro w hw
    have hw' : ‖f w‖ ^ 2 ≠ 0 := hw
    have hfw : f w ≠ 0 := by
      intro h0
      apply hw'
      rw [h0, norm_zero]
      exact zero_pow two_ne_zero
    exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr (hsupp w hfw))
  rw [finsum_eq_sum_of_support_subset _ hsub]
  exact Finset.sum_le_sum fun w hw =>
    hT w (Finset.mem_Icc.mp hw).1 (Finset.mem_Icc.mp hw).2

/-! ### The statement -/

/-- **(cor:endpoint-squares)** from the marked bound, the boundedness of `F_x` on power ranges and
the divisor moments, for every number of slots. -/
theorem endpointSquaresLink (d : ℕ) : EndpointSquaresLink d := by
  intro hMB hCP D m' a₁ a₂ ha₁ ha₁₂ D₀
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha₁₂
  obtain ⟨Cm, xm, hm⟩ := hMB D.P D.q₀ D.q₀_pos D.q₀_lt_one m'
  obtain ⟨B, hB0, hB⟩ := hCP D.q D.q_pos D.q_lt_one D.ε D.ε_pos 3 (by norm_num) D.K
  obtain ⟨xc, hc⟩ := hB D.𝔞
  obtain ⟨Cd, Ad, hCd, hdiv⟩ := (divisorMoments (⌈D.C⌉₊ * 2)).1
  have h1 : ∀ᶠ x : ℝ in atTop,
      max (max (a₂ * B ^ 2) (Cd * a₂ * (3 : ℝ) ^ max Ad 0)) 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    ((h1.and (eventually_ge_atTop xm)).and
      ((eventually_ge_atTop xc).and (eventually_ge_atTop (max (2 * a₂) (max (2 / a₂) 1)))))
  refine ⟨max (D₀ * 2 + Cm * 2 + 1) (D₀ * 2 + D.C * 2 + Cm * 2 + max Ad 0 + 1), x₀, ?_⟩
  intro x hx I Y hxY hYx t ht test htest ψ hψs hψb
  obtain ⟨⟨hL, hxm⟩, hxc, hxa⟩ := hx₀ x hx
  -- the size conditions
  have hL1 : 1 ≤ Real.log x := (le_max_right _ _).trans hL
  have hLB : a₂ * B ^ 2 ≤ Real.log x := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLD : Cd * a₂ * (3 : ℝ) ^ max Ad 0 ≤ Real.log x :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hxa1 : 2 * a₂ ≤ x := (le_max_left _ _).trans hxa
  have hxa2 : 2 / a₂ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hxa
  have hx1 : 1 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hxa
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hY0 : 0 < Y := lt_of_lt_of_le hx0 hxY
  have hY2 : Y ≤ x ^ 2 := by
    rw [Real.rpow_two] at hYx
    exact hYx
  have haY0 : 0 < a₂ * Y := mul_pos ha₂ hY0
  have haY : 2 ≤ a₂ * Y := by
    have h : 2 ≤ a₂ * x := by
      rw [mul_comm]
      exact (div_le_iff₀ ha₂).mp hxa2
    exact h.trans (mul_le_mul_of_nonneg_left hxY ha₂.le)
  have ha₂x : a₂ ≤ x := by linarith
  -- powers of `L`
  have hrp : ∀ a : ℝ, 0 ≤ Real.log x ^ a := fun a => Real.rpow_nonneg hL0.le a
  have hsq : ∀ a : ℝ, (Real.log x ^ a) ^ 2 = Real.log x ^ (a * 2) := fun a => by
    rw [Real.rpow_mul hL0.le, Real.rpow_two]
  have hE₁ : Real.log x ^ (D₀ * 2 + Cm * 2 + 1) =
      Real.log x * (Real.log x ^ (D₀ * 2) * Real.log x ^ (Cm * 2)) := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
    ring
  have hE₂ : Real.log x ^ (D₀ * 2 + D.C * 2 + Cm * 2 + max Ad 0 + 1) =
      Real.log x * (Real.log x ^ (D₀ * 2) * Real.log x ^ (D.C * 2) * Real.log x ^ (Cm * 2) *
        Real.log x ^ max Ad 0) := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0,
      Real.rpow_one]
    ring
  have hmax₁ : Real.log x ^ (D₀ * 2 + Cm * 2 + 1) ≤
      Real.log x ^ max (D₀ * 2 + Cm * 2 + 1) (D₀ * 2 + D.C * 2 + Cm * 2 + max Ad 0 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
  have hmax₂ : Real.log x ^ (D₀ * 2 + D.C * 2 + Cm * 2 + max Ad 0 + 1) ≤
      Real.log x ^ max (D₀ * 2 + Cm * 2 + 1) (D₀ * 2 + D.C * 2 + Cm * 2 + max Ad 0 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
  -- the two bounded factors and the range of the positions
  have hW : ∀ n : ℕ, ‖I.𝔊.activeWeight D.q₀ t test n‖ ≤ Real.log x ^ Cm :=
    hm x hxm I.𝔊 I.groups t ht test htest
  have hwY : ∀ w : ℕ, w ≤ ⌊a₂ * Y⌋₊ → (w : ℝ) ≤ a₂ * Y := fun w hw =>
    (Nat.cast_le.mpr hw).trans (Nat.floor_le haY0.le)
  have hx3 : a₂ * Y ≤ x ^ (3 : ℝ) := by
    have h3 : x ^ (3 : ℝ) = x ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast x 3
    rw [h3]
    calc a₂ * Y ≤ x * x ^ 2 := mul_le_mul ha₂x hY2 hY0.le hx0.le
      _ = x ^ 3 := by ring
  have hF : ∀ w : ℕ, 1 ≤ w → w ≤ ⌊a₂ * Y⌋₊ → |centeredCore D.q D.𝔞 x I.S w| ≤ B :=
    fun w hw1 hw2 => hc x hxc I.S I.slots w hw1 ((hwY w hw2).trans hx3)
  have hcard : ((Finset.Icc 1 ⌊a₂ * Y⌋₊).card : ℝ) ≤ a₂ * Y := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.floor_le haY0.le
  have hsupp : ∀ w : ℕ, ψ ((w : ℝ) / Y) ≠ 0 → 1 ≤ w ∧ w ≤ ⌊a₂ * Y⌋₊ := fun w hw =>
    cutoff_range ha₁ hY0 hψs hw
  refine ⟨fun σ => ?_, ?_⟩
  · -- the first endpoint
    have hterm : ∀ w : ℕ, 1 ≤ w → w ≤ ⌊a₂ * Y⌋₊ →
        ‖comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S t test ψ σ Y w‖ ^ 2 ≤
          (Real.log x ^ D₀ * B * Real.log x ^ Cm) ^ 2 := by
      intro w hw1 hw2
      have hw0 : 0 < w := Nat.lt_of_lt_of_le Nat.zero_lt_one hw1
      have hre : ((σ : ℂ) * Complex.I).re = 0 := by simp
      have hcpow : ‖(w : ℂ) ^ ((σ : ℂ) * Complex.I)‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hw0, hre, Real.rpow_zero]
      have hFn : ‖((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ)‖ ≤ B := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hF w hw1 hw2
      have hn : ‖comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S t test ψ σ Y w‖ ≤
          Real.log x ^ D₀ * B * Real.log x ^ Cm := by
        unfold comparisonEndpoint
        rw [norm_mul, norm_mul, norm_mul, hcpow, mul_one]
        exact mul_le_mul (mul_le_mul (hψb _) hFn (norm_nonneg _) (hrp D₀)) (hW w)
          (norm_nonneg _) (mul_nonneg (hrp D₀) hB0)
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hsupp1 : ∀ w : ℕ, comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S t test ψ σ Y w ≠ 0 →
        1 ≤ w ∧ w ≤ ⌊a₂ * Y⌋₊ := by
      intro w hw
      refine hsupp w fun h0 => hw ?_
      unfold comparisonEndpoint
      simp only [h0, zero_mul]
    calc ∑ᶠ w : ℕ, ‖comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S t test ψ σ Y w‖ ^ 2
        ≤ ∑ _w ∈ Finset.Icc 1 ⌊a₂ * Y⌋₊, (Real.log x ^ D₀ * B * Real.log x ^ Cm) ^ 2 :=
          finsum_normSq_le_sum hsupp1 hterm
      _ = ((Finset.Icc 1 ⌊a₂ * Y⌋₊).card : ℝ) *
            (Real.log x ^ D₀ * B * Real.log x ^ Cm) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ a₂ * Y * (Real.log x ^ D₀ * B * Real.log x ^ Cm) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = Y * ((a₂ * B ^ 2) * (Real.log x ^ (D₀ * 2) * Real.log x ^ (Cm * 2))) := by
          rw [← hsq D₀, ← hsq Cm]
          ring
      _ ≤ Y * (Real.log x * (Real.log x ^ (D₀ * 2) * Real.log x ^ (Cm * 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hLB (mul_nonneg (hrp _) (hrp _))) hY0.le
      _ = Y * Real.log x ^ (D₀ * 2 + Cm * 2 + 1) := by rw [hE₁]
      _ ≤ Y * Real.log x ^ max (D₀ * 2 + Cm * 2 + 1)
            (D₀ * 2 + D.C * 2 + Cm * 2 + max Ad 0 + 1) :=
          mul_le_mul_of_nonneg_left hmax₁ hY0.le
  · -- the second endpoint
    have hterm : ∀ v : ℕ, 1 ≤ v → v ≤ ⌊a₂ * Y⌋₊ →
        ‖secondEndpoint D.q₀ I.𝔊 t test I.G ψ Y v‖ ^ 2 ≤
          (Real.log x ^ D₀ * Real.log x ^ D.C * Real.log x ^ Cm) ^ 2 *
            (v.divisors.card : ℝ) ^ (⌈D.C⌉₊ * 2) := by
      intro v hv1 hv2
      have hG : ‖I.G v‖ ≤ Real.log x ^ D.C * (v.divisors.card : ℝ) ^ ⌈D.C⌉₊ :=
        norm_core_le I.core hL0.le (Nat.lt_of_lt_of_le Nat.zero_lt_one hv1)
      have hn : ‖secondEndpoint D.q₀ I.𝔊 t test I.G ψ Y v‖ ≤
          Real.log x ^ D₀ * (Real.log x ^ D.C * (v.divisors.card : ℝ) ^ ⌈D.C⌉₊) *
            Real.log x ^ Cm := by
        unfold secondEndpoint
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (hψb _) hG (norm_nonneg _) (hrp D₀)) (hW v)
          (norm_nonneg _)
          (mul_nonneg (hrp D₀) (mul_nonneg (hrp D.C) (pow_nonneg (Nat.cast_nonneg _) _)))
      calc ‖secondEndpoint D.q₀ I.𝔊 t test I.G ψ Y v‖ ^ 2
          ≤ (Real.log x ^ D₀ * (Real.log x ^ D.C * (v.divisors.card : ℝ) ^ ⌈D.C⌉₊) *
              Real.log x ^ Cm) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = (Real.log x ^ D₀ * Real.log x ^ D.C * Real.log x ^ Cm) ^ 2 *
              (v.divisors.card : ℝ) ^ (⌈D.C⌉₊ * 2) := by ring
    have hsupp2 : ∀ v : ℕ, secondEndpoint D.q₀ I.𝔊 t test I.G ψ Y v ≠ 0 →
        1 ≤ v ∧ v ≤ ⌊a₂ * Y⌋₊ := by
      intro v hv
      refine hsupp v fun h0 => hv ?_
      unfold secondEndpoint
      simp only [h0, zero_mul]
    -- the logarithm of the divisor moment
    have hlog1 : 1 ≤ Real.log (2 * (a₂ * Y)) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have h := Real.exp_one_lt_three
      linarith
    have hlog2 : Real.log (2 * (a₂ * Y)) ≤ 3 * Real.log x := by
      have h : 2 * (a₂ * Y) ≤ x ^ 3 :=
        calc 2 * (a₂ * Y) = 2 * a₂ * Y := by ring
          _ ≤ x * x ^ 2 := mul_le_mul hxa1 hY2 hY0.le hx0.le
          _ = x ^ 3 := by ring
      calc Real.log (2 * (a₂ * Y)) ≤ Real.log (x ^ 3) := Real.log_le_log (by linarith) h
        _ = 3 * Real.log x := by
          rw [Real.log_pow]
          norm_num
    have hlogA : Real.log (2 * (a₂ * Y)) ^ Ad ≤
        (3 : ℝ) ^ max Ad 0 * Real.log x ^ max Ad 0 :=
      calc Real.log (2 * (a₂ * Y)) ^ Ad ≤ Real.log (2 * (a₂ * Y)) ^ max Ad 0 :=
            Real.rpow_le_rpow_of_exponent_le hlog1 (le_max_left _ _)
        _ ≤ (3 * Real.log x) ^ max Ad 0 :=
            Real.rpow_le_rpow (zero_le_one.trans hlog1) hlog2 (le_max_right _ _)
        _ = (3 : ℝ) ^ max Ad 0 * Real.log x ^ max Ad 0 :=
            Real.mul_rpow (by norm_num) hL0.le
    calc ∑ᶠ v : ℕ, ‖secondEndpoint D.q₀ I.𝔊 t test I.G ψ Y v‖ ^ 2
        ≤ ∑ v ∈ Finset.Icc 1 ⌊a₂ * Y⌋₊,
            (Real.log x ^ D₀ * Real.log x ^ D.C * Real.log x ^ Cm) ^ 2 *
              (v.divisors.card : ℝ) ^ (⌈D.C⌉₊ * 2) := finsum_normSq_le_sum hsupp2 hterm
      _ = (Real.log x ^ D₀ * Real.log x ^ D.C * Real.log x ^ Cm) ^ 2 *
            ∑ v ∈ Finset.Icc 1 ⌊a₂ * Y⌋₊, (v.divisors.card : ℝ) ^ (⌈D.C⌉₊ * 2) := by
          rw [Finset.mul_sum]
      _ ≤ (Real.log x ^ D₀ * Real.log x ^ D.C * Real.log x ^ Cm) ^ 2 *
            (Cd * (a₂ * Y) * Real.log (2 * (a₂ * Y)) ^ Ad) :=
          mul_le_mul_of_nonneg_left (hdiv (a₂ * Y) (by linarith)) (sq_nonneg _)
      _ ≤ (Real.log x ^ D₀ * Real.log x ^ D.C * Real.log x ^ Cm) ^ 2 *
            (Cd * (a₂ * Y) * ((3 : ℝ) ^ max Ad 0 * Real.log x ^ max Ad 0)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlogA (mul_nonneg hCd.le haY0.le)) (sq_nonneg _)
      _ = Y * ((Cd * a₂ * (3 : ℝ) ^ max Ad 0) *
            (Real.log x ^ (D₀ * 2) * Real.log x ^ (D.C * 2) * Real.log x ^ (Cm * 2) *
              Real.log x ^ max Ad 0)) := by
          rw [← hsq D₀, ← hsq D.C, ← hsq Cm]
          ring
      _ ≤ Y * (Real.log x * (Real.log x ^ (D₀ * 2) * Real.log x ^ (D.C * 2) *
            Real.log x ^ (Cm * 2) * Real.log x ^ max Ad 0)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hLD
              (mul_nonneg (mul_nonneg (mul_nonneg (hrp _) (hrp _)) (hrp _)) (hrp _))) hY0.le
      _ = Y * Real.log x ^ (D₀ * 2 + D.C * 2 + Cm * 2 + max Ad 0 + 1) := by rw [hE₂]
      _ ≤ Y * Real.log x ^ max (D₀ * 2 + Cm * 2 + 1)
            (D₀ * 2 + D.C * 2 + Cm * 2 + max Ad 0 + 1) :=
          mul_le_mul_of_nonneg_left hmax₂ hY0.le

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
