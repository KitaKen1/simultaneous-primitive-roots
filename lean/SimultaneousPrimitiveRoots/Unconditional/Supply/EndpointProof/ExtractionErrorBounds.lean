module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.CoefficientBoundProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ModelInterchange
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.PartialWeight
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SquareExceptionsProof
public import SimultaneousPrimitiveRoots.Unconditional.Classical.DivisorMoments

/-!
# The coefficient error of the extraction: the pieces

The pieces of `ExtractionErrorBound` (`[P-06:0692–0703]`); the statement is assembled in
`EndpointProof/ExtractionErrorProof.lean`.

* `card_filter_sq_dvd_le`: "The square exceptions have relative count at most
  `L^{O(1)} exp(-L^{.27})`": the integers `1 ≤ w ≤ N` divisible by the square of an element `≥ W`
  of a set number at most `(N/W)(1 + log N)`.
* `card_filter_dvd_le`, `norm_primeConv_le`: at most `4L` primes of a set divide an integer
  `1 ≤ u ≤ x²`, so a convolution with the indicator of a set of primes costs a factor `4L`.
* `slot_prime_gt`, `errEndpoint_eq_zero_of_not_sq`: for large `x` the slots lie above all marked
  primes and the bands below the active groups, so `ExtractedCoefficientIdentity` applies to an
  admissible configuration: `𝒰_err(w) = 0` unless the square of a prime of `𝒫_{g_s}` or of a slot
  divides `w`.
* `norm_endpoint_le`, `norm_extracted_le`, `norm_errEndpoint_le`: "Both sides are bounded by fixed
  log powers": `|𝒰_err(w)| ≤ K L^E` on `1 ≤ w ≤ x²`.
* `a₂_mul_scale_le_sq`: `a₂ Y ≤ x²` for large `x`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### Counting -/

/-- **The square exceptions**: a set of integers `1 ≤ w ≤ N`, each divisible by the square of an
element `≥ W > 0` of `T`, has at most `(N/W)(1 + log N)` elements. -/
theorem card_filter_sq_dvd_le {T : Finset ℕ} {W : ℝ} (hW : 0 < W) (hT : ∀ p ∈ T, W ≤ (p : ℝ))
    (N : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ Finset.Icc 1 N ∧ ∃ p ∈ T, p ^ 2 ∣ w) :
    (F.card : ℝ) ≤ (N : ℝ) / W * (1 + Real.log N) := by
  have hinj : Set.InjOn (fun w : ℕ => w - 1) (F : Set ℕ) := by
    intro u hu v hv huv
    have h1 := (Finset.mem_Icc.mp (hF u (Finset.mem_coe.mp hu)).1).1
    have h2 := (Finset.mem_Icc.mp (hF v (Finset.mem_coe.mp hv)).1).1
    have huv' : u - 1 = v - 1 := huv
    omega
  have hcard : (F.image fun w : ℕ => w - 1).card = F.card := Finset.card_image_of_injOn hinj
  have hU : ∀ u ∈ F.image (fun w : ℕ => w - 1), u < N ∧ ∃ p ∈ T, p ^ 2 ∣ u + 1 := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hw1, p, hp, hdvd⟩ := hF w hw
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hw1
    have e : w - 1 + 1 = w := by omega
    have hlt : w - 1 < N := by omega
    show w - 1 < N ∧ ∃ p ∈ T, p ^ 2 ∣ w - 1 + 1
    refine ⟨hlt, p, hp, ?_⟩
    rw [e]
    exact hdvd
  have h := Extraction.card_square_multiples_le hW hT N (F.image fun w : ℕ => w - 1) hU
  rw [hcard] at h
  have hharm : ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) ≤ 1 + Real.log N := by
    have h1 := SimultaneousPrimitiveRoots.Unconditional.Classical.sum_Icc_inv_le_one_add_log N
    refine le_trans (le_of_eq ?_) h1
    exact Finset.sum_congr rfl fun d _ => one_div _
  exact h.trans (mul_le_mul_of_nonneg_left hharm (div_nonneg (Nat.cast_nonneg N) hW.le))

/-- At most `4 log x` primes of a set divide an integer `1 ≤ u ≤ x²`. -/
theorem card_filter_dvd_le {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) {u : ℕ} (hu : 1 ≤ u) {x : ℝ}
    (hx : 1 < x) (hux : (u : ℝ) ≤ x ^ (2 : ℝ)) :
    ((T.filter fun p => p ∣ u).card : ℝ) ≤ 4 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have h1 : (2 : ℝ) ^ (T.filter fun p => p ∣ u).card ≤ (u : ℝ) :=
    Extraction.pow_card_le_of_primes_dvd (by norm_num) hu
      (fun ℓ hℓ => hT ℓ (Finset.mem_filter.mp hℓ).1) (fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2)
      (fun ℓ hℓ => by exact_mod_cast (hT ℓ (Finset.mem_filter.mp hℓ).1).two_le)
  have h2 : Real.log ((2 : ℝ) ^ (T.filter fun p => p ∣ u).card) ≤ Real.log (x ^ (2 : ℝ)) :=
    Real.log_le_log (pow_pos two_pos _) (h1.trans hux)
  rw [Real.log_pow, Real.log_rpow hx0] at h2
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hc0 : (0 : ℝ) ≤ ((T.filter fun p => p ∣ u).card : ℝ) := Nat.cast_nonneg _
  have h3 : ((T.filter fun p => p ∣ u).card : ℝ) * (1 / 2) ≤
      ((T.filter fun p => p ∣ u).card : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 hc0
  linarith

/-- A convolution with the indicator of a set of primes, at `1 ≤ w ≤ x²`: at most `4 log x`
terms. -/
theorem norm_primeConv_le {G : Finset ℕ} (hG : ∀ p ∈ G, p.Prime) (F : ℕ → ℂ) {w : ℕ}
    (hw : 1 ≤ w) {x : ℝ} (hx : 1 < x) (hwx : (w : ℝ) ≤ x ^ (2 : ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ p ∈ G, p ∣ w → ‖F (w / p)‖ ≤ B) : ‖primeConv G F w‖ ≤ 4 * Real.log x * B := by
  unfold primeConv
  calc ‖∑ p ∈ G.filter (fun p => p ∣ w), F (w / p)‖
      ≤ ∑ p ∈ G.filter (fun p => p ∣ w), ‖F (w / p)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ G.filter (fun p => p ∣ w), B :=
        Finset.sum_le_sum fun p hp =>
          hF p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
    _ = ((G.filter fun p => p ∣ w).card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * Real.log x * B := mul_le_mul_of_nonneg_right (card_filter_dvd_le hG hw hx hwx) hB

/-- `w / p ≥ 1` for a divisor `p` of `w ≥ 1`. -/
theorem one_le_div_of_dvd {p w : ℕ} (hw : 1 ≤ w) (hpw : p ∣ w) : 1 ≤ w / p := by
  have hw0 : 0 < w := Nat.lt_of_lt_of_le Nat.zero_lt_one hw
  exact Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hw0 hpw) (Nat.pos_of_dvd_of_pos hpw hw0))

/-! ### The disjointness hypotheses for large `x` -/

/-- For large `x` the slot primes exceed `exp(2 L^{.46})`, hence all marked primes. -/
theorem slot_prime_gt {d : ℕ} (D : EndpointData) {x : ℝ} (hL1 : 1 ≤ Real.log x)
    (h54 : 2 / D.ε < Real.log x ^ (0.54 : ℝ)) (hx0 : 0 < x) {c : EndpointConfig d}
    (hc : c.Admissible D x) (i : Fin d) {l : ℕ} (hl : l ∈ c.S i) :
    Real.exp (2 * Real.log x ^ (0.46 : ℝ)) < (l : ℝ) := by
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have h46 : 0 < Real.log x ^ (0.46 : ℝ) := Real.rpow_pos_of_pos hL0 _
  refine lt_of_lt_of_le ?_ (hc.slots.lower i l hl)
  rw [Real.rpow_def_of_pos hx0]
  refine Real.exp_lt_exp.mpr ?_
  have e : Real.log x = Real.log x ^ (0.46 : ℝ) * Real.log x ^ (0.54 : ℝ) := by
    rw [← Real.rpow_add hL0]
    have e1 : (0.46 : ℝ) + 0.54 = 1 := by norm_num
    rw [e1, Real.rpow_one]
  have h1 : 2 < Real.log x ^ (0.54 : ℝ) * D.ε := (div_lt_iff₀ D.ε_pos).mp h54
  have h2 : Real.log x ^ (0.46 : ℝ) * 2 <
      Real.log x ^ (0.46 : ℝ) * (Real.log x ^ (0.54 : ℝ) * D.ε) := mul_lt_mul_of_pos_left h1 h46
  calc 2 * Real.log x ^ (0.46 : ℝ) = Real.log x ^ (0.46 : ℝ) * 2 := by ring
    _ < Real.log x ^ (0.46 : ℝ) * (Real.log x ^ (0.54 : ℝ) * D.ε) := h2
    _ = Real.log x ^ (0.46 : ℝ) * Real.log x ^ (0.54 : ℝ) * D.ε := by ring
    _ = Real.log x * D.ε := by rw [← e]

/-- **The coefficient error vanishes away from the squares**, for an admissible configuration
and large `x`: the slots are disjoint from the marked primes (`x^ε > exp(2 L^{.46})`) and the
bands from the active groups (`exp(2 L^{.2}) < exp(L^{.27})`), so
`ExtractedCoefficientIdentity` applies. -/
theorem errEndpoint_eq_zero_of_not_sq {d : ℕ} (hEI : ExtractedCoefficientIdentity d)
    (D : EndpointData) {x : ℝ} (hL1 : 1 ≤ Real.log x) (h07 : 2 < Real.log x ^ (0.07 : ℝ))
    (h54 : 2 / D.ε < Real.log x ^ (0.54 : ℝ)) (hx0 : 0 < x) {c : EndpointConfig (d + 1)}
    (hc : c.Admissible D x) (i₀ : Fin c.𝔊.numSmall) {w : ℕ} (hw : 0 < w)
    (hsqG : ∀ p ∈ c.smallGroup i₀, ¬ p ^ 2 ∣ w) (hsqS : ∀ i, ∀ l ∈ c.S i, ¬ l ^ 2 ∣ w) :
    c.errEndpoint D x i₀ w = 0 := by
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have h20 : 0 < Real.log x ^ (0.2 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have h46 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlt27 : 2 * Real.log x ^ (0.2 : ℝ) < Real.log x ^ (0.27 : ℝ) := by
    have e : Real.log x ^ (0.27 : ℝ) = Real.log x ^ (0.2 : ℝ) * Real.log x ^ (0.07 : ℝ) := by
      rw [← Real.rpow_add hL0]
      congr 1
      norm_num
    have h := mul_lt_mul_of_pos_left h07 h20
    rw [e]
    linarith
  -- the band primes are at most `exp(2 L^{.2})`
  have hband_le : ∀ j : Fin D.K, ∀ q ∈ bandPrimes (D.𝔞.exponent j) x,
      (q : ℝ) ≤ Real.exp (2 * Real.log x ^ (0.2 : ℝ)) := by
    intro j q hq
    refine (mem_bandPrimes.mp hq).2.2.trans (Real.exp_le_exp.mpr ?_)
    have h2 : Real.log x ^ D.𝔞.exponent j ≤ Real.log x ^ (0.2 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      have e : (0.2 : ℝ) = 1 / 5 := by norm_num
      rw [e]
      exact (D.𝔞.lt_fifth j).le
    linarith
  -- the primes of the active groups lie in `[exp(L^{.27}), exp(L^{.46})]`
  have hgroup_ge : ∀ g : c.𝔊.Index, ∀ p ∈ c.𝔊.group g,
      Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ (p : ℝ) := by
    intro g p hp
    rcases g with i | j
    · exact (hc.groups.small_range i p hp).1
    · refine le_trans (Real.exp_le_exp.mpr ?_) (hc.groups.big_range j p hp).1
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hgroup_le : ∀ g : c.𝔊.Index, ∀ p ∈ c.𝔊.group g,
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) := by
    intro g p hp
    rcases g with i | j
    · refine le_trans (hc.groups.small_range i p hp).2 (Real.exp_le_exp.mpr ?_)
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    · exact (hc.groups.big_range j p hp).2
  refine hEI D x c i₀ hc.groups.prime hc.groups.disjoint hc.slots.prime ?_ ?_ (hc.smallMarks i₀)
    hc.test_big w hw hsqG hsqS
  · -- the slots are disjoint from the marked primes
    intro i
    refine Finset.disjoint_left.mpr fun l hl hmark => ?_
    have hgt := slot_prime_gt D hL1 h54 hx0 hc i hl
    have hmark' : l ∈ (Finset.univ.biUnion fun j : Fin D.K => bandPrimes (D.𝔞.exponent j) x) ∪
        Finset.univ.biUnion c.𝔊.group := hmark
    rcases Finset.mem_union.mp hmark' with h | h
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp h
      have h1 := hband_le j l hj
      have h2 : Real.exp (2 * Real.log x ^ (0.2 : ℝ)) ≤
          Real.exp (2 * Real.log x ^ (0.46 : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have h3 : Real.log x ^ (0.2 : ℝ) ≤ Real.log x ^ (0.46 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        linarith
      linarith
    · obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp h
      have h1 := hgroup_le g l hg
      have h2 : Real.exp (Real.log x ^ (0.46 : ℝ)) ≤ Real.exp (2 * Real.log x ^ (0.46 : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
  · -- the bands are disjoint from the active groups
    intro j
    refine Finset.disjoint_left.mpr fun q hq hall => ?_
    have hall' : q ∈ Finset.univ.biUnion c.𝔊.group := hall
    obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hall'
    have h1 := hband_le j q hq
    have h2 := hgroup_ge g q hg
    have h3 : Real.exp (2 * Real.log x ^ (0.2 : ℝ)) < Real.exp (Real.log x ^ (0.27 : ℝ)) :=
      Real.exp_lt_exp.mpr hlt27
    linarith

/-! ### The size of the three parts -/

/-- `|𝒰(w)| ≤ L^{Dψ 0} · C_W · (bound for |f_x - C_x|) · L^{C₁}`. -/
theorem norm_endpoint_le {d : ℕ} (D : EndpointData) {x : ℝ} {c : EndpointConfig d}
    (hc : c.Admissible D x) {CW SB C₁ : ℝ} (hL0 : 0 < Real.log x)
    (hW : ∀ n, |markedWeight D.q D.𝔞 x n| ≤ CW)
    (hact : ∀ n, ‖c.𝔊.activeWeight D.q₀ c.t c.test n‖ ≤ Real.log x ^ C₁) {w : ℕ} (hw : 0 < w)
    (hslot : |(slotCount c.S w : ℝ) - slotMass c.S| ≤ SB) :
    ‖c.endpoint D x w‖ ≤ Real.log x ^ D.Dψ 0 * (CW * SB * Real.log x ^ C₁) := by
  have hψ : ‖c.ψ₁ ((w : ℝ) / c.Y)‖ ≤ Real.log x ^ D.Dψ 0 := by
    have h := hc.cutoff_deriv 0 ((w : ℝ) / c.Y)
    rw [iteratedDeriv_zero] at h
    exact h
  have hCW0 : 0 ≤ CW := (abs_nonneg _).trans (hW 0)
  have hSB0 : 0 ≤ SB := (abs_nonneg _).trans hslot
  have hP0 : 0 ≤ Real.log x ^ D.Dψ 0 := Real.rpow_nonneg hL0.le _
  have hnorm : ‖c.endpoint D x w‖ = ‖c.ψ₁ ((w : ℝ) / c.Y)‖ *
      (|markedWeight D.q D.𝔞 x w| * |(slotCount c.S w : ℝ) - slotMass c.S|) *
        ‖c.𝔊.activeWeight D.q₀ c.t c.test w‖ := by
    unfold EndpointConfig.endpoint comparisonEndpoint centeredCore
    rw [norm_mul, norm_mul, norm_mul, norm_natCast_cpow_mul_I hw, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
  rw [hnorm]
  calc ‖c.ψ₁ ((w : ℝ) / c.Y)‖ *
        (|markedWeight D.q D.𝔞 x w| * |(slotCount c.S w : ℝ) - slotMass c.S|) *
          ‖c.𝔊.activeWeight D.q₀ c.t c.test w‖
      ≤ Real.log x ^ D.Dψ 0 * (CW * SB) * Real.log x ^ C₁ :=
        mul_le_mul
          (mul_le_mul hψ (mul_le_mul (hW w) hslot (abs_nonneg _) hCW0)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hP0)
          (hact w) (norm_nonneg _) (mul_nonneg hP0 (mul_nonneg hCW0 hSB0))
    _ = Real.log x ^ D.Dψ 0 * (CW * SB * Real.log x ^ C₁) := by ring

/-- The common shape of `𝒰_tuple` and `𝒰_const`:
`|ψ₁(w/Y) w^{iσ} V_{g_s}^{-1} X| ≤ L^{Dψ 0} v₋^{-1} |X|`. -/
theorem norm_extracted_le {d : ℕ} (D : EndpointData) {x : ℝ} {c : EndpointConfig d}
    (hc : c.Admissible D x) (i₀ : Fin c.𝔊.numSmall) (hL0 : 0 < Real.log x) {w : ℕ} (hw : 0 < w)
    (X : ℂ) {B : ℝ} (hX : ‖X‖ ≤ B) :
    ‖c.ψ₁ ((w : ℝ) / c.Y) * (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) *
        (((reciprocalMass (c.smallGroup i₀))⁻¹ : ℝ) : ℂ) * X‖ ≤
      Real.log x ^ D.Dψ 0 * (D.P.vlo⁻¹ * B) := by
  have hψ : ‖c.ψ₁ ((w : ℝ) / c.Y)‖ ≤ Real.log x ^ D.Dψ 0 := by
    have h := hc.cutoff_deriv 0 ((w : ℝ) / c.Y)
    rw [iteratedDeriv_zero] at h
    exact h
  have hV : D.P.vlo ≤ reciprocalMass (c.smallGroup i₀) := hc.groups.mass_ge (Sum.inl i₀)
  have hVpos : 0 < reciprocalMass (c.smallGroup i₀) := lt_of_lt_of_le D.P.vlo_pos hV
  have hVinv : (reciprocalMass (c.smallGroup i₀))⁻¹ ≤ D.P.vlo⁻¹ := inv_anti₀ D.P.vlo_pos hV
  have hVinv0 : 0 ≤ (reciprocalMass (c.smallGroup i₀))⁻¹ := inv_nonneg.mpr hVpos.le
  have hP0 : 0 ≤ Real.log x ^ D.Dψ 0 := Real.rpow_nonneg hL0.le _
  rw [norm_mul, norm_mul, norm_mul, norm_natCast_cpow_mul_I hw, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hVinv0]
  calc ‖c.ψ₁ ((w : ℝ) / c.Y)‖ * (reciprocalMass (c.smallGroup i₀))⁻¹ * ‖X‖
      ≤ Real.log x ^ D.Dψ 0 * D.P.vlo⁻¹ * B :=
        mul_le_mul (mul_le_mul hψ hVinv hVinv0 hP0) hX (norm_nonneg _)
          (mul_nonneg hP0 (inv_nonneg.mpr D.P.vlo_pos.le))
    _ = Real.log x ^ D.Dψ 0 * (D.P.vlo⁻¹ * B) := by ring

/-- **The coefficient error is bounded by a fixed log power** on `1 ≤ w ≤ x²`
(`[P-06:0692–0698]`: "Both sides are bounded by fixed log powers", "Slot multiplicities at each
`w ≍ Y` remain bounded"), from the bounds for `𝒲`, `C_x`, `W_𝐭^𝐛` and the extracted
coefficients. -/
theorem norm_errEndpoint_le {d : ℕ} (D : EndpointData) {x : ℝ} {c : EndpointConfig (d + 1)}
    (hc : c.Admissible D x) (i₀ : Fin c.𝔊.numSmall) {CW Bs C₁ C : ℝ} (hx1 : 1 < x)
    (hL1 : 1 ≤ Real.log x) (hW : ∀ n, |markedWeight D.q D.𝔞 x n| ≤ CW)
    (hBs : slotMass c.S ≤ Bs)
    (hact : ∀ n, ‖c.𝔊.activeWeight D.q₀ c.t c.test n‖ ≤ Real.log x ^ C₁)
    (hcoef : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ (2 : ℝ) →
      ‖c.constCoeff D x i₀ u‖ ≤ Real.log x ^ C ∧ ‖c.tupleCoeff D x i₀ u‖ ≤ Real.log x ^ C)
    {w : ℕ} (hw : 1 ≤ w) (hwx : (w : ℝ) ≤ x ^ (2 : ℝ)) :
    ‖c.errEndpoint D x i₀ w‖ ≤
      (CW * ((2 / D.ε) ^ (d + 1) + Bs) + 16 * D.P.vlo⁻¹ + 4 * Bs * D.P.vlo⁻¹) *
        Real.log x ^ (D.Dψ 0 + max C₁ C + 2) := by
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hw0 : 0 < w := Nat.lt_of_lt_of_le Nat.zero_lt_one hw
  have hCx0 : 0 ≤ slotMass c.S := slotMass_nonneg c.S
  have hBs0 : 0 ≤ Bs := hCx0.trans hBs
  have hCW0 : 0 ≤ CW := (abs_nonneg _).trans (hW 0)
  have hv0 : 0 ≤ D.P.vlo⁻¹ := inv_nonneg.mpr D.P.vlo_pos.le
  have hPC0 : 0 ≤ Real.log x ^ C := Real.rpow_nonneg hL0.le _
  have hSd0 : 0 ≤ (2 / D.ε) ^ (d + 1) := pow_nonneg (div_pos two_pos D.ε_pos).le _
  -- the slot statistic
  have hwxx : (w : ℝ) ≤ x * x := by
    have h := hwx
    rw [Real.rpow_two, pow_two] at h
    exact h
  have hrep : (slotCountRep c.S w : ℝ) ≤ (2 / D.ε) ^ (d + 1) :=
    slotCountRep_le D.ε_pos hx1 hc.slots.prime hc.slots.lower hw hwxx
  have hcount : (slotCount c.S w : ℝ) ≤ (2 / D.ε) ^ (d + 1) := by
    have hle : slotCount c.S w ≤ slotCountRep c.S w := by
      unfold slotCount slotCountRep slotTuples
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
    exact (Nat.cast_le.mpr hle).trans hrep
  have hslot : |(slotCount c.S w : ℝ) - slotMass c.S| ≤ (2 / D.ε) ^ (d + 1) + Bs := by
    have h0 : (0 : ℝ) ≤ (slotCount c.S w : ℝ) := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  -- the three parts
  have e1 := norm_endpoint_le D hc hL0 hW hact hw0 hslot
  have hconv_const : ‖primeConv (c.smallGroup i₀) (c.constCoeff D x i₀) w‖ ≤
      4 * Real.log x * Real.log x ^ C :=
    norm_primeConv_le (fun p hp => hc.groups.prime (Sum.inl i₀) p hp) _ hw hx1 hwx hPC0
      (fun p _ hpw => (hcoef (w / p) (one_le_div_of_dvd hw hpw)
        ((Nat.cast_le.mpr (Nat.div_le_self w p)).trans hwx)).1)
  have hconv_tuple : ‖primeConv (c.smallGroup i₀)
        (primeConv (c.S 0) (c.tupleCoeff D x i₀)) w‖ ≤
      4 * Real.log x * (4 * Real.log x * Real.log x ^ C) :=
    norm_primeConv_le (fun p hp => hc.groups.prime (Sum.inl i₀) p hp) _ hw hx1 hwx
      (mul_nonneg (mul_nonneg (by norm_num) hL0.le) hPC0)
      (fun p _ hpw => by
        have h1 : 1 ≤ w / p := one_le_div_of_dvd hw hpw
        have h2 : ((w / p : ℕ) : ℝ) ≤ x ^ (2 : ℝ) :=
          (Nat.cast_le.mpr (Nat.div_le_self w p)).trans hwx
        exact norm_primeConv_le (hc.slots.prime 0) _ h1 hx1 h2 hPC0
          (fun l _ hl => (hcoef (w / p / l) (one_le_div_of_dvd h1 hl)
            ((Nat.cast_le.mpr (Nat.div_le_self (w / p) l)).trans h2)).2))
  have e2 : ‖c.tupleEndpoint D x i₀ w‖ ≤ Real.log x ^ D.Dψ 0 *
      (D.P.vlo⁻¹ * (4 * Real.log x * (4 * Real.log x * Real.log x ^ C))) :=
    norm_extracted_le D hc i₀ hL0 hw0 _ hconv_tuple
  have e3 : ‖c.constEndpoint D x i₀ w‖ ≤ Real.log x ^ D.Dψ 0 *
      (D.P.vlo⁻¹ * (4 * Real.log x * Real.log x ^ C)) :=
    norm_extracted_le D hc i₀ hL0 hw0 _ hconv_const
  have hnorm : ‖c.errEndpoint D x i₀ w‖ ≤ ‖c.endpoint D x w‖ + ‖c.tupleEndpoint D x i₀ w‖ +
      slotMass c.S * ‖c.constEndpoint D x i₀ w‖ := by
    unfold EndpointConfig.errEndpoint
    calc ‖c.endpoint D x w - c.tupleEndpoint D x i₀ w +
          ((slotMass c.S : ℝ) : ℂ) * c.constEndpoint D x i₀ w‖
        ≤ ‖c.endpoint D x w - c.tupleEndpoint D x i₀ w‖ +
            ‖((slotMass c.S : ℝ) : ℂ) * c.constEndpoint D x i₀ w‖ := norm_add_le _ _
      _ ≤ ‖c.endpoint D x w‖ + ‖c.tupleEndpoint D x i₀ w‖ +
            slotMass c.S * ‖c.constEndpoint D x i₀ w‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hCx0]
          exact add_le_add (norm_sub_le _ _) le_rfl
  -- the powers of `L`
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.log x ^ (D.Dψ 0 + max C₁ C + 2) := ⟨_, rfl⟩
  have hmono : ∀ u : ℝ, u ≤ D.Dψ 0 + max C₁ C + 2 → Real.log x ^ u ≤ Q := fun u hu => by
    rw [hQ]
    exact Real.rpow_le_rpow_of_exponent_le hL1 hu
  have hmax1 : C₁ ≤ max C₁ C := le_max_left _ _
  have hmax2 : C ≤ max C₁ C := le_max_right _ _
  have q1 : Real.log x ^ D.Dψ 0 * Real.log x ^ C₁ ≤ Q := by
    rw [← Real.rpow_add hL0]
    exact hmono _ (by linarith)
  have q2 : Real.log x ^ D.Dψ 0 * (Real.log x * (Real.log x * Real.log x ^ C)) ≤ Q := by
    have e : Real.log x ^ D.Dψ 0 * (Real.log x * (Real.log x * Real.log x ^ C)) =
        Real.log x ^ (D.Dψ 0 + (1 + (1 + C))) := by
      rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
    rw [e]
    exact hmono _ (by linarith)
  have q3 : Real.log x ^ D.Dψ 0 * (Real.log x * Real.log x ^ C) ≤ Q := by
    have e : Real.log x ^ D.Dψ 0 * (Real.log x * Real.log x ^ C) =
        Real.log x ^ (D.Dψ 0 + (1 + C)) := by
      rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
    rw [e]
    exact hmono _ (by linarith)
  have t1 : Real.log x ^ D.Dψ 0 * (CW * ((2 / D.ε) ^ (d + 1) + Bs) * Real.log x ^ C₁) ≤
      CW * ((2 / D.ε) ^ (d + 1) + Bs) * Q :=
    calc Real.log x ^ D.Dψ 0 * (CW * ((2 / D.ε) ^ (d + 1) + Bs) * Real.log x ^ C₁)
        = CW * ((2 / D.ε) ^ (d + 1) + Bs) * (Real.log x ^ D.Dψ 0 * Real.log x ^ C₁) := by ring
      _ ≤ CW * ((2 / D.ε) ^ (d + 1) + Bs) * Q :=
          mul_le_mul_of_nonneg_left q1 (mul_nonneg hCW0 (add_nonneg hSd0 hBs0))
  have t2 : Real.log x ^ D.Dψ 0 *
        (D.P.vlo⁻¹ * (4 * Real.log x * (4 * Real.log x * Real.log x ^ C))) ≤
      16 * D.P.vlo⁻¹ * Q :=
    calc Real.log x ^ D.Dψ 0 *
          (D.P.vlo⁻¹ * (4 * Real.log x * (4 * Real.log x * Real.log x ^ C)))
        = 16 * D.P.vlo⁻¹ *
            (Real.log x ^ D.Dψ 0 * (Real.log x * (Real.log x * Real.log x ^ C))) := by ring
      _ ≤ 16 * D.P.vlo⁻¹ * Q := mul_le_mul_of_nonneg_left q2 (mul_nonneg (by norm_num) hv0)
  have t3 : slotMass c.S * ‖c.constEndpoint D x i₀ w‖ ≤ 4 * Bs * D.P.vlo⁻¹ * Q :=
    calc slotMass c.S * ‖c.constEndpoint D x i₀ w‖
        ≤ Bs * (Real.log x ^ D.Dψ 0 * (D.P.vlo⁻¹ * (4 * Real.log x * Real.log x ^ C))) :=
          mul_le_mul hBs e3 (norm_nonneg _) hBs0
      _ = 4 * Bs * D.P.vlo⁻¹ * (Real.log x ^ D.Dψ 0 * (Real.log x * Real.log x ^ C)) := by ring
      _ ≤ 4 * Bs * D.P.vlo⁻¹ * Q :=
          mul_le_mul_of_nonneg_left q3 (mul_nonneg (mul_nonneg (by norm_num) hBs0) hv0)
  rw [← hQ]
  calc ‖c.errEndpoint D x i₀ w‖
      ≤ ‖c.endpoint D x w‖ + ‖c.tupleEndpoint D x i₀ w‖ +
          slotMass c.S * ‖c.constEndpoint D x i₀ w‖ := hnorm
    _ ≤ CW * ((2 / D.ε) ^ (d + 1) + Bs) * Q + 16 * D.P.vlo⁻¹ * Q + 4 * Bs * D.P.vlo⁻¹ * Q :=
        add_le_add (add_le_add (e1.trans t1) (e2.trans t2)) t3
    _ = (CW * ((2 / D.ε) ^ (d + 1) + Bs) + 16 * D.P.vlo⁻¹ + 4 * Bs * D.P.vlo⁻¹) * Q := by ring

/-! ### The scale -/

/-- `a₂ Y ≤ x²` for large `x`: `log a₂ + c₂ L^{.46} log L ≤ L/2 + L^{.9} ≤ L`. -/
theorem a₂_mul_scale_le_sq (D : EndpointData) {x Y : ℝ} (hx1 : 1 < x)
    (hLL : Real.log (Real.log x) ≤ Real.log x ^ (0.19 : ℝ))
    (hc₂ : |D.c₂| ≤ Real.log x ^ (0.25 : ℝ)) (h10 : 2 ≤ Real.log x ^ (0.1 : ℝ))
    (ha₂ : 2 * Real.log D.a₂ ≤ Real.log x) (hL1 : 1 ≤ Real.log x)
    (hY : Y ≤ x * Real.exp (D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x))) :
    D.a₂ * Y ≤ x ^ (2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have ha₂pos : 0 < D.a₂ := lt_of_lt_of_le D.a₁_pos D.a₁_le_a₂
  have hLL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have hp46 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
  have hp90 : 0 ≤ Real.log x ^ (0.9 : ℝ) := Real.rpow_nonneg hL0.le _
  have h1 : D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤
      Real.log x ^ (0.9 : ℝ) := by
    have h2 : D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤
        |D.c₂| * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hp46) hLL0
    have h3 : |D.c₂| * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤
        Real.log x ^ (0.25 : ℝ) * Real.log x ^ (0.46 : ℝ) * Real.log x ^ (0.19 : ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc₂ hp46) hLL hLL0
        (mul_nonneg (Real.rpow_nonneg hL0.le _) hp46)
    have h4 : Real.log x ^ (0.25 : ℝ) * Real.log x ^ (0.46 : ℝ) * Real.log x ^ (0.19 : ℝ) =
        Real.log x ^ (0.9 : ℝ) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      congr 1
      norm_num
    linarith
  have h5 : 2 * Real.log x ^ (0.9 : ℝ) ≤ Real.log x := by
    have e : Real.log x ^ (0.9 : ℝ) * Real.log x ^ (0.1 : ℝ) = Real.log x := by
      rw [← Real.rpow_add hL0]
      have e1 : (0.9 : ℝ) + 0.1 = 1 := by norm_num
      rw [e1, Real.rpow_one]
    have h6 : Real.log x ^ (0.9 : ℝ) * 2 ≤ Real.log x ^ (0.9 : ℝ) * Real.log x ^ (0.1 : ℝ) :=
      mul_le_mul_of_nonneg_left h10 hp90
    rw [e] at h6
    linarith
  have h7 : D.a₂ * Real.exp (D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) ≤ x :=
    calc D.a₂ * Real.exp (D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x))
        = Real.exp (Real.log D.a₂ +
            D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) := by
          rw [Real.exp_add, Real.exp_log ha₂pos]
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (by linarith)
      _ = x := Real.exp_log hx0
  calc D.a₂ * Y
      ≤ D.a₂ * (x * Real.exp (D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x))) :=
        mul_le_mul_of_nonneg_left hY ha₂pos.le
    _ = x * (D.a₂ * Real.exp (D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x))) := by
        ring
    _ ≤ x * x := mul_le_mul_of_nonneg_left h7 hx0.le
    _ = x ^ (2 : ℝ) := by rw [Real.rpow_two, pow_two]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
