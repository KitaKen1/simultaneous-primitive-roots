module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Statements

/-!
# (ext:core-bound), proved from Mertens' product theorem

`coreGrowth_of_mertensProduct : MertensProduct → CoreGrowth` (`[P-07:0569–0574]`):

`|G_P(v)| ≤ (C / (L V(W)))^j τ_j(v_*) ≤ L^{C_j} τ(v_*)^{C_j}`.

Mertens' product theorem gives `V(W) L^{0.24} ≥ e^{-γ_E}/2` for large `x`
(`eventually_mertensProduct_roughCutoff_ge`), hence `κ(m) = 1/(V(W) log m) ≤ 1` for every
`m > x^γ` (`eventually_proxyKappa_le_one`); so every stripped coefficient is in `[0, 1]`, and
`|G_P(v)|` is at most the number `τ_j(v_*) ≤ τ(v_*)^j` of ordered factorizations. The exponent is
`C = j`.

This discharges the field `coreGrowth` of `ExtractionLeaves`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

/-- `V(y)` as a product over `Finset.Icc 2 ⌊y⌋₊`, the index set of `MertensProduct`. -/
theorem mertensProduct_eq_Icc (y : ℝ) :
    mertensProduct y = ∏ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  unfold mertensProduct
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext p
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, hp⟩
    exact ⟨⟨hp.two_le, by omega⟩, hp⟩
  · rintro ⟨⟨_, h2⟩, hp⟩
    exact ⟨by omega, hp⟩

/-- `V(W) L^{0.24} > e^{-γ_E}/2` for large `x` (`V(W) ≍ L^{-0.24}`, `[P-07:0369]`). -/
theorem eventually_mertensProduct_roughCutoff_ge (hM : MertensProduct) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-Real.eulerMascheroniConstant) / 2 <
        Real.log x ^ (0.24 : ℝ) * mertensProduct (roughCutoff x) := by
  have hM' : Tendsto (fun y : ℝ => Real.log y *
      ∏ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ)))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := hM
  have hpos : (0 : ℝ) < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  have hlt : Real.exp (-Real.eulerMascheroniConstant) / 2 <
      Real.exp (-Real.eulerMascheroniConstant) := by linarith
  have h1 := hM'.eventually (eventually_gt_nhds hlt)
  have hW : Tendsto (fun x : ℝ => Real.exp (Real.log x ^ (0.24 : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.24)).comp Real.tendsto_log_atTop)
  have h2 : ∀ᶠ x : ℝ in atTop, Real.exp (-Real.eulerMascheroniConstant) / 2 <
      Real.log (Real.exp (Real.log x ^ (0.24 : ℝ))) *
        ∏ p ∈ (Finset.Icc 2 ⌊Real.exp (Real.log x ^ (0.24 : ℝ))⌋₊).filter Nat.Prime,
          (1 - 1 / (p : ℝ)) := hW.eventually h1
  filter_upwards [h2] with x hx
  rw [Real.log_exp] at hx
  rw [mertensProduct_eq_Icc]
  exact hx

/-- `κ(m) ≤ 1` for every `m > x^γ`, for large `x` (`[P-07:0361–0362]`: "its size is
`O((L V(W))^{-1})`"). -/
theorem eventually_proxyKappa_le_one (hM : MertensProduct) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ m : ℕ, x ^ γ < (m : ℝ) → proxyKappa x m ≤ 1 := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = Real.exp (-Real.eulerMascheroniConstant) / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]
    exact div_pos (Real.exp_pos _) two_pos
  have hcγ : 0 < c * γ := mul_pos hc hγ
  have hLbig : ∀ᶠ x : ℝ in atTop, 1 / (c * γ) ≤ Real.log x ^ (0.76 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.76)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  filter_upwards [eventually_mertensProduct_roughCutoff_ge hM, hLbig,
    eventually_gt_atTop (1 : ℝ)] with x hV hL76 hx1 m hm
  rw [← hcdef] at hV
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hxγ : 1 ≤ x ^ γ := Real.one_le_rpow hx1.le hγ.le
  have hm1 : (1 : ℝ) < (m : ℝ) := lt_of_le_of_lt hxγ hm
  have hm2 : 2 ≤ m := by
    have h : 1 < m := by exact_mod_cast hm1
    exact h
  have hlogm : γ * Real.log x < Real.log (m : ℝ) := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hx0 γ) hm
    rwa [Real.log_rpow hx0] at h
  have hVpos : 0 < mertensProduct (roughCutoff x) := mertensProduct_pos _
  have h24 : 0 ≤ Real.log x ^ (0.24 : ℝ) := Real.rpow_nonneg hL.le _
  have h76 : 0 ≤ Real.log x ^ (0.76 : ℝ) := Real.rpow_nonneg hL.le _
  have hsplit : Real.log x ^ (0.24 : ℝ) * Real.log x ^ (0.76 : ℝ) = Real.log x := by
    have e : (0.24 : ℝ) + 0.76 = 1 := by norm_num
    rw [← Real.rpow_add hL, e, Real.rpow_one]
  -- `1 ≤ c γ L^{0.76} ≤ (L^{0.24} V) γ L^{0.76} = V γ L ≤ V log m`
  have h1 : 1 ≤ c * γ * Real.log x ^ (0.76 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hL76 hcγ.le
    rwa [mul_one_div_cancel hcγ.ne'] at h
  have h2 : c * γ * Real.log x ^ (0.76 : ℝ) ≤
      Real.log x ^ (0.24 : ℝ) * mertensProduct (roughCutoff x) * γ *
        Real.log x ^ (0.76 : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hV.le hγ.le) h76
  have h3 : Real.log x ^ (0.24 : ℝ) * mertensProduct (roughCutoff x) * γ *
      Real.log x ^ (0.76 : ℝ) = mertensProduct (roughCutoff x) * (γ * Real.log x) :=
    calc Real.log x ^ (0.24 : ℝ) * mertensProduct (roughCutoff x) * γ *
          Real.log x ^ (0.76 : ℝ)
        = mertensProduct (roughCutoff x) *
            (γ * (Real.log x ^ (0.24 : ℝ) * Real.log x ^ (0.76 : ℝ))) := by ring
      _ = mertensProduct (roughCutoff x) * (γ * Real.log x) := by rw [hsplit]
  have h4 : mertensProduct (roughCutoff x) * (γ * Real.log x) ≤
      mertensProduct (roughCutoff x) * Real.log (m : ℝ) :=
    mul_le_mul_of_nonneg_left hlogm.le hVpos.le
  have h5 : 1 ≤ mertensProduct (roughCutoff x) * Real.log (m : ℝ) := by linarith
  unfold proxyKappa
  rw [if_pos hm2]
  exact (div_le_one (by linarith)).mpr h5

/-- **(ext:core-bound)** from Mertens' product theorem, with the exponent `C = j`. -/
theorem coreGrowth_of_mertensProduct (hM : MertensProduct) : CoreGrowth := by
  intro γ hγ j
  refine ⟨(j : ℝ), ?_⟩
  filter_upwards [eventually_proxyKappa_le_one hM hγ, eventually_ge_atTop (Real.exp 1)]
    with x hκ hxe candidates active v _
  have hL1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h
  have hcoef : ∀ m : ℕ, strippedCoeff x γ candidates m ≤ 1 := by
    intro m
    unfold strippedCoeff
    split_ifs with h
    · exact hκ _ h.2
    · exact zero_le_one
  have hprod : ∀ e : Fin j → ℕ, |∏ i, strippedCoeff x γ candidates (e i)| ≤ 1 := by
    intro e
    rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => strippedCoeff_nonneg x γ candidates (e i))]
    exact Finset.prod_le_one (fun i _ => strippedCoeff_nonneg x γ candidates (e i))
      (fun i _ => hcoef (e i))
  have hcard : ((orderedFactorizations j (freePart active v)).card : ℝ) ≤
      ((freePart active v).divisors.card : ℝ) ^ j := by
    have h : (orderedFactorizations j (freePart active v)).card ≤
        (freePart active v).divisors.card ^ j := by
      unfold orderedFactorizations
      refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast h
  have hL : 1 ≤ Real.log x ^ (j : ℝ) := Real.one_le_rpow hL1 (Nat.cast_nonneg j)
  have hτ : 0 ≤ ((freePart active v).divisors.card : ℝ) ^ (j : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [allocationCore_eq_convPow]
  unfold convPow
  calc |∑ e ∈ orderedFactorizations j (freePart active v),
        ∏ i, strippedCoeff x γ candidates (e i)|
      ≤ ∑ e ∈ orderedFactorizations j (freePart active v),
          |∏ i, strippedCoeff x γ candidates (e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ orderedFactorizations j (freePart active v), (1 : ℝ) :=
        Finset.sum_le_sum fun e _ => hprod e
    _ = ((orderedFactorizations j (freePart active v)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((freePart active v).divisors.card : ℝ) ^ j := hcard
    _ = ((freePart active v).divisors.card : ℝ) ^ (j : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ Real.log x ^ (j : ℝ) * ((freePart active v).divisors.card : ℝ) ^ (j : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hL) hτ]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
