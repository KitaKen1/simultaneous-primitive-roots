import ArtinPrimitiveRoots.TypeII.PD.Preliminaries
import SimultaneousPrimitiveRoots.Unconditional.Supply.ClassicalInputs

/-!
# Rough integers in long intervals ([P] Lemma 2.5) from the vendored formalization of [A]

`ArtinPrimitiveRoots.TypeII.PD.rough_counts`
(`vendor/ArtinPrimitiveRoots/TypeII/PD/Preliminaries.lean`) is [P] Lemma 2.5 with the interval
length `hi - lo + 1`, residues in `ZMod d` and the error `H L^{-A}`. The supply-side hypothesis
`Supply.RoughCounts` (`Supply/ClassicalInputs.lean`) uses the length `hi - lo`, natural residues
and an error `M H L^{-A}`. The definitions agree: `roughAbove n W` is `Supply.IsRough W n`,
`roughSieveProduct` is `Supply.mertensProduct`, and both cutoffs are `exp(L^{0.24})`. The two
lengths differ by `1`, which costs `V(W) ≤ 1 ≤ H L^{-A}` once `(log x)^A ≤ x^δ`; so `M = 2`.
-/

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.RoughBridge

open ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

theorem roughCutoff_eq (x : ℝ) : ArtinPrimitiveRoots.TypeII.roughCutoff x = Supply.roughCutoff x := by
  have h : (24 / 100 : ℝ) = 0.24 := by norm_num
  unfold ArtinPrimitiveRoots.TypeII.roughCutoff Supply.roughCutoff
  rw [Real.rpow_eq_pow, h]

theorem roughSieveProduct_eq (y : ℝ) : roughSieveProduct y = Supply.mertensProduct y := rfl

theorem mertensProduct_nonneg (y : ℝ) : 0 ≤ Supply.mertensProduct y := by
  unfold Supply.mertensProduct
  refine Finset.prod_nonneg fun p hp => ?_
  have hp' : p.Prime := (Finset.mem_filter.mp hp).2
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
  have h2 : (1 : ℝ) / p ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact h1
  linarith

theorem mertensProduct_le_one (y : ℝ) : Supply.mertensProduct y ≤ 1 := by
  unfold Supply.mertensProduct
  refine Finset.prod_le_one (fun p hp => ?_) fun p hp => ?_
  · have hp' : p.Prime := (Finset.mem_filter.mp hp).2
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
    have h2 : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact h1
    linarith
  · have h : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith

open _root_.Classical in
/-- The rough integers of `[lo, hi]`, in the two indexings. The decidability instance on the left
is arbitrary, so that the identity rewrites the statement of `Supply.RoughCounts`. -/
theorem filter_isRough_Icc_eq (lo hi W : ℝ) (hhi : 0 ≤ hi)
    {inst : DecidablePred fun n : ℕ => Supply.IsRough W n} :
    @Finset.filter ℕ (fun n => Supply.IsRough W n) inst (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊) =
      roughIntegersInInterval lo hi W := by
  ext n
  rw [roughIntegersInInterval, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_range, Nat.lt_add_one_iff, Nat.ceil_le, Nat.le_floor_iff hhi]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h2, h1, h2, h3⟩, fun ⟨_, h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

open _root_.Classical in
/-- The rough integers of `[lo, hi]` in a residue class, in the two indexings. -/
theorem card_filter_modEq_isRough_Icc_eq (lo hi W : ℝ) (hhi : 0 ≤ hi) (d b : ℕ)
    {inst : DecidablePred fun n : ℕ => n ≡ b [MOD d] ∧ Supply.IsRough W n} :
    ((@Finset.filter ℕ (fun n => n ≡ b [MOD d] ∧ Supply.IsRough W n) inst
        (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊)).card : ℝ) = roughResidueCount lo hi W d (b : ZMod d) := by
  unfold roughResidueCount
  refine congrArg (fun s : Finset ℕ => (s.card : ℝ)) ?_
  ext n
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
    Nat.lt_add_one_iff, Nat.ceil_le, Nat.le_floor_iff hhi, ZMod.natCast_eq_natCast_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h2, h1, h2, h4, h3⟩,
    fun ⟨_, h1, h2, h4, h3⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩

end SimultaneousPrimitiveRoots.Unconditional.Supply.RoughBridge

namespace SimultaneousPrimitiveRoots.Unconditional

open ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD Supply.RoughBridge

open _root_.Classical in
/-- **Rough integers in long intervals** ([P] Lemma 2.5) is a theorem: the supply-side hypothesis
`Supply.RoughCounts` holds. -/
theorem Supply.roughCounts : Supply.RoughCounts := by
  intro δ C a A hδ hC ha ha1 hA
  obtain ⟨C₀, x₀, -, -, hmain⟩ := rough_counts δ C a A hδ hC ha ha1 hA
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop A hδ).bound zero_lt_one)
  refine ⟨2, max x₀ (max x₁ 3), ?_⟩
  intro x hx H hH1 hH2 lo hi hlo hlohi hhi
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hxx₁ : x₁ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx3 : (3 : ℝ) ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hhi0 : 0 ≤ hi :=
    (((Real.rpow_pos_of_pos hxpos δ).le.trans hH1).trans hlo).trans hlohi
  -- the two interval lengths differ by one, which is below the error term
  have hsmall : (1 : ℝ) ≤ H * Real.log x ^ (-A) := by
    have h := hx₁ x hxx₁
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le A),
      Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le δ)] at h
    have hpos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlogpos A
    rw [Real.rpow_neg hlogpos.le, ← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
    exact h.trans hH1
  have hV0 : 0 ≤ Supply.mertensProduct (Supply.roughCutoff x) := mertensProduct_nonneg _
  have hV1 : Supply.mertensProduct (Supply.roughCutoff x) ≤ 1 := mertensProduct_le_one _
  -- the vendored lemma, in the notation of `Supply`
  have hext := hmain x hxx₀ H hH1 hH2 lo hi hlo hlohi hhi
  rw [roughCutoff_eq, roughSieveProduct_eq] at hext
  simp only [Real.rpow_eq_pow] at hext
  obtain ⟨e1, e2, e3⟩ := hext
  refine ⟨?_, ?_, ?_⟩
  · rw [filter_isRough_Icc_eq lo hi _ hhi0]
    have hsplit : ((roughIntegersInInterval lo hi (Supply.roughCutoff x)).card : ℝ) -
          Supply.mertensProduct (Supply.roughCutoff x) * (hi - lo) =
        (((roughIntegersInInterval lo hi (Supply.roughCutoff x)).card : ℝ) -
          Supply.mertensProduct (Supply.roughCutoff x) * (hi - lo + 1)) +
          Supply.mertensProduct (Supply.roughCutoff x) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hV0]
    linarith
  · intro d hd hdle hdrough b
    rw [card_filter_modEq_isRough_Icc_eq lo hi _ hhi0 d b]
    have e := e2 d hd hdle hdrough (b : ZMod d)
    have hD : (0 : ℝ) < d := by exact_mod_cast hd
    have hVd : Supply.mertensProduct (Supply.roughCutoff x) / (d : ℝ) ≤
        H / (d : ℝ) * Real.log x ^ (-A) :=
      calc Supply.mertensProduct (Supply.roughCutoff x) / (d : ℝ)
          = Supply.mertensProduct (Supply.roughCutoff x) * (d : ℝ)⁻¹ := div_eq_mul_inv _ _
        _ ≤ (H * Real.log x ^ (-A)) * (d : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (hV1.trans hsmall) (inv_nonneg.mpr hD.le)
        _ = H / (d : ℝ) * Real.log x ^ (-A) := by ring
    have hsplit : roughResidueCount lo hi (Supply.roughCutoff x) d (b : ZMod d) -
          Supply.mertensProduct (Supply.roughCutoff x) * (hi - lo) / (d : ℝ) =
        (roughResidueCount lo hi (Supply.roughCutoff x) d (b : ZMod d) -
          Supply.mertensProduct (Supply.roughCutoff x) * (hi - lo + 1) / (d : ℝ)) +
          Supply.mertensProduct (Supply.roughCutoff x) / (d : ℝ) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (div_nonneg hV0 hD.le)]
    linarith
  · intro q hq hqle χ
    rw [filter_isRough_Icc_eq lo hi _ hhi0]
    have e := e3 q hq hqle χ
    change ‖(∑ n ∈ roughIntegersInInterval lo hi (Supply.roughCutoff x), χ (n : ZMod q)) - _‖ ≤ _
      at e
    generalize (∑ n ∈ roughIntegersInInterval lo hi (Supply.roughCutoff x), χ (n : ZMod q)) = S
      at e ⊢
    split_ifs at e ⊢ with hχ
    · have hsplit : S - ((Supply.mertensProduct (Supply.roughCutoff x) * (hi - lo) : ℝ) : ℂ) =
          (S - ((Supply.mertensProduct (Supply.roughCutoff x) * (hi - lo + 1) : ℝ) : ℂ)) +
            ((Supply.mertensProduct (Supply.roughCutoff x) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hV0]
      linarith
    · linarith

end SimultaneousPrimitiveRoots.Unconditional
