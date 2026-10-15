module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.MarkedBound

/-!
# (cor:marked-bound) with marks removed

`partialMarkedBound : PartialMarkedBound` (`[P-06:0044–0053]`): `|W_{𝐭'}^𝐛(n)| ≤ L^{C(m')}` for the
active weight with the marks of an arbitrary set `U` of groups removed (`t'_g = t_g` for `g ∉ U`,
`t'_g = 0` for `g ∈ U`), `t_g ≤ m'`, `|𝐛| ≤ 1`.

The proof is that of `TwoSidedProof.markedBound` (the case `U = ∅`):

* the lists are a product over the groups (`partialLists_eq`): the lists of one group
  (`TwoSidedProof.groupLists`) for `g ∉ U`, the dummy list for `g ∈ U` (`partialGroupLists`);
* one group factor is `q_0^{ω_g(n)} ≤ 1` for `g ∈ U`, and it is the factor
  `q_0^{u-t} V_g^{-t} · #lists ≤ markConst v₋ q₀ m'` of (cor:marked-bound) for `g ∉ U`
  (`partialGroupFactor_le`);
* the product over the `≤ 2 C₀ log L` groups is at most `L^{2 C₀ log(markConst)}`.

The exponent `C = 2 C₀ log (markConst v₋ q₀ m')` and the threshold `x₀ = 2` are those of
`TwoSidedProof.markedBound`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### The lists of one group -/

/-- The lists of one group at `n` with the marks of `U` removed: the represented lists of the
group for `g ∉ U`, the dummy list `(0, …, 0)` for `g ∈ U`. -/
def partialGroupLists (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ) (U : Finset 𝔊.Index) (n : ℕ)
    (g : 𝔊.Index) : Finset (Fin (t g) → ℕ) :=
  if g ∈ U then ({fun _ => 0} : Finset (Fin (t g) → ℕ))
  else TwoSidedProof.groupLists (𝔊.group g) (t g) n

/-- The lists with the marks of `U` removed are the product over the groups of the lists of one
group. -/
theorem partialLists_eq (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ) (U : Finset 𝔊.Index) (n : ℕ) :
    partialLists 𝔊 t U n = Fintype.piFinset (partialGroupLists 𝔊 t U n) := rfl

theorem partialGroupLists_of_mem {𝔊 : ActiveGroups} {t : 𝔊.Index → ℕ} {U : Finset 𝔊.Index}
    {g : 𝔊.Index} (hg : g ∈ U) (n : ℕ) :
    partialGroupLists 𝔊 t U n g = {fun _ => 0} := by
  unfold partialGroupLists
  exact if_pos hg

theorem partialGroupLists_of_notMem {𝔊 : ActiveGroups} {t : 𝔊.Index → ℕ} {U : Finset 𝔊.Index}
    {g : 𝔊.Index} (hg : g ∉ U) (n : ℕ) :
    partialGroupLists 𝔊 t U n g = TwoSidedProof.groupLists (𝔊.group g) (t g) n := by
  unfold partialGroupLists
  exact if_neg hg

/-! ### One group factor -/

/-- **One group factor is bounded**: for `g ∈ U` it is `q_0^{ω_g(n)} ≤ 1`; for `g ∉ U`, `t_g ≤ m'`
and `t_g ≤ ω_g(n)` it is the factor of (cor:marked-bound)
(`TwoSidedProof.groupLists_factor_le`). -/
theorem partialGroupFactor_le {P : ActiveGroupConstants} {x : ℝ} {𝔊 : ActiveGroups}
    (h : 𝔊.Admissible P x) {q₀ : ℝ} (hq0 : 0 < q₀) (hq1 : q₀ < 1) {m' : ℕ} {t : 𝔊.Index → ℕ}
    (ht : ∀ g, t g ≤ m') (U : Finset 𝔊.Index) (n : ℕ) (g : 𝔊.Index)
    (hth : (if g ∈ U then 0 else t g) ≤ primeHits (𝔊.group g) n) :
    q₀ ^ (primeHits (𝔊.group g) n - (if g ∈ U then 0 else t g)) *
        (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) *
        ((partialGroupLists 𝔊 t U n g).card : ℝ) ≤ TwoSidedProof.markConst P.vlo q₀ m' := by
  by_cases hg : g ∈ U
  · rw [partialGroupLists_of_mem hg, if_pos hg, if_pos hg, Finset.card_singleton,
      Nat.cast_one, mul_one, mul_one]
    exact (pow_le_one₀ hq0.le hq1.le).trans (TwoSidedProof.one_le_markConst _ _ _)
  · rw [if_neg hg] at hth
    rw [partialGroupLists_of_notMem hg, if_neg hg, if_neg hg]
    exact TwoSidedProof.groupLists_factor_le P.vlo_pos (h.mass_ge g) hq0 hq1 (ht g) n hth

/-- The scalar factor of `partialWeight` times the number of lists is the product of the group
factors, when every group outside `U` has at least `t_g` hits. -/
theorem partialWeight_coeff_mul_card (𝔊 : ActiveGroups) (q₀ : ℝ) (t : 𝔊.Index → ℕ)
    (U : Finset 𝔊.Index) (n : ℕ)
    (hth : ∀ g : 𝔊.Index, (if g ∈ U then 0 else t g) ≤ primeHits (𝔊.group g) n) :
    q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, (if g ∈ U then 0 else t g)) *
        (∏ g : 𝔊.Index, (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹)) *
        ((partialLists 𝔊 t U n).card : ℝ) =
      ∏ g : 𝔊.Index, (q₀ ^ (primeHits (𝔊.group g) n - (if g ∈ U then 0 else t g)) *
        (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) *
        ((partialGroupLists 𝔊 t U n g).card : ℝ)) := by
  have hsum : ∑ g : 𝔊.Index, (primeHits (𝔊.group g) n - (if g ∈ U then 0 else t g)) +
      ∑ g : 𝔊.Index, (if g ∈ U then 0 else t g) = 𝔊.totalHits n := by
    unfold ActiveGroups.totalHits
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => Nat.sub_add_cancel (hth g)
  have hexp : 𝔊.totalHits n - ∑ g : 𝔊.Index, (if g ∈ U then 0 else t g) =
      ∑ g : 𝔊.Index, (primeHits (𝔊.group g) n - (if g ∈ U then 0 else t g)) := by
    omega
  have hcard : ((partialLists 𝔊 t U n).card : ℝ) =
      ∏ g : 𝔊.Index, ((partialGroupLists 𝔊 t U n g).card : ℝ) := by
    rw [partialLists_eq, Fintype.card_piFinset, Nat.cast_prod]
  rw [hexp, hcard, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]

/-! ### The statement -/

/-- **(cor:marked-bound) with marks removed**: `|W_{𝐭'}^𝐛(n)| ≤ L^C` with
`C = 2 C₀ log (markConst v₋ q₀ m')`, for `x ≥ 2` and every set `U` of groups whose marks are
removed. -/
theorem partialMarkedBound : PartialMarkedBound := by
  intro P q₀ hq0 hq1 m'
  have hc1 : 1 ≤ TwoSidedProof.markConst P.vlo q₀ m' := TwoSidedProof.one_le_markConst _ _ _
  have hc0 : 0 < TwoSidedProof.markConst P.vlo q₀ m' := lt_of_lt_of_le one_pos hc1
  refine ⟨Real.log (TwoSidedProof.markConst P.vlo q₀ m') * (2 * P.C₀), 2,
    fun x hx 𝔊 h t ht test htest U n => ?_⟩
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hLC : 0 ≤ Real.log x ^ (Real.log (TwoSidedProof.markConst P.vlo q₀ m') * (2 * P.C₀)) :=
    Real.rpow_nonneg hL.le _
  rcases (partialLists 𝔊 t U n).eq_empty_or_nonempty with hempty | ⟨𝔭₀, h𝔭₀⟩
  · -- no list: the weight vanishes
    unfold partialWeight
    rw [hempty, Finset.sum_empty, mul_zero, norm_zero]
    exact hLC
  · -- every group outside `U` has at least `t g` hits
    have hmem : ∀ g, 𝔭₀ g ∈ partialGroupLists 𝔊 t U n g := by
      have h' : 𝔭₀ ∈ Fintype.piFinset (partialGroupLists 𝔊 t U n) := h𝔭₀
      exact Fintype.mem_piFinset.mp h'
    have hth : ∀ g : 𝔊.Index, (if g ∈ U then 0 else t g) ≤ primeHits (𝔊.group g) n := by
      intro g
      by_cases hg : g ∈ U
      · rw [if_pos hg]
        exact Nat.zero_le _
      · rw [if_neg hg]
        have h1 := hmem g
        rw [partialGroupLists_of_notMem hg] at h1
        exact TwoSidedProof.le_primeHits_of_mem_groupLists h1
    -- the sum of the test
    have hnorm : ‖∑ 𝔭 ∈ partialLists 𝔊 t U n, test 𝔭‖ ≤ ((partialLists 𝔊 t U n).card : ℝ) :=
      calc ‖∑ 𝔭 ∈ partialLists 𝔊 t U n, test 𝔭‖
          ≤ ∑ 𝔭 ∈ partialLists 𝔊 t U n, ‖test 𝔭‖ := norm_sum_le _ _
        _ ≤ ∑ _𝔭 ∈ partialLists 𝔊 t U n, (1 : ℝ) := Finset.sum_le_sum fun 𝔭 _ => htest 𝔭
        _ = ((partialLists 𝔊 t U n).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    -- the scalar factor is nonnegative
    have hV : ∀ g : 𝔊.Index, 0 < reciprocalMass (𝔊.group g) := fun g =>
      lt_of_lt_of_le P.vlo_pos (h.mass_ge g)
    have hfac0 : ∀ g : 𝔊.Index,
        0 ≤ (if g ∈ U then (1 : ℝ) else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) := by
      intro g
      by_cases hg : g ∈ U
      · rw [if_pos hg]
        exact zero_le_one
      · rw [if_neg hg]
        exact inv_nonneg.mpr (pow_nonneg (hV g).le _)
    have hcoef0 : 0 ≤ q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, (if g ∈ U then 0 else t g)) *
        ∏ g : 𝔊.Index, (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) :=
      mul_nonneg (pow_nonneg hq0.le _) (Finset.prod_nonneg fun g _ => hfac0 g)
    -- the product over the groups
    have hprod := partialWeight_coeff_mul_card 𝔊 q₀ t U n hth
    -- the number of groups
    have hgroups : ((Finset.univ : Finset (Fin 𝔊.numSmall ⊕ Fin 𝔊.numBig)).card : ℝ) ≤
        2 * P.C₀ * Real.log (Real.log x) := by
      rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Nat.cast_add]
      linarith [h.numSmall_le, h.numBig_le]
    have hbound :=
      _root_.SimultaneousPrimitiveRoots.Unconditional.Graph.source_finite_norm_product_polynomial
        (Finset.univ : Finset (Fin 𝔊.numSmall ⊕ Fin 𝔊.numBig))
        (fun g => q₀ ^ (primeHits (𝔊.group g) n - (if g ∈ U then 0 else t g)) *
          (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) *
          ((partialGroupLists 𝔊 t U n g).card : ℝ))
        (Real.log x) (Real.log (TwoSidedProof.markConst P.vlo q₀ m')) (2 * P.C₀) hL
        (Real.log_nonneg hc1) hgroups
        (fun g _ => mul_nonneg (mul_nonneg (pow_nonneg hq0.le _) (hfac0 g)) (Nat.cast_nonneg _))
        (fun g _ => by
          rw [Real.exp_log hc0]
          exact partialGroupFactor_le h hq0 hq1 ht U n g (hth g))
    have hnormW : ‖partialWeight 𝔊 q₀ t test U n‖ =
        q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, (if g ∈ U then 0 else t g)) *
          (∏ g : 𝔊.Index, (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹)) *
          ‖∑ 𝔭 ∈ partialLists 𝔊 t U n, test 𝔭‖ := by
      unfold partialWeight
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcoef0]
    rw [hnormW]
    calc q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, (if g ∈ U then 0 else t g)) *
          (∏ g : 𝔊.Index, (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹)) *
          ‖∑ 𝔭 ∈ partialLists 𝔊 t U n, test 𝔭‖
        ≤ q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, (if g ∈ U then 0 else t g)) *
          (∏ g : 𝔊.Index, (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹)) *
          ((partialLists 𝔊 t U n).card : ℝ) := mul_le_mul_of_nonneg_left hnorm hcoef0
      _ = ∏ g : 𝔊.Index, (q₀ ^ (primeHits (𝔊.group g) n - (if g ∈ U then 0 else t g)) *
          (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) *
          ((partialGroupLists 𝔊 t U n g).card : ℝ)) := hprod
      _ ≤ Real.log x ^ (Real.log (TwoSidedProof.markConst P.vlo q₀ m') * (2 * P.C₀)) := hbound

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
