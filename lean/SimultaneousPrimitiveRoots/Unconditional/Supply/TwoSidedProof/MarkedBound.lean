module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.Counting
public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourceGroupPolynomialLoss

/-!
# The marked bound (cor:marked-bound)

`markedBound : MarkedBound` (`[P-06:0044–0053]`): `|W_𝐭^𝐛(n)| ≤ L^{C(m')}` for `t_g ≤ m'`,
`|𝐛| ≤ 1`. "Indeed, each factor `q_0^{u-t} (u)_t / V_g^t`, for `u ≥ t`, is bounded by a constant
depending only on `m', q_0, v_-`, and there are `O(log L)` factors."

* The represented lists of the vector `𝐭` are a product over the groups of the lists of one group
  (`groupLists`, `representedLists_eq`); a group with a list has `u ≥ t` hits
  (`le_primeHits_of_mem_groupLists`) and at most `u^t` lists (`card_groupLists_le`; the paper's
  count is the falling factorial `(u)_t ≤ u^t`).
* One group factor `q_0^{u-t} V^{-t} · #lists` is at most
  `markConst v₋ q₀ m' = max(1, 1/v₋)^{m'+1} · max(1, sup_z (z + m' + 1)^{m'+1} q₀^z)`
  (`groupLists_factor_le`); the supremum is `Transference.Schur.countSup`, the constant of
  [S] (eq:physical-count-bound), which is finite because `n^T ρ^n → 0`.
* The product over the `|𝒮| + |ℬ| ≤ 2 C₀ log L` groups is at most `L^{2 C₀ log(markConst)}`
  (`Graph.source_finite_norm_product_polynomial`).

The exponent is `C = 2 C₀ log (markConst v₋ q₀ m')` and the threshold is `x₀ = 2`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

/-! ### The lists of one group -/

/-- The represented lists of one group at `n`: `t` ordered distinct prime divisors of `n` from
`T` (`[P-06:0033–0035]`). -/
def groupLists (T : Finset ℕ) (t n : ℕ) : Finset (Fin t → ℕ) :=
  (Fintype.piFinset fun _ : Fin t => T.filter fun p => p ∣ n).filter
    fun 𝔭 => Function.Injective 𝔭

/-- The represented lists are the product over the groups of the lists of one group. -/
theorem representedLists_eq (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ) (n : ℕ) :
    𝔊.representedLists t n = Fintype.piFinset fun g => groupLists (𝔊.group g) (t g) n := rfl

/-- There are at most `u^t` lists of `t` divisors when the group has `u` divisors of `n`. -/
theorem card_groupLists_le (T : Finset ℕ) (t n : ℕ) :
    (groupLists T t n).card ≤ primeHits T n ^ t := by
  unfold groupLists primeHits
  exact (Finset.card_filter_le _ _).trans (le_of_eq (by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]))

/-- A group with a list of `t` distinct divisors of `n` has at least `t` divisors of `n`. -/
theorem le_primeHits_of_mem_groupLists {T : Finset ℕ} {t n : ℕ} {𝔭 : Fin t → ℕ}
    (h : 𝔭 ∈ groupLists T t n) : t ≤ primeHits T n := by
  unfold groupLists at h
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
  have h3 : ∀ i, 𝔭 i ∈ T.filter fun p => p ∣ n := Fintype.mem_piFinset.mp h1
  have h4 : (Finset.univ : Finset (Fin t)).card ≤ (T.filter fun p => p ∣ n).card :=
    Finset.card_le_card_of_injOn 𝔭 (fun i _ => Finset.mem_coe.mpr (h3 i))
      (fun i _ j _ hij => h2 hij)
  rw [Finset.card_univ, Fintype.card_fin] at h4
  exact h4

/-! ### One group factor -/

/-- The constant bounding one group factor `q_0^{u-t} V^{-t} · #lists` for `t ≤ m'`, `V ≥ v₋`:
`max(1, 1/v₋)^{m'+1} · max(1, sup_{z ≥ 0} (z + m' + 1)^{m'+1} q₀^z)`. -/
def markConst (vlo q₀ : ℝ) (m' : ℕ) : ℝ :=
  (max 1 vlo⁻¹) ^ (m' + 1) * max 1 (Schur.countSup (m' + 1) q₀)

theorem one_le_markConst (vlo q₀ : ℝ) (m' : ℕ) : 1 ≤ markConst vlo q₀ m' := by
  have h1 : (1 : ℝ) ≤ (max 1 vlo⁻¹) ^ (m' + 1) := one_le_pow₀ (le_max_left _ _)
  have h2 : (1 : ℝ) ≤ max 1 (Schur.countSup (m' + 1) q₀) := le_max_left _ _
  unfold markConst
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ (max 1 vlo⁻¹) ^ (m' + 1) * max 1 (Schur.countSup (m' + 1) q₀) :=
        mul_le_mul h1 h2 zero_le_one (zero_le_one.trans h1)

/-- **One group factor is bounded** (`[P-06:0051–0053]`): for `t ≤ m'`, `t ≤ u = ω_T(n)` and
`V_T ≥ v₋ > 0`, `q_0^{u - t} V_T^{-t} · #lists ≤ markConst v₋ q₀ m'`. -/
theorem groupLists_factor_le {T : Finset ℕ} {vlo q₀ : ℝ} (hv : 0 < vlo)
    (hV : vlo ≤ reciprocalMass T) (hq0 : 0 < q₀) (hq1 : q₀ < 1) {m' t : ℕ} (ht : t ≤ m') (n : ℕ)
    (hth : t ≤ primeHits T n) :
    q₀ ^ (primeHits T n - t) * (reciprocalMass T ^ t)⁻¹ * ((groupLists T t n).card : ℝ) ≤
      markConst vlo q₀ m' := by
  obtain ⟨z, hz⟩ : ∃ z : ℕ, primeHits T n = z + t := ⟨primeHits T n - t, by omega⟩
  have hcard : ((groupLists T t n).card : ℝ) ≤ ((z + (m' + 1) : ℕ) : ℝ) ^ (m' + 1) := by
    have h1 := card_groupLists_le T t n
    rw [hz] at h1
    have h2 := Schur.pow_add_le_pow_add z t (m' + 1) (by omega) (by omega)
    exact_mod_cast h1.trans h2
  have hsub : primeHits T n - t = z := by omega
  have hmax0 : (0 : ℝ) ≤ (max 1 vlo⁻¹) ^ (m' + 1) :=
    pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  rw [hsub]
  unfold markConst
  calc q₀ ^ z * (reciprocalMass T ^ t)⁻¹ * ((groupLists T t n).card : ℝ)
      ≤ q₀ ^ z * (max 1 vlo⁻¹) ^ (m' + 1) * ((z + (m' + 1) : ℕ) : ℝ) ^ (m' + 1) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (Schur.inv_pow_le_max_pow hv hV (by omega))
            (pow_nonneg hq0.le z))
          hcard (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hq0.le z) hmax0)
    _ = (max 1 vlo⁻¹) ^ (m' + 1) * (((z + (m' + 1) : ℕ) : ℝ) ^ (m' + 1) * q₀ ^ z) := by ring
    _ ≤ (max 1 vlo⁻¹) ^ (m' + 1) * max 1 (Schur.countSup (m' + 1) q₀) :=
        mul_le_mul_of_nonneg_left
          ((Schur.le_countSup (m' + 1) hq0 hq1 z).trans (le_max_right _ _)) hmax0

/-! ### The statement -/

/-- **(cor:marked-bound)**: `|W_𝐭^𝐛(n)| ≤ L^C` with `C = 2 C₀ log (markConst v₋ q₀ m')`, for
`x ≥ 2`. -/
theorem markedBound : MarkedBound := by
  intro P q₀ hq0 hq1 m'
  have hc1 : 1 ≤ markConst P.vlo q₀ m' := one_le_markConst _ _ _
  have hc0 : 0 < markConst P.vlo q₀ m' := lt_of_lt_of_le one_pos hc1
  refine ⟨Real.log (markConst P.vlo q₀ m') * (2 * P.C₀), 2,
    fun x hx 𝔊 h t ht test htest n => ?_⟩
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hLC : 0 ≤ Real.log x ^ (Real.log (markConst P.vlo q₀ m') * (2 * P.C₀)) :=
    Real.rpow_nonneg hL.le _
  rcases (𝔊.representedLists t n).eq_empty_or_nonempty with hempty | ⟨𝔭₀, h𝔭₀⟩
  · -- no represented list: the weight vanishes
    unfold ActiveGroups.activeWeight
    rw [hempty, Finset.sum_empty, mul_zero, norm_zero]
    exact hLC
  · -- every group has at least `t g` hits
    have h𝔭₀' : 𝔭₀ ∈ Fintype.piFinset fun g => groupLists (𝔊.group g) (t g) n := h𝔭₀
    have hmem : ∀ g, 𝔭₀ g ∈ groupLists (𝔊.group g) (t g) n := Fintype.mem_piFinset.mp h𝔭₀'
    have hth : ∀ g, t g ≤ primeHits (𝔊.group g) n := fun g =>
      le_primeHits_of_mem_groupLists (hmem g)
    -- the exponent of the damping
    have hsum : ∑ g : 𝔊.Index, (primeHits (𝔊.group g) n - t g) + ∑ g : 𝔊.Index, t g =
        𝔊.totalHits n := by
      unfold ActiveGroups.totalHits
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ => Nat.sub_add_cancel (hth g)
    have hexp : 𝔊.totalHits n - ∑ g : 𝔊.Index, t g =
        ∑ g : 𝔊.Index, (primeHits (𝔊.group g) n - t g) := by
      omega
    -- the sum of the test
    have hnorm : ‖∑ 𝔭 ∈ 𝔊.representedLists t n, test 𝔭‖ ≤
        ((𝔊.representedLists t n).card : ℝ) :=
      calc ‖∑ 𝔭 ∈ 𝔊.representedLists t n, test 𝔭‖
          ≤ ∑ 𝔭 ∈ 𝔊.representedLists t n, ‖test 𝔭‖ := norm_sum_le _ _
        _ ≤ ∑ _𝔭 ∈ 𝔊.representedLists t n, (1 : ℝ) := Finset.sum_le_sum fun 𝔭 _ => htest 𝔭
        _ = ((𝔊.representedLists t n).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((𝔊.representedLists t n).card : ℝ) =
        ∏ g : 𝔊.Index, ((groupLists (𝔊.group g) (t g) n).card : ℝ) := by
      rw [representedLists_eq, Fintype.card_piFinset, Nat.cast_prod]
    -- the scalar factor is nonnegative
    have hV : ∀ g : 𝔊.Index, 0 < reciprocalMass (𝔊.group g) := fun g =>
      lt_of_lt_of_le P.vlo_pos (h.mass_ge g)
    have hcoef0 : 0 ≤ q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, t g) *
        ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ :=
      mul_nonneg (pow_nonneg hq0.le _)
        (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (hV g).le _))
    -- the product over the groups
    have hprod : q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, t g) *
          (∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹) *
          ((𝔊.representedLists t n).card : ℝ) =
        ∏ g : 𝔊.Index, (q₀ ^ (primeHits (𝔊.group g) n - t g) *
          (reciprocalMass (𝔊.group g) ^ t g)⁻¹ *
          ((groupLists (𝔊.group g) (t g) n).card : ℝ)) := by
      rw [hexp, hcard, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
    -- the number of groups
    have hgroups : ((Finset.univ : Finset (Fin 𝔊.numSmall ⊕ Fin 𝔊.numBig)).card : ℝ) ≤
        2 * P.C₀ * Real.log (Real.log x) := by
      rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Nat.cast_add]
      linarith [h.numSmall_le, h.numBig_le]
    have hbound := Graph.source_finite_norm_product_polynomial
      (Finset.univ : Finset (Fin 𝔊.numSmall ⊕ Fin 𝔊.numBig))
      (fun g => q₀ ^ (primeHits (𝔊.group g) n - t g) * (reciprocalMass (𝔊.group g) ^ t g)⁻¹ *
        ((groupLists (𝔊.group g) (t g) n).card : ℝ))
      (Real.log x) (Real.log (markConst P.vlo q₀ m')) (2 * P.C₀) hL (Real.log_nonneg hc1) hgroups
      (fun g _ => mul_nonneg
        (mul_nonneg (pow_nonneg hq0.le _) (inv_nonneg.mpr (pow_nonneg (hV g).le _)))
        (Nat.cast_nonneg _))
      (fun g _ => by
        rw [Real.exp_log hc0]
        exact groupLists_factor_le P.vlo_pos (h.mass_ge g) hq0 hq1 (ht g) n (hth g))
    unfold ActiveGroups.activeWeight
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcoef0]
    calc q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, t g) *
          (∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹) *
          ‖∑ 𝔭 ∈ 𝔊.representedLists t n, test 𝔭‖
        ≤ q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, t g) *
          (∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹) *
          ((𝔊.representedLists t n).card : ℝ) := mul_le_mul_of_nonneg_left hnorm hcoef0
      _ = ∏ g : 𝔊.Index, (q₀ ^ (primeHits (𝔊.group g) n - t g) *
          (reciprocalMass (𝔊.group g) ^ t g)⁻¹ *
          ((groupLists (𝔊.group g) (t g) n).card : ℝ)) := hprod
      _ ≤ Real.log x ^ (Real.log (markConst P.vlo q₀ m') * (2 * P.C₀)) := hbound

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
