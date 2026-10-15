module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.GraphInputs
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The cost bounds of the comparison kernel

`KernelCostsLemma` (the bounds (eq:ideal-cell-costs) of [S] §4, which [P] Prop 6.3 quotes) was a
hypothesis of `idealFamilyInput_of`. It is elementary and is proved here:

* `primitiveCharCount_le_sq`: there are at most `Q²` primitive characters of conductor `≤ Q`;
* `norm_cellKernel_le`: `|𝒦_Λ(D, X)| ≤ #𝒞_Q · ξ⁻¹`;
* `sum_cellKernel_le`: `E_D |𝒦_Λ(D, X)| ≤ #𝒞_Q` (the kernel lives on one log cell, whose mass
  cancels the normalization);
* `cellCount_le`: the tuples of a type `Λ` meet at most `1 + U / h` log cells when `log P_Λ ≤ U`,
  and `log P_Λ ≤ (number of slots) · L^d` (`log_tupleProd_le`);
* `kernelCostsLemma : KernelCostsLemma`, and `idealFamilyInput_of_contract`, the derivation of
  [P] Prop 6.3 with that hypothesis discharged.

The proofs were written by the independent reviewer of the statement layer (2026-10-12) as a check
that `KernelCostsLemma` is true as stated.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### characters -/

theorem norm_primitiveCharSum_le (Q : ℝ) (D X : ℕ) :
    ‖primitiveCharSum Q D X‖ ≤ (primitiveCharCount Q : ℝ) := by
  unfold primitiveCharSum primitiveCharCount
  rw [Nat.cast_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [Finset.natCast_card_filter]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
  by_cases h : χ.IsPrimitive
  · rw [if_pos h, if_pos h, norm_mul, Complex.norm_conj]
    calc ‖χ (D : ZMod r)‖ * ‖χ (X : ZMod r)‖ ≤ 1 * 1 :=
          mul_le_mul (χ.norm_le_one _) (χ.norm_le_one _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · simp [h]

/-- "There are at most `Q²` characters in `𝒞_Q`" [S-03:0196]. -/
theorem primitiveCharCount_le_sq (Q : ℝ) (hQ : 0 ≤ Q) : (primitiveCharCount Q : ℝ) ≤ Q ^ 2 := by
  have h1 : primitiveCharCount Q ≤ ⌊Q⌋₊ * ⌊Q⌋₊ := by
    unfold primitiveCharCount
    calc _ ≤ ∑ _r ∈ Finset.Icc 1 ⌊Q⌋₊, ⌊Q⌋₊ := Finset.sum_le_sum fun r hr => ?_
      _ = ⌊Q⌋₊ * ⌊Q⌋₊ := by simp
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
    have : NeZero r := ⟨by omega⟩
    refine (Finset.card_le_univ _).trans ?_
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r]
    exact (Nat.totient_le r).trans hr2
  have h2 : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ
  calc (primitiveCharCount Q : ℝ) ≤ ((⌊Q⌋₊ * ⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (⌊Q⌋₊ : ℝ) * (⌊Q⌋₊ : ℝ) := by push_cast; ring
    _ ≤ Q * Q := mul_le_mul h2 h2 (Nat.cast_nonneg _) hQ
    _ = Q ^ 2 := by ring

/-! ### the kernel -/

section Kernel

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

theorem norm_cellKernel_le (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ)
    (hξ : 0 < ξ) (D X : ℕ) :
    ‖cellKernel big Λ Q h ξ D X‖ ≤ (primitiveCharCount Q : ℝ) * ξ⁻¹ := by
  unfold cellKernel
  by_cases hc : logCell h D = logCell h X ∧ ξ ≤ cellMass big Λ h (logCell h D)
  · have hpos : 0 < cellMass big Λ h (logCell h D) := lt_of_lt_of_le hξ hc.2
    rw [if_pos hc, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    calc (cellMass big Λ h (logCell h D))⁻¹ * ‖primitiveCharSum Q D X‖
        ≤ ξ⁻¹ * (primitiveCharCount Q : ℝ) :=
          mul_le_mul (inv_anti₀ hξ hc.2) (norm_primitiveCharSum_le Q D X) (norm_nonneg _)
            (inv_nonneg.mpr hξ.le)
      _ = (primitiveCharCount Q : ℝ) * ξ⁻¹ := mul_comm _ _
  · rw [if_neg hc, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr hξ.le)

theorem sum_cellKernel_le (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ)
    (hξ : 0 < ξ) (hw : ∀ t : AuxList big Λ, 0 ≤ auxWeight big Λ t) (X : ℕ) :
    ∑ t : AuxList big Λ, auxWeight big Λ t * ‖cellKernel big Λ Q h ξ (tupleProd Λ t) X‖ ≤
      (primitiveCharCount Q : ℝ) := by
  by_cases hν : ξ ≤ cellMass big Λ h (logCell h X)
  · have hpos : 0 < cellMass big Λ h (logCell h X) := lt_of_lt_of_le hξ hν
    have hterm : ∀ t : AuxList big Λ,
        auxWeight big Λ t * ‖cellKernel big Λ Q h ξ (tupleProd Λ t) X‖ ≤
          (if logCell h (tupleProd Λ t) = logCell h X then auxWeight big Λ t else 0) *
            ((cellMass big Λ h (logCell h X))⁻¹ * (primitiveCharCount Q : ℝ)) := by
      intro t
      by_cases hcell : logCell h (tupleProd Λ t) = logCell h X
      · rw [if_pos hcell]
        refine mul_le_mul_of_nonneg_left ?_ (hw t)
        unfold cellKernel
        by_cases hc : logCell h (tupleProd Λ t) = logCell h X ∧
            ξ ≤ cellMass big Λ h (logCell h (tupleProd Λ t))
        · rw [if_pos hc, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, hcell,
            abs_of_pos hpos]
          exact mul_le_mul_of_nonneg_left (norm_primitiveCharSum_le Q _ X)
            (inv_nonneg.mpr hpos.le)
        · rw [if_neg hc, norm_zero]
          exact mul_nonneg (inv_nonneg.mpr hpos.le) (Nat.cast_nonneg _)
      · simp [hcell, cellKernel_eq_zero_of_logCell_ne hcell]
    calc ∑ t : AuxList big Λ, auxWeight big Λ t * ‖cellKernel big Λ Q h ξ (tupleProd Λ t) X‖
        ≤ ∑ t : AuxList big Λ,
            (if logCell h (tupleProd Λ t) = logCell h X then auxWeight big Λ t else 0) *
              ((cellMass big Λ h (logCell h X))⁻¹ * (primitiveCharCount Q : ℝ)) :=
          Finset.sum_le_sum fun t _ => hterm t
      _ = cellMass big Λ h (logCell h X) *
            ((cellMass big Λ h (logCell h X))⁻¹ * (primitiveCharCount Q : ℝ)) := by
          rw [← Finset.sum_mul]
          rfl
      _ = (primitiveCharCount Q : ℝ) := by
          rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  · have hzero : ∀ t : AuxList big Λ, cellKernel big Λ Q h ξ (tupleProd Λ t) X = 0 := by
      intro t
      unfold cellKernel
      refine if_neg fun hc => hν ?_
      rw [← hc.1]
      exact hc.2
    simp only [hzero, norm_zero, mul_zero, Finset.sum_const_zero]
    exact Nat.cast_nonneg _

end Kernel

/-! ### the number of cells -/

section Cells

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B]

omit [DecidableEq B] in
/-- `log P_Λ ≤ (number of slots) · L^d`. -/
theorem log_tupleProd_le (𝔊 : PrimeGroups P x S B) {J : ℕ} (Λ : B → Finset (Fin J))
    (t : AuxList 𝔊.big Λ) :
    Real.log ((tupleProd Λ t : ℕ) : ℝ) ≤ (∑ g, ((Λ g).card : ℝ)) * Real.log x ^ P.d := by
  have hne : ∀ (g : B) (i : {i : Fin J // i ∈ Λ g}), (((t g i : ℕ) : ℕ) : ℝ) ≠ 0 := by
    intro g i
    exact_mod_cast (𝔊.prime_big g (t g i) (t g i).2).ne_zero
  unfold tupleProd
  rw [Nat.cast_prod, Real.log_prod, Finset.sum_mul]
  · refine Finset.sum_le_sum fun g _ => ?_
    rw [Nat.cast_prod, Real.log_prod]
    · calc ∑ i : {i : Fin J // i ∈ Λ g}, Real.log (((t g i : ℕ) : ℕ) : ℝ)
          ≤ ∑ _i : {i : Fin J // i ∈ Λ g}, Real.log x ^ P.d := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hpos : (0 : ℝ) < (((t g i : ℕ) : ℕ) : ℝ) := by
              exact_mod_cast (𝔊.prime_big g (t g i) (t g i).2).pos
            exact (Real.log_le_iff_le_exp hpos).mpr (𝔊.big_le g (t g i) (t g i).2)
        _ = ((Λ g).card : ℝ) * Real.log x ^ P.d := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    · intro i _
      exact hne g i
  · intro g _
    rw [Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hne g i

/-- The number of log cells met by the tuples of type `Λ` is at most `1 + U / h` when
`log P_Λ ≤ U`. -/
theorem cellCount_le (𝔊 : PrimeGroups P x S B) {J : ℕ} (Λ : B → Finset (Fin J)) (h U : ℝ)
    (hh : 0 < h) (hU0 : 0 ≤ U)
    (hU : ∀ t : AuxList 𝔊.big Λ, Real.log ((tupleProd Λ t : ℕ) : ℝ) ≤ U) :
    (cellCount 𝔊.big Λ h : ℝ) ≤ 1 + U / h := by
  have hsub : (Finset.univ.image fun t : AuxList 𝔊.big Λ => logCell h (tupleProd Λ t)) ⊆
      Finset.Icc 0 ⌊U / h⌋ := by
    intro j hj
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hj
    rw [Finset.mem_Icc]
    have hpos : (1 : ℝ) ≤ ((tupleProd Λ t : ℕ) : ℝ) := by
      have h0 : 0 < tupleProd Λ t := by
        unfold tupleProd
        exact Finset.prod_pos fun g _ => Finset.prod_pos fun i _ =>
          (𝔊.prime_big g (t g i) (t g i).2).pos
      exact_mod_cast h0
    constructor
    · unfold logCell
      exact Int.floor_nonneg.mpr (div_nonneg (Real.log_nonneg hpos) hh.le)
    · unfold logCell
      exact Int.floor_le_floor (div_le_div_of_nonneg_right (hU t) hh.le)
  have hcard : cellCount 𝔊.big Λ h ≤ (Finset.Icc (0 : ℤ) ⌊U / h⌋).card :=
    Finset.card_le_card hsub
  have hfl : (0 : ℤ) ≤ ⌊U / h⌋ := Int.floor_nonneg.mpr (div_nonneg hU0 hh.le)
  have hIccZ : (((Finset.Icc (0 : ℤ) ⌊U / h⌋).card : ℕ) : ℤ) = ⌊U / h⌋ + 1 - 0 :=
    Int.card_Icc_of_le 0 ⌊U / h⌋ (by omega)
  have hIcc : (((Finset.Icc (0 : ℤ) ⌊U / h⌋).card : ℕ) : ℝ) = (⌊U / h⌋ : ℝ) + 1 := by
    have h3 := congrArg (Int.cast : ℤ → ℝ) hIccZ
    rw [Int.cast_natCast] at h3
    rw [h3]
    push_cast
    ring
  calc (cellCount 𝔊.big Λ h : ℝ) ≤ (((Finset.Icc (0 : ℤ) ⌊U / h⌋).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = (⌊U / h⌋ : ℝ) + 1 := hIcc
    _ ≤ 1 + U / h := by linarith [Int.floor_le (U / h)]

end Cells

/-! ### `KernelCostsLemma` -/

/-- **The cost bounds (eq:ideal-cell-costs) of [S] §4** ([S-03:0196–0206], quoted in
[P-06:0228–0235]): at most `Q²` characters, at most `C (1 + L^d log L / h)` nonempty cells,
`sup |𝒦_Λ| ≤ Q² ξ⁻¹` and `sup_X E_D |𝒦_Λ(D, X)| ≤ Q²`. -/
theorem kernelCostsLemma : KernelCostsLemma := by
  intro P m₀ qs hs xs hqs hhs hxs
  refine ⟨max 1 ((m₀ : ℝ) * P.C₀), Real.exp (Real.exp 1), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 hint J Λ hne hΛ
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hT : 1 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hL0).mpr hL
  have hQ : 0 ≤ Real.log x ^ qs := Real.rpow_nonneg hL0.le _
  have hh : 0 < Real.log x ^ (-hs) := Real.rpow_pos_of_pos hL0 _
  have hξ : 0 < Real.log x ^ (-xs) := Real.rpow_pos_of_pos hL0 _
  have hLd : 0 ≤ Real.log x ^ P.d := Real.rpow_nonneg hL0.le _
  have hcount := primitiveCharCount_le_sq (Real.log x ^ qs) hQ
  have hw : ∀ t : AuxList 𝔊.big Λ, 0 ≤ auxWeight 𝔊.big Λ t := by
    intro t
    unfold auxWeight
    exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ =>
      (𝔊.big_law_pos g (t g i) (t g i).2).le
  refine ⟨hcount, ?_, fun D X => ?_, fun X => ?_⟩
  · have hsum : (∑ g, ((Λ g).card : ℝ)) ≤ (m₀ : ℝ) * (P.C₀ * Real.log (Real.log x)) := by
      calc (∑ g, ((Λ g).card : ℝ)) ≤ ∑ _g : B, (m₀ : ℝ) :=
            Finset.sum_le_sum fun g _ => by exact_mod_cast hΛ g
        _ = (Fintype.card B : ℝ) * m₀ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ (P.C₀ * Real.log (Real.log x)) * m₀ :=
            mul_le_mul_of_nonneg_right 𝔊.card_big_le (Nat.cast_nonneg _)
        _ = (m₀ : ℝ) * (P.C₀ * Real.log (Real.log x)) := mul_comm _ _
    have hU0 : 0 ≤ (∑ g, ((Λ g).card : ℝ)) * Real.log x ^ P.d :=
      mul_nonneg (Finset.sum_nonneg fun g _ => Nat.cast_nonneg _) hLd
    have hcc := cellCount_le 𝔊 Λ (Real.log x ^ (-hs)) _ hh hU0
      (fun t => log_tupleProd_le 𝔊 Λ t)
    have hratio : (∑ g, ((Λ g).card : ℝ)) * Real.log x ^ P.d / Real.log x ^ (-hs) ≤
        (m₀ : ℝ) * P.C₀ *
          (Real.log x ^ P.d * Real.log (Real.log x) / Real.log x ^ (-hs)) := by
      calc (∑ g, ((Λ g).card : ℝ)) * Real.log x ^ P.d / Real.log x ^ (-hs)
          ≤ (m₀ : ℝ) * (P.C₀ * Real.log (Real.log x)) * Real.log x ^ P.d /
              Real.log x ^ (-hs) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hLd) hh.le
        _ = (m₀ : ℝ) * P.C₀ *
              (Real.log x ^ P.d * Real.log (Real.log x) / Real.log x ^ (-hs)) := by
            ring
    have hnn : 0 ≤ Real.log x ^ P.d * Real.log (Real.log x) / Real.log x ^ (-hs) :=
      div_nonneg (mul_nonneg hLd (le_trans zero_le_one hT)) hh.le
    have h1 : (1 : ℝ) ≤ max 1 ((m₀ : ℝ) * P.C₀) := le_max_left _ _
    have h2 : (m₀ : ℝ) * P.C₀ ≤ max 1 ((m₀ : ℝ) * P.C₀) := le_max_right _ _
    have h3 := mul_le_mul_of_nonneg_right h2 hnn
    calc (cellCount 𝔊.big Λ (Real.log x ^ (-hs)) : ℝ)
        ≤ 1 + (∑ g, ((Λ g).card : ℝ)) * Real.log x ^ P.d / Real.log x ^ (-hs) := hcc
      _ ≤ 1 + (m₀ : ℝ) * P.C₀ *
            (Real.log x ^ P.d * Real.log (Real.log x) / Real.log x ^ (-hs)) := by linarith
      _ ≤ max 1 ((m₀ : ℝ) * P.C₀) *
            (1 + Real.log x ^ P.d * Real.log (Real.log x) / Real.log x ^ (-hs)) := by
          nlinarith
  · exact (norm_cellKernel_le 𝔊.big Λ _ _ _ hξ D X).trans
      (mul_le_mul_of_nonneg_right hcount (inv_nonneg.mpr hξ.le))
  · exact (sum_cellKernel_le 𝔊.big Λ _ _ _ hξ hw X).trans hcount

/-- **[P] Prop 6.3 from Lemma 4.3 and the construction after it**, with the cost bounds proved. -/
theorem idealFamilyInput_of_contract (h₁ : ComparisonKernelLemma)
    (h₂ : IdealConstructionOfContract) : IdealFamilyInput :=
  idealFamilyInput_of h₁ h₂ kernelCostsLemma

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
