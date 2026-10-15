module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.KernelCells

/-!
# The kernel expansion

`kernelExpansionLink d H 𝔅 : KernelExpansionLink d H 𝔅` (`[P-06:0381–0391]`): "Expand the two
kernels in (cor:comparison-kernel). Their contract supplies only a fixed log-power total cost. In
each term the two nonempty free products are independent and lie in log cells of width at most one
… The cell and character expansion factors into separate bounded tests on the two free tuples and
on each endpoint's big marks."

* For `x > 0` the cutoff `Ψ(w/(x D_C))` vanishes for `w ≥ N` (`exists_cutoff_range`), so the
  stripped sum and every comparison correlation are finite sums of the form `listSum`
  (`strippedSumOf_eq_pairSum`, `comparisonCorrelationOf_eq_listSum`, `pairSum_tests_eq`).
* The stripped kernel is `-(-1)^{|C|} 𝒦_A(D_A, X_A) 𝒦_B(D_B, X_B)`; each kernel is expanded on its
  heavy cells and over the primitive characters (`TwoSidedProof/KernelCells.lean`): at most `ξ⁻¹`
  cells with coefficients at most `ξ⁻¹`, and at most `Q²` characters, for each kernel. The total
  coefficient mass is at most `ξ⁻⁴ Q⁴ = L^{4x_* + 4q_*}`.
* The tests `r ↦ 1_{I_j}(D_A(r)) conj χ(D_A(r))` are `BlockTest`s with `U = max(1, e^{jh})`
  (`blockTest_cellCharD`; `h = L^{-h_*} ≤ 1`), and the tests `𝔭 ↦ 1_{I_j}(X(𝔭)) χ(X(𝔭))` are
  `MarkTest`s (`markTest_cellCharX`).
* `ComparisonCorrelationBound` is used with the saving `A + 4q_* + 4x_*`.

The hypotheses `BigIntervals` and `KernelCostsLemma` of the link are not used: the number of cells
is bounded through their masses (`card_heavyCells_mul_le`), not through `cellCount`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open scoped ComplexConjugate

noncomputable section

/-! ### The cutoff -/

/-- For `x > 0` the cutoff `Ψ(w/(x D_C))` vanishes for `w ≥ N`, uniformly in the free labels. -/
theorem exists_cutoff_range {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {big : B → Finset ℕ}
    (C : B → Finset (Fin J)) {Ψ : ℝ → ℂ} (hcomp : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi 0) {x : ℝ} (hx : 0 < x) :
    ∃ N : ℕ, ∀ (r : AuxList big C) (w : ℕ), N ≤ w →
      Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0 := by
  obtain ⟨R₀, hR₀⟩ := hcomp.isCompact.bddAbove
  have hR : ∀ t, max R₀ 1 < t → Ψ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hmem =>
      absurd ((le_max_left R₀ 1).trans_lt ht) (not_lt.mpr (hR₀ hmem))
  have hΨ0 : Ψ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => lt_irrefl (0 : ℝ) (hsupp h)
  have hRpos : 0 < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨⌊max R₀ 1 * (x * ∑ r : AuxList big C, (tupleProd C r : ℝ))⌋₊ + 1, fun r w hw => ?_⟩
  rcases (Nat.cast_nonneg (tupleProd C r) : (0 : ℝ) ≤ (tupleProd C r : ℝ)).eq_or_lt with
    h0 | hpos
  · rw [← h0, mul_zero, div_zero]
    exact hΨ0
  · refine hR _ ?_
    have hle : (tupleProd C r : ℝ) ≤ ∑ r : AuxList big C, (tupleProd C r : ℝ) :=
      Finset.single_le_sum (f := fun r : AuxList big C => (tupleProd C r : ℝ))
        (fun i _ => Nat.cast_nonneg _) (Finset.mem_univ r)
    have h1 : max R₀ 1 * (x * (tupleProd C r : ℝ)) ≤
        max R₀ 1 * (x * ∑ r : AuxList big C, (tupleProd C r : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hx.le) hRpos.le
    have h2 : max R₀ 1 * (x * ∑ r : AuxList big C, (tupleProd C r : ℝ)) < (w : ℝ) :=
      lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast hw)
    rw [lt_div_iff₀ (mul_pos hx hpos)]
    linarith

/-! ### The stripped sum and the correlations as finite sums -/

section Strip

variable (𝔊 : ActiveGroups) (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) {d : ℕ}
  (S : Fin d → Finset ℕ) {H : ℕ} (𝔅 : JointResidueWeight H) (Ψ : ℝ → ℂ) (G : ℕ → ℂ) {J : ℕ}
  (C : Fin 𝔊.numBig → Finset (Fin J))

/-- The factor of a term of the stripped sums that does not involve the lists. -/
def stripFactor (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) : ℂ :=
  Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
    ((𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H) : ℝ) : ℂ) *
    ((centeredCore q 𝔞 x S w : ℝ) : ℂ) * G (w + tupleProd C r) *
    ((activeCoeff 𝔊 q₀ (markCount 𝔊 C) w *
        activeCoeff 𝔊 q₀ (markCount 𝔊 C) (w + tupleProd C r) : ℝ) : ℂ)

theorem stripFactor_eq_zero {r : AuxList (groupFamily 𝔊).big C} {w : ℕ}
    (h : Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0) :
    stripFactor 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C r w = 0 := by
  unfold stripFactor
  rw [h, zero_div, zero_mul, zero_mul, zero_mul, zero_mul]

/-- The term at the position `w` of a comparison correlation with tests. -/
def corrTerm (t₁ t₂ : ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ)
    (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) : ℂ :=
  Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
    ((𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H) : ℝ) : ℂ) *
    (((centeredCore q 𝔞 x S w : ℝ) : ℂ) * 𝔊.activeWeight q₀ (markCount 𝔊 C) t₁ w) *
    (G (w + tupleProd C r) * 𝔊.activeWeight q₀ (markCount 𝔊 C) t₂ (w + tupleProd C r))

theorem corrTerm_eq_zero (t₁ t₂ : ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ)
    {r : AuxList (groupFamily 𝔊).big C} {w : ℕ}
    (h : Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0) :
    corrTerm 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C t₁ t₂ r w = 0 := by
  unfold corrTerm
  rw [h, zero_div, zero_mul, zero_mul, zero_mul]

/-- **The stripped sum is a pair sum** of the two kernels, once the cutoff vanishes for
`w ≥ N`. -/
theorem strippedSumOf_eq_pairSum (blk : Fin 𝔊.numBig → Bool) (Q h ξ : ℝ) {N : ℕ}
    (hN : ∀ (r : AuxList (groupFamily 𝔊).big C) (w : ℕ), N ≤ w →
      Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0) :
    strippedSumOf 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C blk Q h ξ =
      pairSum N (fun r => ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ))
        (stripFactor 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C)
        (fun _ w => 𝔊.representedLists (markCount 𝔊 C) w)
        (fun r w => 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r))
        (-((-1 : ℂ) ^ (∑ g, (C g).card)))
        (fun r 𝔭' => cellKernel (groupFamily 𝔊).big (restrictBlock blk true C) Q h ξ
          (blockAuxProd blk true C r) (markProd 𝔊 C blk true 𝔭'))
        (fun r 𝔭 => cellKernel (groupFamily 𝔊).big (restrictBlock blk false C) Q h ξ
          (blockAuxProd blk false C r) (markProd 𝔊 C blk false 𝔭)) := by
  unfold strippedSumOf pairSum listSum
  refine Finset.sum_congr rfl fun r _ => ?_
  have hfin : (∑ᶠ w : ℕ, stripFactor 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C r w *
        ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
          ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r),
            strippedKernel 𝔊 C blk Q h ξ r 𝔭 𝔭') =
      ∑ w ∈ Finset.range N, stripFactor 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C r w *
        ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
          ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r),
            strippedKernel 𝔊 C blk Q h ξ r 𝔭 𝔭' :=
    finsum_eq_sum_of_support_subset _ fun w hw =>
      Finset.mem_coe.mpr (Finset.mem_range.mpr (by
        by_contra hcon
        rw [not_lt] at hcon
        refine hw ?_
        show stripFactor 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C r w * _ = 0
        rw [stripFactor_eq_zero 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C (hN r w hcon), zero_mul]))
  exact congrArg (fun z => ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ) * z) hfin

/-- **A comparison correlation with tests is a list sum** with the same data, once the cutoff
vanishes for `w ≥ N`. -/
theorem comparisonCorrelationOf_eq_listSum {N : ℕ}
    (hN : ∀ (r : AuxList (groupFamily 𝔊).big C) (w : ℕ), N ≤ w →
      Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0)
    (b : AuxList (groupFamily 𝔊).big C → ℂ)
    (t₁ t₂ : ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ) :
    comparisonCorrelationOf 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C b t₁ t₂ =
      listSum N (fun r => ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ))
        (stripFactor 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C)
        (fun _ w => 𝔊.representedLists (markCount 𝔊 C) w)
        (fun r w => 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r))
        (fun r 𝔭 𝔭' => b r * (t₁ 𝔭 * t₂ 𝔭')) := by
  unfold comparisonCorrelationOf listSum
  refine Finset.sum_congr rfl fun r _ => ?_
  have hW : ∀ (test : ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ) (n : ℕ),
      𝔊.activeWeight q₀ (markCount 𝔊 C) test n =
        ((activeCoeff 𝔊 q₀ (markCount 𝔊 C) n : ℝ) : ℂ) *
          ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) n, test 𝔭 := fun _ _ => rfl
  have hterm : ∀ w : ℕ, b r * corrTerm 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C t₁ t₂ r w =
      stripFactor 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C r w *
        ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
          ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r),
            b r * (t₁ 𝔭 * t₂ 𝔭') := by
    intro w
    have hsum : ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
        ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r),
          b r * (t₁ 𝔭 * t₂ 𝔭') =
        b r * ((∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w, t₁ 𝔭) *
          ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r), t₂ 𝔭') := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun 𝔭 _ => (Finset.mul_sum _ _ _).symm
    rw [hsum]
    unfold corrTerm stripFactor
    rw [hW, hW, Complex.ofReal_mul]
    ring
  have hfin : ∑ᶠ w : ℕ, corrTerm 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C t₁ t₂ r w =
      ∑ w ∈ Finset.range N, corrTerm 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C t₁ t₂ r w :=
    finsum_eq_sum_of_support_subset _ fun w hw =>
      Finset.mem_coe.mpr (Finset.mem_range.mpr (by
        by_contra hcon
        rw [not_lt] at hcon
        exact hw (corrTerm_eq_zero 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C t₁ t₂ (hN r w hcon))))
  calc ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ) * b r *
        ∑ᶠ w : ℕ, corrTerm 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C t₁ t₂ r w
      = ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ) *
          ∑ w ∈ Finset.range N, b r * corrTerm 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C t₁ t₂ r w := by
        rw [hfin, mul_assoc, Finset.mul_sum]
    _ = ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ) *
          ∑ w ∈ Finset.range N, stripFactor 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C r w *
            ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
              ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r),
                b r * (t₁ 𝔭 * t₂ 𝔭') :=
        congrArg (fun z => ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ) * z)
          (Finset.sum_congr rfl fun w _ => hterm w)

/-- **The pair sum of two products of tests is a comparison correlation** (times the sign). -/
theorem pairSum_tests_eq {N : ℕ}
    (hN : ∀ (r : AuxList (groupFamily 𝔊).big C) (w : ℕ), N ≤ w →
      Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0)
    (s : ℂ) (b₁ b₂ : AuxList (groupFamily 𝔊).big C → ℂ)
    (t₁ t₂ : ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ) :
    pairSum N (fun r => ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ))
        (stripFactor 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C)
        (fun _ w => 𝔊.representedLists (markCount 𝔊 C) w)
        (fun r w => 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r)) s
        (fun r 𝔭' => b₁ r * t₂ 𝔭') (fun r 𝔭 => b₂ r * t₁ 𝔭) =
      s * comparisonCorrelationOf 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C (fun r => b₁ r * b₂ r) t₁ t₂ := by
  rw [comparisonCorrelationOf_eq_listSum 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C hN, ← listSum_smul]
  unfold pairSum
  congr 1
  funext r 𝔭 𝔭'
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Strip

/-! ### The tests -/

theorem blockAuxProd_pos {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {big : B → Finset ℕ}
    (hbig : ∀ g, ∀ p ∈ big g, 0 < p) (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J))
    (r : AuxList big C) : 0 < blockAuxProd blk b C r := by
  unfold blockAuxProd
  refine Finset.prod_pos fun g _ => ?_
  by_cases hg : blk g = b
  · rw [if_pos hg]
    exact Finset.prod_pos fun i _ => hbig g (r g i) (r g i).2
  · rw [if_neg hg]
    exact Nat.one_pos

/-- **The cell test on the free labels of a block is a `BlockTest`** with `U = max(1, e^{jh})`,
for a cell width `0 < h ≤ 1`. -/
theorem blockTest_cellCharD {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {big : B → Finset ℕ}
    (hbig : ∀ g, ∀ p ∈ big g, 0 < p) (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J))
    {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (j : ℤ) {r₀ : ℕ} (χ : DirichletCharacter ℂ r₀) :
    BlockTest blk b C (fun r : AuxList big C => cellCharD h j χ (blockAuxProd blk b C r))
      (max 1 (Real.exp ((j : ℝ) * h))) where
  bound := fun r => norm_cellCharD_le h j χ _
  depends := fun r r' hrr => by
    have hprod : blockAuxProd blk b C r = blockAuxProd blk b C r' := by
      unfold blockAuxProd
      refine Finset.prod_congr rfl fun g _ => ?_
      by_cases hg : blk g = b
      · rw [if_pos hg, if_pos hg, hrr g hg]
      · rw [if_neg hg, if_neg hg]
    show cellCharD h j χ (blockAuxProd blk b C r) = cellCharD h j χ (blockAuxProd blk b C r')
    rw [hprod]
  cell := fun r hne => by
    have hcell : logCell h (blockAuxProd blk b C r) = j := cellCharD_ne_zero hne
    have hD0 : (0 : ℝ) < (blockAuxProd blk b C r : ℝ) :=
      Nat.cast_pos.mpr (blockAuxProd_pos hbig blk b C r)
    have hD1 : (1 : ℝ) ≤ (blockAuxProd blk b C r : ℝ) :=
      Nat.one_le_cast.mpr (blockAuxProd_pos hbig blk b C r)
    unfold logCell at hcell
    obtain ⟨h1, h2⟩ := Int.floor_eq_iff.mp hcell
    have h3 : (j : ℝ) * h ≤ Real.log (blockAuxProd blk b C r) := (le_div_iff₀ hh0).mp h1
    have h4 : Real.log (blockAuxProd blk b C r) < ((j : ℝ) + 1) * h := (div_lt_iff₀ hh0).mp h2
    have h5 : Real.exp ((j : ℝ) * h) ≤ (blockAuxProd blk b C r : ℝ) :=
      (Real.le_log_iff_exp_le hD0).mp h3
    have h6 : (blockAuxProd blk b C r : ℝ) < Real.exp ((j : ℝ) * h + 1) :=
      (Real.log_lt_iff_lt_exp hD0).mp (lt_of_lt_of_le h4 (by nlinarith))
    rw [Real.exp_add] at h6
    constructor
    · exact max_le hD1 h5
    · calc (blockAuxProd blk b C r : ℝ) ≤ Real.exp ((j : ℝ) * h) * Real.exp 1 := h6.le
        _ = Real.exp 1 * Real.exp ((j : ℝ) * h) := mul_comm _ _
        _ ≤ Real.exp 1 * max 1 (Real.exp ((j : ℝ) * h)) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos 1).le

/-- **The cell test on the marks of the freed slots of a block is a `MarkTest`.** -/
theorem markTest_cellCharX (𝔊 : ActiveGroups) {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J))
    (blk : Fin 𝔊.numBig → Bool) (b : Bool) (h : ℝ) (j : ℤ) {r₀ : ℕ}
    (χ : DirichletCharacter ℂ r₀) :
    MarkTest 𝔊 (fun 𝔭 : (g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ =>
      cellCharX h j χ (markProd 𝔊 C blk b 𝔭)) := by
  unfold MarkTest
  refine ⟨fun 𝔭 => norm_cellCharX_le h j χ _, fun 𝔭 𝔭' hpp => ?_⟩
  have hprod : markProd 𝔊 C blk b 𝔭 = markProd 𝔊 C blk b 𝔭' := by
    unfold markProd
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hpp k]
  show cellCharX h j χ (markProd 𝔊 C blk b 𝔭) = cellCharX h j χ (markProd 𝔊 C blk b 𝔭')
  rw [hprod]

/-! ### The statement -/

/-- **The kernel expansion** (`[P-06:0381–0391]`): the stripped comparison correlations are
negligible once the comparison correlations with separated bounded tests are. -/
theorem kernelExpansionLink (d H : ℕ) (𝔅 : JointResidueWeight H) : KernelExpansionLink d H 𝔅 := by
  intro _ _ hCC hH D m₀ J qs hs xs hqs hhs hxs A hA
  obtain ⟨M', x₀', hM'⟩ := hCC hH D m₀ (A + 4 * qs + 4 * xs) (by linarith)
  refine ⟨max M' 0, max x₀' (Real.exp 1), ?_⟩
  intro x hx I C hC
  have hx1 : x₀' ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  -- the parameters of the kernels
  have hQ0 : 0 ≤ Real.log x ^ qs := Real.rpow_nonneg hL0.le _
  have hh0 : 0 < Real.log x ^ (-hs) := Real.rpow_pos_of_pos hL0 _
  have hh1 : Real.log x ^ (-hs) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hξ0 : 0 < Real.log x ^ (-xs) := Real.rpow_pos_of_pos hL0 _
  have hξinv : (Real.log x ^ (-xs))⁻¹ = Real.log x ^ xs := by
    rw [Real.rpow_neg hL0.le, inv_inv]
  -- the big groups
  have hbig : ∀ g, ∀ p ∈ (groupFamily I.𝔊).big g, 0 < p := fun g p hp =>
    (I.groups.prime (Sum.inr g) p hp).pos
  have hlaw : ∀ g, ∑ p ∈ (groupFamily I.𝔊).big g,
      Graph.primeGroupLaw ((groupFamily I.𝔊).big g) p = 1 := fun g =>
    I.primeGroups.big_law_sum g
  have hmass : ∀ Λ : Fin I.𝔊.numBig → Finset (Fin J),
      ∑ t : AuxList (groupFamily I.𝔊).big Λ, auxWeight (groupFamily I.𝔊).big Λ t ≤ 1 :=
    fun Λ => le_of_eq (sum_auxWeight hlaw Λ)
  have hwnn : ∀ (Λ : Fin I.𝔊.numBig → Finset (Fin J)) (t : AuxList (groupFamily I.𝔊).big Λ),
      0 ≤ auxWeight (groupFamily I.𝔊).big Λ t := fun Λ t => Schur.auxWeight_nonneg _ Λ t
  -- the cutoff and the stripped sum as a pair sum
  obtain ⟨N, hN⟩ :=
    exists_cutoff_range (big := (groupFamily I.𝔊).big) C D.compact D.support hx0
  have hstr : I.strippedSum 𝔅 qs hs xs C = _ :=
    strippedSumOf_eq_pairSum I.𝔊 D.q D.q₀ D.𝔞 x I.S 𝔅 D.Ψ I.G C I.blocks
      (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs)) hN
  rw [hstr]
  have hs1 : ‖-((-1 : ℂ) ^ (∑ g, (C g).card))‖ = 1 := by
    rw [norm_neg, norm_pow, norm_neg, norm_one, one_pow]
  refine (norm_pairSum_cellKernel_le (groupFamily I.𝔊).big _ _ _ _ _ hξ0 _ _ _ _ N _ _ _ _ _
    (max M' 0 * Real.log x ^ (-(A + 4 * qs + 4 * xs))) fun j₁ r₁ χ₁ j₂ r₂ χ₂ => ?_).trans ?_
  · -- one product of tests: a comparison correlation
    rw [pairSum_tests_eq I.𝔊 D.q D.q₀ D.𝔞 x I.S 𝔅 D.Ψ I.G C hN _
      (fun r => cellCharD (Real.log x ^ (-hs)) j₁ χ₁ (blockAuxProd I.blocks true C r))
      (fun r => cellCharD (Real.log x ^ (-hs)) j₂ χ₂ (blockAuxProd I.blocks false C r))
      (fun 𝔭 => cellCharX (Real.log x ^ (-hs)) j₂ χ₂ (markProd I.𝔊 C I.blocks false 𝔭))
      (fun 𝔭' => cellCharX (Real.log x ^ (-hs)) j₁ χ₁ (markProd I.𝔊 C I.blocks true 𝔭')),
      norm_mul, hs1, one_mul]
    refine (hM' x hx1 I J C hC _ _ _ _ (le_max_left _ _) (le_max_left _ _)
      (blockTest_cellCharD hbig I.blocks true C hh0 hh1 j₁ χ₁)
      (blockTest_cellCharD hbig I.blocks false C hh0 hh1 j₂ χ₂) _ _
      (markTest_cellCharX I.𝔊 C I.blocks false _ j₂ χ₂)
      (markTest_cellCharX I.𝔊 C I.blocks true _ j₁ χ₁)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hL0.le _)
  · -- the total coefficient mass
    have hS₁ := sum_inv_cellMass_heavy_le (h := Real.log x ^ (-hs)) hξ0
      (hwnn (restrictBlock I.blocks true C)) (hmass _)
      (fun r : AuxList (groupFamily I.𝔊).big C => blockAuxProd I.blocks true C r)
    have hS₂ := sum_inv_cellMass_heavy_le (h := Real.log x ^ (-hs)) hξ0
      (hwnn (restrictBlock I.blocks false C)) (hmass _)
      (fun r : AuxList (groupFamily I.𝔊).big C => blockAuxProd I.blocks false C r)
    have hS₂0 := sum_inv_cellMass_heavy_nonneg (big := (groupFamily I.𝔊).big)
      (Λ := restrictBlock I.blocks false C) (h := Real.log x ^ (-hs)) hξ0
      (fun r : AuxList (groupFamily I.𝔊).big C => blockAuxProd I.blocks false C r)
    rw [hξinv] at hS₁ hS₂
    have hp := primitiveCharCount_le_sq (Real.log x ^ qs) hQ0
    have hp0 : (0 : ℝ) ≤ (primitiveCharCount (Real.log x ^ qs) : ℝ) := Nat.cast_nonneg _
    have he0 : 0 ≤ max M' 0 * Real.log x ^ (-(A + 4 * qs + 4 * xs)) :=
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hL0.le _)
    have ha0 : 0 ≤ Real.log x ^ xs * Real.log x ^ xs :=
      mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
    have hq0 : 0 ≤ (Real.log x ^ qs) ^ 2 := sq_nonneg _
    have h1 := mul_le_mul_of_nonneg_right hp he0
    have h2 := mul_le_mul hS₂ h1 (mul_nonneg hp0 he0) ha0
    have h3 := mul_le_mul hp h2 (mul_nonneg hS₂0 (mul_nonneg hp0 he0)) hq0
    have h4 := mul_le_mul hS₁ h3
      (mul_nonneg hp0 (mul_nonneg hS₂0 (mul_nonneg hp0 he0))) ha0
    refine h4.trans (le_of_eq ?_)
    have h4' : ∀ y : ℝ, y ^ (4 : ℝ) = y ^ (4 : ℕ) := fun y => by
      exact_mod_cast Real.rpow_natCast y 4
    have e1 : Real.log x ^ (-(A + 4 * qs + 4 * xs)) =
        Real.log x ^ (-A) * (Real.log x ^ (-qs)) ^ 4 * (Real.log x ^ (-xs)) ^ 4 := by
      rw [← h4', ← h4', ← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0,
        ← Real.rpow_add hL0]
      congr 1
      ring
    have ha1 : Real.log x ^ xs * (Real.log x ^ xs)⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hL0 _).ne'
    have hq1 : Real.log x ^ qs * (Real.log x ^ qs)⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hL0 _).ne'
    rw [e1, Real.rpow_neg hL0.le qs, Real.rpow_neg hL0.le xs]
    calc _ = max M' 0 * Real.log x ^ (-A) *
          (Real.log x ^ xs * (Real.log x ^ xs)⁻¹) ^ 4 *
          (Real.log x ^ qs * (Real.log x ^ qs)⁻¹) ^ 4 := by ring
      _ = max M' 0 * Real.log x ^ (-A) := by rw [ha1, hq1, one_pow, mul_one, mul_one]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
