module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements

/-!
# The proved chain of [P] §6 with a joint residue weight

This file proves, from the statements of `TwoSidedProof/Statements.lean`:

* `transferData` (`[P-06:0256–0258, 0298–0306]`): Propositions 6.2 and 6.3 for the active groups
  of [P] §6 (`ℓ = k = 1`, `C_4 = 1`, `γ = 1/2`, the exponents of (cor:groups)), with the constants
  in the order `E ⟶ E_id ⟶ (m_0, J_0, C_1, kernel exponents) ⟶ (J_0', C_abs) ⟶ J`:
  `GraphTransferInput ∧ IdealFamilyInput ∧ BigIntervals ∧ HalfSplitBalanced → TransferData d D E`.
* `twoSidedBound_of_stages` (`[P-06:0372–0377, 0927–0935]`): the subtraction. The residual edge
  pairing is the raw edge sum plus the comparison edge sums; the raw edge sum is the two-sided sum
  up to the stripping error; each comparison edge sum is its stripped correlation up to the
  stripping error; the number of comparisons is at most `L^{C_1}`:
  `PatternCountAt ∧ ResidualBoundAt ∧ RawStrippingAt ∧ ComparisonStrippingAt ∧ StrippedBoundAt
    → (eq:two-sided)`.
* `twoSidedBound`: the whole chain for fixed data, with the constants chosen in the manuscript's
  order (`[P-06:0301–0316]`): the saving `A`; `C_3` (`EndpointNorms`); `E = A + 2|C_3| + 2`; the
  family (`transferData`); the residual bound (`InsertionLink`); the stripping errors and the
  comparison bounds with the saving `A + max(C_1, 0)`, "after the known fixed kernel, dyad, arc,
  and separation costs" (`[P-06:0931–0932]`).
* `twoSidedReduction_of_leaves`: `Leaves d H 𝔅 → TwoSidedReduction d H 𝔅` for `0 < H`.

The comparison stage is a chain of links, all inside `twoSidedBound`:
`MarkedBound, CorePowerBounded ⟶ EndpointSquares`; `BilinearFourier ⟶ MultiplierMinor`;
`LocalMellin, EndpointSquares, EndpointEnergy ⟶ ArcEnergy` (the use of (cor:SM));
`MultiplierMinor, ArcEnergy, EndpointSquares ⟶ BilinearBound`;
`BilinearBound, EndpointSquares ⟶ ComparisonCorrelationBound`;
`KernelCostsLemma, ComparisonCorrelationBound ⟶ StrippedComparisonBound`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open scoped ContDiff

noncomputable section

/-! ### The subtraction, for complex numbers -/

/-- If `R + ∑_i c_i` and `R - T` are at most `M ε`, and `c_i - s_i`, `s_i` are at most `M δ` with
`(number of i) · δ ≤ ε`, then `T` is at most `M' ε`: the subtraction of `[P-06:0932–0935]`
("Subtracting these comparison terms from the residual pairing leaves its raw pattern"). -/
theorem norm_le_of_decomposition {ι : Type} [Fintype ι] (T R : ℂ) (c s : ι → ℂ)
    {M₁ M₂ M₃ M₄ ε δ : ℝ}
    (h₁ : ‖R + ∑ i, c i‖ ≤ M₁ * ε) (h₂ : ‖R - T‖ ≤ M₂ * ε)
    (h₃ : ∀ i, ‖c i - s i‖ ≤ M₃ * δ) (h₄ : ∀ i, ‖s i‖ ≤ M₄ * δ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hN : (Fintype.card ι : ℝ) * δ ≤ ε) :
    ‖T‖ ≤ (|M₁| + |M₂| + (|M₃| + |M₄|)) * ε := by
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), ‖c i‖ ≤ (|M₃| + |M₄|) * δ := by
    intro i _
    have h : ‖c i‖ ≤ ‖c i - s i‖ + ‖s i‖ := by
      have h' := norm_add_le (c i - s i) (s i)
      rwa [sub_add_cancel] at h'
    have h3' : M₃ * δ ≤ |M₃| * δ := mul_le_mul_of_nonneg_right (le_abs_self M₃) hδ
    have h4' : M₄ * δ ≤ |M₄| * δ := mul_le_mul_of_nonneg_right (le_abs_self M₄) hδ
    have e : (|M₃| + |M₄|) * δ = |M₃| * δ + |M₄| * δ := by ring
    rw [e]
    linarith [h₃ i, h₄ i]
  have hsum : ‖∑ i, c i‖ ≤ (|M₃| + |M₄|) * ε :=
    calc ‖∑ i, c i‖ ≤ ∑ i, ‖c i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (|M₃| + |M₄|) * δ := Finset.sum_le_sum hterm
      _ = (Fintype.card ι : ℝ) * ((|M₃| + |M₄|) * δ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (|M₃| + |M₄|) * ((Fintype.card ι : ℝ) * δ) := by ring
      _ ≤ (|M₃| + |M₄|) * ε :=
          mul_le_mul_of_nonneg_left hN (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hT : T = (R + ∑ i, c i) - (∑ i, c i) - (R - T) := by ring
  have hT' : ‖T‖ = ‖(R + ∑ i, c i) - (∑ i, c i) - (R - T)‖ :=
    congrArg (fun z : ℂ => ‖z‖) hT
  have a1 := norm_sub_le ((R + ∑ i, c i) - (∑ i, c i)) (R - T)
  have a2 := norm_sub_le (R + ∑ i, c i) (∑ i, c i)
  have b1 : M₁ * ε ≤ |M₁| * ε := mul_le_mul_of_nonneg_right (le_abs_self M₁) hε
  have b2 : M₂ * ε ≤ |M₂| * ε := mul_le_mul_of_nonneg_right (le_abs_self M₂) hε
  have e : (|M₁| + |M₂| + (|M₃| + |M₄|)) * ε =
      |M₁| * ε + |M₂| * ε + (|M₃| + |M₄|) * ε := by ring
  rw [e]
  linarith

/-- The number of comparisons times `L^{-(A + max(C₁, 0))}` is at most `L^{-A}` when the number of
patterns (the comparisons and the raw pattern) is at most `L^{C₁}` and `L ≥ 1`. -/
theorem card_mul_rpow_le {α : Type} [Fintype α] {L C₁ : ℝ} (A : ℝ) (hL : 1 ≤ L)
    (hc : (Fintype.card (Option α) : ℝ) ≤ L ^ C₁) :
    (Fintype.card α : ℝ) * L ^ (-(A + max C₁ 0)) ≤ L ^ (-A) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hle : (Fintype.card α : ℝ) ≤ (Fintype.card (Option α) : ℝ) :=
    Nat.cast_le.mpr (by
      rw [Fintype.card_option]
      exact Nat.le_add_right _ 1)
  have hpow : L ^ C₁ ≤ L ^ max C₁ 0 := Real.rpow_le_rpow_of_exponent_le hL (le_max_left C₁ 0)
  have hc' : (Fintype.card α : ℝ) ≤ L ^ max C₁ 0 := le_trans hle (le_trans hc hpow)
  have hδ : 0 ≤ L ^ (-(A + max C₁ 0)) := Real.rpow_nonneg hL0.le _
  calc (Fintype.card α : ℝ) * L ^ (-(A + max C₁ 0))
      ≤ L ^ max C₁ 0 * L ^ (-(A + max C₁ 0)) := mul_le_mul_of_nonneg_right hc' hδ
    _ = L ^ (-A) := by
        rw [← Real.rpow_add hL0]
        congr 1
        ring

/-! ### Propositions 6.2 and 6.3 for the active groups -/

/-- **The two imported propositions at the constants of [P] §6** (`[P-06:0256–0258, 0298–0306]`).

"We use these two imported propositions with `ℓ = k = 1` and the exponents in (cor:groups)"; "Fix
the cutoff `|ζ| ≤ L` now, so `C_4 = 1` suffices in Proposition 6.3"; "Choose `E_id` from
Proposition 6.2, obtain `m_0, J_0, C_1` from Proposition 6.3, and finally choose a fixed `J`
satisfying both lower bounds."

Proposition 6.3 is applied with the precision `A₀ = 1` of the comparison contract (the contract
itself is not used in [P] §6, only the norm bound and the costs); Proposition 6.2 with `C₂ = 0`
(`|k| = 1 = L^0`), `γ = 1/2` and `C_sup = 1`. The bridge from the active groups to [S]'s prime
groups is `primeGroupsOf`; `BigIntervals` and `HalfSplitBalanced` supply the two hypotheses of
`Transference.IdealFamilyBound`. -/
theorem transferData {d : ℕ} (h62 : GraphTransferInput) (h63 : IdealFamilyInput)
    (hint : BigIntervals) (hsplit : HalfSplitBalanced) (D : FixedData) {E : ℝ} (hE : 0 < E) :
    TransferData d D E := by
  obtain ⟨Eid, hEid, h62'⟩ := h62 D.params E hE
  obtain ⟨m₀, J₁, C₁, qs, hs, xs, hqs, hhs, hxs, -, -, h63'⟩ :=
    h63 D.params Eid 1 1 hEid zero_le_one one_pos
  obtain ⟨J₀, Cabs, h62''⟩ := h62' m₀ C₁
  obtain ⟨hfam, hcnt⟩ := h63' (max J₀ J₁) (le_max_right _ _)
  have h62J := h62'' (max J₀ J₁) (le_max_left _ _)
  refine ⟨m₀, max J₀ J₁, C₁, qs, hs, xs, Cabs, hqs, hhs, hxs, ?_, ?_, ?_⟩
  · -- the number of patterns
    obtain ⟨x₀, hx₀⟩ := hcnt
    exact ⟨x₀, fun x hx I => hx₀ x hx _ _ I.primeGroups I.blocks⟩
  · -- the absolute Schur bound
    obtain ⟨-, hS⟩ := h62J 0 ((1 : ℝ) / 2) 0 1 (by norm_num)
    obtain ⟨x₁, hx₁⟩ := hS
    obtain ⟨x₂, hx₂⟩ := hfam
    refine ⟨max x₁ x₂, fun x hx I ζ s => ?_⟩
    have hmass := (hx₂ x (le_trans (le_max_right _ _) hx) _ _ I.primeGroups
      (fun g => hint D.P x I.𝔊 I.groups g) I.blocks (hsplit _)).1
    exact hx₁ x (le_trans (le_max_left _ _) hx) _ _ I.primeGroups _
      (I.family (max J₀ J₁) m₀ qs hs xs) ζ 1
      ⟨fun ν g => comparisonFamily_card_le _ _ _ _ _ _ _ _ ν g, hmass, one_ne_zero,
        le_of_eq (by rw [Int.cast_one, abs_one, Real.rpow_zero])⟩ s
  · -- the transferred pairing
    intro C₃
    obtain ⟨hP, -⟩ := h62J 0 ((1 : ℝ) / 2) C₃ 1 (by norm_num)
    obtain ⟨M, x₁, hx₁⟩ := hP
    obtain ⟨x₂, hx₂⟩ := hfam
    refine ⟨M, max x₁ x₂, fun x hx I ζ hζ X hX₁ hX₂ fn g hfg => ?_⟩
    obtain ⟨hmass, hnorm⟩ := hx₂ x (le_trans (le_max_right _ _) hx) _ _ I.primeGroups
      (fun g => hint D.P x I.𝔊 I.groups g) I.blocks (hsplit _)
    have hX₂' : X ≤ x ^ (1 / ((1 : ℝ) / 2)) := by
      have e : (1 : ℝ) / ((1 : ℝ) / 2) = 2 := by norm_num
      rw [e]
      exact hX₂
    exact hx₁ x (le_trans (le_max_left _ _) hx) _ _ I.primeGroups _
      (I.family (max J₀ J₁) m₀ qs hs xs) ζ 1
      ⟨fun ν g => comparisonFamily_card_le _ _ _ _ _ _ _ _ ν g, hmass, one_ne_zero,
        le_of_eq (by rw [Int.cast_one, abs_one, Real.rpow_zero])⟩
      (fun Θ => hnorm Θ ζ (by
        rw [Real.rpow_one]
        exact hζ)) X hX₁ hX₂' fn g hfg

/-! ### The subtraction -/

/-- **The conclusion of [P] §6** (`[P-06:0372–0377, 0927–0935]`): "The transferred estimate
therefore controls the desired correlation plus the signed comparison correlations
(cor:stripped). It remains to bound the latter separately." … "Choose that precision after the
known fixed kernel, dyad, arc, and separation costs. Their total is therefore negligible.
Subtracting these comparison terms from the residual pairing leaves its raw pattern, already
identified with (eq:two-sided)."

The stripping errors of the comparisons and the comparison bounds are used with the saving
`A + max(C₁, 0)`, which absorbs the number `≤ L^{C₁}` of comparisons. -/
theorem twoSidedBound_of_stages {d H : ℕ} {𝔅 : JointResidueWeight H} {D : FixedData}
    {m₀ J : ℕ} {C₁ qs hs xs A : ℝ}
    (hcount : PatternCountAt d D m₀ J C₁)
    (hres : ResidualBoundAt d H 𝔅 D m₀ J qs hs xs A)
    (hraw : RawStrippingAt d H 𝔅 D J A)
    (hcomp : ComparisonStrippingAt d H 𝔅 D m₀ J qs hs xs (A + max C₁ 0))
    (hstr : StrippedBoundAt d H 𝔅 D m₀ J qs hs xs (A + max C₁ 0)) :
    ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
      ‖twoSidedSum D.q D.q₀ D.𝔞 x I.𝔊 I.S 𝔅 D.Ψ I.G‖ ≤ M * Real.log x ^ (-A) := by
  obtain ⟨x₅, h₅⟩ := hcount
  obtain ⟨M₁, x₁, h₁⟩ := hres
  obtain ⟨M₂, x₂, h₂⟩ := hraw
  obtain ⟨M₃, x₃, h₃⟩ := hcomp
  obtain ⟨M₄, x₄, h₄⟩ := hstr
  refine ⟨|M₁| + |M₂| + (|M₃| + |M₄|),
    |x₁| + |x₂| + |x₃| + |x₄| + |x₅| + Real.exp 1, fun x hx I => ?_⟩
  have hx₁ : x₁ ≤ x := by
    linarith [le_abs_self x₁, abs_nonneg x₂, abs_nonneg x₃, abs_nonneg x₄, abs_nonneg x₅,
      Real.exp_pos 1]
  have hx₂ : x₂ ≤ x := by
    linarith [abs_nonneg x₁, le_abs_self x₂, abs_nonneg x₃, abs_nonneg x₄, abs_nonneg x₅,
      Real.exp_pos 1]
  have hx₃ : x₃ ≤ x := by
    linarith [abs_nonneg x₁, abs_nonneg x₂, le_abs_self x₃, abs_nonneg x₄, abs_nonneg x₅,
      Real.exp_pos 1]
  have hx₄ : x₄ ≤ x := by
    linarith [abs_nonneg x₁, abs_nonneg x₂, abs_nonneg x₃, le_abs_self x₄, abs_nonneg x₅,
      Real.exp_pos 1]
  have hx₅ : x₅ ≤ x := by
    linarith [abs_nonneg x₁, abs_nonneg x₂, abs_nonneg x₃, abs_nonneg x₄, le_abs_self x₅,
      Real.exp_pos 1]
  have hxe : Real.exp 1 ≤ x := by
    linarith [abs_nonneg x₁, abs_nonneg x₂, abs_nonneg x₃, abs_nonneg x₄, abs_nonneg x₅]
  have hL : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL
  have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0.le _
  have hLδ : 0 ≤ Real.log x ^ (-(A + max C₁ 0)) := Real.rpow_nonneg hL0.le _
  have hcard := card_mul_rpow_le A hL (h₅ x hx₅ I)
  exact norm_le_of_decomposition (twoSidedSum D.q D.q₀ D.𝔞 x I.𝔊 I.S 𝔅 D.Ψ I.G) (I.rawEdge 𝔅 J)
    (fun C : {C : Fin I.𝔊.numBig → Finset (Fin J) // IsComparison I.blocks m₀ C} =>
      I.comparisonEdge 𝔅 qs hs xs C.1)
    (fun C => I.strippedSum 𝔅 qs hs xs C.1)
    (h₁ x hx₁ I) (h₂ x hx₂ I) (fun C => h₃ x hx₃ I C.1 C.2) (fun C => h₄ x hx₄ I C.1 C.2)
    hLA hLδ hcard

/-! ### The chain -/

/-- **Theorem 6.1^{𝔅} for fixed data, from the leaves and the inputs.** The constants are chosen
in the order of `[P-06:0301–0316]`: the saving `A` and the fixed data; `C_3`; the transfer saving
`E = A + 2|C_3| + 2`; `E_id`, then `m_0, J_0, C_1` and the kernel exponents, then `J`
(`transferData`); then the residual bound. "All exponents chosen from now on may depend on the
fixed ideal family" (`[P-06:0415]`): the stripping errors and the comparison bounds are taken
with the saving `A + max(C_1, 0)`. -/
theorem twoSidedBound {d H : ℕ} {𝔅 : JointResidueWeight H} (hH : 0 < H) (L : Leaves d H 𝔅)
    (h62 : GraphTransferInput) (h63 : IdealFamilyInput) (hSM : EndpointEnergy d)
    (hM1 : MertensReciprocal) (D : FixedData) {A : ℝ} (hA : 0 < A) :
    ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
      ‖twoSidedSum D.q D.q₀ D.𝔞 x I.𝔊 I.S 𝔅 D.Ψ I.G‖ ≤ M * Real.log x ^ (-A) := by
  -- bounded factors
  have hcore : CorePowerBounded d := L.corePower hM1
  -- the comparison stage: (cor:SM) enters through the arc energy
  have hsq : EndpointSquares d := L.endpointSquares L.markedBound hcore
  have hmult : MultiplierMinor := L.multiplier L.bilinearFourier
  have harc : ArcEnergy d := L.arcEnergy L.localMellin hsq hSM
  have hbil : BilinearBound d H := L.circle hmult harc hsq
  have hcorr : ComparisonCorrelationBound d H 𝔅 := L.separation hbil hsq
  have hstripped : StrippedComparisonBound d H 𝔅 :=
    L.kernelExpansion L.bigIntervals kernelCostsLemma hcorr
  -- the transfer stage, in the order of the constants
  obtain ⟨C₃, hC₃⟩ := L.endpointNorms hcore D
  have hE : 0 < A + 2 * |C₃| + 2 := by linarith [abs_nonneg C₃]
  obtain ⟨m₀, J, C₁, qs, hs, xs, Cabs, hqs, hhs, hxs, hcount, hschur, hpair⟩ :=
    transferData (d := d) h62 h63 L.bigIntervals L.splitBalanced D hE
  have hres : ResidualBoundAt d H 𝔅 D m₀ J qs hs xs A :=
    L.insertion hH hcore D m₀ J qs hs xs (A + 2 * |C₃| + 2) C₃ Cabs A hA
      (by linarith [le_abs_self C₃]) (hpair C₃) hschur (hC₃ J)
  -- the removal of the shared labels and the comparison bounds
  have hA' : 0 < A + max C₁ 0 := by linarith [le_max_right C₁ 0]
  exact twoSidedBound_of_stages hcount hres
    (L.rawStripping hH L.coreInvariance hcore L.markedBound D J A hA)
    (L.comparisonStripping hH L.coreInvariance hcore L.markedBound D m₀ J qs hs xs hqs hhs hxs
      (A + max C₁ 0) hA')
    (hstripped hH D m₀ J qs hs xs hqs hhs hxs (A + max C₁ 0) hA')

/-- **[P] §6 with a joint residue weight, assembled**: the leaves of `Leaves d H 𝔅` give
`TwoSidedReduction d H 𝔅` for `0 < H`. The inputs of the reduction are used as follows:
Propositions 6.2 and 6.3 in `transferData`; (cor:SM) in the link `ArcEnergyLink`; Mertens'
estimate in the leaf `corePower`. -/
theorem twoSidedReduction_of_leaves {d H : ℕ} {𝔅 : JointResidueWeight H} (hH : 0 < H)
    (L : Leaves d H 𝔅) : TwoSidedReduction d H 𝔅 := by
  intro h62 h63 hSM hM1 ε hε q q₀ hq hq1 hq₀ hq₀1 K 𝔞 P C Ψ hΨ₁ hΨ₂ hΨ₃ A hA
  obtain ⟨M, x₀, h⟩ := twoSidedBound hH L h62 h63 hSM hM1
    ⟨ε, q, q₀, K, 𝔞, P, C, Ψ, hε, hq, hq1, hq₀, hq₀1, hΨ₁, hΨ₂, hΨ₃⟩ hA
  exact ⟨M, x₀, fun x hx 𝔊 h𝔊 S hS G hG => h x hx ⟨𝔊, S, G, h𝔊, hS, hG⟩⟩

/-- The reduction for the class weights `𝓑_{H,b}` of all moduli and reduced classes, for `d`
slots. -/
theorem twoSidedReductionFixedClass_of_leaves {d : ℕ}
    (L : ∀ H b : ℕ, 0 < H → b.Coprime H → Leaves d H (classWeight H b)) :
    TwoSidedReductionFixedClass d :=
  fun H b hH hb => twoSidedReduction_of_leaves hH (L H b hH hb)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
