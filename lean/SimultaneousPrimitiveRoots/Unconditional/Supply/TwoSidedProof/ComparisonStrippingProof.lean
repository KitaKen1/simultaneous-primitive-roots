module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.StripMain

/-!
# Removal of the shared labels: the comparison patterns

`comparisonStrippingLink : ComparisonStrippingLink d H 𝔅` (`[P-06:0318–0370]`,
`[PUB-tex:0482–0485]`), for every number of slots `d`, every modulus `H` and every joint residue
weight `𝔅`.

* `Strip.blockListProd_mk`: the product of the labels of a list in the freed slots of a block is
  the product `markProd` of its unshared labels ("No shared or final `ℓ` label enters these
  kernels"); `Strip.comparison_kernel_eq`: the comparison coefficient (cor:comparison-kernel) on
  a pair of lists with the same shared labels is `strippedKernel` on the unshared labels.
* `Strip.norm_kernel_le`: the pattern cost `sup |K_ν| ≤ Q⁴ ξ⁻² = L^{4q_* + 2x_*}`.
* `Strip.strippedSumOf_eq_genStrip`: `strippedSumOf` is `Strip.genStrip` for `strippedKernel`.

The estimate is `Strip.general` with `c_K = 4 q_* + 2 x_*`; `|C_g| ≤ m₀` because the freed slots
are probes.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

namespace Strip

section Comparison

variable {𝔊 : ActiveGroups} {J : ℕ} {C : Fin 𝔊.numBig → Finset (Fin J)}

/-- **The freed labels of a list are unshared labels**: the product of the labels in the freed
slots of the block `b` is `markProd` of the unshared labels. -/
theorem blockListProd_mk (blk : Fin 𝔊.numBig → Bool) (b : Bool) (σ : ShT 𝔊 C) (u : UnT 𝔊 C) :
    blockListProd blk b C ((listSplit 𝔊 C).symm (σ, u)).2 = markProd 𝔊 C blk b (unVal u) := by
  unfold blockListProd markProd
  refine Finset.prod_congr rfl fun g _ => ?_
  by_cases hb : blk g = b
  · rw [if_pos hb, if_pos hb]
    calc ∏ i ∈ C g, (((listSplit 𝔊 C).symm (σ, u)).2 g (Sum.inl i) : ℕ)
        = ∏ i : {i : Fin J // i ∈ C g},
            (((listSplit 𝔊 C).symm (σ, u)).2 g (Sum.inl i.1) : ℕ) :=
          (Finset.prod_coe_sort (C g)
            (fun i => (((listSplit 𝔊 C).symm (σ, u)).2 g (Sum.inl i) : ℕ))).symm
      _ = ∏ k : Fin (C g).card,
            (((listSplit 𝔊 C).symm (σ, u)).2 g (Sum.inl ((C g).equivFin.symm k).1) : ℕ) :=
          (Equiv.prod_comp (C g).equivFin.symm
            (fun i : {i : Fin J // i ∈ C g} =>
              (((listSplit 𝔊 C).symm (σ, u)).2 g (Sum.inl i.1) : ℕ))).symm
      _ = ∏ k : Fin (C g).card, unVal u (Sum.inr g) (Fin.castSucc k) :=
          Finset.prod_congr rfl fun k _ => by
            have h := mk_snd σ u g (Sum.inr (Fin.castSucc k))
            rw [slotEquiv_castSucc] at h
            exact congrArg Subtype.val h
  · rw [if_neg hb, if_neg hb]

/-- **The comparison coefficient on lists with the same shared labels** is the stripped
coefficient on their unshared labels (`[P-06:0211–0218]`). -/
theorem comparison_kernel_eq (𝔊 : ActiveGroups) {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J))
    (blk : Fin 𝔊.numBig → Bool) (Q h ξ : ℝ) (σ : ShT 𝔊 C) (u u' : UnT 𝔊 C)
    (r : AuxList (groupFamily 𝔊).big C) :
    (comparisonPattern (groupFamily 𝔊).big J 1 blk Q h ξ C).K
        ((listSplit 𝔊 C).symm (σ, u)).2 ((listSplit 𝔊 C).symm (σ, u')).2 r =
      strippedKernel 𝔊 C blk Q h ξ r (unVal u) (unVal u') := by
  unfold strippedKernel
  rw [← blockListProd_mk blk true σ u', ← blockListProd_mk blk false σ u]
  rfl

/-- **The pattern cost** (`[P-06:0280–0281]`): `|𝒦_A 𝒦_B| ≤ (Q² ξ⁻¹)² = L^{4q_* + 2x_*}`. -/
theorem norm_kernel_le {B : Type} [Fintype B] [DecidableEq B] {L : ℝ} (hL : 0 < L)
    (qs xs : ℝ) (big : B → Finset ℕ) (Λ₁ Λ₂ : B → Finset (Fin J)) (h : ℝ) (D₁ X₁ D₂ X₂ n : ℕ) :
    ‖-((-1 : ℂ) ^ n) * (cellKernel big Λ₁ (L ^ qs) h (L ^ (-xs)) D₁ X₁ *
        cellKernel big Λ₂ (L ^ qs) h (L ^ (-xs)) D₂ X₂)‖ ≤ L ^ (4 * qs + 2 * xs) := by
  have hξ : 0 < L ^ (-xs) := Real.rpow_pos_of_pos hL _
  have hQ : 0 ≤ L ^ qs := (Real.rpow_pos_of_pos hL _).le
  have h1 := norm_cellKernel_le big Λ₁ (L ^ qs) h (L ^ (-xs)) hξ D₁ X₁
  have h2 := norm_cellKernel_le big Λ₂ (L ^ qs) h (L ^ (-xs)) hξ D₂ X₂
  have hp := primitiveCharCount_le_sq (L ^ qs) hQ
  have hb : (primitiveCharCount (L ^ qs) : ℝ) * (L ^ (-xs))⁻¹ ≤ L ^ (2 * qs + xs) := by
    have e1 : (L ^ qs) ^ 2 = L ^ (2 * qs) := Pairing.rpow_sq_eq hL qs
    have e2 : (L ^ (-xs))⁻¹ = L ^ xs := by rw [Real.rpow_neg hL.le, inv_inv]
    rw [e2, Real.rpow_add hL, ← e1]
    exact mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hL.le _)
  have e3 : L ^ (2 * qs + xs) * L ^ (2 * qs + xs) = L ^ (4 * qs + 2 * xs) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  rw [norm_mul, norm_neg, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, ← e3]
  exact mul_le_mul (h1.trans hb) (h2.trans hb) (norm_nonneg _) (Real.rpow_nonneg hL.le _)

/-- The stripped expression (cor:stripped) of a comparison is `genStrip` for the stripped
comparison coefficient. -/
theorem strippedSumOf_eq_genStrip (𝔊 : ActiveGroups) (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K)
    (x : ℝ) {d : ℕ} (S : Fin d → Finset ℕ) {H : ℕ} (𝔅 : JointResidueWeight H) (Ψ : ℝ → ℂ)
    (G : ℕ → ℂ) {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J)) (blk : Fin 𝔊.numBig → Bool)
    (Q h ξ : ℝ) :
    strippedSumOf 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C blk Q h ξ =
      genStrip q₀ x Ψ 𝔅 (centeredCore q 𝔞 x S) G C (strippedKernel 𝔊 C blk Q h ξ) := rfl

end Comparison

end Strip

/-- **Removal of the shared labels, comparison patterns** (`[P-06:0318–0370]`; the joint factor:
`[PUB-tex:0482–0485]`): the edge sum of every comparison pattern is its stripped expression
(cor:stripped) up to `M L^{-A}`, uniformly in the comparison. -/
theorem comparisonStrippingLink (d H : ℕ) (𝔅 : JointResidueWeight H) :
    ComparisonStrippingLink d H 𝔅 := by
  intro hH hCI hCP hMB D m₀ J qs hs xs _ _ _ A _
  obtain ⟨M, x₀, h⟩ := Strip.general 𝔅 hH hCI hCP hMB D J m₀ (4 * qs + 2 * xs) A
  refine ⟨M, max x₀ 3, fun x hx I C hCmp => ?_⟩
  have hx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hx3 : (3 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := h x hx₀ I
    (comparisonPattern (groupFamily I.𝔊).big J 1 I.blocks (Real.log x ^ qs)
      (Real.log x ^ (-hs)) (Real.log x ^ (-xs)) C)
    (strippedKernel I.𝔊 C I.blocks (Real.log x ^ qs) (Real.log x ^ (-hs))
      (Real.log x ^ (-xs)))
    (fun g => (Finset.card_le_card (hCmp.1 g)).trans (card_probeSlots_le J m₀))
    (fun σ u u' r => Strip.comparison_kernel_eq I.𝔊 C I.blocks _ _ _ σ u u' r)
    (fun _ _ _ => Strip.norm_kernel_le hL0 qs xs _ _ _ _ _ _ _ _ _)
    (fun _ _ _ => Strip.norm_kernel_le hL0 qs xs _ _ _ _ _ _ _ _ _)
  have e : I.strippedSum 𝔅 qs hs xs C =
      Strip.genStrip D.q₀ x D.Ψ 𝔅 (centeredCore D.q D.𝔞 x I.S) I.G C
        (strippedKernel I.𝔊 C I.blocks (Real.log x ^ qs) (Real.log x ^ (-hs))
          (Real.log x ^ (-xs))) := rfl
  rw [e]
  exact h1

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
