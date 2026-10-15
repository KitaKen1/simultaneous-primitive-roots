module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.StripMain

/-!
# Removal of the shared labels: the raw pattern

`rawStrippingLink : RawStrippingLink d H 𝔅` (`[P-06:0318–0370]`, `[PUB-tex:0482–0485]`), for every
number of slots `d`, every modulus `H` and every joint residue weight `𝔅`.

"For the raw pattern, `D_C = 1` and `t_g = 1`, so (cor:stripped) is precisely the left side of
(eq:two-sided)": `Strip.genStrip_raw` identifies the stripped expression `Strip.genStrip` of the
raw pattern (`C_g = ∅`, `K_0 = 1`) with `twoSidedSum`; the estimate is `Strip.general` with
`m₀ = 0` and `c_K = 0`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

namespace Strip

/-- For `t = (1, …, 1)` the scalar factor of `W_𝐭` times the number of represented lists is the
active one-mark weight `W_1`. -/
theorem coeff_card_eq_oneMark (𝔊 : ActiveGroups) (q₀ : ℝ) {t : 𝔊.Index → ℕ}
    (ht : t = fun _ => 1) (n : ℕ) :
    ((activeCoeff 𝔊 q₀ t n : ℝ) : ℂ) * (((𝔊.representedLists t n).card : ℕ) : ℂ) =
      𝔊.oneMark q₀ n := by
  subst ht
  unfold ActiveGroups.oneMark
  rw [activeWeight_eq_activeCoeff, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The stripped expression of the raw pattern is the two-sided sum** (eq:two-sided)
(`[P-06:0368–0370]`): no free label (`D_C = 1`), one unshared label in every group (`t_g = 1`),
coefficient `1`. -/
theorem genStrip_raw (𝔊 : ActiveGroups) (J : ℕ) (q₀ x : ℝ) (Ψ : ℝ → ℂ) {H : ℕ}
    (𝔅 : JointResidueWeight H) (q : ℝ) {K : ℕ} (𝔞 : MarkingArray K) {d : ℕ}
    (S : Fin d → Finset ℕ) (G : ℕ → ℂ) :
    genStrip q₀ x Ψ 𝔅 (centeredCore q 𝔞 x S) G
        (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))) (fun _ _ _ => 1) =
      twoSidedSum q q₀ 𝔞 x 𝔊 S 𝔅 Ψ G := by
  have hr : ∀ r : AuxList (groupFamily 𝔊).big (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))),
      tupleProd (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))) r = 1 := fun r => by
    unfold tupleProd
    exact Finset.prod_eq_one fun g _ => Finset.prod_eq_one fun i _ =>
      absurd i.2 (Finset.notMem_empty _)
  have haux : ∀ r : AuxList (groupFamily 𝔊).big (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))),
      auxWeight (groupFamily 𝔊).big (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))) r = 1 :=
    fun r => by
      unfold auxWeight
      exact Finset.prod_eq_one fun g _ => Finset.prod_eq_one fun i _ =>
        absurd i.2 (Finset.notMem_empty _)
  have ht : markCount 𝔊 (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))) = fun _ => 1 := by
    funext g
    rcases g with g | g
    · rfl
    · rfl
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : AuxList (groupFamily 𝔊).big
      (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))), ∀ r, r = r₀ :=
    ⟨fun g i => (Finset.notMem_empty _ i.2).elim,
      fun r => funext fun g => funext fun i => (Finset.notMem_empty _ i.2).elim⟩
  have hterm : ∀ w : ℕ,
      corePart x Ψ 𝔅 (centeredCore q 𝔞 x S) G
          (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))) r₀ w *
        ((activeCoeff 𝔊 q₀ (markCount 𝔊 (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J)))) w *
          activeCoeff 𝔊 q₀ (markCount 𝔊 (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))))
            (w + tupleProd (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))) r₀) : ℝ) : ℂ) *
        ∑ _𝔭 ∈ 𝔊.representedLists
            (markCount 𝔊 (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J)))) w,
          ∑ _𝔭' ∈ 𝔊.representedLists
              (markCount 𝔊 (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))))
              (w + tupleProd (fun _ : Fin 𝔊.numBig => (∅ : Finset (Fin J))) r₀), (1 : ℂ) =
      Ψ ((w : ℝ) / x) / (w : ℂ) *
        ((𝔅.toFun (w : ZMod H) ((w + 1 : ℕ) : ZMod H) : ℝ) : ℂ) *
        ((centeredCore q 𝔞 x S w : ℝ) : ℂ) * G (w + 1) * 𝔊.oneMark q₀ w *
        𝔊.oneMark q₀ (w + 1) := by
    intro w
    rw [← coeff_card_eq_oneMark 𝔊 q₀ ht w, ← coeff_card_eq_oneMark 𝔊 q₀ ht (w + 1)]
    unfold corePart
    rw [hr r₀, Nat.cast_one, mul_one]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    push_cast
    ring
  unfold genStrip
  rw [Fintype.sum_eq_single r₀ (fun r hr' => absurd (hr₀ r) hr'), haux r₀, Complex.ofReal_one,
    one_mul]
  unfold twoSidedSum
  exact finsum_congr hterm

end Strip

/-- **Removal of the shared labels, raw pattern** (`[P-06:0318–0370]`; the joint factor:
`[PUB-tex:0482–0485]`): the edge sum of the raw pattern is the two-sided sum (eq:two-sided) up to
`M L^{-A}`. -/
theorem rawStrippingLink (d H : ℕ) (𝔅 : JointResidueWeight H) : RawStrippingLink d H 𝔅 := by
  intro hH hCI hCP hMB D J A _
  obtain ⟨M, x₀, h⟩ := Strip.general 𝔅 hH hCI hCP hMB D J 0 0 A
  refine ⟨M, x₀, fun x hx I => ?_⟩
  have h1 := h x hx I (Pattern.raw (groupFamily I.𝔊).big J 1) (fun _ _ _ => 1)
    (fun g => le_of_eq Finset.card_empty) (fun _ _ _ _ => rfl)
    (fun _ _ _ => by
      rw [Real.rpow_zero]
      exact le_of_eq norm_one)
    (fun _ _ _ => by
      rw [Real.rpow_zero]
      exact le_of_eq norm_one)
  have e := Strip.genStrip_raw I.𝔊 J D.q₀ x D.Ψ 𝔅 D.q D.𝔞 I.S I.G
  rw [← e]
  exact h1

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
