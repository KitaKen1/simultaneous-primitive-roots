module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.SeparationTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.MellinSeparationProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.CircleProof

/-!
# Cutoffs, the Fourier inversion in logarithmic size and the residue partition

`separationLink d H 𝔅 : SeparationLink d H 𝔅`, i.e. `BilinearBound d H → EndpointSquares d →
ComparisonCorrelationBound d H 𝔅` (`[P-06:0391–0415]`, `[PUB-tex:0487–0495]`), for every number
of slots, every modulus and every joint residue weight.

"Insert fixed smooth cutoffs at scale `Y` at both endpoints. Fourier inversion in logarithmic
size separates `Ψ(w/(x D_A D_B))/w` as in (cor:insertion-separation). After a factor `1/Y`, it is
enough to estimate combinations of (cor:comparison-sum) … These estimates also bound the
separated Fourier tails absolutely". With the weight: "Partition each free tuple by its residue
modulo `H`. These bounded tests preserve the endpoint hypotheses. On each part the shift
`d mod H` is fixed, and (eq:B-shift) leaves a fixed residue condition on the first endpoint."

Fixed data: the support `[c₁, c₂] ⊂ (0, ∞)` of `Ψ` and its Mellin density `w`
(`mellinSeparationComplex`); the cutoffs `ψ₁(u) = 1/u`, `ψ₂(u) = 1` on `[c₁, (c₂ + 1)e²]`,
supported in `[a₁, a₂] = [c₁/2, (c₂ + 1)e² + 1]`, with derivative exponents
`Dψ j = max(log B_j, 0)` (`Separation.exists_cutoffs`, `Separation.le_rpow_max_log`); `C₅` from
(cor:endpoint-squares); the decay order `N = ⌈A + max(C₅, 0)⌉` of the density; the bilinear
bound with the twist exponent `Cσ = 1` and the saving `A`.

For `x ≥ x₀`, `Y = x U₁ U₂`, `L = log x`:

* the correlation is a finite sum over `1 ≤ w ≤ a₂ Y` (`Separation.sum_finsum_eq_sum`), and the
  weight `𝔅(w, w + D_A D_B)` is the combination `∑_j cf(D_A D_B mod H, j) e(jw/H)`
  (`Separation.exists_char_coeff`), so the correlation is a combination of at most `H³` twisted
  correlations with the tests `b₁ 1_{D_A ≡ a₁}`, `b₂ 1_{D_B ≡ a₂}` (`Separation.residue_expansion`);
* each twisted correlation is `Y⁻¹ ∫ w(v) x^{-iv} (bilinear sum with the tests
  `b₁ D_A^{-iv}`, `b₂ D_B^{-iv}` and the twist `σ = v`) dv` (`Separation.twisted_bound`,
  `Separation.norm_twisted_le`): for `|v| ≤ L` the bilinear bound applies, and for all `v` the
  trivial bound `Y L^{C₅}` (`Separation.norm_bilinear_le`).

The constant is `H³ (max(M, 0) + 1) C_w π`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Separation

/-! ### Tests, sums and correlations -/

/-- **A block test times a bounded function of the free product of its block is a block test**
with the same cell ("These bounded tests preserve the endpoint hypotheses"). -/
theorem blockTest_mul {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {big : B → Finset ℕ}
    {blk : B → Bool} {b : Bool} {C : B → Finset (Fin J)} {β : AuxList big C → ℂ} {U : ℝ}
    (hβ : BlockTest blk b C β U) (φ : ℕ → ℂ) (hφ : ∀ n, ‖φ n‖ ≤ 1) :
    BlockTest blk b C (fun r => β r * φ (blockAuxProd blk b C r)) U where
  bound := fun r => by
    have h := mul_le_mul (hβ.bound r) (hφ (blockAuxProd blk b C r)) (norm_nonneg _) zero_le_one
    rw [one_mul] at h
    show ‖β r * φ (blockAuxProd blk b C r)‖ ≤ 1
    rw [norm_mul]
    exact h
  depends := fun r r' hrr => by
    have hprod : blockAuxProd blk b C r = blockAuxProd blk b C r' := by
      unfold blockAuxProd
      refine Finset.prod_congr rfl fun g _ => ?_
      by_cases hg : blk g = b
      · rw [if_pos hg, if_pos hg, hrr g hg]
      · rw [if_neg hg, if_neg hg]
    show β r * φ (blockAuxProd blk b C r) = β r' * φ (blockAuxProd blk b C r')
    rw [hprod, hβ.depends r r' hrr]
  cell := fun r hne =>
    hβ.cell r (left_ne_zero_of_mul (show β r * φ (blockAuxProd blk b C r) ≠ 0 from hne))

/-- The bilinear sum as a finite sum over a set that contains the support of the first
sequence. -/
theorem bilinearSum_eq_sum {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} (big : B → Finset ℕ)
    (C : B → Finset (Fin J)) (b : AuxList big C → ℂ) {U : ℕ → ℂ} (V : ℕ → ℂ) {sw : Finset ℕ}
    (hU : ∀ w, U w ≠ 0 → w ∈ sw) :
    bilinearSum big C b U V = ∑ r : AuxList big C, ((auxWeight big C r : ℝ) : ℂ) * b r *
      ∑ w ∈ sw, U w * V (w + tupleProd C r) := by
  unfold bilinearSum
  refine Finset.sum_congr rfl fun r _ => ?_
  have hsub : Function.support (fun w : ℕ => U w * V (w + tupleProd C r)) ⊆ ↑sw := by
    intro w hw
    rw [Function.mem_support] at hw
    exact Finset.mem_coe.mpr (hU w fun h' => hw (by rw [h', zero_mul]))
  rw [finsum_eq_sum_of_support_subset _ hsub]

/-- A weighted sum of sums over `ℕ` is a finite sum, when the terms with a nonzero weight are
supported in a finite set. -/
theorem sum_finsum_eq_sum {R : Type*} [Fintype R] (c : R → ℂ) (f : R → ℕ → ℂ) (sw : Finset ℕ)
    (h : ∀ r, c r ≠ 0 → ∀ w, f r w ≠ 0 → w ∈ sw) :
    ∑ r, c r * ∑ᶠ w : ℕ, f r w = ∑ r, c r * ∑ w ∈ sw, f r w := by
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hc : c r = 0
  · rw [hc, zero_mul, zero_mul]
  · have hsub : Function.support (fun w : ℕ => f r w) ⊆ ↑sw := fun w hw =>
      Finset.mem_coe.mpr (h r hc w hw)
    rw [finsum_eq_sum_of_support_subset _ hsub]

/-- The comparison correlation of a test that vanishes identically is zero. -/
theorem comparisonCorrelationOf_eq_zero (𝔊 : ActiveGroups) (q q₀ : ℝ) {K : ℕ}
    (𝔞 : MarkingArray K) (x : ℝ) {d : ℕ} (S : Fin d → Finset ℕ) {H : ℕ}
    (𝔅 : JointResidueWeight H) (Ψ : ℝ → ℂ) (G : ℕ → ℂ) {J : ℕ}
    (C : Fin 𝔊.numBig → Finset (Fin J)) {b : AuxList (groupFamily 𝔊).big C → ℂ}
    (h : ∀ r, b r = 0) (test₁ test₂ : ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ) :
    comparisonCorrelationOf 𝔊 q q₀ 𝔞 x S 𝔅 Ψ G C b test₁ test₂ = 0 := by
  unfold comparisonCorrelationOf
  exact Finset.sum_eq_zero fun r _ => by rw [h r, mul_zero, zero_mul]

/-- The powers of `L` and the factor `1/Y` in the separation. -/
theorem sep_final {L A C₅ MB Cd Y : ℝ} {N : ℕ} (hL : 1 ≤ L) (hY : 0 < Y)
    (hN : A + C₅ ≤ (N : ℝ)) (hCd : 0 ≤ Cd) :
    Y⁻¹ * ((MB * Y * L ^ (-A) + Y * L ^ C₅ * (L ^ N)⁻¹) * (Cd * Real.pi)) ≤
      (MB + 1) * (Cd * Real.pi) * L ^ (-A) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hp : L ^ C₅ * (L ^ N)⁻¹ ≤ L ^ (-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hL0.le, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hYi : Y⁻¹ * Y = 1 := inv_mul_cancel₀ hY.ne'
  have hK : 0 ≤ Cd * Real.pi := mul_nonneg hCd Real.pi_pos.le
  have e : Y⁻¹ * ((MB * Y * L ^ (-A) + Y * L ^ C₅ * (L ^ N)⁻¹) * (Cd * Real.pi)) =
      (MB * L ^ (-A) + L ^ C₅ * (L ^ N)⁻¹) * (Cd * Real.pi) := by
    linear_combination (MB * L ^ (-A) + L ^ C₅ * (L ^ N)⁻¹) * (Cd * Real.pi) * hYi
  have h2 : MB * L ^ (-A) + L ^ C₅ * (L ^ N)⁻¹ ≤ (MB + 1) * L ^ (-A) := by linarith
  rw [e]
  calc (MB * L ^ (-A) + L ^ C₅ * (L ^ N)⁻¹) * (Cd * Real.pi)
      ≤ (MB + 1) * L ^ (-A) * (Cd * Real.pi) := mul_le_mul_of_nonneg_right h2 hK
    _ = (MB + 1) * (Cd * Real.pi) * L ^ (-A) := by ring

/-! ### A twisted correlation without the weight -/

/-- **A twisted correlation with separated tests** (`[P-06:0391–0400]`): the correlation with
the additive twist `e(jw/H)` and without the residue weight is `Y⁻¹` times a Mellin integral of
bilinear sums (cor:comparison-sum) with the cutoffs `ψ₁`, `ψ₂` at the scale `Y = x U₁ U₂`, the
twists `w^{iv}` and the tests `β₁ D_A^{-iv}`, `β₂ D_B^{-iv}`.

`Fc W₁` and `Gc W₂` are the values of the two endpoints; `hBB` is the bilinear bound for
`|σ| ≤ L`, and `hsqU`, `hsqV` the square sums of the two endpoint sequences. -/
theorem twisted_bound {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {big : B → Finset ℕ}
    (hbig : ∀ g, ∀ p ∈ big g, 0 < p)
    (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1) (blk : B → Bool)
    (C : B → Finset (Fin J)) {H : ℕ} (j : ℕ) {x U₁ U₂ : ℝ} (hx : 1 ≤ x) (hU₁ : 1 ≤ U₁)
    (hU₂ : 1 ≤ U₂) (Fc W₁ Gc W₂ : ℕ → ℂ) {Ψ ψ₁ ψ₂ : ℝ → ℂ} {a₁ a₂ c₁ c₂ : ℝ} (ha₁ : 0 < a₁)
    (hc₁ : 0 < c₁) (hψ₁s : Function.support ψ₁ ⊆ Set.Icc a₁ a₂)
    (hψ₂s : Function.support ψ₂ ⊆ Set.Icc a₁ a₂)
    (hψeq : ∀ u : ℝ, c₁ ≤ u → u ≤ (c₂ + 1) * (Real.exp 1 * Real.exp 1) →
      ψ₁ u = ((u⁻¹ : ℝ) : ℂ) ∧ ψ₂ u = 1)
    (hsup : ∀ t, Ψ t ≠ 0 → c₁ ≤ t ∧ t ≤ c₂) {wd : ℝ → ℂ} (hwd : Continuous wd) {N : ℕ}
    {Cd : ℝ} (hdecay : ∀ v, ‖wd v‖ * (1 + |v|) ^ (N + 2) ≤ Cd)
    (hinv : ∀ t : ℝ, 0 < t → Ψ t = ∫ v, wd v * (t : ℂ) ^ ((v : ℂ) * Complex.I))
    {L B₁ B₂ : ℝ} (hL : 1 ≤ L) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hBB : ∀ β₁ β₂ : AuxList big C → ℂ, BlockTest blk true C β₁ U₁ →
      BlockTest blk false C β₂ U₂ → ∀ σ : ℝ, |σ| ≤ L →
      ‖bilinearSum big C (fun r => β₁ r * β₂ r)
          (fun w => ψ₁ ((w : ℝ) / (x * U₁ * U₂)) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * Fc w *
            W₁ w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)))
          (fun v => ψ₂ ((v : ℝ) / (x * U₁ * U₂)) * Gc v * W₂ v)‖ ≤ B₁)
    (hsqU : ∀ σ : ℝ, ∑ᶠ w : ℕ, ‖ψ₁ ((w : ℝ) / (x * U₁ * U₂)) *
        (w : ℂ) ^ ((σ : ℂ) * Complex.I) * Fc w * W₁ w‖ ^ 2 ≤ B₂)
    (hsqV : ∑ᶠ v : ℕ, ‖ψ₂ ((v : ℝ) / (x * U₁ * U₂)) * Gc v * W₂ v‖ ^ 2 ≤ B₂)
    {β₁ β₂ : AuxList big C → ℂ} (hβ₁ : BlockTest blk true C β₁ U₁)
    (hβ₂ : BlockTest blk false C β₂ U₂) :
    ‖∑ r : AuxList big C, ((auxWeight big C r : ℝ) : ℂ) * (β₁ r * β₂ r) *
        ∑ w ∈ Finset.Icc 1 ⌊a₂ * (x * U₁ * U₂)⌋₊,
          Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
            addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) * (Fc w * W₁ w) *
            (Gc (w + tupleProd C r) * W₂ (w + tupleProd C r))‖ ≤
      (x * U₁ * U₂)⁻¹ * ((B₁ + B₂ * (L ^ N)⁻¹) * (Cd * Real.pi)) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hY : 0 < x * U₁ * U₂ := mul_pos (mul_pos hx0 (by linarith)) (by linarith)
  -- the supports of the two sequences
  have hUs : ∀ (σ : ℝ) (w : ℕ), ψ₁ ((w : ℝ) / (x * U₁ * U₂)) *
      (w : ℂ) ^ ((σ : ℂ) * Complex.I) * Fc w * W₁ w *
        addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) ≠ 0 →
      w ∈ Finset.Icc 1 ⌊a₂ * (x * U₁ * U₂)⌋₊ := by
    intro σ w hw
    have hψw : ψ₁ ((w : ℝ) / (x * U₁ * U₂)) ≠ 0 := by
      intro h'
      apply hw
      rw [h', zero_mul, zero_mul, zero_mul, zero_mul]
    exact Finset.mem_Icc.mpr (cutoff_range ha₁ hY hψ₁s hψw)
  have hVs : ∀ v : ℕ, ψ₂ ((v : ℝ) / (x * U₁ * U₂)) * Gc v * W₂ v ≠ 0 →
      v ∈ Finset.Icc 1 ⌊a₂ * (x * U₁ * U₂)⌋₊ := by
    intro v hv
    have hψv : ψ₂ ((v : ℝ) / (x * U₁ * U₂)) ≠ 0 := by
      intro h'
      apply hv
      rw [h', zero_mul, zero_mul]
    exact Finset.mem_Icc.mpr (cutoff_range ha₁ hY hψ₂s hψv)
  have hph : ∀ (v : ℝ) (n : ℕ), ‖phase v (-Real.log (n : ℝ))‖ ≤ 1 := fun v n =>
    le_of_eq (norm_phase _ _)
  refine norm_twisted_le (auxWeight big C) β₁ β₂ (blockAuxProd blk true C)
    (blockAuxProd blk false C) (tupleProd C) (blockAuxProd_pos hbig blk true C)
    (blockAuxProd_pos hbig blk false C) (tupleProd_eq_blockAuxProd_mul blk C)
    (Finset.Icc 1 ⌊a₂ * (x * U₁ * U₂)⌋₊) (fun w hw => (Finset.mem_Icc.mp hw).1) hx0 hY hwd
    hdecay hinv
    (fun v w => ψ₁ ((w : ℝ) / (x * U₁ * U₂)) * (w : ℂ) ^ ((v : ℂ) * Complex.I) * Fc w * W₁ w *
      addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)))
    (fun w => ψ₁ ((w : ℝ) / (x * U₁ * U₂)) * (Fc w * W₁ w) *
      addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)))
    (fun v => ψ₂ ((v : ℝ) / (x * U₁ * U₂)) * Gc v * W₂ v)
    (fun r w => Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
      addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) * (Fc w * W₁ w) *
      (Gc (w + tupleProd C r) * W₂ (w + tupleProd C r)))
    (fun v w _ => by ring) ?_ hL hB₁ hB₂ ?_ ?_
  · -- the two cutoffs where `Ψ` and the tests do not vanish
    intro r w _
    by_cases hβ : β₁ r * β₂ r = 0
    · rw [hβ]
      ring
    by_cases hΨ0 : Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0
    · rw [hΨ0]
      ring
    obtain ⟨hA1, hA2⟩ := hβ₁.cell r (left_ne_zero_of_mul hβ)
    obtain ⟨hB1, hB2⟩ := hβ₂.cell r (right_ne_zero_of_mul hβ)
    obtain ⟨h1, h2⟩ := hsup _ hΨ0
    have hDr : ((tupleProd C r : ℕ) : ℝ) =
        (blockAuxProd blk true C r : ℝ) * (blockAuxProd blk false C r : ℝ) := by
      rw [tupleProd_eq_blockAuxProd_mul blk C r, Nat.cast_mul]
    rw [hDr] at h1 h2
    obtain ⟨f1, f2, f3, f4⟩ := cut_range hx hU₁ hU₂ hA1 hA2 hB1 hB2 hc₁ h1 h2
    have hψ₁v : ψ₁ ((w : ℝ) / (x * U₁ * U₂)) = ((x * U₁ * U₂ : ℝ) : ℂ) / (w : ℂ) := by
      rw [(hψeq _ f1 f2).1]
      push_cast
      rw [inv_div]
    have hψ₂v : ψ₂ (((w + tupleProd C r : ℕ) : ℝ) / (x * U₁ * U₂)) = 1 := by
      rw [Nat.cast_add, hDr]
      exact (hψeq _ f3 f4).2
    rw [hψ₁v, hψ₂v]
    ring
  · -- the bilinear bound for `|v| ≤ L`
    intro v hv
    have h1 := hBB _ _ (blockTest_mul hβ₁ (fun n => phase v (-Real.log (n : ℝ))) (hph v))
      (blockTest_mul hβ₂ (fun n => phase v (-Real.log (n : ℝ))) (hph v)) v hv
    rw [bilinearSum_eq_sum big C _ _ (hUs v)] at h1
    exact h1
  · -- the trivial bound for all `v`
    intro v
    have hEU : ∑ᶠ w : ℕ, ‖ψ₁ ((w : ℝ) / (x * U₁ * U₂)) * (w : ℂ) ^ ((v : ℂ) * Complex.I) *
        Fc w * W₁ w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))‖ ^ 2 ≤ B₂ := by
      have e : (fun w : ℕ => ‖ψ₁ ((w : ℝ) / (x * U₁ * U₂)) *
            (w : ℂ) ^ ((v : ℂ) * Complex.I) * Fc w * W₁ w *
              addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))‖ ^ 2) =
          fun w : ℕ => ‖ψ₁ ((w : ℝ) / (x * U₁ * U₂)) *
            (w : ℂ) ^ ((v : ℂ) * Complex.I) * Fc w * W₁ w‖ ^ 2 :=
        funext fun w => by rw [norm_mul, EndpointProof.norm_addChar, mul_one]
      rw [e]
      exact hsqU v
    have h1 : ‖bilinearSum big C
        (fun r => β₁ r * phase v (-Real.log (blockAuxProd blk true C r : ℝ)) *
          (β₂ r * phase v (-Real.log (blockAuxProd blk false C r : ℝ))))
        (fun w => ψ₁ ((w : ℝ) / (x * U₁ * U₂)) * (w : ℂ) ^ ((v : ℂ) * Complex.I) * Fc w *
          W₁ w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)))
        (fun v => ψ₂ ((v : ℝ) / (x * U₁ * U₂)) * Gc v * W₂ v)‖ ≤ (B₂ + B₂) / 2 :=
      norm_bilinear_le (auxWeight big C) (fun r => Schur.auxWeight_nonneg big C r)
        (le_of_eq (sum_auxWeight hlaw C))
        (fun r => β₁ r * phase v (-Real.log (blockAuxProd blk true C r : ℝ)) *
          (β₂ r * phase v (-Real.log (blockAuxProd blk false C r : ℝ))))
        (fun r => by
          have h := mul_le_mul
            ((blockTest_mul hβ₁ (fun n => phase v (-Real.log (n : ℝ))) (hph v)).bound r)
            ((blockTest_mul hβ₂ (fun n => phase v (-Real.log (n : ℝ))) (hph v)).bound r)
            (norm_nonneg _) zero_le_one
          rw [one_mul] at h
          rw [norm_mul]
          exact h)
        (tupleProd C) (Finset.Icc 1 ⌊a₂ * (x * U₁ * U₂)⌋₊) (hUs v) hVs hEU hsqV
    rw [bilinearSum_eq_sum big C _ _ (hUs v)] at h1
    exact h1.trans (le_of_eq (by ring))

end Separation

/-! ### The statement -/

/-- **Cutoffs, the Fourier inversion in logarithmic size and the residue partition**
(`[P-06:0391–0415]`, `[PUB-tex:0487–0495]`). This is the field `separation` of
`OpenLeaves d H 𝔅`. -/
theorem separationLink (d H : ℕ) (𝔅 : JointResidueWeight H) : SeparationLink d H 𝔅 := by
  intro hBB hES hH D m₀ A hA
  have : NeZero H := ⟨hH.ne'⟩
  -- the cutoff of the correlation, its Mellin density and the two endpoint cutoffs
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hsup⟩ := MellinSep.exists_support_bounds D.compact D.support
  obtain ⟨wd, hwdc, hwdd, hwdinv⟩ := mellinSeparationComplex D.Ψ D.smooth D.compact D.support
  obtain ⟨ψ₁, ψ₂, Bψ, hψ₁c, hψ₂c, hψ₁s, hψ₂s, hψ₁B, hψ₂B, hψeq⟩ :=
    Separation.exists_cutoffs (c₂ := (c₂ + 1) * (Real.exp 1 * Real.exp 1)) hc₁
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hee : 1 ≤ Real.exp 1 * Real.exp 1 := one_le_mul_of_one_le_of_one_le he1 he1
  have ha₁ : 0 < c₁ / 2 := by linarith
  have ha₁₂ : c₁ / 2 ≤ (c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1 := by
    have h : c₂ + 1 ≤ (c₂ + 1) * (Real.exp 1 * Real.exp 1) :=
      le_mul_of_one_le_right (by linarith) hee
    linarith
  -- the constants
  obtain ⟨C₅, xE, hE⟩ := hES D (m₀ + 1) (c₁ / 2) ((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) ha₁
    ha₁₂ (max (Real.log (Bψ 0)) 0)
  obtain ⟨Cd, hCd⟩ := hwdd (⌈A + max C₅ 0⌉₊ + 2)
  have hCd0 : 0 ≤ Cd := by
    have h0 := hCd 0
    rw [abs_zero, add_zero, one_pow, mul_one] at h0
    exact (norm_nonneg _).trans h0
  obtain ⟨MB, xB, hB⟩ := hBB hH D m₀ (c₁ / 2) ((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) ha₁
    ha₁₂ (fun j => max (Real.log (Bψ j)) 0) 1 A hA
  have hA1 : ∀ᶠ L : ℝ in atTop, ‖Real.log L‖ ≤ 1 * ‖L ^ (0.19 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.19)).def one_pos
  have hD1 : ∀ᶠ L : ℝ in atTop, |2 * (m₀ : ℝ) * D.P.C₀| ≤ L ^ (0.35 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.35)).eventually_ge_atTop _
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (hA1.and hD1))
  have hM0 : 0 ≤ (H : ℝ) ^ 3 * ((max MB 0 + 1) * (Cd * Real.pi)) :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg H) 3)
      (mul_nonneg (add_nonneg (le_max_right _ _) zero_le_one)
        (mul_nonneg hCd0 Real.pi_pos.le))
  refine ⟨(H : ℝ) ^ 3 * ((max MB 0 + 1) * (Cd * Real.pi)),
    max (max xE xB) (max x₁ (Real.exp (Real.exp 1))), ?_⟩
  intro x hx I J C hC b₁ b₂ U₁ U₂ hU₁ hU₂ hb₁ hb₂ test₁ test₂ ht₁ ht₂
  -- the thresholds
  have hxE : xE ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxB : xB ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxe : Real.exp (Real.exp 1) ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hx1 : 1 ≤ x := (Real.one_le_exp (Real.exp_pos 1).le).trans hxe
  have hLe : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL1 : 1 ≤ Real.log x := he1.trans hLe
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hL1' : 1 < Real.log x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) hLe
  obtain ⟨hlogL, hc₂L⟩ := hx₁ x hxx₁
  have hLm0 : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0.le _
  have hcc : I.comparisonCorrelation 𝔅 C (fun r => b₁ r * b₂ r) test₁ test₂ =
      comparisonCorrelationOf I.𝔊 D.q D.q₀ D.𝔞 x I.S 𝔅 D.Ψ I.G C (fun r => b₁ r * b₂ r)
        test₁ test₂ := rfl
  rw [hcc]
  -- a vanishing test
  by_cases hz₁ : ∀ r, b₁ r = 0
  · rw [Separation.comparisonCorrelationOf_eq_zero I.𝔊 D.q D.q₀ D.𝔞 x I.S 𝔅 D.Ψ I.G C
      (b := fun r => b₁ r * b₂ r) (fun r => by
        show b₁ r * b₂ r = 0
        rw [hz₁ r, zero_mul]), norm_zero]
    exact mul_nonneg hM0 hLm0
  by_cases hz₂ : ∀ r, b₂ r = 0
  · rw [Separation.comparisonCorrelationOf_eq_zero I.𝔊 D.q D.q₀ D.𝔞 x I.S 𝔅 D.Ψ I.G C
      (b := fun r => b₁ r * b₂ r) (fun r => by
        show b₁ r * b₂ r = 0
        rw [hz₂ r, mul_zero]), norm_zero]
    exact mul_nonneg hM0 hLm0
  obtain ⟨r₁, hr₁⟩ := not_forall.mp hz₁
  obtain ⟨r₂, hr₂⟩ := not_forall.mp hz₂
  -- the groups and the scale
  have hbig : ∀ g, ∀ p ∈ (groupFamily I.𝔊).big g, 0 < p := fun g p hp =>
    (I.groups.prime (Sum.inr g) p hp).pos
  have hlaw : ∀ g, ∑ q ∈ (groupFamily I.𝔊).big g,
      Graph.primeGroupLaw ((groupFamily I.𝔊).big g) q = 1 := fun g =>
    I.primeGroups.big_law_sum g
  have hCm : ∀ g, (C g).card ≤ m₀ := fun g =>
    (Finset.card_le_card (hC.1 g)).trans (card_probeSlots_le J m₀)
  have hprime : ∀ (g : Fin I.𝔊.numBig) (p : ℕ), p ∈ (groupFamily I.𝔊).big g →
      Real.log x ^ (0 : ℝ) ≤ (p : ℝ) := fun g p hp => by
    rw [Real.rpow_zero]
    exact Nat.one_le_cast.mpr (hbig g p hp)
  obtain ⟨-, -, hup₁⟩ := cell_scale I hL0 hCm hC.2.1 hb₁ hr₁ hprime
  obtain ⟨-, -, hup₂⟩ := cell_scale I hL0 hCm hC.2.2 hb₂ hr₂ hprime
  have hUU1 : 1 ≤ U₁ * U₂ := one_le_mul_of_one_le_of_one_le hU₁ hU₂
  have hY0 : 0 < x * U₁ * U₂ := by
    rw [mul_assoc]
    exact mul_pos hx0 (lt_of_lt_of_le one_pos hUU1)
  have hxY : x ≤ x * U₁ * U₂ := by
    rw [mul_assoc]
    exact le_mul_of_one_le_right hx0.le hUU1
  have hY2 : x * U₁ * U₂ ≤ x * Real.exp (2 * (m₀ : ℝ) * D.P.C₀ * Real.log x ^ (0.46 : ℝ) *
      Real.log (Real.log x)) := by
    have e : 2 * (m₀ : ℝ) * D.P.C₀ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) =
        (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) +
          (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) := by ring
    rw [e, Real.exp_add, mul_assoc x U₁ U₂]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hup₁ hup₂ (by linarith) (Real.exp_pos _).le) hx0.le
  have hYx2 : x * U₁ * U₂ ≤ x ^ (2 : ℝ) := scale_le_sq hx0 hL1' hlogL hc₂L hY2
  -- the two endpoints and their cutoffs
  have hmark : ∀ g, markCount I.𝔊 C g ≤ m₀ + 1 := by
    intro g
    cases g with
    | inl i => exact Nat.le_add_left 1 m₀
    | inr k => exact Nat.add_le_add_right (hCm k) 1
  have hcut₁ : CutoffAt (c₁ / 2) ((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1)
      (fun j => max (Real.log (Bψ j)) 0) x ψ₁ :=
    ⟨hψ₁c, hψ₁s, fun j u => Separation.le_rpow_max_log hLe (hψ₁B j u)⟩
  have hcut₂ : CutoffAt (c₁ / 2) ((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1)
      (fun j => max (Real.log (Bψ j)) 0) x ψ₂ :=
    ⟨hψ₂c, hψ₂s, fun j u => Separation.le_rpow_max_log hLe (hψ₂B j u)⟩
  have hψb₁ : ∀ u : ℝ, ‖ψ₁ u‖ ≤ Real.log x ^ max (Real.log (Bψ 0)) 0 := fun u => by
    have h' := hcut₁.2.2 0 u
    rwa [iteratedDeriv_zero] at h'
  have hψb₂ : ∀ u : ℝ, ‖ψ₂ u‖ ≤ Real.log x ^ max (Real.log (Bψ 0)) 0 := fun u => by
    have h' := hcut₂.2.2 0 u
    rwa [iteratedDeriv_zero] at h'
  obtain ⟨hsqU, -⟩ := hE x hxE I (x * U₁ * U₂) hxY hYx2 (markCount I.𝔊 C) hmark test₁ ht₁.1 ψ₁
    hψ₁s hψb₁
  obtain ⟨-, hsqV⟩ := hE x hxE I (x * U₁ * U₂) hxY hYx2 (markCount I.𝔊 C) hmark test₂ ht₂.1 ψ₂
    hψ₂s hψb₂
  have hP5 : Real.log x ^ C₅ ≤ Real.log x ^ max C₅ 0 :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
  have hB₁0 : 0 ≤ max MB 0 * (x * U₁ * U₂) * Real.log x ^ (-A) :=
    mul_nonneg (mul_nonneg (le_max_right _ _) hY0.le) hLm0
  have hB₂0 : 0 ≤ x * U₁ * U₂ * Real.log x ^ max C₅ 0 :=
    mul_nonneg hY0.le (Real.rpow_nonneg hL0.le _)
  -- the character expansion of the weight
  have hbd : ∀ c a : ZMod H, |𝔅.toFun a (a + c)| ≤ 1 := fun c a =>
    abs_le.mpr ⟨by linarith [𝔅.nonneg a (a + c)], 𝔅.le_one a (a + c)⟩
  choose cf hcf1 hcf2 using fun c : ZMod H =>
    Separation.exists_char_coeff hH (fun a => 𝔅.toFun a (a + c)) (hbd c)
  -- the correlation as a finite sum
  have hsupp : ∀ r, ((auxWeight (groupFamily I.𝔊).big C r : ℝ) : ℂ) * (b₁ r * b₂ r) ≠ 0 →
      ∀ w : ℕ, D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
        ((𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H) : ℝ) : ℂ) *
        (((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ) *
          I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁ w) *
        (I.G (w + tupleProd C r) *
          I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂ (w + tupleProd C r)) ≠ 0 →
      w ∈ Finset.Icc 1 ⌊((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) * (x * U₁ * U₂)⌋₊ := by
    intro r hr w hw
    have hβ : b₁ r * b₂ r ≠ 0 := right_ne_zero_of_mul hr
    have hΨ0 : D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) ≠ 0 := by
      intro h0
      apply hw
      rw [h0, zero_div, zero_mul, zero_mul, zero_mul]
    obtain ⟨hA1, hA2⟩ := hb₁.cell r (left_ne_zero_of_mul hβ)
    obtain ⟨hB1, hB2⟩ := hb₂.cell r (right_ne_zero_of_mul hβ)
    obtain ⟨h1, h2⟩ := hsup _ hΨ0
    have hDr : ((tupleProd C r : ℕ) : ℝ) = (blockAuxProd I.blocks true C r : ℝ) *
        (blockAuxProd I.blocks false C r : ℝ) := by
      rw [tupleProd_eq_blockAuxProd_mul I.blocks C r, Nat.cast_mul]
    rw [hDr] at h1 h2
    obtain ⟨f1, f2, -, -⟩ := Separation.cut_range hx1 hU₁ hU₂ hA1 hA2 hB1 hB2 hc₁ h1 h2
    have hwpos : (0 : ℝ) < (w : ℝ) := by
      have h3 : c₁ * (x * U₁ * U₂) ≤ (w : ℝ) := (le_div_iff₀ hY0).mp f1
      exact lt_of_lt_of_le (mul_pos hc₁ hY0) h3
    have hwle : (w : ℝ) ≤ ((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) * (x * U₁ * U₂) := by
      have h3 : (w : ℝ) ≤ (c₂ + 1) * (Real.exp 1 * Real.exp 1) * (x * U₁ * U₂) :=
        (div_le_iff₀ hY0).mp f2
      have h4 : (c₂ + 1) * (Real.exp 1 * Real.exp 1) * (x * U₁ * U₂) ≤
          ((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) * (x * U₁ * U₂) :=
        mul_le_mul_of_nonneg_right (by linarith) hY0.le
      exact h3.trans h4
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr fun h0 => by
      rw [h0, Nat.cast_zero] at hwpos
      exact lt_irrefl _ hwpos, Nat.le_floor hwle⟩
  have hcorr := Separation.sum_finsum_eq_sum
    (fun r => ((auxWeight (groupFamily I.𝔊).big C r : ℝ) : ℂ) * (b₁ r * b₂ r))
    (fun r w => D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
      ((𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H) : ℝ) : ℂ) *
      (((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ) *
        I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁ w) *
      (I.G (w + tupleProd C r) *
        I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂ (w + tupleProd C r)))
    (Finset.Icc 1 ⌊((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) * (x * U₁ * U₂)⌋₊) hsupp
  -- the partition by the residues of the two free products
  have hexp : ∀ r : AuxList (groupFamily I.𝔊).big C,
      ∀ w ∈ Finset.Icc 1 ⌊((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) * (x * U₁ * U₂)⌋₊,
      D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
        ((𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H) : ℝ) : ℂ) *
        (((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ) *
          I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁ w) *
        (I.G (w + tupleProd C r) *
          I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂ (w + tupleProd C r)) =
      ∑ j ∈ Finset.range H,
        cf (((blockAuxProd I.blocks true C r : ℕ) : ZMod H) *
          ((blockAuxProd I.blocks false C r : ℕ) : ZMod H)) j *
        (D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
          addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) *
          (((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ) *
            I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁ w) *
          (I.G (w + tupleProd C r) *
            I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂ (w + tupleProd C r))) := by
    intro r w _
    have hcast : ((w + tupleProd C r : ℕ) : ZMod H) = (w : ZMod H) +
        ((blockAuxProd I.blocks true C r : ℕ) : ZMod H) *
          ((blockAuxProd I.blocks false C r : ℕ) : ZMod H) := by
      rw [tupleProd_eq_blockAuxProd_mul I.blocks C r, Nat.cast_add, Nat.cast_mul]
    rw [hcast, hcf2, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hres := Separation.residue_expansion
    (fun r => ((auxWeight (groupFamily I.𝔊).big C r : ℝ) : ℂ)) b₁ b₂
    (fun r => ((blockAuxProd I.blocks true C r : ℕ) : ZMod H))
    (fun r => ((blockAuxProd I.blocks false C r : ℕ) : ZMod H))
    (Finset.Icc 1 ⌊((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) * (x * U₁ * U₂)⌋₊) cf
    (fun r w => D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
      ((𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H) : ℝ) : ℂ) *
      (((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ) *
        I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁ w) *
      (I.G (w + tupleProd C r) *
        I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂ (w + tupleProd C r)))
    (fun j r w => D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
      addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) *
      (((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ) *
        I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁ w) *
      (I.G (w + tupleProd C r) *
        I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂ (w + tupleProd C r))) hexp
  -- every twisted correlation
  have hind : ∀ (a : ZMod H) (n : ℕ), ‖(if (n : ZMod H) = a then (1 : ℂ) else 0)‖ ≤ 1 := by
    intro a n
    by_cases h : (n : ZMod H) = a
    · rw [if_pos h, norm_one]
    · rw [if_neg h, norm_zero]
      exact zero_le_one
  have htw : ∀ (a : ZMod H × ZMod H) (j : ℕ),
      ‖∑ r : AuxList (groupFamily I.𝔊).big C,
        ((auxWeight (groupFamily I.𝔊).big C r : ℝ) : ℂ) *
          (b₁ r * (if ((blockAuxProd I.blocks true C r : ℕ) : ZMod H) = a.1 then 1 else 0) *
            (b₂ r *
              (if ((blockAuxProd I.blocks false C r : ℕ) : ZMod H) = a.2 then 1 else 0))) *
          ∑ w ∈ Finset.Icc 1 ⌊((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) * (x * U₁ * U₂)⌋₊,
            D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
              addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) *
              (((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ) *
                I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁ w) *
              (I.G (w + tupleProd C r) *
                I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂ (w + tupleProd C r))‖ ≤
        (x * U₁ * U₂)⁻¹ * ((max MB 0 * (x * U₁ * U₂) * Real.log x ^ (-A) +
          x * U₁ * U₂ * Real.log x ^ max C₅ 0 * (Real.log x ^ ⌈A + max C₅ 0⌉₊)⁻¹) *
            (Cd * Real.pi)) := by
    intro a j
    exact Separation.twisted_bound hbig hlaw I.blocks C j hx1 hU₁ hU₂
      (fun w => ((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ))
      (I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁) I.G
      (I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂) ha₁ hc₁ hψ₁s hψ₂s hψeq hsup hwdc hCd
      hwdinv hL1 hB₁0 hB₂0
      (fun β₁ β₂ h₁ h₂ σ hσ =>
        (hB x hxB I J C hC β₁ β₂ U₁ U₂ hU₁ hU₂ h₁ h₂ test₁ test₂ ht₁ ht₂ σ
          (by rw [Real.rpow_one]; exact hσ) ψ₁ ψ₂ hcut₁ hcut₂ j).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hY0.le) hLm0))
      (fun σ => (hsqU σ).trans (mul_le_mul_of_nonneg_left hP5 hY0.le))
      (hsqV.trans (mul_le_mul_of_nonneg_left hP5 hY0.le))
      (Separation.blockTest_mul hb₁ (fun n => if (n : ZMod H) = a.1 then 1 else 0) (hind a.1))
      (Separation.blockTest_mul hb₂ (fun n => if (n : ZMod H) = a.2 then 1 else 0) (hind a.2))
  -- the assembly
  have hsum := Separation.norm_residue_sum_le cf hcf1
    (fun (a : ZMod H × ZMod H) (j : ℕ) => ∑ r : AuxList (groupFamily I.𝔊).big C,
      ((auxWeight (groupFamily I.𝔊).big C r : ℝ) : ℂ) *
        (b₁ r * (if ((blockAuxProd I.blocks true C r : ℕ) : ZMod H) = a.1 then 1 else 0) *
          (b₂ r *
            (if ((blockAuxProd I.blocks false C r : ℕ) : ZMod H) = a.2 then 1 else 0))) *
        ∑ w ∈ Finset.Icc 1 ⌊((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) * (x * U₁ * U₂)⌋₊,
          D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
            addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) *
            (((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ) *
              I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁ w) *
            (I.G (w + tupleProd C r) *
              I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂ (w + tupleProd C r))) htw
  have hfin := Separation.sep_final (L := Real.log x) (A := A) (C₅ := max C₅ 0)
    (MB := max MB 0) (Cd := Cd) (N := ⌈A + max C₅ 0⌉₊) hL1 hY0 (Nat.le_ceil _) hCd0
  have hgoal : comparisonCorrelationOf I.𝔊 D.q D.q₀ D.𝔞 x I.S 𝔅 D.Ψ I.G C
      (fun r => b₁ r * b₂ r) test₁ test₂ =
      ∑ a : ZMod H × ZMod H, ∑ j ∈ Finset.range H, cf (a.1 * a.2) j *
        ∑ r : AuxList (groupFamily I.𝔊).big C,
          ((auxWeight (groupFamily I.𝔊).big C r : ℝ) : ℂ) *
            (b₁ r * (if ((blockAuxProd I.blocks true C r : ℕ) : ZMod H) = a.1 then 1 else 0) *
              (b₂ r *
                (if ((blockAuxProd I.blocks false C r : ℕ) : ZMod H) = a.2 then 1 else 0))) *
            ∑ w ∈ Finset.Icc 1
                ⌊((c₂ + 1) * (Real.exp 1 * Real.exp 1) + 1) * (x * U₁ * U₂)⌋₊,
              D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
                addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) *
                (((centeredCore D.q D.𝔞 x I.S w : ℝ) : ℂ) *
                  I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₁ w) *
                (I.G (w + tupleProd C r) *
                  I.𝔊.activeWeight D.q₀ (markCount I.𝔊 C) test₂ (w + tupleProd C r)) :=
    hcorr.trans hres
  rw [hgoal]
  refine hsum.trans ?_
  calc (H : ℝ) ^ 3 * ((x * U₁ * U₂)⁻¹ * ((max MB 0 * (x * U₁ * U₂) *
          Real.log x ^ (-A) + x * U₁ * U₂ * Real.log x ^ max C₅ 0 *
            (Real.log x ^ ⌈A + max C₅ 0⌉₊)⁻¹) * (Cd * Real.pi)))
      ≤ (H : ℝ) ^ 3 * ((max MB 0 + 1) * (Cd * Real.pi) * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_left hfin (pow_nonneg (Nat.cast_nonneg H) 3)
    _ = (H : ℝ) ^ 3 * ((max MB 0 + 1) * (Cd * Real.pi)) * Real.log x ^ (-A) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
