module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.InsertionTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.MellinSeparationProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Sanity

/-!
# The insertion of the cutoff and the transferred estimate

`insertionLink d H 𝔅 : InsertionLink d H 𝔅` (`[P-06:0287–0316]`, `[PUB-tex:0479–0482]`), the
field `insertion` of `OpenLeaves d H 𝔅`: the pairing bound with saving `E ≥ A + 2C₃ + 2` for
`|ζ| ≤ L`, the absolute Schur bound for all `ζ` and the endpoint norms give
`|total residual edge pairing| ≤ M L^{-A}`.

"Insert `Ψ(n/(xD))/n` into the physical edge pairing. Its support has `n ≍ n' ≍ xD = x^{1+o(1)}`.
Partition `n` into `O(L)` dyads `[X, 2X)`, restricting `n'` to fixed enlargements. … Put `X/n`
into the first vector and `1/X` outside. … For the tail of (cor:insertion-separation), the
absolute Schur estimate and the endpoint norms cost at most a fixed power of `L`."

* `sum_edgeTerm_eq_dyads`: the total edge sum is the sum over the dyads `[2^j X₀, 2^{j+1} X₀)`,
  `j < K`, and over the `H²` pairs of residues `a` of `𝓑(a)` times the sum of the transition
  coefficients `insCoef` against the cutoff, provided the cutoff confines `n` to
  `[X₀, 2^K X₀)` and the target `n + D` to the enlarged dyad `[X, 4X)`.
* `norm_dyadSum_le`: one dyad and one pair of residues. The two endpoint vectors satisfy the
  hypotheses of the pairing bound (`sup |f| ≤ B_F`, `‖f‖, ‖g‖ ≤ X^{1/2} L^{C₃}` from the two sums
  of `EndpointNormsAt`); the pairing is at most `M X L^{-E+2C₃}` for `|v| ≤ L` and, by Schur's
  test (`SchurTest.norm_pairMarkFree_physOp_le`), at most `X L^{C_abs + 2C₃}` for all `v`; the
  Mellin density decays faster than any power (`Insertion.norm_dyad_le`).
* `final_arith`: `K ≤ 4L` dyads, `H²` pairs of residues, `E ≥ A + 2C₃ + 2` and a decay order
  `N ≥ C_abs + 2C₃ + A + 1`.

The thresholds: `X₀ = x^{1/2}`, `K = numDyads x`; `c₁ x^{1/2} ≥ 1` and `2c₂ < x^{1/2}` for the
support `[c₁, c₂]` of `Ψ`; `D ≤ 2 exp(3 J C₀ log L · L^{0.46}) ≤ 2 x^{1/2}`
(`Config.dil_le`); `B_F² ≤ L` for the bound `B_F` of `F_x` on `u ≤ x³` (`CorePowerBounded` with
`κ = 3`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open Filter
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace Insertion

/-- The damped mass is nonnegative. -/
theorem dampedMass_nonneg (𝔊 : ActiveGroups) (J : ℕ) (q₀ : ℝ) (n : ℤ) :
    0 ≤ dampedMass 𝔊 J q₀ n := by
  unfold dampedMass unitNormSq
  exact mul_nonneg (sq_nonneg _)
    (mul_nonneg (Pairing.stateMass_nonneg _ _ _) (Nat.cast_nonneg _))

/-- The dyad `[X, 2X)` lies in the enlarged dyad `[X, 4X)`. -/
theorem intWindow_subset_wideWindow {X : ℝ} (hX : 0 ≤ X) : intWindow X ⊆ wideWindow X := by
  unfold intWindow wideWindow
  exact Finset.Ico_subset_Ico le_rfl (Int.ceil_mono (by linarith))

/-- A finite combination can be taken out of a fourfold sum. -/
theorem sum_nested_sum_mul {P X N Q : Type} [Fintype X] [Fintype N] [Fintype Q] {A : N → Type}
    [∀ ν, Fintype (A ν)] (I : Finset P) (c : Q → ℂ) (F : Q → P → X → (ν : N) → A ν → ℂ) :
    ∑ n ∈ I, ∑ x, ∑ ν, ∑ ξ, ∑ a, c a * F a n x ν ξ =
      ∑ a, c a * ∑ n ∈ I, ∑ x, ∑ ν, ∑ ξ, F a n x ν ξ := by
  rw [SchurTest.sum_nested_eq I (fun n x ν ξ => ∑ a, c a * F a n x ν ξ), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [SchurTest.sum_nested_eq I (F a), Finset.mul_sum]

/-- **The total edge sum over the dyads and the pairs of residues** (`[P-06:0287–0289]`,
`[PUB-tex:0479–0481]`). -/
theorem sum_edgeTerm_eq_dyads (𝔊 : ActiveGroups) (q₀ : ℝ) {J : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern (groupFamily 𝔊).big J 1) (x : ℝ) (Ψ : ℝ → ℂ) {H : ℕ} [NeZero H]
    (𝔅 : JointResidueWeight H) (F : ℕ → ℝ) (G : ℕ → ℂ) {X₀ : ℝ} (hX₀ : 0 < X₀) (K : ℕ)
    (hsupp : ∀ (ν : N) (n : ℤ) (s : Lists (groupFamily 𝔊) J 1)
      (r : AuxList (groupFamily 𝔊).big (𝔉 ν).C),
      Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s r : ℝ))) ≠ 0 →
        X₀ ≤ (n : ℝ) ∧ (n : ℝ) < (2 : ℝ) ^ K * X₀)
    (hwide : ∀ j : ℕ, j < K → ∀ n ∈ intWindow ((2 : ℝ) ^ j * X₀), ∀ (ν : N)
      (s : Lists (groupFamily 𝔊) J 1) (r : AuxList (groupFamily 𝔊).big (𝔉 ν).C),
      Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s r : ℝ))) ≠ 0 →
        n + (dil (𝔉 ν).C s r : ℤ) ∈ wideWindow ((2 : ℝ) ^ j * X₀)) :
    ∑ ν, edgeTerm 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G =
      ∑ j ∈ Finset.range K, ∑ a : ZMod H × ZMod H, ((𝔅.toFun a.1 a.2 : ℝ) : ℂ) *
        ∑ n ∈ intWindow ((2 : ℝ) ^ j * X₀), ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
          ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
            insCoef 𝔊 q₀ 𝔉 ((2 : ℝ) ^ j * X₀) (wideWindow ((2 : ℝ) ^ j * X₀)) a F G n s ν ξ *
              Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ))) := by
  have hT : ∀ (ν : N) (n : ℤ), n ∉ Finset.Ico ⌈X₀⌉ ⌈(2 : ℝ) ^ K * X₀⌉ →
      ∀ (s : Lists (groupFamily 𝔊) J 1) (r : AuxList (groupFamily 𝔊).big (𝔉 ν).C),
        Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s r : ℝ))) = 0 := by
    intro ν n hn s r
    by_contra hne
    obtain ⟨h1, h2⟩ := hsupp ν n s r hne
    exact hn (Finset.mem_Ico.mpr ⟨Int.ceil_le.mpr h1, Int.lt_ceil.mpr h2⟩)
  have h1 : ∀ ν : N, edgeTerm 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G =
      ∑ n ∈ Finset.Ico ⌈X₀⌉ ⌈(2 : ℝ) ^ K * X₀⌉, ∑ s : Lists (groupFamily 𝔊) J 1,
        ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
          edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s ξ.1 ξ.2 := by
    intro ν
    rw [edgeTerm_eq_sum 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G _ (hT ν)]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun s _ =>
      (Fintype.sum_prod_type' fun r s' => edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s r s').symm
  have h2 : ∀ j ∈ Finset.range K,
      ∑ n ∈ intWindow ((2 : ℝ) ^ j * X₀), ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
        ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
          edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s ξ.1 ξ.2 =
      ∑ a : ZMod H × ZMod H, ((𝔅.toFun a.1 a.2 : ℝ) : ℂ) *
        ∑ n ∈ intWindow ((2 : ℝ) ^ j * X₀), ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
          ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
            insCoef 𝔊 q₀ 𝔉 ((2 : ℝ) ^ j * X₀) (wideWindow ((2 : ℝ) ^ j * X₀)) a F G n s ν ξ *
              Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ))) := by
    intro j hj
    have hj' : j < K := Finset.mem_range.mp hj
    have hXj : 0 < (2 : ℝ) ^ j * X₀ := mul_pos (pow_pos two_pos j) hX₀
    exact (Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ξ _ =>
        edgeSummand_eq_sum_insCoef 𝔊 q₀ 𝔉 x _ hXj _ 𝔅 Ψ F G n s ν ξ
          (hwide j hj' n hn ν s ξ.1)).trans
      (sum_nested_sum_mul (intWindow ((2 : ℝ) ^ j * X₀))
        (fun a : ZMod H × ZMod H => ((𝔅.toFun a.1 a.2 : ℝ) : ℂ))
        (fun (a : ZMod H × ZMod H) (n : ℤ) (s : Lists (groupFamily 𝔊) J 1) (ν : N)
          (ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1) =>
            insCoef 𝔊 q₀ 𝔉 ((2 : ℝ) ^ j * X₀) (wideWindow ((2 : ℝ) ^ j * X₀)) a F G n s ν ξ *
              Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ)))))
  calc ∑ ν, edgeTerm 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G
      = ∑ ν, ∑ n ∈ Finset.Ico ⌈X₀⌉ ⌈(2 : ℝ) ^ K * X₀⌉, ∑ s : Lists (groupFamily 𝔊) J 1,
          ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
            edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s ξ.1 ξ.2 :=
        Finset.sum_congr rfl fun ν _ => h1 ν
    _ = ∑ n ∈ Finset.Ico ⌈X₀⌉ ⌈(2 : ℝ) ^ K * X₀⌉, ∑ ν, ∑ s : Lists (groupFamily 𝔊) J 1,
          ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
            edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s ξ.1 ξ.2 := Finset.sum_comm
    _ = ∑ n ∈ Finset.Ico ⌈X₀⌉ ⌈(2 : ℝ) ^ K * X₀⌉, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
          ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
            edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s ξ.1 ξ.2 :=
        Finset.sum_congr rfl fun n _ => Finset.sum_comm
    _ = ∑ j ∈ Finset.range K, ∑ n ∈ intWindow ((2 : ℝ) ^ j * X₀),
          ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
            ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
              edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s ξ.1 ξ.2 :=
        sum_Ico_dyads (fun n : ℤ => ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
          ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
            edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s ξ.1 ξ.2) hX₀.le K
    _ = ∑ j ∈ Finset.range K, ∑ a : ZMod H × ZMod H, ((𝔅.toFun a.1 a.2 : ℝ) : ℂ) *
          ∑ n ∈ intWindow ((2 : ℝ) ^ j * X₀), ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
            ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
              insCoef 𝔊 q₀ 𝔉 ((2 : ℝ) ^ j * X₀) (wideWindow ((2 : ℝ) ^ j * X₀)) a F G n s ν
                  ξ *
                Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ))) :=
        Finset.sum_congr rfl h2

/-- **One dyad and one pair of residues** (`[P-06:0297–0316]`): from the pairing bound for
`|ζ| ≤ L`, the absolute Schur bound, the bound `B_F` for the first endpoint and the two endpoint
norms on the enlarged dyad. -/
theorem norm_dyadSum_le (𝔊 : ActiveGroups) {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₁ : q₀ ≤ 1) {J : ℕ}
    {N : Type} [Fintype N] (𝔉 : N → Pattern (groupFamily 𝔊).big J 1)
    (hD : ∀ (ν : N) (s : Lists (groupFamily 𝔊) J 1) (r : AuxList (groupFamily 𝔊).big (𝔉 ν).C),
      0 < dil (𝔉 ν).C s r)
    {x X : ℝ} (hx : 0 < x) (hX : 1 ≤ X) {H : ℕ} (a : ZMod H × ZMod H) (F : ℕ → ℝ) (G : ℕ → ℂ)
    {Ψ wd : ℝ → ℂ} (hwd : Continuous wd) {Nn : ℕ} {Cwd : ℝ}
    (hdecay : ∀ v, ‖wd v‖ * (1 + |v|) ^ (Nn + 2) ≤ Cwd)
    (hinv : ∀ t : ℝ, 0 < t → Ψ t = ∫ v : ℝ, wd v * (t : ℂ) ^ ((v : ℂ) * Complex.I))
    {L M E C₃ Cabs Bf : ℝ} (hL : 1 ≤ L)
    (hP : ∀ ζ : ℝ, |ζ| ≤ L → ∀ (fn : ℤ → ℂ) (g : PState intPos (groupFamily 𝔊) J 1 → ℂ),
      (∀ n ∈ intWindow X, ‖fn n‖ ≤ Bf) →
      Real.sqrt (markFreeNormSq intPos (groupFamily 𝔊) J 1 (intWindow X) fn) ≤
        Real.sqrt X * L ^ C₃ →
      MemPhysL2 intPos (groupFamily 𝔊) J 1 g →
      Real.sqrt (physNormSq intPos (groupFamily 𝔊) J 1 g) ≤ Real.sqrt X * L ^ C₃ →
      ‖pairMarkFree intPos (groupFamily 𝔊) J 1 (intWindow X) fn
          (physOp intPos (groupFamily 𝔊) q₀ 𝔉 1 ζ g)‖ ≤ M * X * L ^ (-E + 2 * C₃))
    (hS : ∀ (ζ : ℝ) (s : PState intPos (groupFamily 𝔊) J 1),
      physAbsRowSum intPos (groupFamily 𝔊) q₀ 𝔉 1 ζ s ≤ L ^ Cabs ∧
        physAbsColSum intPos (groupFamily 𝔊) q₀ 𝔉 1 ζ s ≤ L ^ Cabs)
    (hF : ∀ n ∈ intWindow X, |F n.toNat| ≤ Bf)
    (hNF : ∑ n ∈ wideWindow X, F n.toNat ^ 2 * dampedMass 𝔊 J q₀ n ≤ X * L ^ (2 * C₃))
    (hNG : ∑ n ∈ wideWindow X, ‖G n.toNat‖ ^ 2 * dampedMass 𝔊 J q₀ n ≤ X * L ^ (2 * C₃)) :
    ‖∑ n ∈ intWindow X, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
        ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
          insCoef 𝔊 q₀ 𝔉 X (wideWindow X) a F G n s ν ξ *
            Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ)))‖ ≤
      (|M| * L ^ (-E + 2 * C₃) + L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹) * (Cwd * Real.pi) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  have hXX : X⁻¹ * X = 1 := inv_mul_cancel₀ hX0.ne'
  have hsqrt : Real.sqrt (X * L ^ (2 * C₃)) = Real.sqrt X * L ^ C₃ := by
    rw [Real.sqrt_mul hX0.le, ← Pairing.rpow_sq_eq hL0 C₃,
      Real.sqrt_sq (Real.rpow_nonneg hL0.le _)]
  -- the first endpoint
  have hfsup : ∀ (v : ℝ) (n : ℤ), n ∈ intWindow X →
      ‖conj (firstVal 𝔊 J q₀ X a.1 F n * Separation.phase v (Real.log ((n : ℝ) / x)))‖ ≤
        Bf := by
    intro v n hn
    rw [Complex.norm_conj, norm_mul, Separation.norm_phase, mul_one]
    exact (norm_firstVal_le 𝔊 J hq₀ hq₁ a.1 F hX0 (mem_intWindow.mp hn).1).trans (hF n hn)
  have hfnorm : ∀ v : ℝ, Real.sqrt (markFreeNormSq intPos (groupFamily 𝔊) J 1 (intWindow X)
      (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
        Separation.phase v (Real.log ((n : ℝ) / x))))) ≤ Real.sqrt X * L ^ C₃ := by
    intro v
    rw [← hsqrt]
    refine Real.sqrt_le_sqrt ?_
    have e : markFreeNormSq intPos (groupFamily 𝔊) J 1 (intWindow X)
        (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
          Separation.phase v (Real.log ((n : ℝ) / x)))) =
        ∑ n ∈ intWindow X, ‖conj (firstVal 𝔊 J q₀ X a.1 F n *
          Separation.phase v (Real.log ((n : ℝ) / x)))‖ ^ 2 *
            unitNormSq intPos (groupFamily 𝔊) J 1 n := rfl
    rw [e]
    calc ∑ n ∈ intWindow X, ‖conj (firstVal 𝔊 J q₀ X a.1 F n *
          Separation.phase v (Real.log ((n : ℝ) / x)))‖ ^ 2 *
            unitNormSq intPos (groupFamily 𝔊) J 1 n
        ≤ ∑ n ∈ intWindow X, F n.toNat ^ 2 * dampedMass 𝔊 J q₀ n :=
          Finset.sum_le_sum fun n hn => by
            rw [Complex.norm_conj, norm_mul, Separation.norm_phase, mul_one]
            exact normSq_firstVal_mul_le 𝔊 J hq₀ a.1 F hX0 (mem_intWindow.mp hn).1
      _ ≤ ∑ n ∈ wideWindow X, F n.toNat ^ 2 * dampedMass 𝔊 J q₀ n :=
          Finset.sum_le_sum_of_subset_of_nonneg (intWindow_subset_wideWindow hX0.le)
            fun n _ _ => mul_nonneg (sq_nonneg _) (dampedMass_nonneg 𝔊 J q₀ n)
      _ ≤ X * L ^ (2 * C₃) := hNF
  -- the second endpoint
  have hgmem : MemPhysL2 intPos (groupFamily 𝔊) J 1
      (fun s : PState intPos (groupFamily 𝔊) J 1 =>
        secondVal 𝔊 J q₀ (wideWindow X) a.2 G s.1) :=
    memPhysL2_markFree intPos (groupFamily 𝔊) J 1 (wideWindow X)
      (secondVal 𝔊 J q₀ (wideWindow X) a.2 G)
      (fun n hn => secondVal_of_notMem 𝔊 J q₀ a.2 G hn)
  have hgnorm : Real.sqrt (physNormSq intPos (groupFamily 𝔊) J 1
      (fun s : PState intPos (groupFamily 𝔊) J 1 =>
        secondVal 𝔊 J q₀ (wideWindow X) a.2 G s.1)) ≤ Real.sqrt X * L ^ C₃ := by
    rw [← hsqrt]
    exact Real.sqrt_le_sqrt ((physNormSq_secondVal_le 𝔊 J hq₀ (wideWindow X) a.2 G).trans hNG)
  -- the pairing for `|v| ≤ L`
  have hlow : ∀ v : ℝ, |v| ≤ L →
      ‖(X : ℂ)⁻¹ * pairMarkFree intPos (groupFamily 𝔊) J 1 (intWindow X)
        (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
          Separation.phase v (Real.log ((n : ℝ) / x))))
        (physOp intPos (groupFamily 𝔊) q₀ 𝔉 1 (-v)
          (fun s : PState intPos (groupFamily 𝔊) J 1 =>
            secondVal 𝔊 J q₀ (wideWindow X) a.2 G s.1))‖ ≤ |M| * L ^ (-E + 2 * C₃) := by
    intro v hv
    have hv' : |(-v)| ≤ L := by
      rw [abs_neg]
      exact hv
    have h := hP (-v) hv'
      (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
        Separation.phase v (Real.log ((n : ℝ) / x))))
      (fun s : PState intPos (groupFamily 𝔊) J 1 => secondVal 𝔊 J q₀ (wideWindow X) a.2 G s.1)
      (hfsup v) (hfnorm v) hgmem hgnorm
    have e : X⁻¹ * (M * X * L ^ (-E + 2 * C₃)) = M * L ^ (-E + 2 * C₃) :=
      calc X⁻¹ * (M * X * L ^ (-E + 2 * C₃)) = X⁻¹ * X * (M * L ^ (-E + 2 * C₃)) := by ring
        _ = M * L ^ (-E + 2 * C₃) := by rw [hXX, one_mul]
    rw [norm_mul, norm_inv, Complex.norm_of_nonneg hX0.le]
    refine (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hX0.le)).trans ?_
    rw [e]
    exact mul_le_mul_of_nonneg_right (le_abs_self M) (Real.rpow_nonneg hL0.le _)
  -- the pairing for all `v`: Schur's test
  have hall : ∀ v : ℝ,
      ‖(X : ℂ)⁻¹ * pairMarkFree intPos (groupFamily 𝔊) J 1 (intWindow X)
        (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
          Separation.phase v (Real.log ((n : ℝ) / x))))
        (physOp intPos (groupFamily 𝔊) q₀ 𝔉 1 (-v)
          (fun s : PState intPos (groupFamily 𝔊) J 1 =>
            secondVal 𝔊 J q₀ (wideWindow X) a.2 G s.1))‖ ≤ L ^ (Cabs + 2 * C₃) := by
    intro v
    have h := SchurTest.norm_pairMarkFree_physOp_le intPos (groupFamily 𝔊) q₀ 𝔉 1 (-v)
      (Real.rpow_nonneg hL0.le Cabs) (fun s => (hS (-v) s).1) (fun s => (hS (-v) s).2)
      (intWindow X)
      (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
        Separation.phase v (Real.log ((n : ℝ) / x)))) hgmem
    have h' := h.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul (hfnorm v) hgnorm (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hL0.le _)))
      (Real.rpow_nonneg hL0.le Cabs))
    have e1 : Real.sqrt X * L ^ C₃ * (Real.sqrt X * L ^ C₃) = X * L ^ (2 * C₃) := by
      rw [← Pairing.rpow_sq_eq hL0 C₃]
      calc Real.sqrt X * L ^ C₃ * (Real.sqrt X * L ^ C₃)
          = Real.sqrt X * Real.sqrt X * (L ^ C₃) ^ 2 := by ring
        _ = X * (L ^ C₃) ^ 2 := by rw [Real.mul_self_sqrt hX0.le]
    have e2 : X⁻¹ * (L ^ Cabs * (X * L ^ (2 * C₃))) = L ^ (Cabs + 2 * C₃) := by
      rw [Real.rpow_add hL0]
      calc X⁻¹ * (L ^ Cabs * (X * L ^ (2 * C₃)))
          = X⁻¹ * X * (L ^ Cabs * L ^ (2 * C₃)) := by ring
        _ = L ^ Cabs * L ^ (2 * C₃) := by rw [hXX, one_mul]
    rw [norm_mul, norm_inv, Complex.norm_of_nonneg hX0.le, ← e2, ← e1]
    exact mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hX0.le)
  exact norm_dyad_le 𝔊 q₀ 𝔉 hD hx hX (wideWindow X) a F G hwd hdecay hinv hL
    (mul_nonneg (abs_nonneg M) (Real.rpow_nonneg hL0.le _)) (Real.rpow_nonneg hL0.le _)
    hlow hall

/-- The powers of `L` in the conclusion: `K ≤ 4L` dyads, `H²` pairs of residues,
`E ≥ A + 2C₃ + 2` and a decay order `N ≥ C_abs + 2C₃ + A + 1`. -/
theorem final_arith {L M E C₃ Cabs A Cw K Hc : ℝ} {Nn : ℕ} (hL : 1 ≤ L)
    (hE : A + 2 * C₃ + 2 ≤ E) (hNn : Cabs + 2 * C₃ + A + 1 ≤ (Nn : ℝ)) (hK : K ≤ 4 * L)
    (hH : 0 ≤ Hc) (hCw : 0 ≤ Cw) :
    K * (Hc * ((|M| * L ^ (-E + 2 * C₃) + L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹) * Cw)) ≤
      Hc * (4 * ((|M| + 1) * Cw)) * L ^ (-A) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have h1 : L * L ^ (-E + 2 * C₃) ≤ L ^ (-A) := by
    have e : L * L ^ (-E + 2 * C₃) = L ^ (1 + (-E + 2 * C₃)) := by
      rw [Real.rpow_add hL0 1 (-E + 2 * C₃), Real.rpow_one]
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h2 : L * (L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹) ≤ L ^ (-A) := by
    have e : L * (L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹) =
        L ^ (1 + (Cabs + 2 * C₃) + -(Nn : ℝ)) := by
      rw [Real.rpow_add hL0 (1 + (Cabs + 2 * C₃)) (-(Nn : ℝ)),
        Real.rpow_add hL0 1 (Cabs + 2 * C₃), Real.rpow_one, Real.rpow_neg hL0.le,
        Real.rpow_natCast]
      ring
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h3 : L * (|M| * L ^ (-E + 2 * C₃) + L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹) ≤
      (|M| + 1) * L ^ (-A) := by
    have h := mul_le_mul_of_nonneg_left h1 (abs_nonneg M)
    calc L * (|M| * L ^ (-E + 2 * C₃) + L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹)
        = |M| * (L * L ^ (-E + 2 * C₃)) + L * (L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹) := by ring
      _ ≤ |M| * L ^ (-A) + L ^ (-A) := add_le_add h h2
      _ = (|M| + 1) * L ^ (-A) := by ring
  have hin0 : 0 ≤ |M| * L ^ (-E + 2 * C₃) + L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹ :=
    add_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hL0.le _))
      (mul_nonneg (Real.rpow_nonneg hL0.le _) (inv_nonneg.mpr (pow_nonneg hL0.le _)))
  calc K * (Hc * ((|M| * L ^ (-E + 2 * C₃) + L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹) * Cw))
      ≤ 4 * L * (Hc * ((|M| * L ^ (-E + 2 * C₃) + L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹) * Cw)) :=
        mul_le_mul_of_nonneg_right hK (mul_nonneg hH (mul_nonneg hin0 hCw))
    _ = Hc * (4 * Cw) *
          (L * (|M| * L ^ (-E + 2 * C₃) + L ^ (Cabs + 2 * C₃) * (L ^ Nn)⁻¹)) := by ring
    _ ≤ Hc * (4 * Cw) * ((|M| + 1) * L ^ (-A)) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hH (mul_nonneg (by norm_num) hCw))
    _ = Hc * (4 * ((|M| + 1) * Cw)) * L ^ (-A) := by ring

end Insertion

open Insertion in
/-- **The insertion of the cutoff and the transferred estimate** (`[P-06:0287–0316]`,
`[PUB-tex:0479–0482]`). This is the field `insertion` of `OpenLeaves d H 𝔅`. -/
theorem insertionLink (d H : ℕ) (𝔅 : JointResidueWeight H) : InsertionLink d H 𝔅 := by
  intro hH hCP D m₀ J qs hs xs E C₃ Cabs A hA hE hpair hschur hnorm
  have : NeZero H := ⟨hH.ne'⟩
  obtain ⟨M, xP, hP⟩ := hpair
  obtain ⟨xS, hS⟩ := hschur
  obtain ⟨xN, hN⟩ := hnorm
  obtain ⟨Bf, hBf0, hBf⟩ := hCP D.q D.q_pos D.q_lt_one D.ε D.ε_pos 3 (by norm_num) D.K
  obtain ⟨xc, hc⟩ := hBf D.𝔞
  obtain ⟨wd, hwdc, hwdd, hinv⟩ :=
    mellinSeparationComplex D.Ψ D.smooth D.compact D.support
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hsup⟩ := MellinSep.exists_support_bounds D.compact D.support
  obtain ⟨Nn, hNn⟩ : ∃ Nn : ℕ, Cabs + 2 * C₃ + A + 1 ≤ (Nn : ℝ) :=
    ⟨⌈Cabs + 2 * C₃ + A + 1⌉₊, Nat.le_ceil _⟩
  obtain ⟨Cwd, hCwd⟩ := hwdd (Nn + 2)
  have hCwd0 : 0 ≤ Cwd := by
    have h0 := hCwd 0
    rw [abs_zero, add_zero, one_pow, mul_one] at h0
    exact (norm_nonneg _).trans h0
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  -- the thresholds
  have hA1 : ∀ᶠ L : ℝ in atTop, ‖Real.log L‖ ≤ 1 * ‖L ^ (0.19 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.19)).def one_pos
  have hD1 : ∀ᶠ L : ℝ in atTop, 6 * ((J : ℝ) * D.P.C₀) ≤ L ^ (0.35 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.35)).eventually_ge_atTop _
  have hB1 : ∀ᶠ L : ℝ in atTop, max (Bf ^ 2) 1 ≤ L := eventually_ge_atTop _
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually ((hA1.and hD1).and hB1))
  refine ⟨(H : ℝ) ^ 2 * (4 * ((|M| + 1) * (Cwd * Real.pi))),
    max (max xP xS) (max (max xN xc) (max x₁ (max 2 (max ((c₁⁻¹) ^ 2) ((2 * c₂) ^ 2 + 1))))),
    fun x hx I => ?_⟩
  have hxP : xP ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxS : xS ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxa := (le_max_right _ _).trans hx
  have hxN : xN ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hxa)
  have hxc : xc ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hxa)
  have hxb := (le_max_right _ _).trans hxa
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans hxb
  have hxd := (le_max_right _ _).trans hxb
  have hx2 : (2 : ℝ) ≤ x := (le_max_left _ _).trans hxd
  have hxe := (le_max_right _ _).trans hxd
  have hxc₁ : (c₁⁻¹) ^ 2 ≤ x := (le_max_left _ _).trans hxe
  have hxc₂ : (2 * c₂) ^ 2 + 1 ≤ x := (le_max_right _ _).trans hxe
  obtain ⟨⟨hlogL, hJL⟩, hBL⟩ := hx₁ x hxx₁
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := (le_max_right _ _).trans hBL
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hBfL : Bf ^ 2 ≤ Real.log x := (le_max_left _ _).trans hBL
  -- the scale `X₀ = x^{1/2}`
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀ : ℝ, X₀ = x ^ ((1 : ℝ) / 2) := ⟨_, rfl⟩
  have hX₀pos : 0 < X₀ := by
    rw [hX₀def]
    exact Real.rpow_pos_of_pos hx0 _
  have hX₀1 : 1 ≤ X₀ := by
    rw [hX₀def]
    exact Real.one_le_rpow hx1 (by norm_num)
  have hX₀sq : X₀ * X₀ = x := by
    have e : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
    rw [hX₀def, ← Real.rpow_add hx0, e, Real.rpow_one]
  have hx32 : x ^ ((3 : ℝ) / 2) = x * X₀ := by
    have e : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
    rw [hX₀def, e, Real.rpow_add hx0, Real.rpow_one]
  have hc₁X : 1 ≤ c₁ * X₀ := by
    have h : c₁⁻¹ ≤ X₀ := by
      by_contra hcon
      have hlt : X₀ < c₁⁻¹ := not_le.mp hcon
      have h2 : X₀ * X₀ < c₁⁻¹ * c₁⁻¹ := mul_lt_mul'' hlt hlt hX₀pos.le hX₀pos.le
      rw [hX₀sq, ← sq] at h2
      linarith
    calc (1 : ℝ) = c₁ * c₁⁻¹ := (mul_inv_cancel₀ hc₁.ne').symm
      _ ≤ c₁ * X₀ := mul_le_mul_of_nonneg_left h hc₁.le
  have hc₁x : 1 ≤ c₁ * x := by
    rw [← hX₀sq, ← mul_assoc]
    exact one_le_mul_of_one_le_of_one_le hc₁X hX₀1
  have hc₂X : 2 * c₂ < X₀ := by
    by_contra hcon
    have hle : X₀ ≤ 2 * c₂ := not_lt.mp hcon
    have h2 : X₀ * X₀ ≤ 2 * c₂ * (2 * c₂) := mul_le_mul hle hle hX₀pos.le (by linarith)
    rw [hX₀sq, ← sq] at h2
    linarith
  -- the dilations are at most `2 X₀`
  have hEle : 3 * ((J : ℝ) * D.P.C₀) * (Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ)) ≤
      Real.log x * (1 / 2) := by
    have hJC : 0 ≤ (J : ℝ) * D.P.C₀ := mul_nonneg (Nat.cast_nonneg _) D.P.C₀_pos.le
    have hT0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
    have hp19 : 0 ≤ Real.log x ^ (0.19 : ℝ) := Real.rpow_nonneg hL0.le _
    have hp46 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
    have hp35 : 0 ≤ Real.log x ^ (0.35 : ℝ) := Real.rpow_nonneg hL0.le _
    have hlog19 : Real.log (Real.log x) ≤ Real.log x ^ (0.19 : ℝ) := by
      have h' : ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ (0.19 : ℝ)‖ := hlogL
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0,
        abs_of_nonneg hp19] at h'
      exact h'
    have h3 : 3 * ((J : ℝ) * D.P.C₀) ≤ Real.log x ^ (0.35 : ℝ) * (1 / 2) := by linarith
    have h4 : Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤
        Real.log x ^ (0.19 : ℝ) * Real.log x ^ (0.46 : ℝ) :=
      mul_le_mul_of_nonneg_right hlog19 hp46
    have h5 := mul_le_mul h3 h4 (mul_nonneg hT0 hp46)
      (mul_nonneg hp35 (by norm_num : (0 : ℝ) ≤ 1 / 2))
    have e : Real.log x ^ (0.35 : ℝ) *
        (Real.log x ^ (0.19 : ℝ) * Real.log x ^ (0.46 : ℝ)) = Real.log x := by
      have e' : (0.35 : ℝ) + (0.19 + 0.46) = 1 := by norm_num
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, e', Real.rpow_one]
    calc 3 * ((J : ℝ) * D.P.C₀) * (Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ))
        ≤ Real.log x ^ (0.35 : ℝ) * (1 / 2) *
            (Real.log x ^ (0.19 : ℝ) * Real.log x ^ (0.46 : ℝ)) := h5
      _ = Real.log x ^ (0.35 : ℝ) *
            (Real.log x ^ (0.19 : ℝ) * Real.log x ^ (0.46 : ℝ)) * (1 / 2) := by ring
      _ = Real.log x * (1 / 2) := by rw [e]
  have hDle : ∀ (ν : ComparisonIndex (Fin I.𝔊.numBig) I.blocks J m₀)
      (s : Lists (groupFamily I.𝔊) J 1)
      (r : AuxList (groupFamily I.𝔊).big (I.family J m₀ qs hs xs ν).C),
      (dil (I.family J m₀ qs hs xs ν).C s r : ℝ) ≤ 2 * X₀ := by
    intro ν s r
    have h1 := I.dil_le hL1 (I.family J m₀ qs hs xs ν).C s r
    have h2 : Real.exp (3 * ((J : ℝ) * D.P.C₀) *
        (Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ))) ≤ X₀ := by
      rw [hX₀def, Real.rpow_def_of_pos hx0]
      exact Real.exp_le_exp.mpr hEle
    linarith
  have hDone : ∀ (ν : ComparisonIndex (Fin I.𝔊.numBig) I.blocks J m₀)
      (s : Lists (groupFamily I.𝔊) J 1)
      (r : AuxList (groupFamily I.𝔊).big (I.family J m₀ qs hs xs ν).C),
      (1 : ℝ) ≤ (dil (I.family J m₀ qs hs xs ν).C s r : ℝ) := by
    intro ν s r
    exact_mod_cast I.dil_pos (I.family J m₀ qs hs xs ν).C s r
  -- the bound for the first endpoint
  have hBexp : Bf ≤ Real.exp (1 * Real.sqrt (Real.log x)) := by
    have h1 : Bf ≤ Real.sqrt (Real.log x) :=
      calc Bf = Real.sqrt (Bf ^ 2) := (Real.sqrt_sq hBf0).symm
        _ ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt hBfL
    rw [one_mul]
    linarith [Real.add_one_le_exp (Real.sqrt (Real.log x))]
  -- the support of the cutoff
  have hrange : ∀ (ν : ComparisonIndex (Fin I.𝔊.numBig) I.blocks J m₀) (n : ℤ)
      (s : Lists (groupFamily I.𝔊) J 1)
      (r : AuxList (groupFamily I.𝔊).big (I.family J m₀ qs hs xs ν).C),
      D.Ψ ((n : ℝ) / (x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ))) ≠ 0 →
        c₁ * (x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ)) ≤ (n : ℝ) ∧
          (n : ℝ) ≤ c₂ * (x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ)) := by
    intro ν n s r hne
    have hxD : 0 < x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ) :=
      mul_pos hx0 (lt_of_lt_of_le one_pos (hDone ν s r))
    obtain ⟨h1, h2⟩ := hsup _ hne
    exact ⟨(le_div_iff₀ hxD).mp h1, (div_le_iff₀ hxD).mp h2⟩
  have hsupp : ∀ (ν : ComparisonIndex (Fin I.𝔊.numBig) I.blocks J m₀) (n : ℤ)
      (s : Lists (groupFamily I.𝔊) J 1)
      (r : AuxList (groupFamily I.𝔊).big (I.family J m₀ qs hs xs ν).C),
      D.Ψ ((n : ℝ) / (x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ))) ≠ 0 →
        X₀ ≤ (n : ℝ) ∧ (n : ℝ) < (2 : ℝ) ^ numDyads x * X₀ := by
    intro ν n s r hne
    obtain ⟨h1, h2⟩ := hrange ν n s r hne
    have hD1 := hDone ν s r
    have hD2 := hDle ν s r
    constructor
    · calc X₀ ≤ c₁ * X₀ * X₀ := le_mul_of_one_le_left hX₀pos.le hc₁X
        _ = c₁ * x := by rw [mul_assoc, hX₀sq]
        _ ≤ c₁ * (x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ)) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hx0.le hD1) hc₁.le
        _ ≤ (n : ℝ) := h1
    · calc (n : ℝ) ≤ c₂ * (x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ)) := h2
        _ ≤ c₂ * (x * (2 * X₀)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD2 hx0.le) hc₂.le
        _ = 2 * c₂ * (x * X₀) := by ring
        _ < X₀ * (x * X₀) := mul_lt_mul_of_pos_right hc₂X (mul_pos hx0 hX₀pos)
        _ = x ^ ((3 : ℝ) / 2) * X₀ := by
            rw [hx32]
            ring
        _ < (2 : ℝ) ^ numDyads x * X₀ :=
            mul_lt_mul_of_pos_right (lt_two_pow_numDyads hx1) hX₀pos
  have hwide : ∀ j : ℕ, j < numDyads x → ∀ n ∈ intWindow ((2 : ℝ) ^ j * X₀),
      ∀ (ν : ComparisonIndex (Fin I.𝔊.numBig) I.blocks J m₀)
        (s : Lists (groupFamily I.𝔊) J 1)
        (r : AuxList (groupFamily I.𝔊).big (I.family J m₀ qs hs xs ν).C),
      D.Ψ ((n : ℝ) / (x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ))) ≠ 0 →
        n + (dil (I.family J m₀ qs hs xs ν).C s r : ℤ) ∈ wideWindow ((2 : ℝ) ^ j * X₀) := by
    intro j _ n hn ν s r hne
    obtain ⟨hn1, hn2⟩ := mem_intWindow.mp hn
    obtain ⟨h1, -⟩ := hrange ν n s r hne
    have hD1 := hDone ν s r
    have hDn : (dil (I.family J m₀ qs hs xs ν).C s r : ℝ) ≤ (n : ℝ) :=
      calc (dil (I.family J m₀ qs hs xs ν).C s r : ℝ)
          ≤ c₁ * x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ) :=
            le_mul_of_one_le_left (by linarith) hc₁x
        _ = c₁ * (x * (dil (I.family J m₀ qs hs xs ν).C s r : ℝ)) := by ring
        _ ≤ (n : ℝ) := h1
    unfold wideWindow
    rw [Finset.mem_Ico]
    constructor
    · have h3 : ⌈(2 : ℝ) ^ j * X₀⌉ ≤ n := Int.ceil_le.mpr hn1
      have h4 : (0 : ℤ) ≤ (dil (I.family J m₀ qs hs xs ν).C s r : ℤ) := Int.natCast_nonneg _
      linarith
    · rw [Int.lt_ceil]
      push_cast
      linarith
  -- the total edge sum over the dyads
  obtain ⟨Sd, hSd⟩ : ∃ Sd : ℕ → ZMod H × ZMod H → ℂ, ∀ j a, Sd j a =
      ∑ n ∈ intWindow ((2 : ℝ) ^ j * X₀), ∑ s : Lists (groupFamily I.𝔊) J 1,
        ∑ ν : ComparisonIndex (Fin I.𝔊.numBig) I.blocks J m₀,
          ∑ ξ : AuxList (groupFamily I.𝔊).big (I.family J m₀ qs hs xs ν).C ×
              Lists (groupFamily I.𝔊) J 1,
            insCoef I.𝔊 D.q₀ (I.family J m₀ qs hs xs) ((2 : ℝ) ^ j * X₀)
                (wideWindow ((2 : ℝ) ^ j * X₀)) a (centeredCore D.q D.𝔞 x I.S) I.G n s ν ξ *
              D.Ψ ((n : ℝ) / (x * (dil (I.family J m₀ qs hs xs ν).C s ξ.1 : ℝ))) :=
    ⟨_, fun _ _ => rfl⟩
  have hdecomp : I.edgeTotal 𝔅 J m₀ qs hs xs =
      ∑ j ∈ Finset.range (numDyads x), ∑ a : ZMod H × ZMod H,
        ((𝔅.toFun a.1 a.2 : ℝ) : ℂ) * Sd j a :=
    (edgeTotal_eq_sum_family I 𝔅 J m₀ qs hs xs).trans
      ((sum_edgeTerm_eq_dyads I.𝔊 D.q₀ (I.family J m₀ qs hs xs) x D.Ψ 𝔅
        (centeredCore D.q D.𝔞 x I.S) I.G hX₀pos (numDyads x) hsupp hwide).trans
        (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by rw [hSd]))
  -- one dyad
  have hdy : ∀ j ∈ Finset.range (numDyads x), ∀ a : ZMod H × ZMod H,
      ‖Sd j a‖ ≤ (|M| * Real.log x ^ (-E + 2 * C₃) +
        Real.log x ^ (Cabs + 2 * C₃) * (Real.log x ^ Nn)⁻¹) * (Cwd * Real.pi) := by
    intro j hj a
    have hj' : j < numDyads x := Finset.mem_range.mp hj
    have h2j1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ one_le_two
    have hXlo : x ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ j * X₀ := by
      rw [← hX₀def]
      exact le_mul_of_one_le_left hX₀pos.le h2j1
    have hXhi : (2 : ℝ) ^ j * X₀ ≤ x ^ (2 : ℝ) :=
      calc (2 : ℝ) ^ j * X₀ ≤ x ^ ((3 : ℝ) / 2) * X₀ :=
            mul_le_mul_of_nonneg_right (two_pow_le_of_lt_numDyads hx1 hj') hX₀pos.le
        _ = x * (X₀ * X₀) := by
            rw [hx32]
            ring
        _ = x ^ (2 : ℝ) := by
            rw [hX₀sq, Real.rpow_two]
            ring
    have hX1 : 1 ≤ (2 : ℝ) ^ j * X₀ := one_le_mul_of_one_le_of_one_le h2j1 hX₀1
    have hXsq : (2 : ℝ) ^ j * X₀ ≤ x ^ 2 := by
      rw [← Real.rpow_two]
      exact hXhi
    -- the first endpoint is bounded on the dyad
    have hF : ∀ n ∈ intWindow ((2 : ℝ) ^ j * X₀),
        |centeredCore D.q D.𝔞 x I.S n.toNat| ≤ Bf := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := mem_intWindow.mp hn
      have hn0 : (1 : ℤ) ≤ n := by
        have h : (1 : ℝ) ≤ (n : ℝ) := hX1.trans hn1
        exact_mod_cast h
      have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith)]
      refine hc x hxc I.S I.slots n.toNat (by omega) ?_
      have h3 : x ^ (3 : ℝ) = x ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast x 3
      have h4 : 2 * x ^ 2 ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
      have h5 : x * x ^ 2 = x ^ 3 := by ring
      rw [hcast, h3]
      calc (n : ℝ) ≤ 2 * ((2 : ℝ) ^ j * X₀) := hn2.le
        _ ≤ 2 * x ^ 2 := mul_le_mul_of_nonneg_left hXsq (by norm_num)
        _ ≤ x * x ^ 2 := h4
        _ = x ^ 3 := h5
    obtain ⟨hNF, hNG⟩ := hN x hxN I ((2 : ℝ) ^ j * X₀) hXlo hXhi
    have h := norm_dyadSum_le I.𝔊 D.q₀_pos D.q₀_lt_one.le (I.family J m₀ qs hs xs)
      (fun ν s r => I.dil_pos (I.family J m₀ qs hs xs ν).C s r) hx0 hX1 a
      (centeredCore D.q D.𝔞 x I.S) I.G hwdc hCwd hinv hL1
      (fun ζ hζ fn g h1 h2 h3 h4 =>
        hP x hxP I ζ hζ ((2 : ℝ) ^ j * X₀) hXlo hXhi fn g
          ⟨fun n hn => (h1 n hn).trans hBexp, h2, h3, h4⟩)
      (fun ζ s => hS x hxS I ζ s) hF hNF hNG
    rw [hSd]
    exact h
  -- the sum over the dyads and the residues
  have hnum0 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  rw [hdecomp]
  calc ‖∑ j ∈ Finset.range (numDyads x), ∑ a : ZMod H × ZMod H,
        ((𝔅.toFun a.1 a.2 : ℝ) : ℂ) * Sd j a‖
      ≤ ∑ j ∈ Finset.range (numDyads x), ∑ a : ZMod H × ZMod H,
          ‖((𝔅.toFun a.1 a.2 : ℝ) : ℂ) * Sd j a‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ _j ∈ Finset.range (numDyads x), ∑ _a : ZMod H × ZMod H,
          (|M| * Real.log x ^ (-E + 2 * C₃) +
            Real.log x ^ (Cabs + 2 * C₃) * (Real.log x ^ Nn)⁻¹) * (Cwd * Real.pi) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun a _ => by
          rw [norm_mul, Complex.norm_of_nonneg (𝔅.nonneg _ _)]
          have h := mul_le_mul (𝔅.le_one a.1 a.2) (hdy j hj a) (norm_nonneg _) zero_le_one
          rw [one_mul] at h
          exact h
    _ = (numDyads x : ℝ) * ((H : ℝ) ^ 2 * ((|M| * Real.log x ^ (-E + 2 * C₃) +
          Real.log x ^ (Cabs + 2 * C₃) * (Real.log x ^ Nn)⁻¹) * (Cwd * Real.pi))) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_univ,
          Fintype.card_prod, ZMod.card, nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (H : ℝ) ^ 2 * (4 * ((|M| + 1) * (Cwd * Real.pi))) * Real.log x ^ (-A) :=
        final_arith hL1 hE hNn (numDyads_le hL1) hnum0
          (mul_nonneg hCwd0 Real.pi_pos.le)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
