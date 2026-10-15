module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.EdgeSum
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.SchurPairingProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.SeparationTools

/-!
# Tools for the insertion of the cutoff

The parts of the proof of `InsertionLink` (`[P-06:0287–0316]`, `[PUB-tex:0479–0482]`,
`TwoSidedProof/InsertionProof.lean`) that do not involve the constants.

* `memPhysL2_markFree`, `physNormSq_markFree`: a vector with the value `g_n` at every state at the
  position `n`, vanishing outside finitely many positions, lies in `ℋ_ph` and has
  `‖g‖² = ∑_n |g_n|² ‖u_n‖²`.
* `sum_Ico_dyads`, `numDyads`: "Partition `n` into `O(L)` dyads `[X, 2X)`": the integers of
  `[x^{1/2}, 2^K x^{1/2})` are the disjoint union of the windows `[2^j x^{1/2}, 2^{j+1} x^{1/2})`,
  `j < K`, and `K = numDyads x ≤ 4L` of them cover `[x^{1/2}, x²)`.
* `physCoef_mul_phase`: the factor `D^{-iv}` of (cor:insertion-separation) turns the row
  coefficient at `ζ = 0` into the row coefficient at `ζ = -v`.
* `resInd`, `sum_weight_resInd`: "Write `𝓑` as a sum of at most `H²` products of residue
  indicators, one at each endpoint."
* `firstVal`, `secondVal`: the two endpoint vectors — "Use endpoint vectors with values `F_x(n)`
  and `G(n')`, respectively, and with one extra half-damping factor at each endpoint" and "Put
  `X/n` into the first vector" — with a residue indicator at each endpoint; the second vector is
  restricted to the enlarged dyad. Their norms are bounded by the two sums of
  `EndpointNormsAt` (`sum_firstVal_le`, `physNormSq_secondVal_le`).
* `insCoef`, `sum_insCoef_phase_eq`: with the phase `(n/x)^{iv} D^{-iv}` the edge sum over a dyad
  is `X⁻¹ ⟨f_v, 𝒜_{-v} g⟩`; `edgeSummand_eq_sum_insCoef`: with the cutoff it is the edge sum.
* `cutoff_eq_integral`: (cor:insertion-separation) at one term.
* `norm_dyad_le`: the bound for one dyad and one pair of residues from the bounds for
  `⟨f_v, 𝒜_{-v} g⟩`, by `Separation.norm_sum_integral_phase_le`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Insertion

/-! ### Vectors independent of the marks -/

section MarkFree

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

theorem physDensity_markFree_eq_zero (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)
    (W : Finset 𝔭.Pos) (gn : 𝔭.Pos → ℂ) (hgn : ∀ n, n ∉ W → gn n = 0) (s : PState 𝔭 𝒢 J ℓ)
    (hs : s ∉ W ×ˢ (Finset.univ : Finset (Lists 𝒢 J ℓ))) :
    physDensity 𝔭 𝒢 J ℓ (fun s => gn s.1) s = 0 := by
  have hs1 : s.1 ∉ W := fun h => hs (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  rw [Pairing.physDensity_eq 𝔭 𝒢 J ℓ (fun s => gn s.1) s]
  show Pairing.physWeight 𝔭 𝒢 J ℓ s * ‖gn s.1‖ ^ 2 = 0
  rw [hgn s.1 hs1, norm_zero, zero_pow two_ne_zero, mul_zero]

/-- A vector independent of the marks that vanishes outside finitely many positions lies in
`ℋ_ph`. -/
theorem memPhysL2_markFree (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) (W : Finset 𝔭.Pos)
    (gn : 𝔭.Pos → ℂ) (hgn : ∀ n, n ∉ W → gn n = 0) :
    MemPhysL2 𝔭 𝒢 J ℓ (fun s => gn s.1) := by
  unfold MemPhysL2
  exact summable_of_ne_finset_zero (physDensity_markFree_eq_zero 𝔭 𝒢 J ℓ W gn hgn)

/-- `‖g‖² = ∑_n |g_n|² ‖u_n‖²` for a vector independent of the marks that vanishes outside a
finite set of positions. -/
theorem physNormSq_markFree (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) (W : Finset 𝔭.Pos)
    (gn : 𝔭.Pos → ℂ) (hgn : ∀ n, n ∉ W → gn n = 0) :
    physNormSq 𝔭 𝒢 J ℓ (fun s => gn s.1) = ∑ n ∈ W, ‖gn n‖ ^ 2 * unitNormSq 𝔭 𝒢 J ℓ n := by
  unfold physNormSq
  rw [tsum_eq_sum (physDensity_markFree_eq_zero 𝔭 𝒢 J ℓ W gn hgn), Finset.sum_product]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Pairing.unitNormSq_eq_sum 𝔭 𝒢 J ℓ n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pairing.physDensity_eq 𝔭 𝒢 J ℓ (fun s => gn s.1) (n, x)]
  exact mul_comm _ _

end MarkFree

/-! ### Dyads -/

/-- The integers of `[X₀, 2^K X₀)` are the disjoint union of those of the dyads
`[2^j X₀, 2^{j+1} X₀)`, `j < K`. -/
theorem sum_Ico_dyads {M : Type*} [AddCommMonoid M] (f : ℤ → M) {X₀ : ℝ} (hX₀ : 0 ≤ X₀)
    (K : ℕ) :
    ∑ n ∈ Finset.Ico ⌈X₀⌉ ⌈(2 : ℝ) ^ K * X₀⌉, f n =
      ∑ j ∈ Finset.range K, ∑ n ∈ intWindow ((2 : ℝ) ^ j * X₀), f n := by
  induction K with
  | zero =>
    rw [pow_zero, one_mul, Finset.Ico_self, Finset.sum_empty, Finset.range_zero,
      Finset.sum_empty]
  | succ K ih =>
    have h1 : ⌈X₀⌉ ≤ ⌈(2 : ℝ) ^ K * X₀⌉ :=
      Int.ceil_mono (le_mul_of_one_le_left hX₀ (one_le_pow₀ one_le_two))
    have h2 : ⌈(2 : ℝ) ^ K * X₀⌉ ≤ ⌈(2 : ℝ) ^ (K + 1) * X₀⌉ :=
      Int.ceil_mono (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ one_le_two (Nat.le_succ K)) hX₀)
    have e : 2 * ((2 : ℝ) ^ K * X₀) = (2 : ℝ) ^ (K + 1) * X₀ := by
      rw [pow_succ]
      ring
    have hw : intWindow ((2 : ℝ) ^ K * X₀) =
        Finset.Ico ⌈(2 : ℝ) ^ K * X₀⌉ ⌈(2 : ℝ) ^ (K + 1) * X₀⌉ := by
      unfold intWindow
      rw [e]
    rw [Finset.sum_range_succ, ← ih, hw, ← Finset.Ico_union_Ico_eq_Ico h1 h2,
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]

/-- The number of dyads `[2^j x^{1/2}, 2^{j+1} x^{1/2})` that cover `[x^{1/2}, x²)`. -/
def numDyads (x : ℝ) : ℕ := ⌊3 / 2 * Real.log x / Real.log 2⌋₊ + 1

theorem two_rpow_eq {x : ℝ} (hx : 0 < x) :
    (2 : ℝ) ^ (3 / 2 * Real.log x / Real.log 2) = x ^ ((3 : ℝ) / 2) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have e : Real.log 2 * (3 / 2 * Real.log x / Real.log 2) = Real.log x * (3 / 2) := by
    rw [mul_comm (Real.log 2), div_mul_cancel₀ _ hlog2, mul_comm]
  rw [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos hx, e]

/-- `x^{3/2} < 2^K` for `K = numDyads x`. -/
theorem lt_two_pow_numDyads {x : ℝ} (hx : 1 ≤ x) : x ^ ((3 : ℝ) / 2) < (2 : ℝ) ^ numDyads x := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h1 : 3 / 2 * Real.log x / Real.log 2 <
      ((numDyads x : ℕ) : ℝ) := by
    unfold numDyads
    rw [Nat.cast_add_one]
    exact Nat.lt_floor_add_one _
  rw [← two_rpow_eq hx0, ← Real.rpow_natCast]
  exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two h1

/-- `2^j ≤ x^{3/2}` for `j < numDyads x`. -/
theorem two_pow_le_of_lt_numDyads {x : ℝ} (hx : 1 ≤ x) {j : ℕ} (hj : j < numDyads x) :
    (2 : ℝ) ^ j ≤ x ^ ((3 : ℝ) / 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hy0 : 0 ≤ 3 / 2 * Real.log x / Real.log 2 :=
    div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hx)) (Real.log_pos one_lt_two).le
  have hj' : j ≤ ⌊3 / 2 * Real.log x / Real.log 2⌋₊ := by
    unfold numDyads at hj
    omega
  have h1 : (j : ℝ) ≤ 3 / 2 * Real.log x / Real.log 2 :=
    (Nat.cast_le.mpr hj').trans (Nat.floor_le hy0)
  rw [← two_rpow_eq hx0, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two h1

/-- At most `4L` dyads. -/
theorem numDyads_le {x : ℝ} (hL : 1 ≤ Real.log x) : (numDyads x : ℝ) ≤ 4 * Real.log x := by
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog2pos : 0 < Real.log 2 := lt_trans (by norm_num) hlog2
  have hy0 : 0 ≤ 3 / 2 * Real.log x / Real.log 2 :=
    div_nonneg (mul_nonneg (by norm_num) (by linarith)) hlog2pos.le
  have h1 : 3 / 2 * Real.log x / Real.log 2 ≤ 3 * Real.log x := by
    rw [div_le_iff₀ hlog2pos]
    have h := mul_le_mul_of_nonneg_left hlog2.le (by linarith : (0 : ℝ) ≤ 3 * Real.log x)
    linarith
  have h2 : ((⌊3 / 2 * Real.log x / Real.log 2⌋₊ : ℕ) : ℝ) ≤ 3 / 2 * Real.log x / Real.log 2 :=
    Nat.floor_le hy0
  unfold numDyads
  rw [Nat.cast_add_one]
  linarith

/-! ### The phase of the row coefficient -/

/-- `e^{-iv log D} = D^{-iv}` for a positive integer `D`. -/
theorem phase_neg_log_natCast {D : ℕ} (hD : 0 < D) (v : ℝ) :
    Separation.phase v (-Real.log (D : ℝ)) = ((D : ℕ) : ℂ) ^ (((-v : ℝ) : ℂ) * Complex.I) := by
  have e : v * -Real.log (D : ℝ) = -v * Real.log (D : ℝ) := by ring
  rw [Separation.natCast_cpow_eq_phase hD (-v)]
  unfold Separation.phase
  rw [e]

/-- **The factor `D^{-iv}` moves the row coefficient from `ζ = 0` to `ζ = -v`.** -/
theorem physCoef_mul_phase {S B : Type} [Fintype S] [Fintype B] (𝔭 : PosModel)
    (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (n : 𝔭.Pos)
    (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C) (x' : Lists 𝒢 J ℓ) (hD : 0 < dil ν.C x r)
    (v : ℝ) :
    physCoef 𝔭 𝒢 q ν k 0 n x r x' * Separation.phase v (-Real.log (dil ν.C x r : ℝ)) =
      physCoef 𝔭 𝒢 q ν k (-v) n x r x' := by
  rw [phase_neg_log_natCast hD v]
  unfold physCoef
  split_ifs with hc
  · rw [Complex.ofReal_zero, zero_mul, Complex.cpow_zero]
    ring
  · rw [zero_mul]

/-! ### Residue indicators -/

/-- The indicator of a residue class of positions. -/
def resInd {H : ℕ} (a : ZMod H) (n : ℤ) : ℂ := if (n : ZMod H) = a then 1 else 0

theorem norm_resInd_le_one {H : ℕ} (a : ZMod H) (n : ℤ) : ‖resInd a n‖ ≤ 1 := by
  unfold resInd
  split_ifs
  · rw [norm_one]
  · rw [norm_zero]
    exact zero_le_one

theorem sum_indicator_prod {α : Type} [Fintype α] [DecidableEq α] (f : α → α → ℂ) (u v : α) :
    ∑ a : α × α, f a.1 a.2 * ((if u = a.1 then 1 else 0) * (if v = a.2 then 1 else 0)) =
      f u v := by
  rw [Finset.sum_eq_single (u, v)]
  · show f u v * ((if u = u then 1 else 0) * (if v = v then 1 else 0)) = f u v
    rw [if_pos rfl, if_pos rfl, mul_one, mul_one]
  · intro b _ hb
    by_cases h1 : u = b.1
    · by_cases h2 : v = b.2
      · exact absurd (Prod.ext h1.symm h2.symm) hb
      · rw [if_neg h2, mul_zero, mul_zero]
    · rw [if_neg h1, zero_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **A joint weight is a combination of at most `H²` products of residue indicators**, one at
each endpoint (`[PUB-tex:0479–0480]`). -/
theorem sum_weight_resInd {H : ℕ} [NeZero H] (𝔅 : JointResidueWeight H) (n n' : ℤ) :
    ∑ a : ZMod H × ZMod H, ((𝔅.toFun a.1 a.2 : ℝ) : ℂ) * (resInd a.1 n * resInd a.2 n') =
      ((𝔅.toFun (n : ZMod H) (n' : ZMod H) : ℝ) : ℂ) :=
  sum_indicator_prod (fun a₁ a₂ : ZMod H => ((𝔅.toFun a₁ a₂ : ℝ) : ℂ)) (n : ZMod H)
    (n' : ZMod H)

/-! ### The two endpoint vectors -/

open _root_.Classical in
/-- **The first endpoint at the position `n`, without its phase** (`[P-06:0262–0266, 0297]`):
`(X/n) 1_{n ≡ a} F(n) q₀^{(ω(n) - Ms)/2}` at a position that carries a physical state, and `0`
elsewhere. -/
def firstVal (𝔊 : ActiveGroups) (J : ℕ) (q₀ X : ℝ) {H : ℕ} (a : ZMod H) (F : ℕ → ℝ) (n : ℤ) :
    ℂ :=
  if ∃ s : Lists (groupFamily 𝔊) J 1, IsPhys intPos n s then
    ((X / (n : ℝ) : ℝ) : ℂ) * resInd a n * ((F n.toNat : ℝ) : ℂ) *
      ((damping intPos (groupFamily 𝔊) J 1 q₀ n : ℝ) : ℂ)
  else 0

theorem firstVal_of_isPhys {𝔊 : ActiveGroups} {J : ℕ} (q₀ X : ℝ) {H : ℕ} (a : ZMod H)
    (F : ℕ → ℝ) {n : ℤ} {s : Lists (groupFamily 𝔊) J 1} (h : IsPhys intPos n s) :
    firstVal 𝔊 J q₀ X a F n =
      ((X / (n : ℝ) : ℝ) : ℂ) * resInd a n * ((F n.toNat : ℝ) : ℂ) *
        ((damping intPos (groupFamily 𝔊) J 1 q₀ n : ℝ) : ℂ) := by
  unfold firstVal
  exact if_pos ⟨s, h⟩

/-- `|first endpoint| ≤ |F(n)| q₀^{(ω(n) - Ms)/2}` on `n ≥ X > 0`. -/
theorem norm_firstVal_le_mul (𝔊 : ActiveGroups) (J : ℕ) {q₀ X : ℝ} (hq₀ : 0 < q₀) {H : ℕ}
    (a : ZMod H) (F : ℕ → ℝ) {n : ℤ} (hX : 0 < X) (hn : X ≤ (n : ℝ)) :
    ‖firstVal 𝔊 J q₀ X a F n‖ ≤ |F n.toNat| * damping intPos (groupFamily 𝔊) J 1 q₀ n := by
  have hd : 0 < damping intPos (groupFamily 𝔊) J 1 q₀ n :=
    Schur.damping_pos intPos (groupFamily 𝔊) J 1 hq₀ n
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hX hn
  have hXn0 : 0 ≤ X / (n : ℝ) := div_nonneg hX.le hn0.le
  have hXn1 : X / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hn
  unfold firstVal
  split_ifs with hex
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_of_nonneg hXn0, Complex.norm_of_nonneg hd.le,
      Complex.norm_real, Real.norm_eq_abs]
    have h1 : X / (n : ℝ) * ‖resInd a n‖ ≤ 1 := by
      calc X / (n : ℝ) * ‖resInd a n‖ ≤ 1 * 1 :=
            mul_le_mul hXn1 (norm_resInd_le_one a n) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc X / (n : ℝ) * ‖resInd a n‖ * |F n.toNat| * damping intPos (groupFamily 𝔊) J 1 q₀ n
        ≤ 1 * |F n.toNat| * damping intPos (groupFamily 𝔊) J 1 q₀ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) hd.le
      _ = |F n.toNat| * damping intPos (groupFamily 𝔊) J 1 q₀ n := by rw [one_mul]
  · rw [norm_zero]
    exact mul_nonneg (abs_nonneg _) hd.le

/-- `|first endpoint| ≤ |F(n)|` on `n ≥ X > 0`: the damping is at most one where a physical state
exists. -/
theorem norm_firstVal_le (𝔊 : ActiveGroups) (J : ℕ) {q₀ X : ℝ} (hq₀ : 0 < q₀) (hq₁ : q₀ ≤ 1)
    {H : ℕ} (a : ZMod H) (F : ℕ → ℝ) {n : ℤ} (hX : 0 < X) (hn : X ≤ (n : ℝ)) :
    ‖firstVal 𝔊 J q₀ X a F n‖ ≤ |F n.toNat| := by
  by_cases hex : ∃ s : Lists (groupFamily 𝔊) J 1, IsPhys intPos n s
  · obtain ⟨s, hs⟩ := hex
    have hd1 : damping intPos (groupFamily 𝔊) J 1 q₀ n ≤ 1 := Schur.damping_le_one hq₀ hq₁ hs
    calc ‖firstVal 𝔊 J q₀ X a F n‖
        ≤ |F n.toNat| * damping intPos (groupFamily 𝔊) J 1 q₀ n :=
          norm_firstVal_le_mul 𝔊 J hq₀ a F hX hn
      _ ≤ |F n.toNat| * 1 := mul_le_mul_of_nonneg_left hd1 (abs_nonneg _)
      _ = |F n.toNat| := mul_one _
  · have h0 : firstVal 𝔊 J q₀ X a F n = 0 := by
      unfold firstVal
      exact if_neg hex
    rw [h0, norm_zero]
    exact abs_nonneg _

/-- The part of `‖f‖²` at one position: `|first endpoint|² ‖u_n‖² ≤ F(n)² · dampedMass(n)`. -/
theorem normSq_firstVal_mul_le (𝔊 : ActiveGroups) (J : ℕ) {q₀ X : ℝ} (hq₀ : 0 < q₀) {H : ℕ}
    (a : ZMod H) (F : ℕ → ℝ) {n : ℤ} (hX : 0 < X) (hn : X ≤ (n : ℝ)) :
    ‖firstVal 𝔊 J q₀ X a F n‖ ^ 2 * unitNormSq intPos (groupFamily 𝔊) J 1 n ≤
      F n.toNat ^ 2 * dampedMass 𝔊 J q₀ n := by
  have hU : 0 ≤ unitNormSq intPos (groupFamily 𝔊) J 1 n := by
    unfold unitNormSq
    exact mul_nonneg (Pairing.stateMass_nonneg _ _ _) (Nat.cast_nonneg _)
  have h1 : ‖firstVal 𝔊 J q₀ X a F n‖ ^ 2 ≤
      (|F n.toNat| * damping intPos (groupFamily 𝔊) J 1 q₀ n) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_firstVal_le_mul 𝔊 J hq₀ a F hX hn) 2
  calc ‖firstVal 𝔊 J q₀ X a F n‖ ^ 2 * unitNormSq intPos (groupFamily 𝔊) J 1 n
      ≤ (|F n.toNat| * damping intPos (groupFamily 𝔊) J 1 q₀ n) ^ 2 *
          unitNormSq intPos (groupFamily 𝔊) J 1 n := mul_le_mul_of_nonneg_right h1 hU
    _ = F n.toNat ^ 2 * dampedMass 𝔊 J q₀ n := by
        unfold dampedMass
        rw [mul_pow, sq_abs]
        ring

/-- **The second endpoint at the position `n`** (`[P-06:0262–0266, 0288–0289]`):
`1_{n ≡ b} G(n) q₀^{(ω(n) - Ms)/2}` on the positions of `W` and `0` elsewhere. -/
def secondVal (𝔊 : ActiveGroups) (J : ℕ) (q₀ : ℝ) (W : Finset ℤ) {H : ℕ} (b : ZMod H)
    (G : ℕ → ℂ) (n : ℤ) : ℂ :=
  if n ∈ W then
    resInd b n * G n.toNat * ((damping intPos (groupFamily 𝔊) J 1 q₀ n : ℝ) : ℂ)
  else 0

theorem secondVal_of_mem (𝔊 : ActiveGroups) (J : ℕ) (q₀ : ℝ) {W : Finset ℤ} {H : ℕ}
    (b : ZMod H) (G : ℕ → ℂ) {n : ℤ} (h : n ∈ W) :
    secondVal 𝔊 J q₀ W b G n =
      resInd b n * G n.toNat * ((damping intPos (groupFamily 𝔊) J 1 q₀ n : ℝ) : ℂ) := by
  unfold secondVal
  exact if_pos h

theorem secondVal_of_notMem (𝔊 : ActiveGroups) (J : ℕ) (q₀ : ℝ) {W : Finset ℤ} {H : ℕ}
    (b : ZMod H) (G : ℕ → ℂ) {n : ℤ} (h : n ∉ W) : secondVal 𝔊 J q₀ W b G n = 0 := by
  unfold secondVal
  exact if_neg h

/-- `‖g‖² ≤ ∑_{n ∈ W} |G(n)|² · dampedMass(n)` for the second endpoint vector. -/
theorem physNormSq_secondVal_le (𝔊 : ActiveGroups) (J : ℕ) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (W : Finset ℤ) {H : ℕ} (b : ZMod H) (G : ℕ → ℂ) :
    physNormSq intPos (groupFamily 𝔊) J 1
        (fun s : PState intPos (groupFamily 𝔊) J 1 => secondVal 𝔊 J q₀ W b G s.1) ≤
      ∑ n ∈ W, ‖G n.toNat‖ ^ 2 * dampedMass 𝔊 J q₀ n := by
  rw [physNormSq_markFree intPos (groupFamily 𝔊) J 1 W (secondVal 𝔊 J q₀ W b G)
    (fun n hn => secondVal_of_notMem 𝔊 J q₀ b G hn)]
  refine Finset.sum_le_sum fun n hn => ?_
  have hd : 0 < damping intPos (groupFamily 𝔊) J 1 q₀ n :=
    Schur.damping_pos intPos (groupFamily 𝔊) J 1 hq₀ n
  have hU : 0 ≤ unitNormSq intPos (groupFamily 𝔊) J 1 n := by
    unfold unitNormSq
    exact mul_nonneg (Pairing.stateMass_nonneg _ _ _) (Nat.cast_nonneg _)
  have h1 : ‖secondVal 𝔊 J q₀ W b G n‖ ≤
      ‖G n.toNat‖ * damping intPos (groupFamily 𝔊) J 1 q₀ n := by
    rw [secondVal_of_mem 𝔊 J q₀ b G hn, norm_mul, norm_mul, Complex.norm_of_nonneg hd.le]
    have h2 : ‖resInd b n‖ * ‖G n.toNat‖ ≤ 1 * ‖G n.toNat‖ :=
      mul_le_mul_of_nonneg_right (norm_resInd_le_one b n) (norm_nonneg _)
    rw [one_mul] at h2
    exact mul_le_mul_of_nonneg_right h2 hd.le
  have h3 : ‖secondVal 𝔊 J q₀ W b G n‖ ^ 2 ≤
      (‖G n.toNat‖ * damping intPos (groupFamily 𝔊) J 1 q₀ n) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ‖secondVal 𝔊 J q₀ W b G n‖ ^ 2 * unitNormSq intPos (groupFamily 𝔊) J 1 n
      ≤ (‖G n.toNat‖ * damping intPos (groupFamily 𝔊) J 1 q₀ n) ^ 2 *
          unitNormSq intPos (groupFamily 𝔊) J 1 n := mul_le_mul_of_nonneg_right h3 hU
    _ = ‖G n.toNat‖ ^ 2 * dampedMass 𝔊 J q₀ n := by
        unfold dampedMass
        rw [mul_pow]
        ring

/-! ### The coefficient of one transition -/

/-- **The coefficient of one transition in the pairing of the two endpoint vectors**, without
the phase: `X⁻¹ · (first endpoint at n) · ∏_g V_g^{-M} · (row coefficient at ζ = 0) · (second
endpoint at n + D)`. -/
def insCoef (𝔊 : ActiveGroups) (q₀ : ℝ) {J : ℕ} {N : Type}
    (𝔉 : N → Pattern (groupFamily 𝔊).big J 1) (X : ℝ) (W : Finset ℤ) {H : ℕ}
    (a : ZMod H × ZMod H) (F : ℕ → ℝ) (G : ℕ → ℂ) (n : ℤ) (s : Lists (groupFamily 𝔊) J 1)
    (ν : N) (ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1) : ℂ :=
  (X : ℂ)⁻¹ * (firstVal 𝔊 J q₀ X a.1 F n * ((stateMass (groupFamily 𝔊) J 1 : ℂ) *
    (physCoef intPos (groupFamily 𝔊) q₀ (𝔉 ν) 1 0 n s ξ.1 ξ.2 *
      secondVal 𝔊 J q₀ W a.2 G (intPos.shift (1 * dil (𝔉 ν).C s ξ.1) n))))

/-- The logarithm of the argument `n/(xD)` of the cutoff. -/
def insLog (x : ℝ) (n : ℤ) (D : ℕ) : ℝ := Real.log ((n : ℝ) / x) + -Real.log (D : ℝ)

/-- **The edge sum over a set of positions with the phase `(n/x)^{iv} D^{-iv}` is the pairing
`X⁻¹ ⟨f_v, 𝒜_{-v} g⟩`** of the two endpoint vectors (`[P-06:0290–0298]`). -/
theorem sum_insCoef_phase_eq (𝔊 : ActiveGroups) (q₀ : ℝ) {J : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern (groupFamily 𝔊).big J 1)
    (hD : ∀ (ν : N) (s : Lists (groupFamily 𝔊) J 1) (r : AuxList (groupFamily 𝔊).big (𝔉 ν).C),
      0 < dil (𝔉 ν).C s r)
    (x X : ℝ) (W : Finset ℤ) {H : ℕ} (a : ZMod H × ZMod H) (F : ℕ → ℝ) (G : ℕ → ℂ)
    (I : Finset ℤ) (v : ℝ) :
    ∑ n ∈ I, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
        ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
          insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
            Separation.phase v (insLog x n (dil (𝔉 ν).C s ξ.1)) =
      (X : ℂ)⁻¹ * pairMarkFree intPos (groupFamily 𝔊) J 1 I
        (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
          Separation.phase v (Real.log ((n : ℝ) / x))))
        (physOp intPos (groupFamily 𝔊) q₀ 𝔉 1 (-v)
          (fun s : PState intPos (groupFamily 𝔊) J 1 => secondVal 𝔊 J q₀ W a.2 G s.1)) := by
  have hterm : ∀ (n : ℤ) (ν : N) (s : Lists (groupFamily 𝔊) J 1)
      (ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1),
      insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
          Separation.phase v (insLog x n (dil (𝔉 ν).C s ξ.1)) =
        (X : ℂ)⁻¹ * (firstVal 𝔊 J q₀ X a.1 F n * Separation.phase v (Real.log ((n : ℝ) / x)) *
          ((stateMass (groupFamily 𝔊) J 1 : ℂ) *
            (physCoef intPos (groupFamily 𝔊) q₀ (𝔉 ν) 1 (-v) n s ξ.1 ξ.2 *
              secondVal 𝔊 J q₀ W a.2 G (intPos.shift (1 * dil (𝔉 ν).C s ξ.1) n)))) := by
    intro n ν s ξ
    unfold insCoef insLog
    rw [Separation.phase_add,
      ← physCoef_mul_phase intPos (groupFamily 𝔊) q₀ (𝔉 ν) 1 n s ξ.1 ξ.2 (hD ν s ξ.1) v]
    ring
  have key : ∀ n : ℤ, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
        ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
          insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
            Separation.phase v (insLog x n (dil (𝔉 ν).C s ξ.1)) =
      (X : ℂ)⁻¹ * (firstVal 𝔊 J q₀ X a.1 F n * Separation.phase v (Real.log ((n : ℝ) / x)) *
          ∑ ν, ∑ s : Lists (groupFamily 𝔊) J 1,
            ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
              (stateMass (groupFamily 𝔊) J 1 : ℂ) *
                (physCoef intPos (groupFamily 𝔊) q₀ (𝔉 ν) 1 (-v) n s ξ.1 ξ.2 *
                  secondVal 𝔊 J q₀ W a.2 G (intPos.shift (1 * dil (𝔉 ν).C s ξ.1) n))) := by
    intro n
    calc ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
          ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
            insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
              Separation.phase v (insLog x n (dil (𝔉 ν).C s ξ.1))
        = ∑ ν, ∑ s : Lists (groupFamily 𝔊) J 1,
            ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
              insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
                Separation.phase v (insLog x n (dil (𝔉 ν).C s ξ.1)) := Finset.sum_comm
      _ = ∑ ν, ∑ s : Lists (groupFamily 𝔊) J 1,
            ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
              (X : ℂ)⁻¹ * (firstVal 𝔊 J q₀ X a.1 F n *
                Separation.phase v (Real.log ((n : ℝ) / x)) *
                ((stateMass (groupFamily 𝔊) J 1 : ℂ) *
                  (physCoef intPos (groupFamily 𝔊) q₀ (𝔉 ν) 1 (-v) n s ξ.1 ξ.2 *
                    secondVal 𝔊 J q₀ W a.2 G (intPos.shift (1 * dil (𝔉 ν).C s ξ.1) n)))) :=
          Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun s _ =>
            Finset.sum_congr rfl fun ξ _ => hterm n ν s ξ
      _ = (X : ℂ)⁻¹ * (firstVal 𝔊 J q₀ X a.1 F n * Separation.phase v (Real.log ((n : ℝ) / x)) *
            ∑ ν, ∑ s : Lists (groupFamily 𝔊) J 1,
              ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
                (stateMass (groupFamily 𝔊) J 1 : ℂ) *
                  (physCoef intPos (groupFamily 𝔊) q₀ (𝔉 ν) 1 (-v) n s ξ.1 ξ.2 *
                    secondVal 𝔊 J q₀ W a.2 G (intPos.shift (1 * dil (𝔉 ν).C s ξ.1) n))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
  rw [pairMarkFree_physOp_markFree intPos (groupFamily 𝔊) q₀ 𝔉 1 (-v) I
    (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
      Separation.phase v (Real.log ((n : ℝ) / x))))
    (secondVal 𝔊 J q₀ W a.2 G)]
  refine (Finset.sum_congr rfl fun n _ => key n).trans ?_
  refine (Finset.mul_sum I _ ((X : ℂ)⁻¹)).symm.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.conj_conj]

/-- **The summand of the edge sum as a combination of the transition coefficients**, on a dyad:
for `n ≥ X > 0`, when the cutoff forces the target into `W`,
`(summand) = ∑_{a} 𝓑(a) · (coefficient for the residues a) · Ψ(n/(xD))`. -/
theorem edgeSummand_eq_sum_insCoef (𝔊 : ActiveGroups) (q₀ : ℝ) {J : ℕ} {N : Type}
    (𝔉 : N → Pattern (groupFamily 𝔊).big J 1) (x X : ℝ) (hX : 0 < X) (W : Finset ℤ) {H : ℕ}
    [NeZero H] (𝔅 : JointResidueWeight H) (Ψ : ℝ → ℂ) (F : ℕ → ℝ) (G : ℕ → ℂ) (n : ℤ)
    (s : Lists (groupFamily 𝔊) J 1) (ν : N)
    (ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1)
    (hW : Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ))) ≠ 0 →
      n + (dil (𝔉 ν).C s ξ.1 : ℤ) ∈ W) :
    edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s ξ.1 ξ.2 =
      ∑ a : ZMod H × ZMod H, ((𝔅.toFun a.1 a.2 : ℝ) : ℂ) *
        (insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
          Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ)))) := by
  by_cases hpc : physCoef intPos (groupFamily 𝔊) q₀ (𝔉 ν) 1 0 n s ξ.1 ξ.2 = 0
  · -- no transition
    have hL : edgeSummand 𝔊 q₀ (𝔉 ν) x Ψ 𝔅 F G n s ξ.1 ξ.2 = 0 := by
      unfold edgeSummand
      rw [hpc, mul_zero]
    rw [hL]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    unfold insCoef
    rw [hpc, zero_mul, mul_zero, mul_zero, mul_zero, zero_mul, mul_zero]
  · by_cases hΨ : Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ))) = 0
    · -- outside the support of the cutoff
      rw [edgeSummand_eq_zero ξ.2 hΨ]
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      rw [hΨ, mul_zero, mul_zero]
    · -- the main case
      have hphys : IsPhys intPos n s := (Pairing.isPhys_of_physCoef_ne_zero hpc).1
      have hmem := hW hΨ
      have hXC : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
      have hXn : (X : ℂ)⁻¹ * ((X / (n : ℝ) : ℝ) : ℂ) = (n : ℂ)⁻¹ := by
        rw [Complex.ofReal_div, Complex.ofReal_intCast, div_eq_mul_inv, ← mul_assoc,
          inv_mul_cancel₀ hXC, one_mul]
      have hterm : ∀ a : ZMod H × ZMod H, ((𝔅.toFun a.1 a.2 : ℝ) : ℂ) *
          (insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
            Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ)))) =
          ((𝔅.toFun a.1 a.2 : ℝ) : ℂ) *
              (resInd a.1 n * resInd a.2 (n + (dil (𝔉 ν).C s ξ.1 : ℤ))) *
            ((n : ℂ)⁻¹ * (Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ))) *
              ((F n.toNat : ℝ) : ℂ) * G (n + (dil (𝔉 ν).C s ξ.1 : ℤ)).toNat *
              ((stateMass (groupFamily 𝔊) J 1 : ℂ) *
                (((damping intPos (groupFamily 𝔊) J 1 q₀ n : ℝ) : ℂ) *
                  ((damping intPos (groupFamily 𝔊) J 1 q₀
                    (n + (dil (𝔉 ν).C s ξ.1 : ℤ)) : ℝ) : ℂ))) *
              physCoef intPos (groupFamily 𝔊) q₀ (𝔉 ν) 1 0 n s ξ.1 ξ.2)) := by
        intro a
        unfold insCoef
        rw [intPos_shift_one_mul, firstVal_of_isPhys q₀ X a.1 F hphys,
          secondVal_of_mem 𝔊 J q₀ a.2 G hmem, ← hXn]
        ring
      rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_mul,
        sum_weight_resInd 𝔅 n (n + (dil (𝔉 ν).C s ξ.1 : ℤ))]
      unfold edgeSummand
      rw [Complex.ofReal_mul, Complex.ofReal_mul]
      ring

/-! ### The Mellin separation at one term -/

/-- **(cor:insertion-separation) at one term** (`[P-06:0290–0296]`):
`Ψ(n/(xD)) = ∫ w(v) e^{iv (log(n/x) - log D)} dv` for `n, x, D > 0`. -/
theorem cutoff_eq_integral {Ψ wd : ℝ → ℂ}
    (hinv : ∀ t : ℝ, 0 < t → Ψ t = ∫ v : ℝ, wd v * (t : ℂ) ^ ((v : ℂ) * Complex.I)) {x : ℝ}
    (hx : 0 < x) {n : ℤ} (hn : 0 < n) {D : ℕ} (hD : 0 < D) :
    Ψ ((n : ℝ) / (x * (D : ℝ))) = ∫ v : ℝ, wd v * Separation.phase v (insLog x n D) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have ht : 0 < (n : ℝ) / (x * (D : ℝ)) := div_pos hnR (mul_pos hx hDR)
  have hlog : Real.log ((n : ℝ) / (x * (D : ℝ))) = insLog x n D := by
    unfold insLog
    rw [← div_div, Real.log_div (div_pos hnR hx).ne' hDR.ne', sub_eq_add_neg]
  have hfun : (fun v : ℝ => wd v * (((n : ℝ) / (x * (D : ℝ)) : ℝ) : ℂ) ^ ((v : ℂ) * Complex.I)) =
      fun v : ℝ => wd v * Separation.phase v (insLog x n D) := by
    funext v
    rw [Separation.cpow_eq_phase ht v, hlog]
  rw [hinv _ ht, hfun]

/-! ### One dyad and one pair of residues -/

/-- **The edge sum over one dyad for one pair of residues** (`[P-06:0297–0316]`): if
`X⁻¹ |⟨f_v, 𝒜_{-v} g⟩| ≤ B₁` for `|v| ≤ L` and `≤ B₂` for all `v`, then the sum of the transition
coefficients against the cutoff is at most `(B₁ + B₂ L^{-N}) C_w π`, for a Mellin density `w` with
`|w(v)| (1 + |v|)^{N+2} ≤ C_w`. -/
theorem norm_dyad_le (𝔊 : ActiveGroups) (q₀ : ℝ) {J : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern (groupFamily 𝔊).big J 1)
    (hD : ∀ (ν : N) (s : Lists (groupFamily 𝔊) J 1) (r : AuxList (groupFamily 𝔊).big (𝔉 ν).C),
      0 < dil (𝔉 ν).C s r)
    {x X : ℝ} (hx : 0 < x) (hX : 1 ≤ X) (W : Finset ℤ) {H : ℕ} (a : ZMod H × ZMod H)
    (F : ℕ → ℝ) (G : ℕ → ℂ) {Ψ wd : ℝ → ℂ} (hwd : Continuous wd) {Nn : ℕ} {Cwd : ℝ}
    (hdecay : ∀ v, ‖wd v‖ * (1 + |v|) ^ (Nn + 2) ≤ Cwd)
    (hinv : ∀ t : ℝ, 0 < t → Ψ t = ∫ v : ℝ, wd v * (t : ℂ) ^ ((v : ℂ) * Complex.I))
    {L B₁ B₂ : ℝ} (hL : 1 ≤ L) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hlow : ∀ v : ℝ, |v| ≤ L → ‖(X : ℂ)⁻¹ * pairMarkFree intPos (groupFamily 𝔊) J 1 (intWindow X)
        (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
          Separation.phase v (Real.log ((n : ℝ) / x))))
        (physOp intPos (groupFamily 𝔊) q₀ 𝔉 1 (-v)
          (fun s : PState intPos (groupFamily 𝔊) J 1 => secondVal 𝔊 J q₀ W a.2 G s.1))‖ ≤ B₁)
    (hall : ∀ v : ℝ, ‖(X : ℂ)⁻¹ * pairMarkFree intPos (groupFamily 𝔊) J 1 (intWindow X)
        (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
          Separation.phase v (Real.log ((n : ℝ) / x))))
        (physOp intPos (groupFamily 𝔊) q₀ 𝔉 1 (-v)
          (fun s : PState intPos (groupFamily 𝔊) J 1 => secondVal 𝔊 J q₀ W a.2 G s.1))‖ ≤ B₂) :
    ‖∑ n ∈ intWindow X, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
        ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
          insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
            Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ)))‖ ≤
      (B₁ + B₂ * (L ^ Nn)⁻¹) * (Cwd * Real.pi) := by
  -- the positions of the dyad are positive
  have hpos : ∀ n ∈ intWindow X, (0 : ℤ) < n := by
    intro n hn
    have h1 : X ≤ (n : ℝ) := (mem_intWindow.mp hn).1
    have h2 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (lt_of_lt_of_le one_pos hX) h1
    exact_mod_cast h2
  -- the cutoff as an integral
  have h1 : ∑ n ∈ intWindow X, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
        ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
          insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
            Ψ ((n : ℝ) / (x * (dil (𝔉 ν).C s ξ.1 : ℝ))) =
      ∑ n ∈ intWindow X, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ ν,
        ∑ ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1,
          insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
            ∫ v : ℝ, wd v * Separation.phase v (insLog x n (dil (𝔉 ν).C s ξ.1)) :=
    Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ξ _ => by
        rw [cutoff_eq_integral hinv hx (hpos n hn) (hD ν s ξ.1)]
  rw [h1, SchurTest.sum_nested_eq (intWindow X)
    (fun (n : ℤ) (s : Lists (groupFamily 𝔊) J 1) (ν : N)
      (ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1) =>
        insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
          ∫ v : ℝ, wd v * Separation.phase v (insLog x n (dil (𝔉 ν).C s ξ.1)))]
  -- the combination of phases is the pairing
  have hΦ : ∀ v : ℝ,
      ∑ p ∈ intWindow X ×ˢ (Finset.univ : Finset (Lists (groupFamily 𝔊) J 1 ×
          (Σ ν, AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1))),
        insCoef 𝔊 q₀ 𝔉 X W a F G p.1 p.2.1 p.2.2.1 p.2.2.2 *
          Separation.phase v (insLog x p.1 (dil (𝔉 p.2.2.1).C p.2.1 p.2.2.2.1)) =
      (X : ℂ)⁻¹ * pairMarkFree intPos (groupFamily 𝔊) J 1 (intWindow X)
        (fun n : ℤ => conj (firstVal 𝔊 J q₀ X a.1 F n *
          Separation.phase v (Real.log ((n : ℝ) / x))))
        (physOp intPos (groupFamily 𝔊) q₀ 𝔉 1 (-v)
          (fun s : PState intPos (groupFamily 𝔊) J 1 => secondVal 𝔊 J q₀ W a.2 G s.1)) := by
    intro v
    rw [← sum_insCoef_phase_eq 𝔊 q₀ 𝔉 hD x X W a F G (intWindow X) v]
    exact (SchurTest.sum_nested_eq (intWindow X)
      (fun (n : ℤ) (s : Lists (groupFamily 𝔊) J 1) (ν : N)
        (ξ : AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1) =>
          insCoef 𝔊 q₀ 𝔉 X W a F G n s ν ξ *
            Separation.phase v (insLog x n (dil (𝔉 ν).C s ξ.1)))).symm
  have hlow' : ∀ v : ℝ, |v| ≤ L →
      ‖∑ p ∈ intWindow X ×ˢ (Finset.univ : Finset (Lists (groupFamily 𝔊) J 1 ×
          (Σ ν, AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1))),
        insCoef 𝔊 q₀ 𝔉 X W a F G p.1 p.2.1 p.2.2.1 p.2.2.2 *
          Separation.phase v (insLog x p.1 (dil (𝔉 p.2.2.1).C p.2.1 p.2.2.2.1))‖ ≤ B₁ := by
    intro v hv
    rw [hΦ v]
    exact hlow v hv
  have hall' : ∀ v : ℝ,
      ‖∑ p ∈ intWindow X ×ˢ (Finset.univ : Finset (Lists (groupFamily 𝔊) J 1 ×
          (Σ ν, AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1))),
        insCoef 𝔊 q₀ 𝔉 X W a F G p.1 p.2.1 p.2.2.1 p.2.2.2 *
          Separation.phase v (insLog x p.1 (dil (𝔉 p.2.2.1).C p.2.1 p.2.2.2.1))‖ ≤ B₂ := by
    intro v
    rw [hΦ v]
    exact hall v
  exact Separation.norm_sum_integral_phase_le _
    (fun p : ℤ × (Lists (groupFamily 𝔊) J 1 ×
        (Σ ν, AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1)) =>
      insCoef 𝔊 q₀ 𝔉 X W a F G p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p : ℤ × (Lists (groupFamily 𝔊) J 1 ×
        (Σ ν, AuxList (groupFamily 𝔊).big (𝔉 ν).C × Lists (groupFamily 𝔊) J 1)) =>
      insLog x p.1 (dil (𝔉 p.2.2.1).C p.2.1 p.2.2.2.1))
    hwd hdecay hL hB₁ hB₂ hlow' hall'

end Insertion

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
