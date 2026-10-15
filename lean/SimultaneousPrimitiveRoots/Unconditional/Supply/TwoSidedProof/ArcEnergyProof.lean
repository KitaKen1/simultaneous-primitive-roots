module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.ArcEnergyTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.WeightedTail
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ScaleFacts

/-!
# The arc energy from (cor:SM)

`arcEnergyLink d : ArcEnergyLink d`, i.e. `LocalMellin → EndpointSquares d → EndpointEnergy d →
ArcEnergy d` (`[P-06:0530–0553]`), for every number of slots.

"Apply the lemma to `a_w = 𝒰(w) e(hw/k)`. The additive error is negligible by
(cor:endpoint-squares). The Dirichlet mean-square bound in Lemma 2.2 gives [the bound of the
tail] … which is as small as required on choosing `j` last. It remains to prove (cor:SM) …
Notice that the first term in (cor:local-mellin) is `Y` times the integral in (cor:SM)."

With `H = Y/(x L^{C₆})` (so that the arc is `|β| ≤ 1/H`), `T₀ = x L^{C₆+1}` (so that
`H T₀ / Y = L`) and `P_a(t) = ∑_w a_w w^{it}`, `a_w = 𝒰(w) e(hw/k)` (`arcCoeff`):

* `∑_w 𝒰(w) e((h/k + β) w) = ∑_w a_w e(β w)` (`finsum_arc_eq_sum`), a finite sum over
  `a₁ Y ≤ w ≤ a₂ Y`;
* the weighted integral of (cor:local-mellin) is at most
  `∫_{|t| ≤ T₀} |P_a|² + 2 G L^{-(j-1)}` (`integral_weighted_le`), where `G` bounds the mean
  square of `P_a` on every interval of length `Y` (`integral_window_poly_le`, from
  `Classical.integral_normSq_dirichletPolynomial_le_nat`; the length term is `≤ Cs Y L` by
  `EndpointProof.scaleFacts`, and `∑ |a_w|² ≤ Y L^{C₅}` by `EndpointSquares d`);
* `∫_{|t| ≤ T₀} |P_a|² = Y² ∫_{|τ| ≤ x L^{C₆+1}} |Y⁻¹ P_a(τ)|² dτ ≤ Y² M L^{-A}`
  (`normSq_window_poly_eq`) by `EndpointEnergyAt d B (C₆ + 1)`, with `h` not required coprime
  to `k`;
* the additive error is `(x L^{C₆})⁻² ∑ |a_w|² ≤ Y L^{-A}` because `L^{A + C₅} ≤ x`
  (`additive_error_le`).

The decay order is `j = ⌈A + C₅ + 3⌉ + 2`, chosen after `C₅`; the final constant is
`max(C_j, 0) (max(M, 0) + 2 (1 + |Cs|) + 1)` (`arc_final`). The estimate for one sequence is
`arcEnergy_core`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open Filter MeasureTheory
open scoped Topology

noncomputable section

/-! ### The estimate for one sequence -/

/-- **The arc energy of one sequence** supported on `a₁ Y ≤ w ≤ a₂ Y`, from the lemma
(local Mellin energy) with decay order `j`, the square sum `∑ |𝒰(w)|² ≤ Y L^{C₅}`, the length
term of the mean value theorem and the energy at the times `|τ| ≤ x L^{C₆ + 1}`. -/
theorem arcEnergy_core {j : ℕ} (hj2 : 2 ≤ j) {a₁ a₂ CM : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hCM : ∀ Y H : ℝ, 1 ≤ H → H ≤ Y → ∀ (s : Finset ℕ) (a : ℕ → ℂ),
      (∀ w ∈ s, a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y) →
      ∫ β in (-(1 / H))..(1 / H), ‖∑ w ∈ s, a w * addChar (β * (w : ℝ))‖ ^ 2 ≤
        CM * (Y⁻¹ * (∫ t : ℝ, (1 + H * |t| / Y) ^ (-(j : ℝ)) *
            ‖∑ w ∈ s, a w * (w : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) +
          (H / Y) ^ 2 * ∑ w ∈ s, ‖a w‖ ^ 2))
    {x Y C₆ C₅ A ME Cs : ℝ} (hC₆ : 0 < C₆) (hx1 : 1 ≤ x) (hL1 : 1 < Real.log x) (hY0 : 0 < Y)
    (hT₀Y : x * Real.log x ^ (C₆ + 1) ≤ Y) (hjA : A + C₅ + 3 ≤ ((j - 1 : ℕ) : ℝ))
    (hLx : Real.log x ^ (A + C₅) ≤ x)
    (hlen : 4 * (⌊a₂ * Y⌋₊ : ℝ) * (1 + Real.log (⌊a₂ * Y⌋₊ : ℝ)) ≤ Cs * Y * Real.log x)
    (U : ℕ → ℂ) (hUw : ∀ w : ℕ, U w ≠ 0 → a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y)
    (hsqU : ∑ᶠ w : ℕ, ‖U w‖ ^ 2 ≤ Y * Real.log x ^ C₅) (k : ℕ) (n : ℤ)
    (hSM : ∫ τ in (-(x * Real.log x ^ (C₆ + 1)))..(x * Real.log x ^ (C₆ + 1)),
      ‖endpointPolynomial U Y n k τ‖ ^ 2 ≤ ME * Real.log x ^ (-A)) :
    ∫ β in (-(x * Real.log x ^ C₆ / Y))..(x * Real.log x ^ C₆ / Y),
        ‖∑ᶠ w : ℕ, U w * addChar (((n : ℝ) / (k : ℝ) + β) * (w : ℝ))‖ ^ 2 ≤
      max CM 0 * (max ME 0 + 2 * (1 + |Cs|) + 1) * Y * Real.log x ^ (-A) := by
  have hL0 : 0 < Real.log x := lt_trans one_pos hL1
  obtain ⟨hq1, hxq, hH1, hHY, hΛT, hHρ, h1H, hT₀0⟩ := arc_width hC₆ hx1 hL1 hY0 hT₀Y
  have hq0 : 0 < x * Real.log x ^ C₆ := lt_of_lt_of_le one_pos hq1
  -- the window
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊a₂ * Y⌋₊ := ⟨_, rfl⟩
  obtain ⟨s, hsd⟩ : ∃ s : Finset ℕ, s = Finset.Icc ⌈a₁ * Y⌉₊ N := ⟨_, rfl⟩
  have hUs : ∀ w : ℕ, U w ≠ 0 → w ∈ s := by
    intro w hw
    obtain ⟨h1, h2⟩ := hUw w hw
    rw [hsd, hN]
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩
  have hs : ∀ w ∈ s, a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y := by
    intro w hw
    rw [hsd, hN] at hw
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hw
    exact ⟨Nat.ceil_le.mp h1,
      (Nat.cast_le.mpr h2).trans (Nat.floor_le (mul_nonneg ha₂.le hY0.le))⟩
  have hsN : s ⊆ Finset.Icc 1 N := by
    rw [hsd]
    exact Finset.Icc_subset_Icc (Nat.ceil_pos.mpr (mul_pos ha₁ hY0)) le_rfl
  have ha0 : ∀ w, w ∉ s → arcCoeff U n k w = 0 := fun w hw =>
    arcCoeff_eq_zero (by
      by_contra h'
      exact hw (hUs w h')) n k
  -- the square sums
  have hsq : ∑ w ∈ Finset.Icc 1 N, ‖arcCoeff U n k w‖ ^ 2 ≤ Y * Real.log x ^ C₅ := by
    rw [sum_normSq_arcCoeff_eq (U := U) (N := N) (fun w hw => hsN (hUs w hw)) n k]
    exact hsqU
  have hSa : ∑ w ∈ s, ‖arcCoeff U n k w‖ ^ 2 ≤ Y * Real.log x ^ C₅ :=
    (Finset.sum_le_sum_of_subset_of_nonneg (f := fun w => ‖arcCoeff U n k w‖ ^ 2) hsN
      fun w _ _ => sq_nonneg _).trans hsq
  -- the mean square of `P_a` on the intervals of length `Y`
  have hlen' : Y + 4 * (N : ℝ) * (1 + Real.log (N : ℝ)) ≤ Y + Cs * Y * Real.log x := by
    rw [hN]
    exact add_le_add le_rfl hlen
  have hlen0 : (0 : ℝ) ≤ Y + 4 * (N : ℝ) * (1 + Real.log (N : ℝ)) :=
    add_nonneg hY0.le (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
      (add_nonneg zero_le_one (Real.log_natCast_nonneg N)))
  have hMV : ∀ T : ℝ,
      ∫ τ in T..(T + Y), ‖∑ w ∈ s, arcCoeff U n k w * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2 ≤
        (Y + Cs * Y * Real.log x) * (Y * Real.log x ^ C₅) := fun T =>
    (integral_window_poly_le hsN ha0 hY0.le T).trans
      (mul_le_mul hlen' hsq (Finset.sum_nonneg fun w _ => sq_nonneg _) (hlen0.trans hlen'))
  -- the low times: (cor:SM)
  have hmid : ∫ τ in (-(x * Real.log x ^ (C₆ + 1)))..(x * Real.log x ^ (C₆ + 1)),
      ‖∑ w ∈ s, arcCoeff U n k w * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2 ≤
        Y ^ 2 * (ME * Real.log x ^ (-A)) := by
    have hfun2 : (fun τ : ℝ =>
          ‖∑ w ∈ s, arcCoeff U n k w * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2) =
        fun τ : ℝ => Y ^ 2 * ‖endpointPolynomial U Y n k τ‖ ^ 2 :=
      funext fun τ => normSq_window_poly_eq hUs hY0 n k τ
    rw [hfun2, intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hSM (sq_nonneg Y)
  -- the weighted integral of (cor:local-mellin)
  obtain ⟨Iw, hIw⟩ : ∃ Iw : ℝ, Iw = ∫ τ : ℝ,
      (1 + Y / (x * Real.log x ^ C₆) * |τ| / Y) ^ (-(j : ℝ)) *
        ‖∑ w ∈ s, arcCoeff U n k w * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2 := ⟨_, rfl⟩
  have htail : Iw ≤ (∫ τ in (-(x * Real.log x ^ (C₆ + 1)))..(x * Real.log x ^ (C₆ + 1)),
        ‖∑ w ∈ s, arcCoeff U n k w * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2) +
      2 * ((Y + Cs * Y * Real.log x) * (Y * Real.log x ^ C₅)) *
        (Real.log x ^ (j - 1))⁻¹ := by
    rw [hIw]
    exact integral_weighted_le hj2 hY0 hH1 hL0 hT₀0 hΛT (continuous_window_poly hsN ha0)
      (fun τ => sq_nonneg _) hMV
  have htail' : Iw ≤ Y ^ 2 * (ME * Real.log x ^ (-A)) +
      2 * ((Y + Cs * Y * Real.log x) * (Y * Real.log x ^ C₅)) *
        (Real.log x ^ (j - 1))⁻¹ := htail.trans (add_le_add hmid le_rfl)
  have hIw0 : 0 ≤ Iw := by
    rw [hIw]
    exact integral_nonneg fun τ => mul_nonneg
      (Real.rpow_nonneg (add_nonneg zero_le_one (div_nonneg
        (mul_nonneg (div_nonneg hY0.le hq0.le) (abs_nonneg τ)) hY0.le)) _) (sq_nonneg _)
  -- the lemma (local Mellin energy)
  have hLMx := hCM Y (Y / (x * Real.log x ^ C₆)) hH1 hHY s (arcCoeff U n k) hs
  rw [h1H, ← hIw, hHρ] at hLMx
  -- the additive error and the powers of `L`
  have hT2 : ((x * Real.log x ^ C₆)⁻¹) ^ 2 * ∑ w ∈ s, ‖arcCoeff U n k w‖ ^ 2 ≤
      Y * Real.log x ^ (-A) := additive_error_le hq1 hL0 hY0.le hSa (hLx.trans hxq)
  have hpow : Real.log x * Real.log x ^ C₅ * (Real.log x ^ (j - 1))⁻¹ ≤ Real.log x ^ (-A) :=
    tail_power_le hL1 hjA
  -- the arc
  have hfun1 : (fun β : ℝ =>
        ‖∑ᶠ w : ℕ, U w * addChar (((n : ℝ) / (k : ℝ) + β) * (w : ℝ))‖ ^ 2) =
      fun β : ℝ => ‖∑ w ∈ s, arcCoeff U n k w * addChar (β * (w : ℝ))‖ ^ 2 :=
    funext fun β => by rw [finsum_arc_eq_sum hUs n k β]
  rw [hfun1]
  have hLm0 : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0.le _
  have hP0 : 0 ≤ Real.log x ^ C₅ := Real.rpow_nonneg hL0.le _
  have hKi0 : 0 ≤ (Real.log x ^ (j - 1))⁻¹ := inv_nonneg.mpr (pow_nonneg hL0.le _)
  have hSa0 : 0 ≤ ((x * Real.log x ^ C₆)⁻¹) ^ 2 * ∑ w ∈ s, ‖arcCoeff U n k w‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun w _ => sq_nonneg _)
  exact arc_final hY0 hL1.le hLm0 hP0 hKi0 hIw0 hSa0 hLMx htail' hT2 hpow

/-! ### The statement -/

/-- The data of (cor:SM) for the fixed data of Theorem 6.1, a bound `m'` for the marks, a cutoff
class, a twist exponent, the scale constants and the exponent `C₆`. -/
def arcData (D : FixedData) (m' : ℕ) {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₁₂ : a₁ ≤ a₂) (Dψ : ℕ → ℝ)
    (Cσ c₁ c₂ : ℝ) {C₆ : ℝ} (hC₆ : 0 < C₆) : EndpointProof.EndpointData where
  ε := D.ε
  q := D.q
  q₀ := D.q₀
  K := D.K
  𝔞 := D.𝔞
  P := D.P
  m' := m'
  a₁ := a₁
  a₂ := a₂
  Dψ := Dψ
  Cσ := Cσ
  c₁ := c₁
  c₂ := c₂
  C₆ := C₆
  ε_pos := D.ε_pos
  q_pos := D.q_pos
  q_lt_one := D.q_lt_one
  q₀_pos := D.q₀_pos
  q₀_lt_one := D.q₀_lt_one
  a₁_pos := ha₁
  a₁_le_a₂ := ha₁₂
  C₆_pos := hC₆

/-- **The arc energy from (cor:SM)** (`[P-06:0530–0553]`), for every number of slots. This is the
field `arcEnergy` of `OpenLeaves d H 𝔅`. -/
theorem arcEnergyLink (d : ℕ) : ArcEnergyLink d := by
  intro hLM hES hEE B C₆ hB hC₆ D m' a₁ a₂ ha₁ ha₁₂ Dψ Cσ c₁ c₂ A hA
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha₁₂
  -- (cor:endpoint-squares), then the decay order, then the lemma, (cor:SM) and the scales
  obtain ⟨C₅, xE, hE⟩ := hES D m' a₁ a₂ ha₁ ha₁₂ (Dψ 0)
  obtain ⟨j, hj2, hjA⟩ : ∃ j : ℕ, 2 ≤ j ∧ A + C₅ + 3 ≤ ((j - 1 : ℕ) : ℝ) := by
    refine ⟨⌈A + C₅ + 3⌉₊ + 2, by omega, ?_⟩
    have e : ⌈A + C₅ + 3⌉₊ + 2 - 1 = ⌈A + C₅ + 3⌉₊ + 1 := by omega
    rw [e, Nat.cast_add_one]
    exact (Nat.le_ceil (A + C₅ + 3)).trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨CM, hCM⟩ := hLM j hj2 a₁ a₂ ha₁ ha₁₂
  obtain ⟨ME, xS, hS⟩ := hEE B (C₆ + 1) hB (add_pos hC₆ one_pos) D.ε D.ε_pos D.q D.q₀ D.q_pos
    D.q_lt_one D.q₀_pos D.q₀_lt_one D.K D.𝔞 D.P m' a₁ a₂ ha₁ ha₁₂ Dψ Cσ c₁ c₂ A hA
  obtain ⟨Cs, xF, hF⟩ := EndpointProof.scaleFacts (arcData D m' ha₁ ha₁₂ Dψ Cσ c₁ c₂ hC₆)
  have hA1 : ∀ᶠ L : ℝ in atTop, ‖Real.log L‖ ≤ 1 * ‖L ^ (0.19 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.19)).def one_pos
  have hD1 : ∀ᶠ L : ℝ in atTop, |c₂| ≤ L ^ (0.35 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.35)).eventually_ge_atTop _
  have hE2 : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ (A + C₅)‖ ≤ 1 * ‖x ^ (1 : ℝ)‖ :=
    (isLittleO_log_rpow_rpow_atTop (A + C₅) one_pos).def one_pos
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.eventually (hA1.and hD1)).and hE2)
  refine ⟨max CM 0 * (max ME 0 + 2 * (1 + |Cs|) + 1),
    max (max xE xS) (max xF (max x₁ 1)), ?_⟩
  intro x hx I Y hY1 hY2 t ht ht1 test htest σ hσ ψ₁ hψ k hk hkB n
  obtain ⟨hψc, hψs, hψd⟩ := hψ
  -- the thresholds
  have hxE : xE ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxS : xS ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxF : xF ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxx₁ : x₁ ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hx1 : 1 ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  obtain ⟨hL1, hY0, hT₀Y, hlen⟩ : 1 < Real.log x ∧ 0 < Y ∧
      x * Real.log x ^ (C₆ + 1) ≤ Y ∧
      4 * (⌊a₂ * Y⌋₊ : ℝ) * (1 + Real.log (⌊a₂ * Y⌋₊ : ℝ)) ≤ Cs * Y * Real.log x :=
    hF x hxF Y hY1 hY2
  obtain ⟨⟨hlogL, hc₂L⟩, hLx⟩ := hx₁ x hxx₁
  have hL0 : 0 < Real.log x := lt_trans one_pos hL1
  have hYx2 : Y ≤ x ^ (2 : ℝ) := scale_le_sq hx0 hL1 hlogL hc₂L hY2
  have hLx' : Real.log x ^ (A + C₅) ≤ x := log_rpow_le_of_norm hx0 hL0 hLx
  have hxY : x ≤ Y :=
    (le_mul_of_one_le_right hx0.le
      (Real.one_le_rpow hL1.le (add_pos hC₆ one_pos).le)).trans hT₀Y
  -- (cor:endpoint-squares) and (cor:SM) for the comparison endpoint
  have hψb : ∀ u : ℝ, ‖ψ₁ u‖ ≤ Real.log x ^ Dψ 0 := fun u => by
    have h' := hψd 0 u
    rwa [iteratedDeriv_zero] at h'
  exact arcEnergy_core hj2 ha₁ ha₂ hCM hC₆ hx1 hL1 hY0 hT₀Y hjA hLx' hlen
    (comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S t test ψ₁ σ Y)
    (fun w hw => comparisonEndpoint_window D.q D.q₀ D.𝔞 x I.𝔊 I.S t test hψs σ hY0 w hw)
    ((hE x hxE I Y hxY hYx2 t (fun g => (ht g).2) test htest.1 ψ₁ hψs hψb).1 σ) k n
    (hS x hxS I.𝔊 I.groups I.S I.slots Y hY1 hY2 t ht ht1 test htest.1 htest.2 σ hσ ψ₁ hψc
      hψs hψd k hk hkB n)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
