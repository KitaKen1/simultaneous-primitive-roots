module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.CircleTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.MultiplierProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.EndpointSquaresProof

/-!
# Parseval, the minor arcs and the major arcs

`circleLink d H : CircleLink d H`, i.e. `MultiplierMinor → ArcEnergy d → EndpointSquares d →
BilinearBound d H` (`[P-06:0476–0486]`, `[PUB-tex:0496–0500]`), for every number of slots and
every modulus.

"Use the Fourier convention `â(θ) = ∑_w a_w e(θ w)`. Parseval and (cor:endpoint-squares) handle
the complement of `𝔐_H`. On its `O(L^{2C_6})` arcs, Cauchy and the global energy of `𝒱` reduce
the problem to (cor:arc-energy-target)."

With `Y = x U₁ U₂`, `𝒰_j(w) = 𝒰(w) e(jw/H)` and `𝔪(θ) = E b(D) e(θ D)`,

`E b(D) ∑_w 𝒰_j(w) 𝒱(w + D) = ∫_0^1 𝒰̂_j(θ) 𝒱̂(-θ) 𝔪(θ) dθ`

(`CircleMethod.sum_mul_finsum_eq_integral`). The order of the constants:

* the saving `A`; `C₅` from (cor:endpoint-squares) with `m' = m₀ + 1` and `D₀ = Dψ 0`, replaced by
  `C₅⁺ = max(C₅, 0)`;
* the minor-arc saving `A + C₅⁺` and `C₆` from `MultiplierMinor`;
* the arc energy `ArcEnergyAt d (C₆ + 1) C₆` at the precision `2A + 4C₆ + C₅⁺`, with the scale
  constants `c₁ = 2` and `c₂ = 2 m₀ C₀`.

For `x ≥ x₀` (`log x ≥ max(3, H)` among the conditions): if one of the two tests vanishes
identically the sum is `0`. Otherwise each cell `[U_i, eU_i]` contains a product of free labels
of its block, which gives (cor:comparison-scales): `U_i ≥ exp(L^{.39} - 1)`,
`U_i ≤ exp(m₀ C₀ L^{.46} log L)` and `L^{2C₆ + 2} ≤ e U₁` (`cell_scale`). Hence the scale `Y` is
in the range of (cor:SM), `x ≤ Y ≤ x²`, the arcs `|θ - h/k| ≤ δ = L^{C₆}/(U₁U₂)` have `2δ ≤ 1`
and `L^{C₆} δ ≤ 1`, and the shifted denominators are `kH ≤ L^{C₆ + 1}`. The estimate is
`CircleMethod.circle_core` with `λ = L^{A + 2C₆ + C₅⁺}`; the constant is `2 max(M, 0) + 3`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The bilinear sum of a test that vanishes identically is zero. -/
theorem bilinearSum_eq_zero {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} (big : B → Finset ℕ)
    (C : B → Finset (Fin J)) {b : AuxList big C → ℂ} (h : ∀ r, b r = 0) (U V : ℕ → ℂ) :
    bilinearSum big C b U V = 0 := by
  unfold bilinearSum
  exact Finset.sum_eq_zero fun r _ => by rw [h r, mul_zero, zero_mul]

/-- **(cor:comparison-scales) for one cell** (`[P-06:0385–0389]`): a cell `[U, eU]` that carries
a tuple of free labels of a block with a freed slot has `exp(L^{.39} - 1) ≤ U`,
`U ≤ exp(m₀ C₀ log L · L^{.46})`, and `e U` is at least any lower bound for the big primes. -/
theorem cell_scale {d : ℕ} {D : FixedData} {x : ℝ} (I : Config d D x) (hL0 : 0 < Real.log x)
    {m₀ J : ℕ} {C : Fin I.𝔊.numBig → Finset (Fin J)} (hCm : ∀ g, (C g).card ≤ m₀) {b : Bool}
    (hne : ∃ g, I.blocks g = b ∧ (C g).Nonempty)
    {β : AuxList (groupFamily I.𝔊).big C → ℂ} {U : ℝ} (hβ : BlockTest I.blocks b C β U)
    {r : AuxList (groupFamily I.𝔊).big C} (hr : β r ≠ 0) {E : ℝ}
    (hprime : ∀ (g : Fin I.𝔊.numBig) (p : ℕ), p ∈ (groupFamily I.𝔊).big g →
      Real.log x ^ E ≤ (p : ℝ)) :
    Real.exp (Real.log x ^ (0.39 : ℝ) - 1) ≤ U ∧ Real.log x ^ E ≤ Real.exp 1 * U ∧
      U ≤ Real.exp ((m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := hβ.cell r hr
  obtain ⟨g, hg, i, hi⟩ := hne
  have hbig : ∀ g, ∀ p ∈ (groupFamily I.𝔊).big g, 0 < p := fun g p hp =>
    (I.groups.prime (Sum.inr g) p hp).pos
  have hlabel : ((r g ⟨i, hi⟩ : ℕ) : ℝ) ≤ (blockAuxProd I.blocks b C r : ℝ) := by
    exact_mod_cast label_le_blockAuxProd hbig I.blocks C r hg ⟨i, hi⟩
  have hrange := I.groups.big_range g (r g ⟨i, hi⟩) (r g ⟨i, hi⟩).2
  have hE := hprime g (r g ⟨i, hi⟩) (r g ⟨i, hi⟩).2
  -- the product of the block is at most the product of all the free labels
  have hT : blockAuxProd I.blocks b C r ≤ tupleProd C r := by
    have hpt := blockAuxProd_pos hbig I.blocks true C r
    have hpf := blockAuxProd_pos hbig I.blocks false C r
    rw [tupleProd_eq_blockAuxProd_mul I.blocks C r]
    cases b
    · exact Nat.le_mul_of_pos_left _ hpt
    · exact Nat.le_mul_of_pos_right _ hpf
  have hBT : (blockAuxProd I.blocks b C r : ℝ) ≤ ((tupleProd C r : ℕ) : ℝ) := by
    exact_mod_cast hT
  have hTpos : (0 : ℝ) < ((tupleProd C r : ℕ) : ℝ) := by
    exact_mod_cast tupleProd_pos I.primeGroups C r
  have hlogT : Real.log ((tupleProd C r : ℕ) : ℝ) ≤
      (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) :=
    log_tupleProd_le_const I.primeGroups hL0.le C hCm r
  have hTle : ((tupleProd C r : ℕ) : ℝ) ≤
      Real.exp ((m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ)) :=
    (Real.log_le_iff_le_exp hTpos).mp hlogT
  refine ⟨?_, (hE.trans hlabel).trans hhi, (hlo.trans hBT).trans hTle⟩
  rw [Real.exp_sub, div_le_iff₀ (Real.exp_pos 1)]
  calc Real.exp (Real.log x ^ (0.39 : ℝ)) ≤ ((r g ⟨i, hi⟩ : ℕ) : ℝ) := hrange.1
    _ ≤ (blockAuxProd I.blocks b C r : ℝ) := hlabel
    _ ≤ Real.exp 1 * U := hhi
    _ = U * Real.exp 1 := mul_comm _ _

/-- **Parseval, the minor arcs and the major arcs** (`[P-06:0476–0486]`, `[PUB-tex:0496–0500]`).
This is the field `circle` of `OpenLeaves d H 𝔅`. -/
theorem circleLink (d H : ℕ) : CircleLink d H := by
  intro hMM hAE hES hH D m₀ a₁ a₂ ha₁ ha₁₂ Dψ Cσ A hA
  -- the constants, in the order of the manuscript
  obtain ⟨C₅, xE, hE⟩ := hES D (m₀ + 1) a₁ a₂ ha₁ ha₁₂ (Dψ 0)
  have hC₅0 : 0 ≤ max C₅ 0 := le_max_right _ _
  obtain ⟨C₆, xM, hC₆, hM⟩ := hMM D.P m₀ (A + max C₅ 0) (by linarith)
  obtain ⟨MA, xA, hArc⟩ := hAE (C₆ + 1) C₆ (by linarith) hC₆ D (m₀ + 1) a₁ a₂ ha₁ ha₁₂ Dψ Cσ 2
    (2 * (m₀ : ℝ) * D.P.C₀) (2 * A + 4 * C₆ + max C₅ 0) (by linarith)
  obtain ⟨xS, hSC⟩ := scaleLowerBound D.params (2 * C₆ + 2)
  have hA1 : ∀ᶠ L : ℝ in atTop, ‖Real.log L‖ ≤ 1 * ‖L ^ (0.19 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.19)).def one_pos
  have hD1 : ∀ᶠ L : ℝ in atTop, |2 * (m₀ : ℝ) * D.P.C₀| ≤ L ^ (0.35 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.35)).eventually_ge_atTop _
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (hA1.and hD1))
  refine ⟨2 * max MA 0 + 3,
    max (max xE xM) (max (max xA xS) (max x₁ (Real.exp (max 3 (H : ℝ))))), ?_⟩
  intro x hx I J C hC b₁ b₂ U₁ U₂ hU₁ hU₂ hb₁ hb₂ test₁ test₂ ht₁ ht₂ σ hσ ψ₁ ψ₂ hψ₁ hψ₂ j
  -- the thresholds
  have hxE : xE ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxM : xM ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxA : xA ≤ x :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hx))
  have hxS : xS ≤ x :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hx))
  have hxx₁ : x₁ ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxe : Real.exp (max 3 (H : ℝ)) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hLbig : max 3 (H : ℝ) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL3 : 3 ≤ Real.log x := (le_max_left _ _).trans hLbig
  have hHL : (H : ℝ) ≤ Real.log x := (le_max_right _ _).trans hLbig
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 < Real.log x := by linarith
  obtain ⟨hlogL, hc₂L⟩ := hx₁ x hxx₁
  -- a vanishing test
  have hRHS0 : 0 ≤ (2 * max MA 0 + 3) * (x * U₁ * U₂) * Real.log x ^ (-A) := by
    have h1 : 0 ≤ max MA 0 := le_max_right _ _
    have h2 : 0 ≤ x * U₁ * U₂ := mul_nonneg (mul_nonneg hx0.le (by linarith)) (by linarith)
    exact mul_nonneg (mul_nonneg (by linarith) h2) (Real.rpow_nonneg hL0.le _)
  by_cases hz₁ : ∀ r, b₁ r = 0
  · rw [bilinearSum_eq_zero (groupFamily I.𝔊).big C (b := fun r => b₁ r * b₂ r)
      (fun r => by
        show b₁ r * b₂ r = 0
        rw [hz₁ r, zero_mul]), norm_zero]
    exact hRHS0
  by_cases hz₂ : ∀ r, b₂ r = 0
  · rw [bilinearSum_eq_zero (groupFamily I.𝔊).big C (b := fun r => b₁ r * b₂ r)
      (fun r => by
        show b₁ r * b₂ r = 0
        rw [hz₂ r, mul_zero]), norm_zero]
    exact hRHS0
  obtain ⟨r₁, hr₁⟩ := not_forall.mp hz₁
  obtain ⟨r₂, hr₂⟩ := not_forall.mp hz₂
  -- (cor:comparison-scales)
  have hCm : ∀ g, (C g).card ≤ m₀ := fun g =>
    (Finset.card_le_card (hC.1 g)).trans (card_probeSlots_le J m₀)
  have hprime : ∀ (g : Fin I.𝔊.numBig) (p : ℕ), p ∈ (groupFamily I.𝔊).big g →
      Real.log x ^ (2 * C₆ + 2) ≤ (p : ℝ) :=
    (hSC x hxS (Fin I.𝔊.numSmall) (Fin I.𝔊.numBig) I.primeGroups).1
  obtain ⟨h39₁, hE₁, hup₁⟩ := cell_scale I hL0 hCm hC.2.1 hb₁ hr₁ hprime
  obtain ⟨h39₂, -, hup₂⟩ := cell_scale I hL0 hCm hC.2.2 hb₂ hr₂ hprime
  have hUU1 : 1 ≤ U₁ * U₂ := one_le_mul_of_one_le_of_one_le hU₁ hU₂
  have hUU0 : 0 < U₁ * U₂ := lt_of_lt_of_le one_pos hUU1
  have hY0 : 0 < x * U₁ * U₂ := by
    rw [mul_assoc]
    exact mul_pos hx0 hUU0
  have hxY : x ≤ x * U₁ * U₂ := by
    rw [mul_assoc]
    exact le_mul_of_one_le_right hx0.le hUU1
  have hY1 : x * Real.exp (2 * Real.log x ^ (0.39 : ℝ) - 2) ≤ x * U₁ * U₂ := by
    have e : 2 * Real.log x ^ (0.39 : ℝ) - 2 =
        (Real.log x ^ (0.39 : ℝ) - 1) + (Real.log x ^ (0.39 : ℝ) - 1) := by ring
    rw [e, Real.exp_add, mul_assoc x U₁ U₂]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul h39₁ h39₂ (Real.exp_pos _).le (by linarith)) hx0.le
  have hY2 : x * U₁ * U₂ ≤ x * Real.exp (2 * (m₀ : ℝ) * D.P.C₀ * Real.log x ^ (0.46 : ℝ) *
      Real.log (Real.log x)) := by
    have e : 2 * (m₀ : ℝ) * D.P.C₀ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) =
        (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) +
          (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) := by ring
    rw [e, Real.exp_add, mul_assoc x U₁ U₂]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hup₁ hup₂ (by linarith) (Real.exp_pos _).le) hx0.le
  have hYx2 : x * U₁ * U₂ ≤ x ^ (2 : ℝ) := scale_le_sq hx0 hL1 hlogL hc₂L hY2
  -- the two endpoints
  have hmark : ∀ g, 1 ≤ markCount I.𝔊 C g ∧ markCount I.𝔊 C g ≤ m₀ + 1 := by
    intro g
    cases g with
    | inl i => exact ⟨le_rfl, Nat.le_add_left 1 m₀⟩
    | inr k => exact ⟨Nat.le_add_left 1 _, Nat.add_le_add_right (hCm k) 1⟩
  have hsmall : ∀ i : Fin I.𝔊.numSmall, markCount I.𝔊 C (Sum.inl i) = 1 := fun _ => rfl
  have hψb₁ : ∀ u : ℝ, ‖ψ₁ u‖ ≤ Real.log x ^ Dψ 0 := fun u => by
    have h' := hψ₁.2.2 0 u
    rwa [iteratedDeriv_zero] at h'
  have hψb₂ : ∀ u : ℝ, ‖ψ₂ u‖ ≤ Real.log x ^ Dψ 0 := fun u => by
    have h' := hψ₂.2.2 0 u
    rwa [iteratedDeriv_zero] at h'
  obtain ⟨hsqU, -⟩ := hE x hxE I (x * U₁ * U₂) hxY hYx2 (markCount I.𝔊 C)
    (fun g => (hmark g).2) test₁ ht₁.1 ψ₁ hψ₁.2.1 hψb₁
  obtain ⟨-, hsqV⟩ := hE x hxE I (x * U₁ * U₂) hxY hYx2 (markCount I.𝔊 C)
    (fun g => (hmark g).2) test₂ ht₂.1 ψ₂ hψ₂.2.1 hψb₂
  have hUs : ∀ w, comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S (markCount I.𝔊 C) test₁ ψ₁ σ
      (x * U₁ * U₂) w ≠ 0 → w ∈ Finset.Icc 1 ⌊a₂ * (x * U₁ * U₂)⌋₊ := by
    intro w hw
    have hψw : ψ₁ ((w : ℝ) / (x * U₁ * U₂)) ≠ 0 := by
      intro h'
      apply hw
      unfold comparisonEndpoint
      rw [h', zero_mul, zero_mul, zero_mul]
    exact Finset.mem_Icc.mpr (cutoff_range ha₁ hY0 hψ₁.2.1 hψw)
  have hVs : ∀ v, secondEndpoint D.q₀ I.𝔊 (markCount I.𝔊 C) test₂ I.G ψ₂ (x * U₁ * U₂) v ≠ 0 →
      v ∈ Finset.Icc 1 ⌊a₂ * (x * U₁ * U₂)⌋₊ := by
    intro v hv
    have hψv : ψ₂ ((v : ℝ) / (x * U₁ * U₂)) ≠ 0 := by
      intro h'
      apply hv
      unfold secondEndpoint
      rw [h', zero_mul, zero_mul]
    exact Finset.mem_Icc.mpr (cutoff_range ha₁ hY0 hψ₂.2.1 hψv)
  have hP5 : Real.log x ^ C₅ ≤ Real.log x ^ max C₅ 0 :=
    Real.rpow_le_rpow_of_exponent_le hL1.le (le_max_left _ _)
  have hEU : ∑ᶠ w : ℕ, ‖comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S (markCount I.𝔊 C) test₁ ψ₁ σ
      (x * U₁ * U₂) w‖ ^ 2 ≤ x * U₁ * U₂ * Real.log x ^ max C₅ 0 :=
    (hsqU σ).trans (mul_le_mul_of_nonneg_left hP5 hY0.le)
  have hEV : ∑ᶠ v : ℕ, ‖secondEndpoint D.q₀ I.𝔊 (markCount I.𝔊 C) test₂ I.G ψ₂
      (x * U₁ * U₂) v‖ ^ 2 ≤ x * U₁ * U₂ * Real.log x ^ max C₅ 0 :=
    hsqV.trans (mul_le_mul_of_nonneg_left hP5 hY0.le)
  -- the arcs: their number, their width and the shifted denominators
  have hq0 : 0 < Real.log x ^ C₆ := Real.rpow_pos_of_pos hL0 _
  have hQ1 : 1 ≤ Real.log x ^ C₆ := Real.one_le_rpow hL1.le hC₆.le
  have hQH : Real.log x ^ C₆ * (H : ℝ) ≤ Real.log x ^ (C₆ + 1) := by
    rw [Real.rpow_add_one hL0.ne']
    exact mul_le_mul_of_nonneg_left hHL hq0.le
  have hqq : 0 < Real.log x ^ C₆ * Real.log x ^ C₆ := mul_pos hq0 hq0
  have hUU : 2 * (Real.log x ^ C₆ * Real.log x ^ C₆) ≤ U₁ * U₂ := by
    have hpowE : Real.log x ^ (2 * C₆ + 2) =
        Real.log x ^ C₆ * Real.log x ^ C₆ * Real.log x ^ 2 := by
      have e : (2 : ℝ) * C₆ + 2 = C₆ + C₆ + 2 := by ring
      rw [e, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_two]
    have h9 : (9 : ℝ) ≤ Real.log x ^ 2 := by nlinarith
    have he3 : Real.exp 1 * U₁ ≤ 3 * U₁ :=
      mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by linarith)
    have h1 : Real.log x ^ C₆ * Real.log x ^ C₆ * 9 ≤ 3 * U₁ :=
      calc Real.log x ^ C₆ * Real.log x ^ C₆ * 9
          ≤ Real.log x ^ C₆ * Real.log x ^ C₆ * Real.log x ^ 2 :=
            mul_le_mul_of_nonneg_left h9 hqq.le
        _ = Real.log x ^ (2 * C₆ + 2) := hpowE.symm
        _ ≤ Real.exp 1 * U₁ := hE₁
        _ ≤ 3 * U₁ := he3
    have h2 : U₁ ≤ U₁ * U₂ := le_mul_of_one_le_right (by linarith) hU₂
    linarith
  have hδ0 : 0 ≤ Real.log x ^ C₆ / (U₁ * U₂) := div_nonneg hq0.le hUU0.le
  have hQδ : Real.log x ^ C₆ * (Real.log x ^ C₆ / (U₁ * U₂)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hUU0]
    linarith
  have hδ1 : 2 * (Real.log x ^ C₆ / (U₁ * U₂)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hUU0]
    have h1 : Real.log x ^ C₆ ≤ Real.log x ^ C₆ * Real.log x ^ C₆ :=
      le_mul_of_one_le_right hq0.le hQ1
    linarith
  have hδeq : x * Real.log x ^ C₆ / (x * U₁ * U₂) = Real.log x ^ C₆ / (U₁ * U₂) := by
    rw [mul_assoc x U₁ U₂, mul_div_mul_left _ _ hx0.ne']
  -- the arc energy at the shifted fractions
  have harc : ∀ (k : ℕ) (h : ℤ), 0 < k → (k : ℝ) ≤ Real.log x ^ (C₆ + 1) →
      ∫ β in (-(Real.log x ^ C₆ / (U₁ * U₂)))..(Real.log x ^ C₆ / (U₁ * U₂)),
        ‖∑ᶠ w : ℕ, comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S (markCount I.𝔊 C) test₁ ψ₁ σ
          (x * U₁ * U₂) w * addChar (((h : ℝ) / (k : ℝ) + β) * (w : ℝ))‖ ^ 2 ≤
        max MA 0 * (x * U₁ * U₂) * Real.log x ^ (-(2 * A + 4 * C₆ + max C₅ 0)) := by
    intro k h hk hkQ
    have h1 := hArc x hxA I (x * U₁ * U₂) hY1 hY2 (markCount I.𝔊 C) hmark hsmall test₁ ht₁ σ hσ
      ψ₁ hψ₁ k hk hkQ h
    rw [hδeq] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hY0.le) (Real.rpow_nonneg hL0.le _))
  -- the circle method
  have hlaw : ∀ g, ∑ q ∈ (groupFamily I.𝔊).big g,
      Graph.primeGroupLaw ((groupFamily I.𝔊).big g) q = 1 := fun g =>
    I.primeGroups.big_law_sum g
  have hbb : ∀ r, ‖b₁ r * b₂ r‖ ≤ 1 := fun r => by
    have h := mul_le_mul (hb₁.bound r) (hb₂.bound r) (norm_nonneg _) zero_le_one
    rw [one_mul] at h
    rw [norm_mul]
    exact h
  have hcore := CircleMethod.circle_core (auxWeight (groupFamily I.𝔊).big C)
    (fun r => Schur.auxWeight_nonneg (groupFamily I.𝔊).big C r)
    (le_of_eq (sum_auxWeight hlaw C)) (fun r => b₁ r * b₂ r) hbb (tupleProd C)
    (Finset.Icc 1 ⌊a₂ * (x * U₁ * U₂)⌋₊) hUs hVs hH j
    (lam := Real.log x ^ (A + 2 * C₆ + max C₅ 0)) hEU hEV hQ1 hQH hδ0 hQδ hδ1
    (Real.rpow_nonneg hL0.le (-(A + max C₅ 0))) (Real.rpow_pos_of_pos hL0 _)
    (fun θ => hM x hxM I.𝔊 I.groups J C hC b₁ b₂ U₁ U₂ hU₁ hU₂ hb₁ hb₂ θ) harc
  refine le_trans hcore (le_of_eq ?_)
  exact CircleMethod.circle_final hL0

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
