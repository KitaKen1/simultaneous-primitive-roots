module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.MultiplierForm
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.MinorArc
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.PhaseBilinear
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Assembly

/-!
# The multiplier is small off the major arcs

`multiplierLink : MultiplierLink`, i.e. `BilinearFourier → MultiplierMinor`
(`[P-06:0417–0474]`, (cor:bilinear-multiplier) and (cor:major-arcs)).

"Dirichlet approximation with denominator bound `⌊H'/L^{C_6-1}⌋` gives a fraction `h/r` with
`|θ - h/r| ≤ r⁻²`. If `r ≤ L^{C_6}`, this places `θ` in `𝔐_H`. Otherwise `L^{C_6} < r ≪
H'/L^{C_6-1}`, and the expression under the square root in (cor:bilinear-multiplier) is bounded by
`1/r + log(2r)/U_2 + 1/U_1 + r log(2r)/H'`. The middle terms save every log power by
(cor:comparison-scales), and the other terms give any desired fixed saving by increasing `C_6`."

* The bound (cor:bilinear-multiplier),
  `|𝔪(θ)| ≤ K L^κ (1/U₂ + 1/r + log(2r)/U₁ + r log(2r)/(U₁U₂))^{1/2}`,
  is [S] (eq:ideal-probability-bilinear) (`Comparison.probabilityBilinear`: the product
  probability bound `ρ(u) ≤ L^κ/u`, the collapse, and the integer bilinear estimate, which is the
  elementary bilinear Fourier estimate `bilinearFourier`) for the two tests of modulus at most one
  on the tuples of the two blocks (`multiplier_eq_phaseForm`). So the hypothesis `BilinearFourier`
  of the link is not used a second time.
* `arc_or_small`: the dichotomy, with the Dirichlet approximation
  (`Comparison.exists_dirichletData` with `Z = U₁U₂`, `S = L^{C₆-1}`) and the arithmetic
  `Comparison.Minor.sigma_sqrt_le`, `Comparison.Minor.final_le`.
* (cor:comparison-scales): a cell that carries a tuple has `e U_i ≥ exp(L^{.39})`, which exceeds
  every power of `L` (`Comparison.scaleLowerBound`), and `log(2r) ≤ L^{d+1}`
  (`Comparison.log_tupleProd_le_const`).

Constants: `κ = atomExponent`, `C₆ = 2(A + κ + 10) + d + 3` with `d = 0.46`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction
open SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

noncomputable section

/-- [S]'s constants for the active groups of [P] §6 with the damping `1/2` (the damping plays no
role for the multiplier). -/
def halfParams (P : ActiveGroupConstants) : GroupParams :=
  groupParams P (1 / 2) (by norm_num) (by norm_num)

/-- Admissible active groups as prime groups of [S] for the constants `halfParams P`. -/
def halfGroups {P : ActiveGroupConstants} {x : ℝ} {𝔊 : ActiveGroups} (h : 𝔊.Admissible P x) :
    PrimeGroups (halfParams P) x (Fin 𝔊.numSmall) (Fin 𝔊.numBig) :=
  primeGroupsOf h (1 / 2) (by norm_num) (by norm_num)

/-- **Arc or small** (`[P-06:0455–0474]`): if `M` satisfies the bilinear bound for every rational
approximation `θ = u/r + β`, `|β| ≤ r⁻²`, and the scales `U₁, U₂` exceed `L^{q_* + d + 2}`, then
`θ` lies in an arc `|θ - h/k| ≤ L^{q_*}/(U₁U₂)` with `k ≤ L^{q_*}`, or `M ≤ L^{-A}`. -/
theorem arc_or_small {L K κ d A qs U₁ U₂ M θ : ℝ} (hL : 2 ≤ L) (hK : 0 < K) (hLK : 10 * K ≤ L)
    (hd : 0 < d) (hA : 0 < A) (hκ : 0 ≤ κ) (hq : 2 * (A + κ + 10) + d + 2 < qs)
    (hU₁ : L ^ (qs + d + 2) ≤ U₁) (hU₂ : L ^ (qs + d + 2) ≤ U₂)
    (hlog : ∀ r : ℕ, 0 < r → (r : ℝ) ≤ U₁ * U₂ → Real.log (2 * (r : ℝ)) ≤ L ^ (d + 1))
    (hM : ∀ (β : ℝ) (u : ℤ) (r : ℕ), 0 < r → IsCoprime u (r : ℤ) →
      θ = (u : ℝ) / (r : ℝ) + β → |β| ≤ ((r : ℝ) ^ 2)⁻¹ →
        M ≤ K * L ^ κ * Real.sqrt (1 / U₂ + 1 / (r : ℝ) + Real.log (2 * (r : ℝ)) / U₁ +
          (r : ℝ) * Real.log (2 * (r : ℝ)) / (U₁ * U₂))) :
    (∃ (k : ℕ) (h : ℤ), 0 < k ∧ (k : ℝ) ≤ L ^ qs ∧
        |θ - (h : ℝ) / (k : ℝ)| ≤ L ^ qs / (U₁ * U₂)) ∨ M ≤ L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hS : 0 < L ^ (qs - 1) := Real.rpow_pos_of_pos hL0 _
  have hS1 : 1 ≤ L ^ (qs - 1) := Real.one_le_rpow hL1 (by linarith)
  have hSle : L ^ (qs - 1) ≤ L ^ (qs + d + 2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hU₁1 : 1 ≤ U₁ := (hS1.trans hSle).trans hU₁
  have hU₂1 : 1 ≤ U₂ := (hS1.trans hSle).trans hU₂
  have hZ : L ^ (qs - 1) ≤ U₁ * U₂ :=
    calc L ^ (qs - 1) ≤ U₁ := hSle.trans hU₁
      _ = U₁ * 1 := (mul_one _).symm
      _ ≤ U₁ * U₂ := mul_le_mul_of_nonneg_left hU₂1 (by linarith)
  have hZ0 : 0 < U₁ * U₂ := lt_of_lt_of_le hS hZ
  obtain ⟨u, r, β, hdata⟩ := exists_dirichletData θ hS hZ
  obtain ⟨hr, hcop, hα, hrle, hβ, hβZ⟩ := hdata
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
  by_cases hcase : (r : ℝ) ≤ L ^ qs
  · -- the major arcs
    left
    refine ⟨r, u, hr, hcase, ?_⟩
    have hθ : θ - (u : ℝ) / (r : ℝ) = β := by
      rw [hα]
      ring
    rw [hθ, le_div_iff₀ hZ0]
    have h1 : 2 * L ^ (qs - 1) / (r : ℝ) ≤ 2 * L ^ (qs - 1) :=
      div_le_self (mul_nonneg zero_le_two hS.le) hr1
    have h2 : L ^ qs = L ^ (qs - 1) * L := by
      rw [← Real.rpow_add_one hL0.ne']
      congr 1
      ring
    have h3 : L ^ (qs - 1) * 2 ≤ L ^ (qs - 1) * L := mul_le_mul_of_nonneg_left hL hS.le
    linarith
  · -- the minor arcs
    right
    have hQr : L ^ qs < (r : ℝ) := not_le.mp hcase
    have hℓ0 : 0 ≤ Real.log (2 * (r : ℝ)) := Real.log_nonneg (by linarith)
    have hrU : (r : ℝ) ≤ U₁ * U₂ := hrle.trans (div_le_self hZ0.le hS1)
    have hℓ := hlog r hr hrU
    have hsig := Minor.sigma_sqrt_le (w := A + κ + 10) (qs := qs) (ss := qs - 1) (U := U₁)
      (V := U₂) hL hd (by linarith) (by linarith) (by linarith) (by linarith) hQr hrle hℓ0 hℓ
    have hKE : 0 ≤ K * L ^ κ := mul_nonneg hK.le (Real.rpow_nonneg hL0.le _)
    have hfin := Minor.final_le (κ := κ) (B₀ := A) hL hK hLK
    have h0 : 0 ≤ K * L ^ κ * (2 * L ^ (-(A + κ + 10))) :=
      mul_nonneg hKE (mul_nonneg zero_le_two (Real.rpow_nonneg hL0.le _))
    calc M ≤ K * L ^ κ * Real.sqrt (1 / U₂ + 1 / (r : ℝ) + Real.log (2 * (r : ℝ)) / U₁ +
            (r : ℝ) * Real.log (2 * (r : ℝ)) / (U₁ * U₂)) := hM β u r hr hcop hα hβ
      _ ≤ K * L ^ κ * (2 * L ^ (-(A + κ + 10))) := mul_le_mul_of_nonneg_left hsig hKE
      _ ≤ 5 * (K * L ^ κ * (2 * L ^ (-(A + κ + 10)))) := by linarith
      _ ≤ L ^ (-A) := hfin

/-- **The multiplier is small off the major arcs** (`[P-06:0417–0474]`). This is the field
`multiplier` of `OpenLeaves d H 𝔅`; the hypothesis `BilinearFourier` is not needed, because the
bilinear bound is taken from [S] (eq:ideal-probability-bilinear), which is proved from the same
estimate. -/
theorem multiplierLink : MultiplierLink := by
  intro _ P m₀ A hA
  have hκ : 0 ≤ atomExponent (halfParams P) m₀ := atomExponent_nonneg (halfParams P) m₀
  have hd : 0 < (halfParams P).d := d_pos (halfParams P)
  obtain ⟨K, hK, x₁, hPB⟩ := probabilityBilinear (halfParams P) m₀ 1 (Real.exp 1) one_pos
    (Real.one_le_exp zero_le_one)
  obtain ⟨x₃, hSC⟩ := scaleLowerBound (halfParams P)
    (2 * (A + atomExponent (halfParams P) m₀ + 10) + (halfParams P).d + 3 +
      (halfParams P).d + 2 + 1 + 1)
  have hc0 : 0 ≤ 2 * (m₀ : ℝ) * (halfParams P).C₀ :=
    mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (halfParams P).C₀_pos.le
  refine ⟨2 * (A + atomExponent (halfParams P) m₀ + 10) + (halfParams P).d + 3,
    max (max x₁ x₃) (Real.exp (max (max 2 (10 * K))
      ((2 * (2 * (m₀ : ℝ) * (halfParams P).C₀) + 1) ^ 2))), by linarith, ?_⟩
  intro x hx 𝔊 h𝔊 J C hC b₁ b₂ U₁ U₂ hU₁ hU₂ hb₁ hb₂ θ
  -- the thresholds
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx₃ : x₃ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxe : Real.exp (max (max 2 (10 * K))
      ((2 * (2 * (m₀ : ℝ) * (halfParams P).C₀) + 1) ^ 2)) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hLbig : max (max 2 (10 * K)) ((2 * (2 * (m₀ : ℝ) * (halfParams P).C₀) + 1) ^ 2) ≤
      Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL2 : 2 ≤ Real.log x := (le_max_left _ _).trans ((le_max_left _ _).trans hLbig)
  have hLK : 10 * K ≤ Real.log x := (le_max_right _ _).trans ((le_max_left _ _).trans hLbig)
  have hLc : (2 * (2 * (m₀ : ℝ) * (halfParams P).C₀) + 1) ^ 2 ≤ Real.log x :=
    (le_max_right _ _).trans hLbig
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  -- the groups
  have hlaw : ∀ g, ∑ q ∈ (groupFamily 𝔊).big g,
      Graph.primeGroupLaw ((groupFamily 𝔊).big g) q = 1 := (halfGroups h𝔊).big_law_sum
  have hbig : ∀ g, ∀ p ∈ (groupFamily 𝔊).big g, 0 < p := fun g p hp =>
    (h𝔊.prime (Sum.inr g) p hp).pos
  have hCm : ∀ g, (C g).card ≤ m₀ := fun g =>
    (Finset.card_le_card (hC.1 g)).trans (card_probeSlots_le J m₀)
  -- a vanishing test
  by_cases hz₁ : ∀ r, b₁ r = 0
  · right
    have h0 : multiplier (groupFamily 𝔊).big C (fun r => b₁ r * b₂ r) θ = 0 :=
      multiplier_eq_zero C (fun r => by
        show b₁ r * b₂ r = 0
        rw [hz₁ r, zero_mul]) θ
    rw [h0, norm_zero]
    exact Real.rpow_nonneg hL0.le _
  by_cases hz₂ : ∀ r, b₂ r = 0
  · right
    have h0 : multiplier (groupFamily 𝔊).big C (fun r => b₁ r * b₂ r) θ = 0 :=
      multiplier_eq_zero C (fun r => by
        show b₁ r * b₂ r = 0
        rw [hz₂ r, mul_zero]) θ
    rw [h0, norm_zero]
    exact Real.rpow_nonneg hL0.le _
  obtain ⟨r₁, hr₁⟩ := not_forall.mp hz₁
  obtain ⟨r₂, hr₂⟩ := not_forall.mp hz₂
  obtain ⟨hlo₁, hhi₁⟩ := hb₁.cell r₁ hr₁
  obtain ⟨hlo₂, hhi₂⟩ := hb₂.cell r₂ hr₂
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  -- (cor:comparison-scales): the two cells exceed `L^{q_* + d + 2}`
  have hprime : ∀ (g : Fin 𝔊.numBig) (p : ℕ), p ∈ (groupFamily 𝔊).big g →
      Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) + (halfParams P).d + 3 +
        (halfParams P).d + 2 + 1 + 1) ≤ (p : ℝ) :=
    (hSC x hx₃ (Fin 𝔊.numSmall) (Fin 𝔊.numBig) (halfGroups h𝔊)).1
  have hscale : ∀ (b : Bool) (r : AuxList (groupFamily 𝔊).big C),
      (∃ g, halfSplit 𝔊.numBig g = b ∧ (C g).Nonempty) →
        Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) + (halfParams P).d + 3 +
          (halfParams P).d + 2 + 1 + 1) ≤ (blockAuxProd (halfSplit 𝔊.numBig) b C r : ℝ) := by
    intro b r ⟨g, hg, i, hi⟩
    have h1 := hprime g (r g ⟨i, hi⟩) (r g ⟨i, hi⟩).2
    have h2 : ((r g ⟨i, hi⟩ : ℕ) : ℝ) ≤ (blockAuxProd (halfSplit 𝔊.numBig) b C r : ℝ) := by
      exact_mod_cast label_le_blockAuxProd hbig (halfSplit 𝔊.numBig) C r hg ⟨i, hi⟩
    exact h1.trans h2
  have hEpos : 0 < Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) +
      (halfParams P).d + 3 + (halfParams P).d + 2) := Real.rpow_pos_of_pos hL0 _
  have hE4 : 4 * Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) +
        (halfParams P).d + 3 + (halfParams P).d + 2) ≤
      Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) + (halfParams P).d + 3 +
        (halfParams P).d + 2 + 1 + 1) := by
    have h4 : (4 : ℝ) ≤ Real.log x * Real.log x := by nlinarith
    rw [Real.rpow_add_one hL0.ne', Real.rpow_add_one hL0.ne', mul_assoc]
    calc 4 * Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) +
          (halfParams P).d + 3 + (halfParams P).d + 2)
        = Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) +
          (halfParams P).d + 3 + (halfParams P).d + 2) * 4 := mul_comm _ _
      _ ≤ Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) +
          (halfParams P).d + 3 + (halfParams P).d + 2) * (Real.log x * Real.log x) :=
          mul_le_mul_of_nonneg_left h4 hEpos.le
  have hUE₁ : Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) +
      (halfParams P).d + 3 + (halfParams P).d + 2) ≤ U₁ := by
    have h1 := hscale true r₁ hC.2.1
    have h2 : Real.exp 1 * U₁ ≤ 3 * U₁ := mul_le_mul_of_nonneg_right he (by linarith)
    linarith
  have hUE₂ : Real.log x ^ (2 * (A + atomExponent (halfParams P) m₀ + 10) +
      (halfParams P).d + 3 + (halfParams P).d + 2) ≤ U₂ := by
    have h1 := hscale false r₂ hC.2.2
    have h2 : Real.exp 1 * U₂ ≤ 3 * U₂ := mul_le_mul_of_nonneg_right he (by linarith)
    linarith
  -- `log(2r) ≤ L^{d+1}` for `r ≤ U₁ U₂`
  have hT₁ : (blockAuxProd (halfSplit 𝔊.numBig) true C r₁ : ℝ) ≤ ((tupleProd C r₁ : ℕ) : ℝ) := by
    have h := tupleProd_eq_blockAuxProd_mul (halfSplit 𝔊.numBig) C r₁
    have hpos : 0 < blockAuxProd (halfSplit 𝔊.numBig) false C r₁ :=
      blockAuxProd_pos hbig (halfSplit 𝔊.numBig) false C r₁
    exact_mod_cast (Nat.le_mul_of_pos_right _ hpos).trans (le_of_eq h.symm)
  have hT₂ : (blockAuxProd (halfSplit 𝔊.numBig) false C r₂ : ℝ) ≤ ((tupleProd C r₂ : ℕ) : ℝ) := by
    have h := tupleProd_eq_blockAuxProd_mul (halfSplit 𝔊.numBig) C r₂
    have hpos : 0 < blockAuxProd (halfSplit 𝔊.numBig) true C r₂ :=
      blockAuxProd_pos hbig (halfSplit 𝔊.numBig) true C r₂
    exact_mod_cast (Nat.le_mul_of_pos_left _ hpos).trans (le_of_eq h.symm)
  have hlog : ∀ r : ℕ, 0 < r → (r : ℝ) ≤ U₁ * U₂ →
      Real.log (2 * (r : ℝ)) ≤ Real.log x ^ ((halfParams P).d + 1) := by
    intro r hr hrU
    have hPA : (0 : ℝ) < ((tupleProd C r₁ : ℕ) : ℝ) := by
      exact_mod_cast tupleProd_pos (halfGroups h𝔊) C r₁
    have hPB' : (0 : ℝ) < ((tupleProd C r₂ : ℕ) : ℝ) := by
      exact_mod_cast tupleProd_pos (halfGroups h𝔊) C r₂
    have h2 : U₁ * U₂ ≤ ((tupleProd C r₁ : ℕ) : ℝ) * ((tupleProd C r₂ : ℕ) : ℝ) :=
      mul_le_mul (hlo₁.trans hT₁) (hlo₂.trans hT₂) (by linarith) hPA.le
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
    have h3 : 2 * (r : ℝ) ≤
        2 * (((tupleProd C r₁ : ℕ) : ℝ) * ((tupleProd C r₂ : ℕ) : ℝ)) := by linarith
    have h4 : Real.log (2 * (r : ℝ)) ≤
        Real.log (2 * (((tupleProd C r₁ : ℕ) : ℝ) * ((tupleProd C r₂ : ℕ) : ℝ))) :=
      Real.log_le_log (by linarith) h3
    have h5 : Real.log (2 * (((tupleProd C r₁ : ℕ) : ℝ) * ((tupleProd C r₂ : ℕ) : ℝ))) =
        Real.log 2 + (Real.log ((tupleProd C r₁ : ℕ) : ℝ) +
          Real.log ((tupleProd C r₂ : ℕ) : ℝ)) := by
      rw [Real.log_mul two_ne_zero (mul_pos hPA hPB').ne', Real.log_mul hPA.ne' hPB'.ne']
    have h6 : Real.log ((tupleProd C r₁ : ℕ) : ℝ) ≤
        (m₀ : ℝ) * (halfParams P).C₀ * Real.log (Real.log x) *
          Real.log x ^ (halfParams P).d :=
      log_tupleProd_le_const (halfGroups h𝔊) hL0.le C hCm r₁
    have h7 : Real.log ((tupleProd C r₂ : ℕ) : ℝ) ≤
        (m₀ : ℝ) * (halfParams P).C₀ * Real.log (Real.log x) *
          Real.log x ^ (halfParams P).d :=
      log_tupleProd_le_const (halfGroups h𝔊) hL0.le C hCm r₂
    have h8 : Real.log 2 ≤ 1 := by
      have h := Real.log_two_lt_d9
      linarith
    have hLd : 1 ≤ Real.log x ^ (halfParams P).d := Real.one_le_rpow hL1 hd.le
    have h9 : 2 * (m₀ : ℝ) * (halfParams P).C₀ * Real.log (Real.log x) + 1 ≤ Real.log x :=
      mul_log_add_one_le hc0 hLc
    have h10 : Real.log x ^ ((halfParams P).d + 1) =
        Real.log x ^ (halfParams P).d * Real.log x := Real.rpow_add_one hL0.ne' (halfParams P).d
    have h11 : Real.log x ^ (halfParams P).d *
          (2 * (m₀ : ℝ) * (halfParams P).C₀ * Real.log (Real.log x) + 1) ≤
        Real.log x ^ (halfParams P).d * Real.log x :=
      mul_le_mul_of_nonneg_left h9 (le_trans zero_le_one hLd)
    rw [h10]
    linarith
  -- the two tests on the tuples of the two blocks
  have hne : ∀ g, ∃ p, p ∈ (groupFamily 𝔊).big g := fun g => (halfGroups h𝔊).big_nonempty g
  choose f hf using hne
  obtain ⟨p₀⟩ : Nonempty (LabelList (groupFamily 𝔊).big J 0) := ⟨fun g _ => ⟨f g, hf g⟩⟩
  have hA' : ∃ g, (restrictBlock (halfSplit 𝔊.numBig) true C g).Nonempty := by
    obtain ⟨g, hg, hne⟩ := hC.2.1
    exact ⟨g, by rw [restrictBlock_of_eq C hg]; exact hne⟩
  have hBs' : ∃ g, (restrictBlock (halfSplit 𝔊.numBig) false C g).Nonempty := by
    obtain ⟨g, hg, hne⟩ := hC.2.2
    exact ⟨g, by rw [restrictBlock_of_eq C hg]; exact hne⟩
  have hbm : ∀ (b : Bool) (g : Fin 𝔊.numBig),
      (restrictBlock (halfSplit 𝔊.numBig) b C g).card ≤ m₀ := fun b g =>
    (Finset.card_le_card fun i hi => mem_of_mem_restrictBlock hi).trans (hCm g)
  have hGs : ∀ t, blockRestrict (halfSplit 𝔊.numBig) true C p₀ b₁ t ≠ 0 →
      1 * U₁ ≤ ((tupleProd (restrictBlock (halfSplit 𝔊.numBig) true C) t : ℕ) : ℝ) ∧
        ((tupleProd (restrictBlock (halfSplit 𝔊.numBig) true C) t : ℕ) : ℝ) ≤
          Real.exp 1 * U₁ := by
    intro t ht
    obtain ⟨h1, h2⟩ := blockRestrict_cell p₀ hb₁ t ht
    exact ⟨by rw [one_mul]; exact h1, h2⟩
  have hFs : ∀ t, blockRestrict (halfSplit 𝔊.numBig) false C p₀ b₂ t ≠ 0 →
      1 * U₂ ≤ ((tupleProd (restrictBlock (halfSplit 𝔊.numBig) false C) t : ℕ) : ℝ) ∧
        ((tupleProd (restrictBlock (halfSplit 𝔊.numBig) false C) t : ℕ) : ℝ) ≤
          Real.exp 1 * U₂ := by
    intro t ht
    obtain ⟨h1, h2⟩ := blockRestrict_cell p₀ hb₂ t ht
    exact ⟨by rw [one_mul]; exact h1, h2⟩
  have hnG : tupleNorm (groupFamily 𝔊).big (restrictBlock (halfSplit 𝔊.numBig) true C)
      (blockRestrict (halfSplit 𝔊.numBig) true C p₀ b₁) ≤ 1 :=
    tupleNorm_le_one hlaw _ fun t => hb₁.bound _
  have hnF : tupleNorm (groupFamily 𝔊).big (restrictBlock (halfSplit 𝔊.numBig) false C)
      (blockRestrict (halfSplit 𝔊.numBig) false C p₀ b₂) ≤ 1 :=
    tupleNorm_le_one hlaw _ fun t => hb₂.bound _
  -- the dichotomy
  refine arc_or_small (K := K) (κ := atomExponent (halfParams P) m₀) (d := (halfParams P).d)
    (A := A) hL2 hK hLK hd hA hκ (by linarith) hUE₁ hUE₂ hlog ?_
  intro β u r hr hcop hα hβ
  have hbound : ‖phaseForm (groupFamily 𝔊).big (restrictBlock (halfSplit 𝔊.numBig) true C)
        (restrictBlock (halfSplit 𝔊.numBig) false C)
        (blockRestrict (halfSplit 𝔊.numBig) false C p₀ b₂)
        (blockRestrict (halfSplit 𝔊.numBig) true C p₀ b₁) θ 0‖ ≤
      K * Real.log x ^ atomExponent (halfParams P) m₀ *
        Real.sqrt (1 / U₂ + 1 / (r : ℝ) + Real.log (2 * (r : ℝ)) / U₁ +
          (r : ℝ) * Real.log (2 * (r : ℝ)) / (U₁ * U₂)) *
        (tupleNorm (groupFamily 𝔊).big (restrictBlock (halfSplit 𝔊.numBig) false C)
            (blockRestrict (halfSplit 𝔊.numBig) false C p₀ b₂) *
          tupleNorm (groupFamily 𝔊).big (restrictBlock (halfSplit 𝔊.numBig) true C)
            (blockRestrict (halfSplit 𝔊.numBig) true C p₀ b₁)) :=
    hPB x hx₁ (Fin 𝔊.numSmall) (Fin 𝔊.numBig) (halfGroups h𝔊) J
      (restrictBlock (halfSplit 𝔊.numBig) true C) (restrictBlock (halfSplit 𝔊.numBig) false C)
      hA' hBs' (hbm true) (hbm false) U₁ U₂ hU₁ hU₂
      (blockRestrict (halfSplit 𝔊.numBig) false C p₀ b₂)
      (blockRestrict (halfSplit 𝔊.numBig) true C p₀ b₁) hFs hGs θ 0 β u r hr hcop hα hβ
  rw [multiplier_eq_phaseForm hlaw p₀ (halfSplit 𝔊.numBig) C hb₁.depends hb₂.depends θ]
  have hσ0 : 0 ≤ K * Real.log x ^ atomExponent (halfParams P) m₀ *
      Real.sqrt (1 / U₂ + 1 / (r : ℝ) + Real.log (2 * (r : ℝ)) / U₁ +
        (r : ℝ) * Real.log (2 * (r : ℝ)) / (U₁ * U₂)) :=
    mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg hL0.le _)) (Real.sqrt_nonneg _)
  have hnorms : tupleNorm (groupFamily 𝔊).big (restrictBlock (halfSplit 𝔊.numBig) false C)
        (blockRestrict (halfSplit 𝔊.numBig) false C p₀ b₂) *
      tupleNorm (groupFamily 𝔊).big (restrictBlock (halfSplit 𝔊.numBig) true C)
        (blockRestrict (halfSplit 𝔊.numBig) true C p₀ b₁) ≤ 1 := by
    have h := mul_le_mul hnF hnG (wNorm_nonneg _ _) zero_le_one
    rw [one_mul] at h
    exact h
  have h1 := mul_le_mul_of_nonneg_left hnorms hσ0
  rw [mul_one] at h1
  exact hbound.trans h1

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
