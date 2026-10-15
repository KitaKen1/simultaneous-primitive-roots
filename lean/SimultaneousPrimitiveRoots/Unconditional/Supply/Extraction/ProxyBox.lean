module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProxyConv
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProxySums
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProxyFamily

/-!
# The Type II step in one dyadic box

For the Type II step (`[P-07:0249–0315]`, `Extraction/ProxyProof.lean`): the estimate of

`∑_{m ∈ [A₀, 2A₀), n ∈ [C₀, 2C₀), mn ≡ b (H)} Φ((mn-1)/x) F_x(mn-1) (P(m) - a(m)) β(n)`

for one box, at one `x`, in terms of the Type II bound `Mb` at the scales `(A₀, C₀)`.

* `Proxy.CoeffFacts x γ`: what is used about the coefficients at `x`: `z = x^γ ≥ 1`, `W ≤ z`,
  and `κ(m) ≤ 1` for `m > z`.
* `Proxy.diffCoeff = P - a`, `Proxy.beta = β_j` (the companion coefficient), and the truncation
  `β = βlo + βhi` at the level `T` (`[P-07:0269–0281]`): `Proxy.sum_betaHi_le` is
  `∑_n β_n 1_{β_n > T} ≤ T^{-1} ∑_n β_n² ≪ T^{-1} N (log 2N)^A` by the divisor moment of order
  `2J` (the manuscript's `t = 2`).
* `Proxy.abs_cutoff_sub_le`: on a block `m / ℓ = k` the cutoff `Φ((mn-1)/x)` is
  `Φ((kℓn-1)/x)` up to `Lip · ℓ n / x`. **This replaces the Fourier inversion of
  `[P-07:0285–0291]`**: the factor `Φ((kℓn-1)/x)` depends on `n` only and is put into the second
  coefficient, and Theorem 3.1 is applied on the sub-interval of the block ("supported on an
  arbitrary interval in `[H_m, 2H_m]`") with `v = 0`.
* `Proxy.abs_cell_le`: one block is `Bs` times a sum of the form of `Proxy.abs_bilinear_le`; here
  `F` is the normalized clipped statistic and `F_x(u) = 𝒲(u) · Bs · F(u)` on the box.
* `Proxy.abs_box_concrete_le`: the box, by `Proxy.abs_box_le`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

namespace Proxy

/-! ### The coefficients at one `x` -/

/-- The facts about the coefficients used at one `x`: `z = x^γ ≥ 1`, `W ≤ z` and `κ(m) ≤ 1` for
`m > z`. They hold for all large `x` (the last one by Mertens' product theorem). -/
structure CoeffFacts (x γ : ℝ) : Prop where
  one_le : 1 ≤ x ^ γ
  rough_le : roughCutoff x ≤ x ^ γ
  kappa_le : ∀ m : ℕ, x ^ γ < (m : ℝ) → proxyKappa x m ≤ 1

theorem primeCoeff_le_one (z : ℝ) (m : ℕ) : primeCoeff z m ≤ 1 := by
  unfold primeCoeff
  split_ifs
  · exact le_rfl
  · exact zero_le_one

theorem primeCoeff_ne_zero {z : ℝ} {m : ℕ} (h : primeCoeff z m ≠ 0) :
    m.Prime ∧ z < (m : ℝ) := by
  by_contra hcon
  refine h ?_
  unfold primeCoeff
  exact if_neg hcon

theorem proxyCoeff_ne_zero {x γ : ℝ} {m : ℕ} (h : proxyCoeff x γ m ≠ 0) :
    x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m := by
  by_contra hcon
  refine h ?_
  unfold proxyCoeff
  exact if_neg hcon

theorem proxyCoeff_le_one {x γ : ℝ} (hF : CoeffFacts x γ) (m : ℕ) : proxyCoeff x γ m ≤ 1 := by
  unfold proxyCoeff
  split_ifs with h
  · exact hF.kappa_le m h.1
  · exact zero_le_one

theorem isRough_of_primeCoeff {x γ : ℝ} (hF : CoeffFacts x γ) {m : ℕ}
    (h : primeCoeff (x ^ γ) m ≠ 0) : IsRough (roughCutoff x) m := by
  obtain ⟨hp, hz⟩ := primeCoeff_ne_zero h
  intro p hpp hdvd
  have hpm : p = m := (Nat.prime_dvd_prime_iff_eq hpp hp).mp hdvd
  rw [hpm]
  exact lt_of_le_of_lt hF.rough_le hz

/-- `P(m) - a(m)`: the discrepancy in the `m` slot. -/
def diffCoeff (x γ : ℝ) (m : ℕ) : ℝ := primeCoeff (x ^ γ) m - proxyCoeff x γ m

theorem abs_diffCoeff_le_one {x γ : ℝ} (hF : CoeffFacts x γ) (m : ℕ) :
    |diffCoeff x γ m| ≤ 1 := by
  unfold diffCoeff
  have h1 := primeCoeff_nonneg (x ^ γ) m
  have h2 := primeCoeff_le_one (x ^ γ) m
  have h3 := proxyCoeff_nonneg x γ m
  have h4 := proxyCoeff_le_one hF m
  rw [abs_le]
  constructor <;> linarith

theorem diffCoeff_eq_zero {x γ : ℝ} {m : ℕ} (h : ¬x ^ γ < (m : ℝ)) : diffCoeff x γ m = 0 := by
  unfold diffCoeff primeCoeff proxyCoeff
  rw [if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.1), sub_zero]

/-- The companion coefficient `β_j` of the prime indicator and the proxy coefficient. -/
def beta (x γ : ℝ) (j n : ℕ) : ℝ := companion (primeCoeff (x ^ γ)) (proxyCoeff x γ) j n

theorem beta_nonneg (x γ : ℝ) (j n : ℕ) : 0 ≤ beta x γ j n :=
  companion_nonneg (primeCoeff_nonneg _) (proxyCoeff_nonneg x γ) j n

theorem beta_le {x γ : ℝ} (hF : CoeffFacts x γ) (j n : ℕ) :
    beta x γ j n ≤ (j : ℝ) * (n.divisors.card : ℝ) ^ j :=
  companion_le (primeCoeff_nonneg _) (primeCoeff_le_one _) (proxyCoeff_nonneg x γ)
    (proxyCoeff_le_one hF) j n

theorem beta_rough {x γ : ℝ} (hF : CoeffFacts x γ) (j : ℕ) {n : ℕ} (h : beta x γ j n ≠ 0) :
    IsRough (roughCutoff x) n :=
  companion_rough (fun _ hm => isRough_of_primeCoeff hF hm)
    (fun _ hm => (proxyCoeff_ne_zero hm).2) j h

theorem beta_lt {x γ : ℝ} {j : ℕ} (hj : 1 ≤ j) {n : ℕ} (h : beta x γ (j + 1) n ≠ 0) :
    x ^ γ < (n : ℝ) :=
  companion_lt (fun _ hm => (primeCoeff_ne_zero hm).2) (fun _ hm => (proxyCoeff_ne_zero hm).1)
    hj h

/-! ### Truncation of the companion coefficient -/

/-- `β_n 1_{β_n ≤ T}`. -/
def betaLo (T x γ : ℝ) (j n : ℕ) : ℝ := if beta x γ j n ≤ T then beta x γ j n else 0

/-- `β_n 1_{β_n > T}`. -/
def betaHi (T x γ : ℝ) (j n : ℕ) : ℝ := if beta x γ j n ≤ T then 0 else beta x γ j n

theorem betaLo_add_betaHi (T x γ : ℝ) (j n : ℕ) :
    beta x γ j n = betaLo T x γ j n + betaHi T x γ j n := by
  unfold betaLo betaHi
  split_ifs
  · rw [add_zero]
  · rw [zero_add]

theorem betaLo_nonneg (T x γ : ℝ) (j n : ℕ) : 0 ≤ betaLo T x γ j n := by
  unfold betaLo
  split_ifs
  · exact beta_nonneg x γ j n
  · exact le_rfl

theorem betaLo_le {T : ℝ} (hT : 0 ≤ T) (x γ : ℝ) (j n : ℕ) : betaLo T x γ j n ≤ T := by
  unfold betaLo
  split_ifs with h
  · exact h
  · exact hT

theorem betaLo_ne_zero {T x γ : ℝ} {j n : ℕ} (h : betaLo T x γ j n ≠ 0) : beta x γ j n ≠ 0 := by
  intro h0
  refine h ?_
  unfold betaLo
  rw [h0]
  exact ite_self 0

theorem betaHi_nonneg (T x γ : ℝ) (j n : ℕ) : 0 ≤ betaHi T x γ j n := by
  unfold betaHi
  split_ifs
  · exact le_rfl
  · exact beta_nonneg x γ j n

theorem betaHi_le {T : ℝ} (hT : 0 < T) (x γ : ℝ) (j n : ℕ) :
    betaHi T x γ j n ≤ beta x γ j n ^ 2 / T := by
  unfold betaHi
  split_ifs with h
  · exact div_nonneg (sq_nonneg _) hT.le
  · have hlt : T < beta x γ j n := not_le.mp h
    rw [le_div_iff₀ hT]
    nlinarith [beta_nonneg x γ j n]

/-- **The discarded part of the companion coefficient** (`[P-07:0272–0277]` with `t = 2`):
`∑_{N₁ ≤ n < N₂} β_n 1_{β_n > T} ≤ J² T^{-1} · C N₂ (log 2N₂)^A`, from the divisor moment of
order `2J`. -/
theorem sum_betaHi_le {x γ T : ℝ} (hF : CoeffFacts x γ) (hT : 0 < T) {j J : ℕ} (hjJ : j ≤ J)
    {Cτ Aτ : ℝ}
    (hτ : ∀ Y : ℝ, 1 ≤ Y → ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ (J * 2) ≤
      Cτ * Y * Real.log (2 * Y) ^ Aτ)
    {N₁ N₂ : ℕ} (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) :
    ∑ n ∈ Finset.Ico N₁ N₂, betaHi T x γ j n ≤
      (J : ℝ) ^ 2 / T * (Cτ * (N₂ : ℝ) * Real.log (2 * (N₂ : ℝ)) ^ Aτ) := by
  have hJT : 0 ≤ (J : ℝ) ^ 2 / T := div_nonneg (sq_nonneg _) hT.le
  have hterm : ∀ n ∈ Finset.Ico N₁ N₂,
      betaHi T x γ j n ≤ (J : ℝ) ^ 2 / T * (n.divisors.card : ℝ) ^ (J * 2) := by
    intro n hn
    have hn1 : 1 ≤ n := hN₁.trans (Finset.mem_Ico.mp hn).1
    have hτ1 : (1 : ℝ) ≤ (n.divisors.card : ℝ) :=
      Nat.one_le_cast.mpr (Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩)
    have hb0 := beta_nonneg x γ j n
    have hb1 := beta_le hF j n
    have hjJ' : (j : ℝ) ≤ (J : ℝ) := Nat.cast_le.mpr hjJ
    have h1 : (j : ℝ) * (n.divisors.card : ℝ) ^ j ≤ (J : ℝ) * (n.divisors.card : ℝ) ^ J :=
      mul_le_mul hjJ' (pow_le_pow_right₀ hτ1 hjJ) (pow_nonneg (le_trans zero_le_one hτ1) _)
        (Nat.cast_nonneg J)
    have h2 : beta x γ j n ^ 2 ≤ ((J : ℝ) * (n.divisors.card : ℝ) ^ J) ^ 2 :=
      pow_le_pow_left₀ hb0 (hb1.trans h1) 2
    have h3 : ((J : ℝ) * (n.divisors.card : ℝ) ^ J) ^ 2 =
        (J : ℝ) ^ 2 * (n.divisors.card : ℝ) ^ (J * 2) := by rw [mul_pow, ← pow_mul]
    calc betaHi T x γ j n ≤ beta x γ j n ^ 2 / T := betaHi_le hT x γ j n
      _ ≤ ((J : ℝ) ^ 2 * (n.divisors.card : ℝ) ^ (J * 2)) / T :=
          div_le_div_of_nonneg_right (h2.trans (le_of_eq h3)) hT.le
      _ = (J : ℝ) ^ 2 / T * (n.divisors.card : ℝ) ^ (J * 2) := by ring
  have hsub : Finset.Ico N₁ N₂ ⊆ Finset.Icc 1 ⌊(N₂ : ℝ)⌋₊ := by
    intro n hn
    rw [Nat.floor_natCast, Finset.mem_Icc]
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
    exact ⟨by omega, by omega⟩
  have hY : (1 : ℝ) ≤ (N₂ : ℝ) := Nat.one_le_cast.mpr hN₂
  calc ∑ n ∈ Finset.Ico N₁ N₂, betaHi T x γ j n
      ≤ ∑ n ∈ Finset.Ico N₁ N₂, (J : ℝ) ^ 2 / T * (n.divisors.card : ℝ) ^ (J * 2) :=
        Finset.sum_le_sum hterm
    _ = (J : ℝ) ^ 2 / T * ∑ n ∈ Finset.Ico N₁ N₂, (n.divisors.card : ℝ) ^ (J * 2) := by
        rw [Finset.mul_sum]
    _ ≤ (J : ℝ) ^ 2 / T * ∑ n ∈ Finset.Icc 1 ⌊(N₂ : ℝ)⌋₊, (n.divisors.card : ℝ) ^ (J * 2) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
            pow_nonneg (Nat.cast_nonneg _) _) hJT
    _ ≤ (J : ℝ) ^ 2 / T * (Cτ * (N₂ : ℝ) * Real.log (2 * (N₂ : ℝ)) ^ Aτ) :=
        mul_le_mul_of_nonneg_left (hτ _ hY) hJT

/-! ### The cutoff on a block -/

/-- For a Lipschitz cutoff, `Φ((mn-1)/x)` and `Φ((kℓn-1)/x)`, `k = ⌊m/ℓ⌋`, differ by at most
`Lip · ℓ N / x` for `n ≤ N`. -/
theorem abs_cutoff_sub_le {Φ : ℝ → ℝ} {Lip x : ℝ} (hx : 0 < x) (hLip0 : 0 ≤ Lip)
    (hLip : ∀ s t : ℝ, |Φ s - Φ t| ≤ Lip * |s - t|) {m n ℓ N : ℕ} (hℓ : 0 < ℓ) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    |Φ (((m * n - 1 : ℕ) : ℝ) / x) - Φ ((((m / ℓ * ℓ * n : ℕ) : ℝ) - 1) / x)| ≤
      Lip * ((ℓ : ℝ) * (N : ℝ) / x) := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have h1 : ((m * n - 1 : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) - 1 := by
    rw [Nat.cast_pred hmn, Nat.cast_mul]
  have hk1 : ((m / ℓ * ℓ : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (Nat.div_mul_le_self m ℓ)
  have hk2 : (m : ℝ) ≤ ((m / ℓ * ℓ : ℕ) : ℝ) + (ℓ : ℝ) := by
    have h : m ≤ m / ℓ * ℓ + ℓ := (Nat.lt_div_mul_add hℓ).le
    exact_mod_cast h
  have h2 : ((m / ℓ * ℓ * n : ℕ) : ℝ) = ((m / ℓ * ℓ : ℕ) : ℝ) * (n : ℝ) := Nat.cast_mul _ _
  have hdiff : ((m * n - 1 : ℕ) : ℝ) / x - (((m / ℓ * ℓ * n : ℕ) : ℝ) - 1) / x =
      ((m : ℝ) - ((m / ℓ * ℓ : ℕ) : ℝ)) * (n : ℝ) / x := by
    rw [h1, h2]
    ring
  have hnn : 0 ≤ ((m : ℝ) - ((m / ℓ * ℓ : ℕ) : ℝ)) * (n : ℝ) / x :=
    div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg n)) hx.le
  refine (hLip _ _).trans (mul_le_mul_of_nonneg_left ?_ hLip0)
  rw [hdiff, abs_of_nonneg hnn]
  refine div_le_div_of_nonneg_right ?_ hx.le
  exact mul_le_mul (by linarith) (Nat.cast_le.mpr hnN) (Nat.cast_nonneg n) (Nat.cast_nonneg ℓ)

/-! ### One block -/

/-- **One block** (`[P-07:0290–0299]`): the sum over the block `m / ℓ = k` of the box
`[A₀, 2A₀) × [C₀, 2C₀)` with the separated cutoff factor is `Bs` times a Type II sum, so it is at
most `Bs · Mb`. -/
theorem abs_cell_le {H b : ℕ} (hH : 0 < H) (hb : b.Coprime H) {q : ℝ} {K : ℕ}
    (𝔞 : MarkingArray K) {d : ℕ} (S : Fin d → Finset ℕ) {x γ C Bs BΦ T Mb : ℝ} (Φ : ℝ → ℝ)
    (hF : CoeffFacts x γ) {j A₀ C₀ ℓ : ℕ} (hA₀ : x ^ γ < (A₀ : ℝ)) (hℓ : 0 < ℓ) (k : ℕ)
    (hBs : 0 < Bs)
    (hrange : ∀ m ∈ Finset.Ico A₀ (2 * A₀), ∀ n ∈ Finset.Ico C₀ (2 * C₀),
      |(slotCount S (m * n - 1) : ℝ) - slotMass S| ≤ Bs)
    (hT0 : 0 ≤ T) (hBΦ : ∀ t, |Φ t| ≤ BΦ) (hC : T * BΦ ≤ Real.log x ^ C)
    (hTII : ∀ lo hi : ℝ, (A₀ : ℝ) ≤ lo → hi ≤ 2 * (A₀ : ℝ) →
      ∀ (lam : DirichletCharacter ℂ H) (β : ℕ → ℂ), RoughDyadCoefficient x C (C₀ : ℝ) β →
        ‖markedBilinearSum q 𝔞 x (A₀ : ℝ) (C₀ : ℝ)
          (fun m => primeMinusRough x 0 lo hi m * lam (m : ZMod H)) β
          (fun h => ((clipCore Bs S h : ℝ) : ℂ))‖ ≤ Mb) :
    |∑ m ∈ Finset.Ico A₀ (2 * A₀), ∑ n ∈ Finset.Ico C₀ (2 * C₀),
        if m / ℓ = k then
          Φ ((((k * ℓ * n : ℕ) : ℝ) - 1) / x) *
            (clsInd H b (m * n) * centeredCore q 𝔞 x S (m * n - 1) * diffCoeff x γ m) *
              betaLo T x γ j n
        else 0| ≤ Bs * Mb := by
  have hA₀1 : 1 ≤ A₀ := by
    have h : (0 : ℝ) < (A₀ : ℝ) := lt_of_lt_of_le one_pos (hF.one_le.trans hA₀.le)
    exact_mod_cast h
  -- the interval of the block
  obtain ⟨lo, hlodef⟩ : ∃ lo : ℕ, lo = max (k * ℓ) A₀ := ⟨_, rfl⟩
  obtain ⟨hi, hhidef⟩ : ∃ hi : ℕ, hi = min (k * ℓ + ℓ - 1) (2 * A₀ - 1) := ⟨_, rfl⟩
  have hlo : (A₀ : ℝ) ≤ (lo : ℝ) := Nat.cast_le.mpr (by
    rw [hlodef]
    exact le_max_right _ _)
  have hhi : (hi : ℝ) ≤ 2 * (A₀ : ℝ) := by
    have h : hi ≤ 2 * A₀ := by
      rw [hhidef]
      exact (min_le_right _ _).trans (Nat.sub_le _ _)
    exact_mod_cast h
  have hmem : ∀ m : ℕ, ((lo : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (hi : ℝ)) ↔
      (k * ℓ ≤ m ∧ A₀ ≤ m) ∧ (m ≤ k * ℓ + ℓ - 1 ∧ m ≤ 2 * A₀ - 1) := by
    intro m
    rw [Nat.cast_le, Nat.cast_le, hlodef, hhidef, max_le_iff, le_min_iff]
  -- the second coefficient: the truncated companion coefficient with the cutoff of the block
  obtain ⟨β', hβ'⟩ : ∃ β' : ℕ → ℝ, β' = fun n => if n ∈ Finset.Ico C₀ (2 * C₀) then
      betaLo T x γ j n * Φ ((((k * ℓ * n : ℕ) : ℝ) - 1) / x) else 0 := ⟨_, rfl⟩
  have hβ'in : ∀ n ∈ Finset.Ico C₀ (2 * C₀),
      β' n = betaLo T x γ j n * Φ ((((k * ℓ * n : ℕ) : ℝ) - 1) / x) := by
    intro n hn
    rw [hβ']
    exact if_pos hn
  have hβ'out : ∀ n, n ∉ Finset.Ico C₀ (2 * C₀) → β' n = 0 := by
    intro n hn
    rw [hβ']
    exact if_neg hn
  have hLC0 : 0 ≤ Real.log x ^ C :=
    (mul_nonneg hT0 ((abs_nonneg _).trans (hBΦ 0))).trans hC
  have hsupp : ∀ n, β' n ≠ 0 →
      (C₀ : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (C₀ : ℝ) ∧ IsRough (roughCutoff x) n := by
    intro n hn
    have hnJ : n ∈ Finset.Ico C₀ (2 * C₀) := by
      by_contra hcon
      exact hn (hβ'out n hcon)
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hnJ
    rw [hβ'in n hnJ] at hn
    refine ⟨Nat.cast_le.mpr h1, ?_, beta_rough hF j (betaLo_ne_zero (left_ne_zero_of_mul hn))⟩
    have h3 : n ≤ 2 * C₀ := h2.le
    exact_mod_cast h3
  have hbd : ∀ n, |β' n| ≤ Real.log x ^ C := by
    intro n
    by_cases hnJ : n ∈ Finset.Ico C₀ (2 * C₀)
    · rw [hβ'in n hnJ, abs_mul, abs_of_nonneg (betaLo_nonneg T x γ j n)]
      exact (mul_le_mul (betaLo_le hT0 x γ j n) (hBΦ _) (abs_nonneg _) hT0).trans hC
    · rw [hβ'out n hnJ, abs_zero]
      exact hLC0
  have hA := abs_bilinear_le hH hb 𝔞 (clipCore Bs S) (hTII lo hi hlo hhi) β' hsupp hbd
  -- the dyads contain the half-open intervals, and the summand vanishes outside them
  have hI : Finset.Ico A₀ (2 * A₀) ⊆ dyad (A₀ : ℝ) := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hm
    have h3 : m ≤ 2 * A₀ := h2.le
    exact (mem_dyad (Nat.cast_nonneg A₀)).mpr ⟨Nat.cast_le.mpr h1, by exact_mod_cast h3⟩
  have hJ : Finset.Ico C₀ (2 * C₀) ⊆ dyad (C₀ : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
    have h3 : n ≤ 2 * C₀ := h2.le
    exact (mem_dyad (Nat.cast_nonneg C₀)).mpr ⟨Nat.cast_le.mpr h1, by exact_mod_cast h3⟩
  have hres : ∑ m ∈ Finset.Ico A₀ (2 * A₀), ∑ n ∈ Finset.Ico C₀ (2 * C₀),
      pmrReal x lo hi m * β' n * clsInd H b (m * n) * clipCore Bs S (m * n - 1) *
        markedWeight q 𝔞 x (m * n - 1) =
      ∑ m ∈ dyad (A₀ : ℝ), ∑ n ∈ dyad (C₀ : ℝ),
        pmrReal x lo hi m * β' n * clsInd H b (m * n) * clipCore Bs S (m * n - 1) *
          markedWeight q 𝔞 x (m * n - 1) := by
    refine (Finset.sum_congr rfl fun m _ => Finset.sum_subset hJ fun n _ hn => ?_).trans
      (Finset.sum_subset hI fun m _ hm => ?_)
    · rw [hβ'out n hn]
      ring
    · have hnot : ¬((lo : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (hi : ℝ)) := by
        intro hin
        obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := (hmem m).mp hin
        exact hm (Finset.mem_Ico.mpr ⟨h1, by omega⟩)
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [pmrReal_eq_zero hnot]
      ring
  -- the block is `Bs` times the Type II sum
  have hkey : ∑ m ∈ Finset.Ico A₀ (2 * A₀), ∑ n ∈ Finset.Ico C₀ (2 * C₀),
      (if m / ℓ = k then
        Φ ((((k * ℓ * n : ℕ) : ℝ) - 1) / x) *
          (clsInd H b (m * n) * centeredCore q 𝔞 x S (m * n - 1) * diffCoeff x γ m) *
            betaLo T x γ j n
      else 0) =
      Bs * ∑ m ∈ dyad (A₀ : ℝ), ∑ n ∈ dyad (C₀ : ℝ),
        pmrReal x lo hi m * β' n * clsInd H b (m * n) * clipCore Bs S (m * n - 1) *
          markedWeight q 𝔞 x (m * n - 1) := by
    rw [← hres, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hmA, hmB⟩ := Finset.mem_Ico.mp hm
    have hmz : x ^ γ < (m : ℝ) := lt_of_lt_of_le hA₀ (Nat.cast_le.mpr hmA)
    have hclip := clipCore_eq hBs S (hrange m hm n hn)
    rw [hβ'in n hn]
    by_cases hk : m / ℓ = k
    · have h1 : k * ℓ ≤ m := by
        rw [← hk]
        exact Nat.div_mul_le_self m ℓ
      have h2 : m < k * ℓ + ℓ := by
        rw [← hk]
        exact Nat.lt_div_mul_add hℓ
      have hin : (lo : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (hi : ℝ) :=
        (hmem m).mpr ⟨⟨h1, hmA⟩, ⟨by omega, by omega⟩⟩
      rw [if_pos hk, pmrReal_eq hF.one_le hmz hin]
      unfold centeredCore diffCoeff
      rw [← hclip]
      ring
    · have hnot : ¬((lo : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (hi : ℝ)) := by
        intro hin
        obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := (hmem m).mp hin
        exact hk (Nat.div_eq_of_lt_le h1 (by
          rw [Nat.add_mul, Nat.one_mul]
          omega))
      rw [if_neg hk, pmrReal_eq_zero hnot]
      ring
  rw [hkey, abs_mul, abs_of_pos hBs]
  exact mul_le_mul_of_nonneg_left hA hBs.le

/-! ### One box -/

theorem abs_weight_le {H b : ℕ} {q : ℝ} {K : ℕ} (𝔞 : MarkingArray K) {d : ℕ}
    (S : Fin d → Finset ℕ) {x γ BF : ℝ} (hF : CoeffFacts x γ) {u m n : ℕ}
    (hBF : |centeredCore q 𝔞 x S u| ≤ BF) :
    |clsInd H b (m * n) * centeredCore q 𝔞 x S u * diffCoeff x γ m| ≤ BF := by
  rw [abs_mul, abs_mul]
  calc |clsInd H b (m * n)| * |centeredCore q 𝔞 x S u| * |diffCoeff x γ m| ≤ 1 * BF * 1 :=
        mul_le_mul (mul_le_mul (abs_clsInd_le_one _ _ _) hBF (abs_nonneg _) zero_le_one)
          (abs_diffCoeff_le_one hF m) (abs_nonneg _)
          (mul_nonneg zero_le_one ((abs_nonneg _).trans hBF))
    _ = BF := by ring

/-- **One box** (`[P-07:0256–0299]`): blocks of length `ℓ`, truncation at `T`, and the Type II
bound `Mb` at the scales `(A₀, C₀)`. -/
theorem abs_box_concrete_le {H b : ℕ} (hH : 0 < H) (hb : b.Coprime H) {q : ℝ} {K : ℕ}
    (𝔞 : MarkingArray K) {d : ℕ} (S : Fin d → Finset ℕ) {x γ C Bs BF BΦ Lip T Mb : ℝ}
    (Φ : ℝ → ℝ) (hF : CoeffFacts x γ) (hx : 0 < x) {j A₀ C₀ ℓ : ℕ} (hA₀ : x ^ γ < (A₀ : ℝ))
    (hC₀ : 1 ≤ C₀) (hℓ : 0 < ℓ) (hBs : 0 < Bs) (hBF0 : 0 ≤ BF)
    (hrange : ∀ m ∈ Finset.Ico A₀ (2 * A₀), ∀ n ∈ Finset.Ico C₀ (2 * C₀),
      |(slotCount S (m * n - 1) : ℝ) - slotMass S| ≤ Bs)
    (hcore : ∀ m ∈ Finset.Ico A₀ (2 * A₀), ∀ n ∈ Finset.Ico C₀ (2 * C₀),
      |centeredCore q 𝔞 x S (m * n - 1)| ≤ BF)
    (hT0 : 0 ≤ T) (hBΦ : ∀ t, |Φ t| ≤ BΦ) (hLip0 : 0 ≤ Lip)
    (hLip : ∀ s t : ℝ, |Φ s - Φ t| ≤ Lip * |s - t|) (hC : T * BΦ ≤ Real.log x ^ C)
    (hTII : ∀ lo hi : ℝ, (A₀ : ℝ) ≤ lo → hi ≤ 2 * (A₀ : ℝ) →
      ∀ (lam : DirichletCharacter ℂ H) (β : ℕ → ℂ), RoughDyadCoefficient x C (C₀ : ℝ) β →
        ‖markedBilinearSum q 𝔞 x (A₀ : ℝ) (C₀ : ℝ)
          (fun m => primeMinusRough x 0 lo hi m * lam (m : ZMod H)) β
          (fun h => ((clipCore Bs S h : ℝ) : ℂ))‖ ≤ Mb) :
    |∑ m ∈ Finset.Ico A₀ (2 * A₀), ∑ n ∈ Finset.Ico C₀ (2 * C₀),
        Φ (((m * n - 1 : ℕ) : ℝ) / x) *
          (clsInd H b (m * n) * centeredCore q 𝔞 x S (m * n - 1) * diffCoeff x γ m) *
            beta x γ j n| ≤
      ((Finset.Icc (A₀ / ℓ) (2 * A₀ / ℓ)).card : ℝ) * (Bs * Mb) +
        (A₀ : ℝ) * (C₀ : ℝ) * (Lip * ((ℓ : ℝ) * ((2 * C₀ : ℕ) : ℝ) / x) * BF * T) +
          (A₀ : ℝ) * (BΦ * BF * ∑ n ∈ Finset.Ico C₀ (2 * C₀), betaHi T x γ j n) := by
  have hA₀1 : 1 ≤ A₀ := by
    have h : (0 : ℝ) < (A₀ : ℝ) := lt_of_lt_of_le one_pos (hF.one_le.trans hA₀.le)
    exact_mod_cast h
  have hBΦ0 : 0 ≤ BΦ := (abs_nonneg _).trans (hBΦ 0)
  have hcardI : ((Finset.Ico A₀ (2 * A₀)).card : ℝ) = (A₀ : ℝ) := by
    rw [Nat.card_Ico]
    congr 1
    omega
  have hcardJ : ((Finset.Ico C₀ (2 * C₀)).card : ℝ) = (C₀ : ℝ) := by
    rw [Nat.card_Ico]
    congr 1
    omega
  have h := abs_box_le (I := Finset.Ico A₀ (2 * A₀)) (J := Finset.Ico C₀ (2 * C₀))
    (K := Finset.Icc (A₀ / ℓ) (2 * A₀ / ℓ)) (ℓ := ℓ)
    (fun m hm => Finset.mem_Icc.mpr
      ⟨Nat.div_le_div_right (Finset.mem_Ico.mp hm).1,
        Nat.div_le_div_right (Finset.mem_Ico.mp hm).2.le⟩)
    (fun m n => Φ (((m * n - 1 : ℕ) : ℝ) / x))
    (fun k n => Φ ((((k * ℓ * n : ℕ) : ℝ) - 1) / x))
    (fun m n => clsInd H b (m * n) * centeredCore q 𝔞 x S (m * n - 1) * diffCoeff x γ m)
    (beta x γ j) (betaLo T x γ j) (betaHi T x γ j)
    (fun n => betaLo_add_betaHi T x γ j n) (betaLo_nonneg T x γ j) (betaLo_le hT0 x γ j)
    (betaHi_nonneg T x γ j) hBF0
    (fun m hm n hn => abs_weight_le 𝔞 S hF (hcore m hm n hn)) hBΦ0 (fun m _ n _ => hBΦ _)
    (fun m hm n hn => abs_cutoff_sub_le hx hLip0 hLip hℓ
      (hA₀1.trans (Finset.mem_Ico.mp hm).1) (hC₀.trans (Finset.mem_Ico.mp hn).1)
      (Finset.mem_Ico.mp hn).2.le)
    (fun k _ => abs_cell_le hH hb 𝔞 S Φ hF hA₀ hℓ k hBs hrange hT0 hBΦ hC hTII)
  rw [hcardI, hcardJ] at h
  exact h

end Proxy

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
