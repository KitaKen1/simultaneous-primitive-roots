module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinPatterns
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Sanity

/-!
# The coin step: a polynomial minorant of the success probability

`[P-07:0390–0396, 0478–0488]`. With `n = ω_g(u)`, `n' = ω_g(u + 1)`, `q₁ = q₀/j` and
`0 < q₁ ≤ q₀ ≤ 1`, the success probability (ext:success-probability)

`s_g(u, u + 1) = c₁ · q₀^{n-1} n / V_g · q₁^{n'-1} n' / V_g`

satisfies, for every natural number `N₀ ≥ 1` and every `v₊ ≥ V_g`,

`s_g ≥ c₁ q₁^{N₀} / (N₀ v₊²) · n n' (N₀ + 2 - n - n')`.

Indeed the right side is `≤ 0` unless `n, n' ≥ 1` and `n + n' ≤ N₀ + 1`, and then
`q₀^{n-1} q₁^{n'-1} ≥ q₁^{n+n'-2} ≥ q₁^{N₀}` and `N₀ + 2 - n - n' ≤ N₀`.

The manuscript bounds `s_g` from below on the event "exactly one hit of each type", where it is
`c₁/V_g²` (`[P-07:0487–0488]`); the polynomial `tee N₀ g u = n n' (N₀ + 2 - n - n')` replaces the
indicator of that event, so that its mean over a product box is a finite combination of pattern
counts and no Bonferroni limit is needed.

* `markFactor_mul_ge`: the inequality for the two mark factors;
* `coinProb_ge_tee`: the inequality for `coinProb`, with `N₀ = 2j + 2`.

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

noncomputable section

/-- **The polynomial minorant of the two mark factors.** -/
theorem markFactor_mul_ge {q₀ q₁ vhi : ℝ} (hq₁ : 0 < q₁) (hq₁₀ : q₁ ≤ q₀) (hq₀ : q₀ ≤ 1)
    {S : Finset ℕ} (hV : 0 < reciprocalMass S) (hVhi : reciprocalMass S ≤ vhi) {N₀ : ℕ}
    (hN₀ : 1 ≤ N₀) (u : ℕ) :
    q₁ ^ N₀ / ((N₀ : ℝ) * vhi ^ 2) * tee (N₀ : ℝ) S u ≤
      markFactor q₀ S u * markFactor q₁ S (u + 1) := by
  have hq₀0 : 0 ≤ q₀ := hq₁.le.trans hq₁₀
  have hq₁1 : q₁ ≤ 1 := hq₁₀.trans hq₀
  have hvhi : 0 < vhi := lt_of_lt_of_le hV hVhi
  have hN₀R : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
  have hN₀pos : (0 : ℝ) < (N₀ : ℝ) := by linarith
  have hRHS0 : 0 ≤ markFactor q₀ S u * markFactor q₁ S (u + 1) :=
    mul_nonneg (markFactor_nonneg hq₀0 S u) (markFactor_nonneg hq₁.le S (u + 1))
  have hK0 : 0 ≤ q₁ ^ N₀ / ((N₀ : ℝ) * vhi ^ 2) :=
    div_nonneg (pow_nonneg hq₁.le _) (mul_nonneg hN₀pos.le (sq_nonneg vhi))
  rw [tee_eq]
  unfold markFactor
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = primeHits S u := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = primeHits S (u + 1) := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = reciprocalMass S := ⟨_, rfl⟩
  unfold markFactor at hRHS0
  rw [← ha, ← hb, ← hVdef] at hRHS0 ⊢
  rw [← hVdef] at hV hVhi
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hab0 : (0 : ℝ) ≤ (a : ℝ) * (b : ℝ) := mul_nonneg ha0 hb0
  by_cases hsmall : 1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ N₀ + 1
  · obtain ⟨ha1, hb1, hab⟩ := hsmall
    have ha1R : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have hb1R : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    -- the powers
    have hexp : a - 1 + (b - 1) ≤ N₀ := by omega
    have h1 : q₁ ^ N₀ ≤ q₀ ^ (a - 1) * q₁ ^ (b - 1) :=
      calc q₁ ^ N₀ ≤ q₁ ^ (a - 1 + (b - 1)) := pow_le_pow_of_le_one hq₁.le hq₁1 hexp
        _ = q₁ ^ (a - 1) * q₁ ^ (b - 1) := pow_add _ _ _
        _ ≤ q₀ ^ (a - 1) * q₁ ^ (b - 1) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq₁.le hq₁₀ _) (pow_nonneg hq₁.le _)
    -- the last factor is at most `N₀`
    have h2 : (a : ℝ) * (b : ℝ) * ((N₀ : ℝ) + 2 - (a : ℝ) - (b : ℝ)) ≤
        (a : ℝ) * (b : ℝ) * (N₀ : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) hab0
    have hV2 : 0 < V ^ 2 := pow_pos hV 2
    have hvhi2 : V ^ 2 ≤ vhi ^ 2 := pow_le_pow_left₀ hV.le hVhi 2
    have hnum0 : 0 ≤ q₁ ^ N₀ * ((a : ℝ) * (b : ℝ)) := mul_nonneg (pow_nonneg hq₁.le _) hab0
    calc q₁ ^ N₀ / ((N₀ : ℝ) * vhi ^ 2) *
          ((a : ℝ) * (b : ℝ) * ((N₀ : ℝ) + 2 - (a : ℝ) - (b : ℝ)))
        ≤ q₁ ^ N₀ / ((N₀ : ℝ) * vhi ^ 2) * ((a : ℝ) * (b : ℝ) * (N₀ : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hK0
      _ = q₁ ^ N₀ * ((a : ℝ) * (b : ℝ)) / vhi ^ 2 := by
          field_simp
      _ ≤ q₁ ^ N₀ * ((a : ℝ) * (b : ℝ)) / V ^ 2 :=
          div_le_div_of_nonneg_left hnum0 hV2 hvhi2
      _ ≤ q₀ ^ (a - 1) * q₁ ^ (b - 1) * ((a : ℝ) * (b : ℝ)) / V ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hab0) hV2.le
      _ = q₀ ^ (a - 1) * (a : ℝ) / V * (q₁ ^ (b - 1) * (b : ℝ) / V) := by
          field_simp
  · -- the polynomial is `≤ 0`
    have hneg : (a : ℝ) * (b : ℝ) * ((N₀ : ℝ) + 2 - (a : ℝ) - (b : ℝ)) ≤ 0 := by
      by_cases ha1 : 1 ≤ a
      · by_cases hb1 : 1 ≤ b
        · have hab : N₀ + 2 ≤ a + b := by
            by_contra hc
            exact hsmall ⟨ha1, hb1, by omega⟩
          have habR : (N₀ : ℝ) + 2 ≤ (a : ℝ) + (b : ℝ) := by exact_mod_cast hab
          exact mul_nonpos_of_nonneg_of_nonpos hab0 (by linarith)
        · have hb0' : b = 0 := by omega
          rw [hb0', Nat.cast_zero, mul_zero, zero_mul]
      · have ha0' : a = 0 := by omega
        rw [ha0', Nat.cast_zero, zero_mul, zero_mul]
    exact (mul_nonpos_of_nonneg_of_nonpos hK0 hneg).trans hRHS0

/-- **The polynomial minorant of the success probability** (`[P-07:0390–0396]`), with
`N₀ = 2j + 2`: `s_g(u, u + 1) ≥ c₁ (q₀/j)^{N₀} / (N₀ v₊²) · T_g(u)`. -/
theorem coinProb_ge_tee (𝔊 : ActiveGroups) {c₁ q₀ vhi : ℝ} (hc₁ : 0 ≤ c₁) (hq₀ : 0 < q₀)
    (hq₀1 : q₀ ≤ 1) {j : ℕ} (hj : 1 ≤ j) (g : 𝔊.Index)
    (hV : 0 < reciprocalMass (𝔊.group g)) (hVhi : reciprocalMass (𝔊.group g) ≤ vhi) (u : ℕ) :
    c₁ * ((q₀ / (j : ℝ)) ^ (2 * j + 2) / (((2 * j + 2 : ℕ) : ℝ) * vhi ^ 2)) *
        tee ((2 * j + 2 : ℕ) : ℝ) (𝔊.group g) u ≤ coinProb 𝔊 c₁ q₀ j u g := by
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hq₁ : 0 < q₀ / (j : ℝ) := div_pos hq₀ (by linarith)
  have hq₁₀ : q₀ / (j : ℝ) ≤ q₀ := div_le_self hq₀.le hjR
  have h := markFactor_mul_ge hq₁ hq₁₀ hq₀1 hV hVhi (N₀ := 2 * j + 2) (by omega) u
  unfold coinProb
  calc c₁ * ((q₀ / (j : ℝ)) ^ (2 * j + 2) / (((2 * j + 2 : ℕ) : ℝ) * vhi ^ 2)) *
        tee ((2 * j + 2 : ℕ) : ℝ) (𝔊.group g) u
      = c₁ * ((q₀ / (j : ℝ)) ^ (2 * j + 2) / (((2 * j + 2 : ℕ) : ℝ) * vhi ^ 2) *
          tee ((2 * j + 2 : ℕ) : ℝ) (𝔊.group g) u) := by ring
    _ ≤ c₁ * (markFactor q₀ (𝔊.group g) u * markFactor (q₀ / (j : ℝ)) (𝔊.group g) (u + 1)) :=
        mul_le_mul_of_nonneg_left h hc₁
    _ = c₁ * markFactor q₀ (𝔊.group g) u * markFactor (q₀ / (j : ℝ)) (𝔊.group g) (u + 1) := by
        ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin
