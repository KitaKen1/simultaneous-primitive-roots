module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects
public import Mathlib.NumberTheory.Divisors

/-!
# Finite sums of the Type II step

Reorganizations of finite sums used in the proof of `ProxyLink d H b q` (`[P-07:0249–0315]`,
`Extraction/ProxyProof.lean`). Nothing here is arithmetic.

* `Proxy.shiftSum_antidiagonal`: a shifted sum of a Dirichlet convolution at `u + 1` is a double
  sum over the two variables `m, n` with `mn = u + 1`.
* `Proxy.sum_Ico_mul_two_pow`, `Proxy.sum_sum_boxes`: "Dyadically decompose `m, n`"
  (`[P-07:0259–0260]`): the integers of `[m₀, m₀ 2^A)` are the disjoint union of the half-open
  dyads `[m₀ 2^a, m₀ 2^{a+1})`, `a < A`.
* `Proxy.abs_box_le`: the estimate of one box. The cutoff factor `φ₁(m, n)` is replaced by a factor
  `φ₀(k, n)` that is constant on the blocks `m / ℓ = k`, and the second coefficient is split into a
  bounded part `βlo ≤ T` and a part `βhi` of small `ℓ¹` norm ("truncation of `β_n` at `L^B`",
  `[P-07:0269–0281]`):

  `|∑_{m ∈ I, n ∈ J} φ₁ w β| ≤ |K| E₁ + |I| |J| ε₂ W T + |I| B_Φ W ∑_{n ∈ J} βhi(n)`,

  where `E₁` bounds the sum over one block with the separated factor `φ₀(k, n)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

namespace Proxy

/-! ### A shifted sum of a convolution is a double sum -/

open _root_.Classical in
/-- `∑_u Φ(u/x) F(u) ∑_{mn = u+1} h(m, n) = ∑_{m, n} Φ((mn-1)/x) F(mn-1) h(m, n)`, the sum over
`1 ≤ m, n < N` for any `N` beyond the support of the cutoff. -/
theorem shiftSum_antidiagonal {Φ : ℝ → ℝ} {R x : ℝ} (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x)
    (cls : ℕ → Prop) (F : ℕ → ℝ) (h : ℕ → ℕ → ℝ) {N : ℕ} (hN : ⌊R * x⌋₊ + 1 < N) :
    shiftSum Φ x cls (fun u => F u * ∑ p ∈ (u + 1).divisorsAntidiagonal, h p.1 p.2) =
      ∑ m ∈ Finset.Ico 1 N, ∑ n ∈ Finset.Ico 1 N,
        if cls (m * n) then Φ (((m * n - 1 : ℕ) : ℝ) / x) * (F (m * n - 1) * h m n) else 0 := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ × ℕ → ℝ, G = fun p =>
      if cls (p.1 * p.2) then
        Φ (((p.1 * p.2 - 1 : ℕ) : ℝ) / x) * (F (p.1 * p.2 - 1) * h p.1 p.2) else 0 := ⟨_, rfl⟩
  have hGp : ∀ p : ℕ × ℕ, G p = if cls (p.1 * p.2) then
      Φ (((p.1 * p.2 - 1 : ℕ) : ℝ) / x) * (F (p.1 * p.2 - 1) * h p.1 p.2) else 0 := by
    intro p
    rw [hG]
  -- the shifted sum as a sum over `u` and the factorizations of `u + 1`
  have hL : shiftSum Φ x cls (fun u => F u * ∑ p ∈ (u + 1).divisorsAntidiagonal, h p.1 p.2) =
      ∑ u ∈ Finset.range (⌊R * x⌋₊ + 1), ∑ p ∈ (u + 1).divisorsAntidiagonal, G p := by
    rw [shiftSum_eq_sum hR hx]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hterm : ∀ p ∈ (u + 1).divisorsAntidiagonal,
        G p = if cls (u + 1) then Φ ((u : ℝ) / x) * (F u * h p.1 p.2) else 0 := by
      intro p hp
      have hp1 : p.1 * p.2 = u + 1 := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [hGp, hp1, Nat.add_sub_cancel]
    rw [Finset.sum_congr rfl hterm]
    by_cases hc : cls (u + 1)
    · rw [if_pos hc, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => (if_pos hc).symm
    · rw [if_neg hc]
      exact (Finset.sum_eq_zero fun p _ => if_neg hc).symm
  -- exchange the two sums
  have hswap : ∑ u ∈ Finset.range (⌊R * x⌋₊ + 1), ∑ p ∈ (u + 1).divisorsAntidiagonal, G p =
      ∑ p ∈ (Finset.Ico 1 N ×ˢ Finset.Ico 1 N).filter (fun p => p.1 * p.2 ≤ ⌊R * x⌋₊ + 1),
        ∑ _u ∈ ({p.1 * p.2 - 1} : Finset ℕ), G p := by
    refine Finset.sum_comm' fun u p => ?_
    simp only [Finset.mem_range, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton,
      Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]
    constructor
    · rintro ⟨hu, hp, -⟩
      have h1 : 1 ≤ p.1 := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, zero_mul] at hp
        omega
      have h2 : 1 ≤ p.2 := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, mul_zero] at hp
        omega
      have h3 : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right _ h2
      have h4 : p.2 ≤ p.1 * p.2 := Nat.le_mul_of_pos_left _ h1
      exact ⟨by omega, ⟨⟨h1, by omega⟩, ⟨h2, by omega⟩⟩, by omega⟩
    · rintro ⟨hu, ⟨⟨h1, -⟩, ⟨h2, -⟩⟩, hle⟩
      have h3 : 0 < p.1 * p.2 := Nat.mul_pos h1 h2
      exact ⟨by omega, by omega, by omega⟩
  -- the pairs beyond the support contribute nothing
  have hsub : ∑ p ∈ (Finset.Ico 1 N ×ˢ Finset.Ico 1 N).filter
        (fun p => p.1 * p.2 ≤ ⌊R * x⌋₊ + 1), G p =
      ∑ p ∈ Finset.Ico 1 N ×ˢ Finset.Ico 1 N, G p := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hnot => ?_
    have hgt : ⌊R * x⌋₊ + 1 < p.1 * p.2 := by
      by_contra hcon
      exact hnot (Finset.mem_filter.mpr ⟨hp, not_lt.mp hcon⟩)
    have h1 : R * x < ((p.1 * p.2 - 1 : ℕ) : ℝ) := by
      have h2 : ⌊R * x⌋₊ + 1 ≤ p.1 * p.2 - 1 := by omega
      exact lt_of_lt_of_le (Nat.lt_floor_add_one (R * x)) (by exact_mod_cast h2)
    have h3 : Φ (((p.1 * p.2 - 1 : ℕ) : ℝ) / x) = 0 := hR _ (by rwa [lt_div_iff₀ hx])
    rw [hGp, h3, zero_mul]
    exact ite_self 0
  rw [hL, hswap, Finset.sum_congr rfl fun p _ => Finset.sum_singleton (fun _ => G p) _, hsub,
    Finset.sum_product]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => hGp (m, n)

/-! ### Dyadic boxes -/

/-- The integers of `[m₀, m₀ 2^A)` are the disjoint union of the dyads `[m₀ 2^a, m₀ 2^{a+1})`. -/
theorem sum_Ico_mul_two_pow (f : ℕ → ℝ) (m₀ A : ℕ) :
    ∑ m ∈ Finset.Ico m₀ (m₀ * 2 ^ A), f m =
      ∑ a ∈ Finset.range A, ∑ m ∈ Finset.Ico (m₀ * 2 ^ a) (m₀ * 2 ^ (a + 1)), f m := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive f (Nat.le_mul_of_pos_right m₀ (pow_pos two_pos A))
      (Nat.mul_le_mul_left m₀ (Nat.pow_le_pow_right two_pos (Nat.le_succ A)))).symm

/-- The decomposition of a double sum into dyadic boxes. -/
theorem sum_sum_boxes (m₀ A : ℕ) (t : ℕ → ℕ → ℝ) :
    ∑ m ∈ Finset.Ico m₀ (m₀ * 2 ^ A), ∑ n ∈ Finset.Ico m₀ (m₀ * 2 ^ A), t m n =
      ∑ a ∈ Finset.range A, ∑ c ∈ Finset.range A,
        ∑ m ∈ Finset.Ico (m₀ * 2 ^ a) (m₀ * 2 ^ (a + 1)),
          ∑ n ∈ Finset.Ico (m₀ * 2 ^ c) (m₀ * 2 ^ (c + 1)), t m n := by
  rw [sum_Ico_mul_two_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Finset.sum_congr rfl fun m _ => sum_Ico_mul_two_pow (fun n => t m n) m₀ A).trans
    Finset.sum_comm

/-! ### Double sums with termwise bounds -/

theorem abs_sum_sum_le_const {I J : Finset ℕ} {f : ℕ → ℕ → ℝ} {c : ℝ}
    (h : ∀ m ∈ I, ∀ n ∈ J, |f m n| ≤ c) :
    |∑ m ∈ I, ∑ n ∈ J, f m n| ≤ (I.card : ℝ) * (J.card : ℝ) * c :=
  calc |∑ m ∈ I, ∑ n ∈ J, f m n| ≤ ∑ m ∈ I, |∑ n ∈ J, f m n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ I, ∑ n ∈ J, |f m n| :=
        Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ I, ∑ _n ∈ J, c :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => h m hm n hn
    _ = (I.card : ℝ) * (J.card : ℝ) * c := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

theorem abs_sum_sum_le_sum {I J : Finset ℕ} {f : ℕ → ℕ → ℝ} {g : ℕ → ℝ} {c : ℝ}
    (h : ∀ m ∈ I, ∀ n ∈ J, |f m n| ≤ c * g n) :
    |∑ m ∈ I, ∑ n ∈ J, f m n| ≤ (I.card : ℝ) * (c * ∑ n ∈ J, g n) :=
  calc |∑ m ∈ I, ∑ n ∈ J, f m n| ≤ ∑ m ∈ I, |∑ n ∈ J, f m n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ I, ∑ n ∈ J, |f m n| :=
        Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ I, ∑ n ∈ J, c * g n :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => h m hm n hn
    _ = (I.card : ℝ) * (c * ∑ n ∈ J, g n) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]

/-! ### One box -/

/-- **The estimate of one box**, for abstract summands: blocks `m / ℓ = k`, `k ∈ K`, on which the
cutoff factor `φ₁(m, n)` is replaced by `φ₀(k, n)` at the cost `ε₂`, and the splitting
`β = βlo + βhi` with `0 ≤ βlo ≤ T`. -/
theorem abs_box_le {I J K : Finset ℕ} {ℓ : ℕ} (hK : ∀ m ∈ I, m / ℓ ∈ K)
    (φ₁ φ₀ w : ℕ → ℕ → ℝ) (β βlo βhi : ℕ → ℝ) {T W BΦ ε₂ E₁ : ℝ}
    (hβ : ∀ n, β n = βlo n + βhi n) (hlo0 : ∀ n, 0 ≤ βlo n) (hloT : ∀ n, βlo n ≤ T)
    (hhi0 : ∀ n, 0 ≤ βhi n) (hW0 : 0 ≤ W) (hw : ∀ m ∈ I, ∀ n ∈ J, |w m n| ≤ W)
    (hBΦ0 : 0 ≤ BΦ) (hBΦ : ∀ m ∈ I, ∀ n ∈ J, |φ₁ m n| ≤ BΦ)
    (hε : ∀ m ∈ I, ∀ n ∈ J, |φ₁ m n - φ₀ (m / ℓ) n| ≤ ε₂)
    (hmain : ∀ k ∈ K,
      |∑ m ∈ I, ∑ n ∈ J, if m / ℓ = k then φ₀ k n * w m n * βlo n else 0| ≤ E₁) :
    |∑ m ∈ I, ∑ n ∈ J, φ₁ m n * w m n * β n| ≤
      (K.card : ℝ) * E₁ + (I.card : ℝ) * (J.card : ℝ) * (ε₂ * W * T) +
        (I.card : ℝ) * (BΦ * W * ∑ n ∈ J, βhi n) := by
  have h1 : ∑ k ∈ K, ∑ m ∈ I, ∑ n ∈ J,
      (if m / ℓ = k then φ₀ k n * w m n * βlo n else 0) =
        ∑ m ∈ I, ∑ n ∈ J, φ₀ (m / ℓ) n * w m n * βlo n := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_ite_eq, if_pos (hK m hm)]
  have hsplit : ∑ m ∈ I, ∑ n ∈ J, φ₁ m n * w m n * β n =
      (∑ k ∈ K, ∑ m ∈ I, ∑ n ∈ J, if m / ℓ = k then φ₀ k n * w m n * βlo n else 0) +
        (∑ m ∈ I, ∑ n ∈ J, (φ₁ m n - φ₀ (m / ℓ) n) * w m n * βlo n) +
          ∑ m ∈ I, ∑ n ∈ J, φ₁ m n * w m n * βhi n := by
    rw [h1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hβ n]
    ring
  have hA : |∑ k ∈ K, ∑ m ∈ I, ∑ n ∈ J,
      if m / ℓ = k then φ₀ k n * w m n * βlo n else 0| ≤ (K.card : ℝ) * E₁ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hmain).trans (le_of_eq ?_))
    rw [Finset.sum_const, nsmul_eq_mul]
  have hB : |∑ m ∈ I, ∑ n ∈ J, (φ₁ m n - φ₀ (m / ℓ) n) * w m n * βlo n| ≤
      (I.card : ℝ) * (J.card : ℝ) * (ε₂ * W * T) := by
    refine abs_sum_sum_le_const fun m hm n hn => ?_
    have h2 := hε m hm n hn
    have hε0 : 0 ≤ ε₂ := (abs_nonneg _).trans h2
    rw [abs_mul, abs_mul, abs_of_nonneg (hlo0 n)]
    exact mul_le_mul (mul_le_mul h2 (hw m hm n hn) (abs_nonneg _) hε0) (hloT n) (hlo0 n)
      (mul_nonneg hε0 hW0)
  have hC : |∑ m ∈ I, ∑ n ∈ J, φ₁ m n * w m n * βhi n| ≤
      (I.card : ℝ) * (BΦ * W * ∑ n ∈ J, βhi n) := by
    refine abs_sum_sum_le_sum fun m hm n hn => ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hhi0 n)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hBΦ m hm n hn) (hw m hm n hn) (abs_nonneg _) hBΦ0) (hhi0 n)
  rw [hsplit]
  exact (abs_add_three _ _ _).trans (add_le_add (add_le_add hA hB) hC)

end Proxy

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
