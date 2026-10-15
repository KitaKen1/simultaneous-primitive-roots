module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.AllocationIdentityProof
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Convolution powers and the companion coefficient of the Type II step

For the Type II step (`[P-07:0249–0315]`, `Extraction/ProxyProof.lean`) the difference of the
tuple sums over primes and over proxy coefficients is written with one distinguished variable:
"Telescope one variable `m` at a time and write `n` for the product of the other `j - 1`
variables" (`[P-07:0257–0259]`). In terms of Dirichlet convolutions,

`P^{*j} - a^{*j} = (P - a) * β_j`,  `β_1 = 1`, `β_{j+1} = P^{*j} + a * β_j`,

so the `j` telescoping steps are collected in one companion coefficient `β_j`
(`Proxy.companion`), "a fixed convolution of prime indicators and proxy coefficients"
(`[P-07:0264–0266]`).

* `Proxy.convPow_succ`: `a^{*(j+1)}(v) = ∑_{mn = v} a(m) a^{*j}(n)`; the bijection removes the first
  coordinate of an ordered factorization.
* `Proxy.toAF`, `Proxy.toAF_pow_apply`: `convPow j a` is the `j`-th power of `a` in the ring of
  arithmetic functions; the identity above is then a computation in a commutative ring
  (`Proxy.pow_sub_pow_eq`, `Proxy.convPow_sub_convPow`).
* `Proxy.companion_nonneg`, `Proxy.companion_le`: `0 ≤ β_j(n) ≤ j τ(n)^j` for coefficients in
  `[0, 1]` ("it is bounded by `L^{C_j} τ_{j-1}(n)`", `[P-07:0266–0267]`).
* `Proxy.companion_rough`, `Proxy.companion_lt`: `β_j` is supported on rough integers, and on
  integers `> z` for `j ≥ 2`, when the two coefficients are.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

namespace Proxy

/-! ### Ordered factorizations: removing the first coordinate -/

theorem orderedFactorizations_zero_right (j : ℕ) : orderedFactorizations j 0 = ∅ := by
  unfold orderedFactorizations
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  have h1 : ∏ i, e i = 0 := (Finset.mem_filter.mp he).2
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h1
  have h2 : e i ∈ (0 : ℕ).divisors := Fintype.mem_piFinset.mp (Finset.mem_filter.mp he).1 i
  rw [Nat.divisors_zero] at h2
  exact Finset.notMem_empty _ h2

theorem convPow_zero_right (j : ℕ) (a : ℕ → ℝ) : convPow j a 0 = 0 := by
  unfold convPow
  rw [orderedFactorizations_zero_right, Finset.sum_empty]

/-- The empty convolution is the indicator of `1`. -/
theorem convPow_zero_left (a : ℕ → ℝ) (v : ℕ) : convPow 0 a v = if v = 1 then 1 else 0 := by
  unfold convPow
  have hterm : ∀ e : Fin 0 → ℕ, ∏ i, a (e i) = 1 := fun e => Fin.prod_univ_zero _
  rw [Finset.sum_congr rfl fun e _ => hterm e, Finset.sum_const, nsmul_eq_mul, mul_one]
  by_cases h1 : v = 1
  · rw [if_pos h1, h1]
    have hcard : (orderedFactorizations 0 1).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨fun _ => 0, ?_⟩
      ext e
      rw [Finset.mem_singleton]
      constructor
      · intro _
        exact funext fun i => i.elim0
      · intro _
        exact (mem_orderedFactorizations one_ne_zero).mpr (Fin.prod_univ_zero _)
    rw [hcard, Nat.cast_one]
  · rw [if_neg h1]
    have hempty : orderedFactorizations 0 v = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      rcases Nat.eq_zero_or_pos v with h0 | h0
      · rw [h0, orderedFactorizations_zero_right] at he
        exact Finset.notMem_empty _ he
      · exact h1 (((mem_orderedFactorizations h0.ne').mp he).symm.trans (Fin.prod_univ_zero _))
    rw [hempty, Finset.card_empty, Nat.cast_zero]

/-- `a^{*(j+1)}(v) = ∑_{mn = v} a(m) a^{*j}(n)`. -/
theorem convPow_succ (j : ℕ) (a : ℕ → ℝ) (v : ℕ) :
    convPow (j + 1) a v = ∑ p ∈ v.divisorsAntidiagonal, a p.1 * convPow j a p.2 := by
  rcases Nat.eq_zero_or_pos v with hv | hv
  · rw [hv, convPow_zero_right, Nat.divisorsAntidiagonal_zero, Finset.sum_empty]
  · have hv0 : v ≠ 0 := hv.ne'
    have hR : ∑ p ∈ v.divisorsAntidiagonal, a p.1 * convPow j a p.2 =
        ∑ y ∈ v.divisorsAntidiagonal.sigma (fun p => orderedFactorizations j p.2),
          a y.1.1 * ∏ i, a (y.2 i) := by
      rw [Finset.sum_sigma]
      exact Finset.sum_congr rfl fun p _ => Finset.mul_sum _ _ _
    rw [hR]
    unfold convPow
    refine Finset.sum_nbij'
      (fun e : Fin (j + 1) → ℕ =>
        (⟨(e 0, ∏ i : Fin j, e i.succ), Fin.tail e⟩ : (_ : ℕ × ℕ) × (Fin j → ℕ)))
      (fun y => Fin.cons y.1.1 y.2) ?_ ?_ ?_ ?_ ?_
    · intro e he
      have hprod : ∏ i, e i = v := (mem_orderedFactorizations hv0).mp he
      rw [Fin.prod_univ_succ] at hprod
      have hne : ∏ i : Fin j, e i.succ ≠ 0 := fun h0 => hv0 (by rw [← hprod, h0, mul_zero])
      exact Finset.mem_sigma.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hv0⟩,
        (mem_orderedFactorizations hne).mpr rfl⟩
    · intro y hy
      obtain ⟨⟨m, n⟩, e'⟩ := y
      obtain ⟨h1, h2⟩ := Finset.mem_sigma.mp hy
      have h3 : m * n = v := (Nat.mem_divisorsAntidiagonal.mp h1).1
      have hne : n ≠ 0 := fun h0 => hv0 (by rw [← h3, h0, mul_zero])
      have hprod : ∏ i, e' i = n := (mem_orderedFactorizations hne).mp h2
      refine (mem_orderedFactorizations hv0).mpr ?_
      show ∏ i, (Fin.cons m e' : Fin (j + 1) → ℕ) i = v
      rw [Fin.prod_cons, hprod, h3]
    · intro e _
      exact Fin.cons_self_tail e
    · intro y hy
      obtain ⟨⟨m, n⟩, e'⟩ := y
      obtain ⟨h1, h2⟩ := Finset.mem_sigma.mp hy
      have h3 : m * n = v := (Nat.mem_divisorsAntidiagonal.mp h1).1
      have hne : n ≠ 0 := fun h0 => hv0 (by rw [← h3, h0, mul_zero])
      have hprod : ∏ i, e' i = n := (mem_orderedFactorizations hne).mp h2
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons, hprod]
    · intro e _
      rw [Fin.prod_univ_succ]
      rfl

/-! ### Coefficients as arithmetic functions -/

/-- A coefficient as an arithmetic function (the value at `0` is `0`). -/
def toAF (a : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else a n, if_pos rfl⟩

theorem toAF_apply (a : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) : toAF a n = a n := by
  show (if n = 0 then (0 : ℝ) else a n) = a n
  exact if_neg hn

theorem toAF_nonneg {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m) (n : ℕ) : 0 ≤ toAF a n := by
  show 0 ≤ (if n = 0 then (0 : ℝ) else a n)
  split_ifs
  · exact le_rfl
  · exact ha n

theorem toAF_le_one {a : ℕ → ℝ} (ha : ∀ m, a m ≤ 1) (n : ℕ) : toAF a n ≤ 1 := by
  show (if n = 0 then (0 : ℝ) else a n) ≤ 1
  split_ifs
  · exact zero_le_one
  · exact ha n

theorem toAF_ne_zero {a : ℕ → ℝ} {n : ℕ} (h : toAF a n ≠ 0) : n ≠ 0 ∧ a n ≠ 0 := by
  have hn : n ≠ 0 := fun h0 => h (by rw [h0]; exact ArithmeticFunction.map_zero)
  exact ⟨hn, by rwa [toAF_apply a hn] at h⟩

/-- `convPow j a` is the `j`-th power of `a` for the Dirichlet convolution. -/
theorem toAF_pow_apply (a : ℕ → ℝ) (j v : ℕ) : (toAF a ^ j) v = convPow j a v := by
  induction j generalizing v with
  | zero => rw [pow_zero, ArithmeticFunction.one_apply, convPow_zero_left]
  | succ j ih =>
    rw [pow_succ', ArithmeticFunction.mul_apply, convPow_succ]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp1, hv⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hp0 : p.1 ≠ 0 := fun h0 => hv (by rw [← hp1, h0, zero_mul])
    rw [ih, toAF_apply a hp0]

/-! ### The companion coefficient -/

/-- The companion coefficient of the telescoping (`[P-07:0257–0267]`): `β_0 = 0`,
`β_{j+1} = P^{*j} + a * β_j`, so that `P^{*j} - a^{*j} = (P - a) * β_j`. -/
def companion (P a : ℕ → ℝ) : ℕ → ArithmeticFunction ℝ
  | 0 => 0
  | j + 1 => toAF P ^ j + toAF a * companion P a j

theorem companion_zero_apply (P a : ℕ → ℝ) (n : ℕ) : companion P a 0 n = 0 := by
  show (0 : ArithmeticFunction ℝ) n = 0
  exact ArithmeticFunction.zero_apply

theorem companion_succ_apply (P a : ℕ → ℝ) (j n : ℕ) :
    companion P a (j + 1) n =
      convPow j P n + ∑ p ∈ n.divisorsAntidiagonal, toAF a p.1 * companion P a j p.2 := by
  show (toAF P ^ j + toAF a * companion P a j) n = _
  rw [ArithmeticFunction.add_apply, toAF_pow_apply, ArithmeticFunction.mul_apply]

/-- `P^{*j} - a^{*j} = (P - a) * β_j` in the ring of arithmetic functions. -/
theorem pow_sub_pow_eq (P a : ℕ → ℝ) (j : ℕ) :
    toAF P ^ j - toAF a ^ j = (toAF P - toAF a) * companion P a j := by
  induction j with
  | zero =>
    show toAF P ^ 0 - toAF a ^ 0 = (toAF P - toAF a) * 0
    rw [pow_zero, pow_zero, sub_self, mul_zero]
  | succ j ih =>
    have h : toAF P ^ (j + 1) - toAF a ^ (j + 1) =
        (toAF P - toAF a) * toAF P ^ j + toAF a * (toAF P ^ j - toAF a ^ j) := by ring
    rw [h, ih]
    show _ = (toAF P - toAF a) * (toAF P ^ j + toAF a * companion P a j)
    ring

/-- **The telescoping identity** (`[P-07:0256–0259]`):
`P^{*j}(v) - a^{*j}(v) = ∑_{mn = v} (P(m) - a(m)) β_j(n)`. -/
theorem convPow_sub_convPow (P a : ℕ → ℝ) (j v : ℕ) :
    convPow j P v - convPow j a v =
      ∑ p ∈ v.divisorsAntidiagonal, (P p.1 - a p.1) * companion P a j p.2 := by
  have hsub : ∀ (f g : ArithmeticFunction ℝ) (n : ℕ), (f - g) n = f n - g n := by
    intro f g n
    rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
      ← sub_eq_add_neg]
  have h : (toAF P ^ j - toAF a ^ j) v = ((toAF P - toAF a) * companion P a j) v := by
    rw [pow_sub_pow_eq]
  rw [hsub, toAF_pow_apply, toAF_pow_apply, ArithmeticFunction.mul_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, hv⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hp0 : p.1 ≠ 0 := fun h0 => hv (by rw [← hp1, h0, zero_mul])
  rw [hsub, toAF_apply P hp0, toAF_apply a hp0]

/-! ### Size of the companion coefficient -/

theorem card_divisorsAntidiagonal (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]

/-- A convolution power of a coefficient with values in `[0, 1]` is at most the number of ordered
factorizations, `τ_i(n) ≤ τ(n)^i`. -/
theorem convPow_le_card_pow {c : ℕ → ℝ} (h0 : ∀ m, 0 ≤ c m) (h1 : ∀ m, c m ≤ 1) (i n : ℕ) :
    convPow i c n ≤ (n.divisors.card : ℝ) ^ i := by
  unfold convPow
  have hprod : ∀ e : Fin i → ℕ, ∏ l, c (e l) ≤ 1 := fun e =>
    Finset.prod_le_one (fun l _ => h0 (e l)) (fun l _ => h1 (e l))
  have hcard : (orderedFactorizations i n).card ≤ n.divisors.card ^ i := by
    unfold orderedFactorizations
    refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ∑ e ∈ orderedFactorizations i n, ∏ l, c (e l)
      ≤ ∑ _e ∈ orderedFactorizations i n, (1 : ℝ) := Finset.sum_le_sum fun e _ => hprod e
    _ = ((orderedFactorizations i n).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (n.divisors.card : ℝ) ^ i := by exact_mod_cast hcard

theorem companion_nonneg {P a : ℕ → ℝ} (hP : ∀ m, 0 ≤ P m) (ha : ∀ m, 0 ≤ a m) (j n : ℕ) :
    0 ≤ companion P a j n := by
  induction j generalizing n with
  | zero => rw [companion_zero_apply]
  | succ j ih =>
    rw [companion_succ_apply]
    exact add_nonneg (convPow_nonneg hP j n)
      (Finset.sum_nonneg fun p _ => mul_nonneg (toAF_nonneg ha _) (ih _))

/-- `β_j(n) ≤ j τ(n)^j` for coefficients with values in `[0, 1]`. -/
theorem companion_le {P a : ℕ → ℝ} (hP0 : ∀ m, 0 ≤ P m) (hP1 : ∀ m, P m ≤ 1)
    (ha0 : ∀ m, 0 ≤ a m) (ha1 : ∀ m, a m ≤ 1) (j n : ℕ) :
    companion P a j n ≤ (j : ℝ) * (n.divisors.card : ℝ) ^ j := by
  induction j generalizing n with
  | zero => rw [companion_zero_apply, Nat.cast_zero, zero_mul]
  | succ j ih =>
    rw [companion_succ_apply]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, convPow_zero_right, Nat.divisorsAntidiagonal_zero, Finset.sum_empty, add_zero]
      positivity
    · have hτ1 : (1 : ℝ) ≤ (n.divisors.card : ℝ) :=
        Nat.one_le_cast.mpr (Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩)
      have h1 : convPow j P n ≤ (n.divisors.card : ℝ) ^ (j + 1) :=
        (convPow_le_card_pow hP0 hP1 j n).trans (pow_le_pow_right₀ hτ1 (Nat.le_succ j))
      have hterm : ∀ p ∈ n.divisorsAntidiagonal,
          toAF a p.1 * companion P a j p.2 ≤ (j : ℝ) * (n.divisors.card : ℝ) ^ j := by
        intro p hp
        have hdvd : p.2 ∣ n := Dvd.intro_left p.1 (Nat.mem_divisorsAntidiagonal.mp hp).1
        have hcard : ((p.2).divisors.card : ℝ) ≤ (n.divisors.card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hdvd))
        calc toAF a p.1 * companion P a j p.2
            ≤ 1 * ((j : ℝ) * ((p.2).divisors.card : ℝ) ^ j) :=
              mul_le_mul (toAF_le_one ha1 _) (ih _) (companion_nonneg hP0 ha0 j _) zero_le_one
          _ = (j : ℝ) * ((p.2).divisors.card : ℝ) ^ j := one_mul _
          _ ≤ (j : ℝ) * (n.divisors.card : ℝ) ^ j :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard j)
                (Nat.cast_nonneg j)
      have h2 : ∑ p ∈ n.divisorsAntidiagonal, toAF a p.1 * companion P a j p.2 ≤
          (n.divisors.card : ℝ) * ((j : ℝ) * (n.divisors.card : ℝ) ^ j) :=
        calc ∑ p ∈ n.divisorsAntidiagonal, toAF a p.1 * companion P a j p.2
            ≤ ∑ _p ∈ n.divisorsAntidiagonal, (j : ℝ) * (n.divisors.card : ℝ) ^ j :=
              Finset.sum_le_sum hterm
          _ = (n.divisors.card : ℝ) * ((j : ℝ) * (n.divisors.card : ℝ) ^ j) := by
              rw [Finset.sum_const, nsmul_eq_mul, card_divisorsAntidiagonal]
      calc convPow j P n + ∑ p ∈ n.divisorsAntidiagonal, toAF a p.1 * companion P a j p.2
          ≤ (n.divisors.card : ℝ) ^ (j + 1) +
              (n.divisors.card : ℝ) * ((j : ℝ) * (n.divisors.card : ℝ) ^ j) := add_le_add h1 h2
        _ = ((j + 1 : ℕ) : ℝ) * (n.divisors.card : ℝ) ^ (j + 1) := by
            push_cast
            ring

/-! ### Support of the companion coefficient -/

theorem isRough_mul {W : ℝ} {m n : ℕ} (hm : IsRough W m) (hn : IsRough W n) :
    IsRough W (m * n) := by
  intro p hp hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · exact hm p hp h
  · exact hn p hp h

theorem isRough_prod {W : ℝ} {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, IsRough W (f i)) : IsRough W (∏ i ∈ s, f i) := by
  intro p hp hdvd
  obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff (Nat.Prime.prime hp) f).mp hdvd
  exact h i hi p hp hpi

/-- A nonzero convolution power has a factorization with all coefficients nonzero. -/
theorem convPow_ne_zero {c : ℕ → ℝ} {i n : ℕ} (h : convPow i c n ≠ 0) :
    n ≠ 0 ∧ ∃ e : Fin i → ℕ, ∏ l, e l = n ∧ ∀ l, c (e l) ≠ 0 := by
  have hn : n ≠ 0 := fun h0 => h (by rw [h0, convPow_zero_right])
  refine ⟨hn, ?_⟩
  unfold convPow at h
  obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨e, (mem_orderedFactorizations hn).mp he,
    fun l => (Finset.prod_ne_zero_iff.mp hne) l (Finset.mem_univ l)⟩

theorem convPow_rough {W : ℝ} {c : ℕ → ℝ} (hc : ∀ m, c m ≠ 0 → IsRough W m) {i n : ℕ}
    (h : convPow i c n ≠ 0) : IsRough W n := by
  obtain ⟨-, e, he, hne⟩ := convPow_ne_zero h
  rw [← he]
  exact isRough_prod _ _ fun l _ => hc _ (hne l)

theorem convPow_lt {z : ℝ} {c : ℕ → ℝ} (hc : ∀ m, c m ≠ 0 → z < (m : ℝ)) {i n : ℕ}
    (hi : 1 ≤ i) (h : convPow i c n ≠ 0) : z < (n : ℝ) := by
  obtain ⟨hn, e, he, hne⟩ := convPow_ne_zero h
  have h0 : e ⟨0, hi⟩ ∣ n := by
    rw [← he]
    exact Finset.dvd_prod_of_mem e (Finset.mem_univ _)
  have hle : e ⟨0, hi⟩ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h0
  exact lt_of_lt_of_le (hc _ (hne _)) (Nat.cast_le.mpr hle)

/-- "The companion coefficient `β_n` is supported on `W`-rough integers" (`[P-07:0264–0265]`). -/
theorem companion_rough {W : ℝ} {P a : ℕ → ℝ} (hP : ∀ m, P m ≠ 0 → IsRough W m)
    (ha : ∀ m, a m ≠ 0 → IsRough W m) (j : ℕ) {n : ℕ} (h : companion P a j n ≠ 0) :
    IsRough W n := by
  induction j generalizing n with
  | zero => exact absurd (companion_zero_apply P a n) h
  | succ j ih =>
    rw [companion_succ_apply] at h
    by_cases h1 : convPow j P n = 0
    · rw [h1, zero_add] at h
      obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have hp1 : toAF a p.1 ≠ 0 := left_ne_zero_of_mul hne
      have hp2 : companion P a j p.2 ≠ 0 := right_ne_zero_of_mul hne
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1]
      exact isRough_mul (ha _ (toAF_ne_zero hp1).2) (ih hp2)
    · exact convPow_rough hP h1

/-- For `j ≥ 2` the companion coefficient is supported on the integers `> z` when the two
coefficients are: `n` is a product of `j - 1 ≥ 1` variables `> z`. -/
theorem companion_lt {z : ℝ} {P a : ℕ → ℝ} (hP : ∀ m, P m ≠ 0 → z < (m : ℝ))
    (ha : ∀ m, a m ≠ 0 → z < (m : ℝ)) {j : ℕ} (hj : 1 ≤ j) {n : ℕ}
    (h : companion P a (j + 1) n ≠ 0) : z < (n : ℝ) := by
  rw [companion_succ_apply] at h
  by_cases h1 : convPow j P n = 0
  · rw [h1, zero_add] at h
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hp1 := toAF_ne_zero (left_ne_zero_of_mul hne)
    obtain ⟨hpn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hle : p.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Dvd.intro _ hpn)
    exact lt_of_lt_of_le (ha _ hp1.2) (Nat.cast_le.mpr hle)
  · exact convPow_lt hP hj h1

end Proxy

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
