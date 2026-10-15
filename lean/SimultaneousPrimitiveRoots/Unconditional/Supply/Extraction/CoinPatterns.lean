module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects

/-!
# The coin step: divisibility patterns and the polynomial minorant

`[P-07:0432–0449]`. Throughout, `u` is an integer and `v = u + 1` (the manuscript's
`v = m_1 ⋯ m_j`, `u = v - 1`).

* `hit A A' u`: the indicator of "every prime of `A` divides `u` and every prime of `A'` divides
  `u + 1`" (a *pattern*); `hit_mul_hit`: patterns multiply by taking unions.
* `alphaU j p = (p-1)^{j-1}/p^j`, `alphaV j p = 1 - (1 - 1/p)^j`: the probabilities `a_p`, `b_p` of
  (ext:prime-event-probabilities) `[P-07:0434–0437]`; `dens j A A'`: the density of a pattern in
  the independent residue model (`0` if the two sets meet: "the events `p ∣ u` and `p ∣ v` are
  disjoint").
* `BoxEq j P Ω u M ε`: the patterns with at most six primes of `P` have their model density on the
  finite sample `Ω`, with total mass `M` and relative error `ε`.
* `mono a g u` (`a : Fin 3`): the monomials `n n'`, `n² n'`, `n n'²` of the two hit counts
  `n = ω_g(u)`, `n' = ω_g(u + 1)` of a group `g`, written as sums of patterns over triples of
  primes of `g`; `mdl j a g`: their model values.
* `tee N₀ g u = n n' (N₀ + 2 - n - n')`: a polynomial of degree three in the two hit counts. It is
  a minorant of the success probability of the coin of `g` (`CoinMinorant.lean`); the manuscript
  uses instead the exact event "one hit of each type" and a Bonferroni limit
  (`[P-07:0450–0489]`).

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

noncomputable section

/-! ### Patterns -/

/-- The indicator of the pattern `(A, A')` at `u`: every prime of `A` divides `u`, every prime of
`A'` divides `u + 1`. -/
def hit (A A' : Finset ℕ) (u : ℕ) : ℝ :=
  if (∀ p ∈ A, p ∣ u) ∧ (∀ p ∈ A', p ∣ u + 1) then 1 else 0

/-- `1_{p ∣ u}`. -/
def indU (p u : ℕ) : ℝ := if p ∣ u then 1 else 0

/-- `1_{p ∣ u + 1}`. -/
def indV (p u : ℕ) : ℝ := if p ∣ u + 1 then 1 else 0

theorem hit_nonneg (A A' : Finset ℕ) (u : ℕ) : 0 ≤ hit A A' u := by
  unfold hit
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem hit_le_one (A A' : Finset ℕ) (u : ℕ) : hit A A' u ≤ 1 := by
  unfold hit
  split_ifs
  · exact le_rfl
  · exact zero_le_one

theorem hit_of {A A' : Finset ℕ} {u : ℕ} (h : (∀ p ∈ A, p ∣ u) ∧ (∀ p ∈ A', p ∣ u + 1)) :
    hit A A' u = 1 :=
  if_pos h

theorem hit_of_not {A A' : Finset ℕ} {u : ℕ}
    (h : ¬ ((∀ p ∈ A, p ∣ u) ∧ (∀ p ∈ A', p ∣ u + 1))) : hit A A' u = 0 :=
  if_neg h

theorem hit_empty (u : ℕ) : hit ∅ ∅ u = 1 :=
  hit_of ⟨fun p hp => absurd hp (Finset.notMem_empty p),
    fun p hp => absurd hp (Finset.notMem_empty p)⟩

/-- Patterns multiply by taking unions. -/
theorem hit_mul_hit (A A' B B' : Finset ℕ) (u : ℕ) :
    hit A A' u * hit B B' u = hit (A ∪ B) (A' ∪ B') u := by
  by_cases h1 : (∀ p ∈ A, p ∣ u) ∧ (∀ p ∈ A', p ∣ u + 1)
  · by_cases h2 : (∀ p ∈ B, p ∣ u) ∧ (∀ p ∈ B', p ∣ u + 1)
    · have h3 : (∀ p ∈ A ∪ B, p ∣ u) ∧ (∀ p ∈ A' ∪ B', p ∣ u + 1) :=
        ⟨fun p hp => (Finset.mem_union.mp hp).elim (h1.1 p) (h2.1 p),
          fun p hp => (Finset.mem_union.mp hp).elim (h1.2 p) (h2.2 p)⟩
      rw [hit_of h1, hit_of h2, hit_of h3, mul_one]
    · have h3 : ¬ ((∀ p ∈ A ∪ B, p ∣ u) ∧ (∀ p ∈ A' ∪ B', p ∣ u + 1)) := fun h =>
        h2 ⟨fun p hp => h.1 p (Finset.mem_union_right _ hp),
          fun p hp => h.2 p (Finset.mem_union_right _ hp)⟩
      rw [hit_of_not h2, hit_of_not h3, mul_zero]
  · have h3 : ¬ ((∀ p ∈ A ∪ B, p ∣ u) ∧ (∀ p ∈ A' ∪ B', p ∣ u + 1)) := fun h =>
      h1 ⟨fun p hp => h.1 p (Finset.mem_union_left _ hp),
        fun p hp => h.2 p (Finset.mem_union_left _ hp)⟩
    rw [hit_of_not h1, hit_of_not h3, zero_mul]

theorem hit_singleton_empty (p u : ℕ) : hit {p} ∅ u = indU p u := by
  unfold indU
  by_cases h : p ∣ u
  · rw [if_pos h]
    exact hit_of ⟨fun x hx => by rwa [Finset.mem_singleton.mp hx],
      fun x hx => absurd hx (Finset.notMem_empty x)⟩
  · rw [if_neg h]
    exact hit_of_not fun hc => h (hc.1 p (Finset.mem_singleton_self p))

theorem hit_empty_singleton (q u : ℕ) : hit ∅ {q} u = indV q u := by
  unfold indV
  by_cases h : q ∣ u + 1
  · rw [if_pos h]
    exact hit_of ⟨fun x hx => absurd hx (Finset.notMem_empty x),
      fun x hx => by rwa [Finset.mem_singleton.mp hx]⟩
  · rw [if_neg h]
    exact hit_of_not fun hc => h (hc.2 q (Finset.mem_singleton_self q))

/-- `hit A A' u = hit A ∅ u · hit ∅ A' u`. -/
theorem hit_eq_mul (A A' : Finset ℕ) (u : ℕ) : hit A A' u = hit A ∅ u * hit ∅ A' u := by
  rw [hit_mul_hit, Finset.union_empty, Finset.empty_union]

theorem hit_left_eq_prod (A : Finset ℕ) (u : ℕ) : hit A ∅ u = ∏ p ∈ A, indU p u := by
  induction A using Finset.induction_on with
  | empty => rw [Finset.prod_empty, hit_empty]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← hit_singleton_empty, hit_mul_hit, Finset.union_empty,
      ← Finset.insert_eq]

theorem hit_right_eq_prod (A' : Finset ℕ) (u : ℕ) : hit ∅ A' u = ∏ p ∈ A', indV p u := by
  induction A' using Finset.induction_on with
  | empty => rw [Finset.prod_empty, hit_empty]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← hit_empty_singleton, hit_mul_hit, Finset.union_empty,
      ← Finset.insert_eq]

/-- A pattern is the product of the indicators of its primes. -/
theorem hit_eq_prod (A A' : Finset ℕ) (u : ℕ) :
    hit A A' u = (∏ p ∈ A, indU p u) * ∏ p ∈ A', indV p u := by
  rw [hit_eq_mul, hit_left_eq_prod, hit_right_eq_prod]

/-- A pattern whose two sets share a prime never occurs. -/
theorem hit_eq_zero_of_not_disjoint {A A' : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (h : ¬ Disjoint A A') (u : ℕ) : hit A A' u = 0 := by
  obtain ⟨p, hp, hp'⟩ := Finset.not_disjoint_iff.mp h
  refine hit_of_not fun hc => ?_
  have h1 : p ∣ u := hc.1 p hp
  have h2 : p ∣ u + 1 := hc.2 p hp'
  have h3 : p ∣ 1 := (Nat.dvd_add_right h1).mp h2
  exact (hA p hp).one_lt.ne' (Nat.dvd_one.mp h3)

/-- The sum of the indicators `1_{p ∣ u}` over a group is the hit count `ω_g(u)`. -/
theorem sum_indU (g : Finset ℕ) (u : ℕ) : ∑ p ∈ g, indU p u = (primeHits g u : ℝ) := by
  unfold indU primeHits
  exact Finset.sum_boole _ _

theorem sum_indV (g : Finset ℕ) (u : ℕ) : ∑ p ∈ g, indV p u = (primeHits g (u + 1) : ℝ) := by
  unfold indV primeHits
  exact Finset.sum_boole _ _

/-! ### The model -/

/-- `a_p = (p - 1)^{j-1} / p^j`: the probability of `p ∣ u` when the `j` residues are independent
and uniform (`[P-07:0434–0440]`). -/
def alphaU (j p : ℕ) : ℝ := ((p : ℝ) - 1) ^ (j - 1) / (p : ℝ) ^ j

/-- `b_p = 1 - (1 - 1/p)^j`: the probability of `p ∣ v`. -/
def alphaV (j p : ℕ) : ℝ := 1 - (1 - 1 / (p : ℝ)) ^ j

/-- The model density of the pattern `(A, A')`: `∏_{p ∈ A} a_p ∏_{p ∈ A'} b_p`, and `0` if the two
sets meet. -/
def dens (j : ℕ) (A A' : Finset ℕ) : ℝ :=
  if Disjoint A A' then (∏ p ∈ A, alphaU j p) * ∏ p ∈ A', alphaV j p else 0

theorem dens_of {j : ℕ} {A A' : Finset ℕ} (h : Disjoint A A') :
    dens j A A' = (∏ p ∈ A, alphaU j p) * ∏ p ∈ A', alphaV j p :=
  if_pos h

theorem dens_of_not {j : ℕ} {A A' : Finset ℕ} (h : ¬ Disjoint A A') : dens j A A' = 0 :=
  if_neg h

theorem dens_empty (j : ℕ) : dens j ∅ ∅ = 1 := by
  rw [dens_of (Finset.disjoint_empty_left _), Finset.prod_empty, Finset.prod_empty, mul_one]

/-- **Equidistribution of the patterns on a finite sample** (`[P-07:0409–0449]`): every pattern
`(A, A')` of at most six primes of `P` occurs on `Ω` with its model density, with total mass `M`
and relative error `ε`. -/
def BoxEq {ι : Type*} (j : ℕ) (P : Finset ℕ) (Ω : Finset ι) (u : ι → ℕ) (M ε : ℝ) : Prop :=
  ∀ A A' : Finset ℕ, A ⊆ P → A' ⊆ P → A.card + A'.card ≤ 6 →
    |∑ m ∈ Ω, hit A A' (u m) - M * dens j A A'| ≤ ε * (M * dens j A A')

/-! ### The monomials of the two hit counts -/

/-- The primes of the triple `t = (p, q, r)` that are required to divide `u`, for the kind `a`:
`{p}` for `a = 0, 2`, `{p, r}` for `a = 1`. -/
def patU (a : Fin 3) (t : ℕ × ℕ × ℕ) : Finset ℕ := if a = 1 then {t.1, t.2.2} else {t.1}

/-- The primes of the triple `t = (p, q, r)` that are required to divide `u + 1`:
`{q}` for `a = 0, 1`, `{q, r}` for `a = 2`. -/
def patV (a : Fin 3) (t : ℕ × ℕ × ℕ) : Finset ℕ := if a = 2 then {t.2.1, t.2.2} else {t.2.1}

/-- The index set of the kind `a` in the group `g`: pairs `(p, q)` for `a = 0` (the third
coordinate is `0`), triples for `a = 1, 2`. -/
def idx (a : Fin 3) (g : Finset ℕ) : Finset (ℕ × ℕ × ℕ) := g ×ˢ g ×ˢ (if a = 0 then {0} else g)

/-- The monomial of kind `a` of the hit counts `n = ω_g(u)`, `n' = ω_g(u + 1)`: `n n'`, `n² n'`,
`n n'²` for `a = 0, 1, 2` (`mono_zero`, `mono_one`, `mono_two`), as a sum of patterns. -/
def mono (a : Fin 3) (g : Finset ℕ) (u : ℕ) : ℝ :=
  ∑ t ∈ idx a g, hit (patU a t) (patV a t) u

/-- The model value of the monomial of kind `a`. -/
def mdl (j : ℕ) (a : Fin 3) (g : Finset ℕ) : ℝ := ∑ t ∈ idx a g, dens j (patU a t) (patV a t)

/-- The coefficients of `tee`: `N₀ + 2, -1, -1`. -/
def gam (N₀ : ℝ) (a : Fin 3) : ℝ := if a = 0 then N₀ + 2 else -1

/-- `T_g(u) = (N₀ + 2) n n' - n² n' - n n'² = n n' (N₀ + 2 - n - n')` (`tee_eq`). -/
def tee (N₀ : ℝ) (g : Finset ℕ) (u : ℕ) : ℝ := ∑ a, gam N₀ a * mono a g u

theorem sum_triple (s₁ s₂ s₃ : Finset ℕ) (f : ℕ × ℕ × ℕ → ℝ) :
    ∑ t ∈ s₁ ×ˢ s₂ ×ˢ s₃, f t = ∑ p ∈ s₁, ∑ q ∈ s₂, ∑ r ∈ s₃, f (p, q, r) := by
  rw [Finset.sum_product]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_product _ _ _

theorem mono_zero (g : Finset ℕ) (u : ℕ) :
    mono 0 g u = (primeHits g u : ℝ) * (primeHits g (u + 1) : ℝ) := by
  have hidx : idx 0 g = g ×ˢ g ×ˢ {0} := by
    unfold idx
    rw [if_pos rfl]
  have hterm : ∀ p q : ℕ, hit (patU 0 (p, q, 0)) (patV 0 (p, q, 0)) u = indU p u * indV q u := by
    intro p q
    have e1 : patU 0 (p, q, 0) = {p} := if_neg (by decide)
    have e2 : patV 0 (p, q, 0) = {q} := if_neg (by decide)
    rw [e1, e2, hit_eq_mul, hit_singleton_empty, hit_empty_singleton]
  unfold mono
  rw [hidx, sum_triple, ← sum_indU, ← sum_indV, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_singleton]
  exact hterm p q

theorem mono_one (g : Finset ℕ) (u : ℕ) :
    mono 1 g u = (primeHits g u : ℝ) * (primeHits g u : ℝ) * (primeHits g (u + 1) : ℝ) := by
  have hidx : idx 1 g = g ×ˢ g ×ˢ g := by
    unfold idx
    rw [if_neg (by decide)]
  have hterm : ∀ p q r : ℕ,
      hit (patU 1 (p, q, r)) (patV 1 (p, q, r)) u = indU p u * indU r u * indV q u := by
    intro p q r
    have e1 : patU 1 (p, q, r) = {p, r} := if_pos rfl
    have e2 : patV 1 (p, q, r) = {q} := if_neg (by decide)
    rw [e1, e2, hit_eq_mul, hit_empty_singleton, ← hit_singleton_empty, ← hit_singleton_empty,
      hit_mul_hit, Finset.union_empty, ← Finset.insert_eq]
  unfold mono
  rw [hidx, sum_triple, ← sum_indU, ← sum_indV, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => hterm p q r

theorem mono_two (g : Finset ℕ) (u : ℕ) :
    mono 2 g u =
      (primeHits g u : ℝ) * (primeHits g (u + 1) : ℝ) * (primeHits g (u + 1) : ℝ) := by
  have hidx : idx 2 g = g ×ˢ g ×ˢ g := by
    unfold idx
    rw [if_neg (by decide)]
  have hterm : ∀ p q r : ℕ,
      hit (patU 2 (p, q, r)) (patV 2 (p, q, r)) u = indU p u * indV q u * indV r u := by
    intro p q r
    have e1 : patU 2 (p, q, r) = {p} := if_neg (by decide)
    have e2 : patV 2 (p, q, r) = {q, r} := if_pos rfl
    rw [e1, e2, hit_eq_mul, hit_singleton_empty, mul_assoc, ← hit_empty_singleton,
      ← hit_empty_singleton, hit_mul_hit, Finset.union_empty, ← Finset.insert_eq]
  unfold mono
  rw [hidx, sum_triple, ← sum_indU, ← sum_indV, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact Finset.sum_congr rfl fun r _ => hterm p q r

/-- `T_g(u) = n n' (N₀ + 2 - n - n')` with `n = ω_g(u)`, `n' = ω_g(u + 1)`. -/
theorem tee_eq (N₀ : ℝ) (g : Finset ℕ) (u : ℕ) :
    tee N₀ g u = (primeHits g u : ℝ) * (primeHits g (u + 1) : ℝ) *
      (N₀ + 2 - (primeHits g u : ℝ) - (primeHits g (u + 1) : ℝ)) := by
  have g0 : gam N₀ 0 = N₀ + 2 := if_pos rfl
  have g1 : gam N₀ 1 = -1 := if_neg (by decide)
  have g2 : gam N₀ 2 = -1 := if_neg (by decide)
  unfold tee
  rw [Fin.sum_univ_three, g0, g1, g2, mono_zero, mono_one, mono_two]
  ring

/-! ### The patterns of a monomial -/

theorem patU_subset {a : Fin 3} {g : Finset ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ idx a g) :
    patU a t ⊆ g := by
  unfold idx at ht
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp ht
  obtain ⟨-, h3⟩ := Finset.mem_product.mp h2
  unfold patU
  by_cases ha : a = 1
  · have ha0 : ¬ a = 0 := by
      rw [ha]
      decide
    rw [if_neg ha0] at h3
    rw [if_pos ha]
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rwa [hx]
    · rwa [Finset.mem_singleton.mp hx]
  · rw [if_neg ha]
    exact Finset.singleton_subset_iff.mpr h1

theorem patV_subset {a : Fin 3} {g : Finset ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ idx a g) :
    patV a t ⊆ g := by
  unfold idx at ht
  obtain ⟨-, h2⟩ := Finset.mem_product.mp ht
  obtain ⟨h4, h3⟩ := Finset.mem_product.mp h2
  unfold patV
  by_cases ha : a = 2
  · have ha0 : ¬ a = 0 := by
      rw [ha]
      decide
    rw [if_neg ha0] at h3
    rw [if_pos ha]
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rwa [hx]
    · rwa [Finset.mem_singleton.mp hx]
  · rw [if_neg ha]
    exact Finset.singleton_subset_iff.mpr h4

/-- A pattern of a monomial has at most three primes. -/
theorem pat_card_le (a : Fin 3) (t : ℕ × ℕ × ℕ) : (patU a t).card + (patV a t).card ≤ 3 := by
  have hU : (patU a t).card ≤ if a = 1 then 2 else 1 := by
    unfold patU
    by_cases ha : a = 1
    · rw [if_pos ha, if_pos ha]
      exact Finset.card_le_two
    · rw [if_neg ha, if_neg ha, Finset.card_singleton]
  have hV : (patV a t).card ≤ if a = 2 then 2 else 1 := by
    unfold patV
    by_cases ha : a = 2
    · rw [if_pos ha, if_pos ha]
      exact Finset.card_le_two
    · rw [if_neg ha, if_neg ha, Finset.card_singleton]
  have hsum : (if a = 1 then 2 else 1) + (if a = 2 then 2 else 1) ≤ 3 := by
    fin_cases a <;> decide
  omega

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin
