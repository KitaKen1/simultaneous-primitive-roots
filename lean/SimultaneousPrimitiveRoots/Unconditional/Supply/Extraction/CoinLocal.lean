module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinPatterns
public import Mathlib.Data.ZMod.QuotientRing

/-!
# The coin step: the local residue model at one prime

(ext:prime-event-probabilities) `[P-07:0432–0440]`: "in the independent residue model, for a
candidate prime `p` the events `p ∣ u` and `p ∣ v` are disjoint, with probabilities
`a_p = (p-1)^{j-1}/p^j`, `b_p = 1 - (1 - 1/p)^j`. For the first formula all residues must be
nonzero, and the first `j - 1` determine the last. For the second, at least one of the `j`
residues must be zero."

* `card_prod_eq_one`: `#{t ∈ (ℤ/p)^{k+1} : ∏ t_i = 1} = (p - 1)^k`;
  `card_prod_eq_zero`: `#{t ∈ (ℤ/p)^j : ∏ t_i = 0} = p^j - (p - 1)^j`.
* `sum_ind_prod_eq_one`, `sum_ind_prod_eq_zero`: the same counts as `p^j a_p` and `p^j b_p`.
* `alphaU_le`, `alphaU_ge`, `alphaV_le`, `alphaV_ge`: `1/(2p) ≤ a_p ≤ 1/p` (for `p ≥ 2j`) and
  `1/p ≤ b_p ≤ j/p` ("`∑ a_p = V_g + o(1)`, `∑ b_p = j V_g + o(1)`, while the largest individual
  probability tends to zero", `[P-07:0441–0443]`).

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

noncomputable section

/-! ### Counting residue tuples -/

/-- There are `(p - 1)^k` tuples of `k` nonzero residues. -/
theorem card_piFinset_erase_zero (p : ℕ) [NeZero p] (k : ℕ) :
    (Fintype.piFinset fun _ : Fin k => (Finset.univ : Finset (ZMod p)).erase 0).card =
      (p - 1) ^ k := by
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-- `#{t ∈ (ℤ/p)^j : ∏ t_i = 0} = p^j - (p - 1)^j`: at least one residue is zero. -/
theorem card_prod_eq_zero (p : ℕ) [NeZero p] (hp : p.Prime) (j : ℕ) :
    (Finset.univ.filter fun t : Fin j → ZMod p => ∏ i, t i = 0).card =
      p ^ j - (p - 1) ^ j := by
  have : Fact p.Prime := ⟨hp⟩
  have hcompl : (Finset.univ.filter fun t : Fin j → ZMod p => ∏ i, t i = 0) =
      (Fintype.piFinset fun _ : Fin j => (Finset.univ : Finset (ZMod p)).erase 0)ᶜ := by
    ext t
    rw [Finset.mem_filter, Finset.mem_compl, Fintype.mem_piFinset, Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨-, i, -, hi⟩ hall
      exact (Finset.mem_erase.mp (hall i)).1 hi
    · intro h
      refine ⟨Finset.mem_univ t, ?_⟩
      by_contra hc
      apply h
      intro i
      exact Finset.mem_erase.mpr ⟨fun hi => hc ⟨i, Finset.mem_univ i, hi⟩, Finset.mem_univ _⟩
  rw [hcompl, Finset.card_compl, card_piFinset_erase_zero, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

/-- `#{t ∈ (ℤ/p)^{k+1} : ∏ t_i = 1} = (p - 1)^k`: all residues are nonzero and the last `k`
determine the first. -/
theorem card_prod_eq_one (p : ℕ) [NeZero p] (hp : p.Prime) (k : ℕ) :
    (Finset.univ.filter fun t : Fin (k + 1) → ZMod p => ∏ i, t i = 1).card = (p - 1) ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← card_piFinset_erase_zero p k]
  refine Finset.card_nbij' (fun t : Fin (k + 1) → ZMod p => Fin.tail t)
    (fun s : Fin k → ZMod p => (Fin.cons (∏ i, s i)⁻¹ s : Fin (k + 1) → ZMod p)) ?_ ?_ ?_ ?_
  · intro t ht
    have ht' : ∏ i, t i = 1 := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
    rw [Fin.prod_univ_succ] at ht'
    refine Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_erase.mpr ⟨fun hi => ?_, Finset.mem_univ _⟩)
    have hz : ∏ i : Fin k, t i.succ = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hz, mul_zero] at ht'
    exact zero_ne_one ht'
  · intro s hs
    have hs' : ∀ i, s i ≠ 0 := fun i =>
      (Finset.mem_erase.mp (Fintype.mem_piFinset.mp (Finset.mem_coe.mp hs) i)).1
    have hne : ∏ i, s i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hs' i
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    show ∏ i, (Fin.cons (∏ i, s i)⁻¹ s : Fin (k + 1) → ZMod p) i = 1
    rw [Fin.prod_univ_succ, Fin.cons_zero]
    have e : ∀ i : Fin k, (Fin.cons (∏ i, s i)⁻¹ s : Fin (k + 1) → ZMod p) i.succ = s i :=
      fun i => Fin.cons_succ _ _ i
    rw [Finset.prod_congr rfl fun i _ => e i]
    exact inv_mul_cancel₀ hne
  · intro t ht
    have ht' : ∏ i, t i = 1 := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
    rw [Fin.prod_univ_succ] at ht'
    have h0 : t 0 = (∏ i : Fin k, t i.succ)⁻¹ := eq_inv_of_mul_eq_one_left ht'
    show (Fin.cons (∏ i : Fin k, t i.succ)⁻¹ (Fin.tail t) : Fin (k + 1) → ZMod p) = t
    rw [← h0]
    exact Fin.cons_self_tail t
  · intro s _
    exact Fin.tail_cons _ _

/-! ### The model probabilities -/

/-- `∑_{t ∈ (ℤ/p)^j} 1_{∏ t_i = 1} = p^j a_p`. -/
theorem sum_ind_prod_eq_one (p : ℕ) [NeZero p] (hp : p.Prime) {j : ℕ} (hj : 1 ≤ j) :
    ∑ t : Fin j → ZMod p, (if ∏ i, t i = 1 then (1 : ℝ) else 0) =
      (p : ℝ) ^ j * alphaU j p := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [Finset.sum_boole, card_prod_eq_one p hp k]
  unfold alphaU
  rw [Nat.add_sub_cancel, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
  field_simp

/-- `∑_{t ∈ (ℤ/p)^j} 1_{∏ t_i = 0} = p^j b_p`. -/
theorem sum_ind_prod_eq_zero (p : ℕ) [NeZero p] (hp : p.Prime) (j : ℕ) :
    ∑ t : Fin j → ZMod p, (if ∏ i, t i = 0 then (1 : ℝ) else 0) =
      (p : ℝ) ^ j * alphaV j p := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hle : (p - 1) ^ j ≤ p ^ j := Nat.pow_le_pow_left (Nat.sub_le p 1) j
  rw [Finset.sum_boole, card_prod_eq_zero p hp j]
  unfold alphaV
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
  have e : (1 - 1 / (p : ℝ)) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
  rw [e, div_pow]
  field_simp

/-- `a_p = (1 - 1/p)^k · (1/p)` for `j = k + 1`. -/
theorem alphaU_succ (k : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    alphaU (k + 1) p = (1 - 1 / (p : ℝ)) ^ k * (1 / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e : (1 - 1 / (p : ℝ)) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
  unfold alphaU
  rw [Nat.add_sub_cancel, e, div_pow, pow_succ]
  field_simp

theorem one_sub_inv_mem {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 ∧ 0 < 1 / (p : ℝ) ∧ 1 / (p : ℝ) ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h0 : 0 < 1 / (p : ℝ) := one_div_pos.mpr (by linarith)
  have h1 : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hp1
  exact ⟨by linarith, by linarith, h0, h1⟩

theorem alphaU_nonneg {j p : ℕ} (hj : 1 ≤ j) (hp : 1 ≤ p) : 0 ≤ alphaU j p := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨h0, -, h2, -⟩ := one_sub_inv_mem hp
  rw [alphaU_succ k hp]
  exact mul_nonneg (pow_nonneg h0 k) h2.le

/-- `a_p ≤ 1/p`. -/
theorem alphaU_le {j p : ℕ} (hj : 1 ≤ j) (hp : 1 ≤ p) : alphaU j p ≤ 1 / (p : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨h0, h1, h2, -⟩ := one_sub_inv_mem hp
  rw [alphaU_succ k hp]
  exact mul_le_of_le_one_left h2.le (pow_le_one₀ h0 h1)

/-- `a_p ≥ 1/(2p)` for `p ≥ 2j`. -/
theorem alphaU_ge {j p : ℕ} (hj : 1 ≤ j) (hp : 2 * j ≤ p) : 1 / (2 * (p : ℝ)) ≤ alphaU j p := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hp1 : 1 ≤ p := by omega
  obtain ⟨h0, h1, h2, h3⟩ := one_sub_inv_mem hp1
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
  rw [alphaU_succ k hp1]
  have hbern : 1 + (k : ℝ) * (-(1 / (p : ℝ))) ≤ (1 + -(1 / (p : ℝ))) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have e : (1 + -(1 / (p : ℝ))) = 1 - 1 / (p : ℝ) := by ring
  rw [e] at hbern
  have hk : (k : ℝ) * (1 / (p : ℝ)) ≤ 1 / 2 := by
    have h2k : (2 * (k : ℝ)) ≤ (p : ℝ) := by
      have : 2 * k ≤ p := by omega
      exact_mod_cast this
    rw [mul_one_div, div_le_iff₀ hpR]
    linarith
  have hhalf : (1 / 2 : ℝ) ≤ (1 - 1 / (p : ℝ)) ^ k := by linarith
  calc 1 / (2 * (p : ℝ)) = 1 / 2 * (1 / (p : ℝ)) := by
        field_simp
    _ ≤ (1 - 1 / (p : ℝ)) ^ k * (1 / (p : ℝ)) := mul_le_mul_of_nonneg_right hhalf h2.le

theorem alphaV_nonneg {j p : ℕ} (hp : 1 ≤ p) : 0 ≤ alphaV j p := by
  obtain ⟨h0, h1, -, -⟩ := one_sub_inv_mem hp
  unfold alphaV
  have := pow_le_one₀ (n := j) h0 h1
  linarith

/-- `b_p ≤ j/p`. -/
theorem alphaV_le {j p : ℕ} (hp : 1 ≤ p) : alphaV j p ≤ (j : ℝ) / (p : ℝ) := by
  obtain ⟨-, -, -, h3⟩ := one_sub_inv_mem hp
  unfold alphaV
  have hbern : 1 + (j : ℝ) * (-(1 / (p : ℝ))) ≤ (1 + -(1 / (p : ℝ))) ^ j :=
    one_add_mul_le_pow (by linarith) j
  have e : (1 + -(1 / (p : ℝ))) = 1 - 1 / (p : ℝ) := by ring
  rw [e] at hbern
  have e2 : (j : ℝ) / (p : ℝ) = (j : ℝ) * (1 / (p : ℝ)) := by ring
  rw [e2]
  linarith

/-- `b_p ≥ 1/p` for `j ≥ 1`. -/
theorem alphaV_ge {j p : ℕ} (hj : 1 ≤ j) (hp : 1 ≤ p) : 1 / (p : ℝ) ≤ alphaV j p := by
  obtain ⟨h0, h1, -, -⟩ := one_sub_inv_mem hp
  unfold alphaV
  have := pow_le_of_le_one h0 h1 (n := j) (by omega)
  linarith

theorem dens_nonneg {j : ℕ} (hj : 1 ≤ j) {A A' : Finset ℕ} (hA : ∀ p ∈ A, 1 ≤ p)
    (hA' : ∀ p ∈ A', 1 ≤ p) : 0 ≤ dens j A A' := by
  unfold dens
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg fun p hp => alphaU_nonneg hj (hA p hp))
      (Finset.prod_nonneg fun p hp => alphaV_nonneg (hA' p hp))
  · exact le_rfl

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin
