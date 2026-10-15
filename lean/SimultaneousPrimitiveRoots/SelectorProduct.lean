module

public import SimultaneousPrimitiveRoots.ProductBound
public import SimultaneousPrimitiveRoots.ResidueCounting

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable def sieveFactor (q : ℕ) : ℝ := ((q : ℝ) - 2) / ((q : ℝ) - 1)

theorem wallisProduct_eq_prod_range (m : ℕ) :
    wallisProduct m = ∏ j ∈ Finset.range m, ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) := by
  induction m with
  | zero => simp [wallisProduct]
  | succ m ih => rw [wallisProduct, Finset.prod_range_succ, ih]

/-- Dropping factors at composite odd integers only enlarges the product. -/
theorem wallisProduct_le_prime_sieve_product {S : Finset ℕ} {m : ℕ}
    (hS : ∀ q ∈ S, q.Prime ∧ 3 ≤ q ∧ q ≤ 2 * m + 1) :
    wallisProduct m ≤ ∏ q ∈ S, sieveFactor q := by
  classical
  let k : ℕ → ℕ := fun q => (q - 3) / 2
  have hk (q : ℕ) (hq : q ∈ S) : q = 2 * k q + 3 := by
    have h := hS q hq
    have hodd := h.1.eq_two_or_odd.resolve_left (by omega)
    dsimp [k]
    omega
  have hsub : S.image k ⊆ Finset.range m := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    have := hk q hq
    have := (hS q hq).2.2
    exact Finset.mem_range.mpr (by omega)
  have hinj : ∀ q ∈ S, ∀ t ∈ S, k q = k t → q = t := by
    intro q hq t ht hqt
    have := hk q hq
    have := hk t ht
    omega
  rw [wallisProduct_eq_prod_range]
  calc
    (∏ j ∈ Finset.range m, ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2))) ≤
        ∏ j ∈ S.image k, ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) := by
      apply Finset.prod_le_prod_of_subset_of_le_one hsub
      · intro j _
        positivity
      · intro j _ _
        apply (div_le_one (by positivity : 0 < 2 * (j : ℝ) + 2)).mpr
        linarith
    _ = ∏ q ∈ S, sieveFactor q := by
      rw [Finset.prod_image hinj]
      apply Finset.prod_congr rfl
      intro q hq
      have hcast : (q : ℝ) = 2 * (k q : ℝ) + 3 := by exact_mod_cast hk q hq
      unfold sieveFactor
      rw [hcast]
      congr 1 <;> ring

theorem prime_sieve_product_square_index_lower {S : Finset ℕ} {T : ℕ}
    (hT : 1 ≤ T) (hS : ∀ q ∈ S, q.Prime ∧ 3 ≤ q ∧ q ≤ 2 * T ^ 2 + 1) :
    1 / (2 * (T : ℝ)) ≤ ∏ q ∈ S, sieveFactor q :=
  wallisProduct_square_index_bound hT |>.trans (wallisProduct_le_prime_sieve_product hS)

theorem allowedExtensions_density_product_lower {M b : ℕ} {S : Finset ℕ}
    (hM : 0 < M) (hb : b < M) (hbc : b.Coprime M)
    (hS : ∀ q ∈ S, q.Prime) (hc : ∀ q ∈ S, M.Coprime q) :
    (1 / (Nat.totient M : ℝ)) * (∏ q ∈ S, sieveFactor q) ≤
      ((allowedExtensions M b S).card : ℝ) / Nat.totient (M * (∏ q ∈ S, q)) := by
  have htot : 0 < (Nat.totient (M * (∏ q ∈ S, q)) : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Nat.totient_pos.mpr
    exact Nat.mul_pos hM (Finset.prod_pos fun q hq => (hS q hq).pos)
  have ht : Nat.totient (M * (∏ q ∈ S, q)) =
      Nat.totient M * (∏ q ∈ S, (q - 1)) := by
    rw [Nat.totient_mul (Nat.coprime_prod_right_iff.mpr hc), totient_prod_primes hS]
  have hprod : ((∏ q ∈ S, (q - 2) : ℕ) : ℝ) /
      ((∏ q ∈ S, (q - 1) : ℕ) : ℝ) = ∏ q ∈ S, sieveFactor q := by
    rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro q hq
    simp only [sieveFactor, Nat.cast_sub (hS q hq).two_le, Nat.cast_ofNat,
      Nat.cast_sub (by have := (hS q hq).two_le; omega : 1 ≤ q), Nat.cast_one]
  calc
    (1 / (Nat.totient M : ℝ)) * (∏ q ∈ S, sieveFactor q) =
        ((∏ q ∈ S, (q - 2) : ℕ) : ℝ) / Nat.totient (M * (∏ q ∈ S, q)) := by
      rw [ht, Nat.cast_mul, ← hprod]
      ring
    _ ≤ ((allowedExtensions M b S).card : ℝ) / Nat.totient (M * (∏ q ∈ S, q)) := by
      apply div_le_div_of_nonneg_right _ htot.le
      exact_mod_cast allowedExtensions_card_lower hM hb hbc hS hc

theorem allowedExtensions_density_lower {M b : ℕ} {S : Finset ℕ} {T : ℕ}
    (hM : 0 < M) (hb : b < M) (hbc : b.Coprime M) (hT : 1 ≤ T)
    (hS : ∀ q ∈ S, q.Prime ∧ 3 ≤ q ∧ q ≤ 2 * T ^ 2 + 1)
    (hc : ∀ q ∈ S, M.Coprime q) :
    1 / (2 * (Nat.totient M : ℝ) * (T : ℝ)) ≤
      ((allowedExtensions M b S).card : ℝ) / Nat.totient (M * (∏ q ∈ S, q)) := by
  have hphi : 0 < (Nat.totient M : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  have hprod := prime_sieve_product_square_index_lower hT hS
  have hmul := mul_le_mul_of_nonneg_left hprod (le_of_lt (one_div_pos.mpr hphi))
  have heq : (1 / (Nat.totient M : ℝ)) * (1 / (2 * (T : ℝ))) =
      1 / (2 * (Nat.totient M : ℝ) * (T : ℝ)) := by ring
  rw [heq] at hmul
  exact hmul.trans (allowedExtensions_density_product_lower hM hb hbc
    (fun q hq => (hS q hq).1) hc)

end SimultaneousPrimitiveRoots
