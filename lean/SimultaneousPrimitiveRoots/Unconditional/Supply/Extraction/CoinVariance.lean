module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinMoments

/-!
# The coin step: the second-level Chebyshev inequality

(ext:success-covariance) and (ext:success-chebyshev) `[P-07:0489–0504]`: "there are `β > 0` and
`ε_x → 0`, uniform in the dyads and groups, such that `E I_g ≥ β`,
`|Cov(I_g, I_{g'})| ≤ ε_x` (`g ≠ g'`). For a family of `N ≍ log L` groups, Chebyshev gives
`P(∑_g I_g < β N / 2) ≤ 4/(β² N) + 4 ε_x/β² = o(1)`."

Here the variable is the polynomial minorant `T_g` of `CoinPatterns.lean` instead of the coin
indicator. For a family `fam : Fin n → Finset ℕ` of pairwise disjoint groups of primes of `P` with
`A_g + B_g ≤ N₀ - 1` and `M(n n') ≥ β`, on a sample `Ω` with `BoxEq j P Ω u M ε`, `ε ≤ 1`:

`#{m ∈ Ω : ∑_g T_g(u_m) < β n / 2} ≤ M (8 D / (β² n) + 16 ν² ε / β²)`

(`BoxEq.card_lowerTail_le`), with `D = teeDiag N₀` (the bound for the second moment of one `T_g`)
and `ν = teeBar N₀` (the bound for `teeNorm`). The mean of `T_g` is `≥ β` (`teeMean_ge`), the
mixed moments of two groups factor up to `ε ν²`, and no rate for `ε` relative to `1/n` is needed.

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

noncomputable section

/-- The bound for the second moment of one `T_g`: `(N₀ + 2)² (2 · 9⁶ + 92160 e^{N₀})`. -/
def teeDiag (N₀ : ℝ) : ℝ := (N₀ + 2) ^ 2 * (2 * 9 ^ 6 + 92160 * Real.exp N₀)

/-- The bound for `teeNorm`: `(2 N₀ + 3) N₀²`. -/
def teeBar (N₀ : ℝ) : ℝ := (2 * N₀ + 3) * N₀ ^ 2

theorem teeDiag_pos (N₀ : ℝ) (hN₀ : 0 ≤ N₀) : 0 < teeDiag N₀ := by
  unfold teeDiag
  have := Real.exp_pos N₀
  positivity

variable {ι : Type*} {j : ℕ} {P : Finset ℕ} {Ω : Finset ι} {u : ι → ℕ} {M ε : ℝ}

/-- **The second-level Chebyshev inequality** (`[P-07:0496–0504]`). -/
theorem BoxEq.card_lowerTail_le (hbox : BoxEq j P Ω u M ε) (hj : 1 ≤ j) (hP : ∀ p ∈ P, 1 ≤ p)
    (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {n : ℕ} (hn : 1 ≤ n) (fam : Fin n → Finset ℕ)
    (hfam : ∀ i, fam i ⊆ P) (hdisj : ∀ i i', i ≠ i' → Disjoint (fam i) (fam i'))
    {N₀ β : ℝ} (hN₀ : 1 ≤ N₀) (hβ : 0 < β)
    (hsum : ∀ i, sumU j (fam i) + sumV j (fam i) ≤ N₀ - 1)
    (hlow : ∀ i, β ≤ mdl j 0 (fam i)) :
    ((Ω.filter fun m => ∑ i, tee N₀ (fam i) (u m) < β * (n : ℝ) / 2).card : ℝ) ≤
      M * (8 * teeDiag N₀ / (β ^ 2 * (n : ℝ)) + 16 * teeBar N₀ ^ 2 * ε / β ^ 2) := by
  have hfam1 : ∀ i, ∀ p ∈ fam i, 1 ≤ p := fun i p hp => hP p (hfam i hp)
  have hN₀0 : 0 ≤ N₀ := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hD0 : 0 < teeDiag N₀ := teeDiag_pos N₀ hN₀0
  -- the mean and the norm of each group
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin n → ℝ, ∀ i, μ i = teeMean j N₀ (fam i) := ⟨_, fun _ => rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Fin n → ℝ, ∀ i, ν i = teeNorm j N₀ (fam i) := ⟨_, fun _ => rfl⟩
  have hm0 : ∀ i, 0 ≤ mdl j 0 (fam i) := fun i => mdl_nonneg hj 0 (hfam1 i)
  have hμβ : ∀ i, β ≤ μ i := by
    intro i
    rw [hμ]
    have h1 := teeMean_ge hj N₀ (hfam1 i)
    have h2 : 1 ≤ N₀ - sumU j (fam i) - sumV j (fam i) := by
      have := hsum i
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (hm0 i)
    have h4 := hlow i
    linarith
  have hν0 : ∀ i, 0 ≤ ν i := fun i => by
    rw [hν]
    exact teeNorm_nonneg hj N₀ (hfam1 i)
  have hμν : ∀ i, μ i ≤ ν i := fun i => by
    rw [hμ, hν]
    exact teeMean_le_teeNorm hj N₀ (hfam1 i)
  have hνbar : ∀ i, ν i ≤ teeBar N₀ := by
    intro i
    rw [hν]
    have h1 := teeNorm_le hj hN₀0 (hfam1 i)
    have h2 := mdl_zero_le hj (hfam1 i)
    have hU := sumU_nonneg hj (hfam1 i)
    have hV := sumV_nonneg j (hfam1 i)
    have hs := hsum i
    have h3 : sumU j (fam i) * sumV j (fam i) ≤ N₀ * N₀ :=
      mul_le_mul (by linarith) (by linarith) hV hN₀0
    have h4 : (N₀ + 4 + sumU j (fam i) + sumV j (fam i)) * mdl j 0 (fam i) ≤
        (2 * N₀ + 3) * (N₀ * N₀) :=
      mul_le_mul (by linarith) (h2.trans h3) (hm0 i) (by linarith)
    unfold teeBar
    calc teeNorm j N₀ (fam i)
        ≤ (N₀ + 4 + sumU j (fam i) + sumV j (fam i)) * mdl j 0 (fam i) := h1
      _ ≤ (2 * N₀ + 3) * (N₀ * N₀) := h4
      _ = (2 * N₀ + 3) * N₀ ^ 2 := by ring
  -- the totals
  obtain ⟨μs, hμsdef⟩ : ∃ μs : ℝ, μs = ∑ i, μ i := ⟨_, rfl⟩
  obtain ⟨νs, hνsdef⟩ : ∃ νs : ℝ, νs = ∑ i, ν i := ⟨_, rfl⟩
  have hcardn : ∀ c : ℝ, ∑ _i : Fin n, c = (n : ℝ) * c := fun c => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hμs : β * (n : ℝ) ≤ μs := by
    rw [hμsdef, mul_comm, ← hcardn β]
    exact Finset.sum_le_sum fun i _ => hμβ i
  have hνs0 : 0 ≤ νs := by
    rw [hνsdef]
    exact Finset.sum_nonneg fun i _ => hν0 i
  have hμsνs : μs ≤ νs := by
    rw [hμsdef, hνsdef]
    exact Finset.sum_le_sum fun i _ => hμν i
  have hνsbar : νs ≤ (n : ℝ) * teeBar N₀ := by
    rw [hνsdef, ← hcardn (teeBar N₀)]
    exact Finset.sum_le_sum fun i _ => hνbar i
  have hμs0 : 0 ≤ μs := le_trans (mul_nonneg hβ.le hn0.le) hμs
  -- the variable
  obtain ⟨Z, hZ⟩ : ∃ Z : ι → ℝ, ∀ m, Z m = ∑ i, tee N₀ (fam i) (u m) := ⟨_, fun _ => rfl⟩
  -- the first moment
  have hfirst : M * μs - ε * (M * νs) ≤ ∑ m ∈ Ω, Z m := by
    have e : ∑ m ∈ Ω, Z m = ∑ i, ∑ m ∈ Ω, tee N₀ (fam i) (u m) := by
      rw [Finset.sum_congr rfl fun m _ => hZ m]
      exact Finset.sum_comm
    have hi : ∀ i, M * μ i - ε * (M * ν i) ≤ ∑ m ∈ Ω, tee N₀ (fam i) (u m) := fun i => by
      have h := (abs_le.mp (hbox.abs_tee_sub_le (hfam i) N₀)).1
      rw [hμ, hν]
      linarith
    have e2 : M * μs - ε * (M * νs) = ∑ i, (M * μ i - ε * (M * ν i)) := by
      rw [Finset.sum_sub_distrib, hμsdef, hνsdef, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
    rw [e, e2]
    exact Finset.sum_le_sum fun i _ => hi i
  -- the second moment
  have hsecond : ∑ m ∈ Ω, Z m ^ 2 ≤
      (n : ℝ) * ((1 + ε) * M * teeDiag N₀) + M * μs ^ 2 + ε * (M * νs ^ 2) := by
    have e : ∑ m ∈ Ω, Z m ^ 2 =
        ∑ i, ∑ i', ∑ m ∈ Ω, tee N₀ (fam i) (u m) * tee N₀ (fam i') (u m) := by
      calc ∑ m ∈ Ω, Z m ^ 2
          = ∑ m ∈ Ω, ∑ i, ∑ i', tee N₀ (fam i) (u m) * tee N₀ (fam i') (u m) :=
            Finset.sum_congr rfl fun m _ => by rw [hZ, sq, Finset.sum_mul_sum]
        _ = ∑ i, ∑ m ∈ Ω, ∑ i', tee N₀ (fam i) (u m) * tee N₀ (fam i') (u m) :=
            Finset.sum_comm
        _ = ∑ i, ∑ i', ∑ m ∈ Ω, tee N₀ (fam i) (u m) * tee N₀ (fam i') (u m) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
    have hpair : ∀ i i', ∑ m ∈ Ω, tee N₀ (fam i) (u m) * tee N₀ (fam i') (u m) ≤
        (if i = i' then (1 + ε) * M * teeDiag N₀ else 0) + M * (μ i * μ i') +
          ε * (M * (ν i * ν i')) := by
      intro i i'
      have hμμ : 0 ≤ M * (μ i * μ i') :=
        mul_nonneg hM (mul_nonneg (hβ.le.trans (hμβ i)) (hβ.le.trans (hμβ i')))
      have hνν : 0 ≤ ε * (M * (ν i * ν i')) :=
        mul_nonneg hε0 (mul_nonneg hM (mul_nonneg (hν0 i) (hν0 i')))
      by_cases hii : i = i'
      · rw [if_pos hii, ← hii]
        have h := hbox.sum_tee_sq_le hj hP hM hε0 (hfam i) hN₀0
        have hexp : Real.exp (sumU j (fam i) + sumV j (fam i)) ≤ Real.exp N₀ :=
          Real.exp_le_exp.mpr (by
            have := hsum i
            linarith)
        have hdiag : (N₀ + 2) ^ 2 *
            (2 * 9 ^ 6 + 92160 * Real.exp (sumU j (fam i) + sumV j (fam i))) ≤ teeDiag N₀ := by
          unfold teeDiag
          exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        have e2 : ∑ m ∈ Ω, tee N₀ (fam i) (u m) * tee N₀ (fam i) (u m) =
            ∑ m ∈ Ω, tee N₀ (fam i) (u m) ^ 2 :=
          Finset.sum_congr rfl fun m _ => (sq _).symm
        have h3 := mul_le_mul_of_nonneg_left hdiag
          (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hM)
        have hμμ' : 0 ≤ M * (μ i * μ i) :=
          mul_nonneg hM (mul_nonneg (hβ.le.trans (hμβ i)) (hβ.le.trans (hμβ i)))
        have hνν' : 0 ≤ ε * (M * (ν i * ν i)) :=
          mul_nonneg hε0 (mul_nonneg hM (mul_nonneg (hν0 i) (hν0 i)))
        rw [e2]
        linarith
      · rw [if_neg hii, zero_add]
        have h := (abs_le.mp
          (hbox.abs_tee_mul_sub_le (hfam i) (hfam i') (hdisj i i' hii) N₀)).2
        rw [hμ, hμ, hν, hν]
        linarith
    have e1 : ∑ i : Fin n, ∑ i' : Fin n, (if i = i' then (1 + ε) * M * teeDiag N₀ else 0) =
        (n : ℝ) * ((1 + ε) * M * teeDiag N₀) := by
      have hrow : ∀ i : Fin n,
          ∑ i' : Fin n, (if i = i' then (1 + ε) * M * teeDiag N₀ else 0) =
            (1 + ε) * M * teeDiag N₀ := fun i => by
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
      rw [Finset.sum_congr rfl fun i _ => hrow i, hcardn]
    have e2 : ∑ i : Fin n, ∑ i' : Fin n, M * (μ i * μ i') = M * μs ^ 2 := by
      rw [hμsdef, sq, Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    have e3 : ∑ i : Fin n, ∑ i' : Fin n, ε * (M * (ν i * ν i')) = ε * (M * νs ^ 2) := by
      rw [hνsdef, sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [e, ← e1, ← e2, ← e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i' _ => hpair i i'
  have hcard := hbox.card_le
  -- the variance
  have hvar : ∑ m ∈ Ω, (Z m - μs) ^ 2 ≤
      2 * (n : ℝ) * M * teeDiag N₀ + 4 * ε * M * ((n : ℝ) * teeBar N₀) ^ 2 := by
    have e : ∑ m ∈ Ω, (Z m - μs) ^ 2 =
        ∑ m ∈ Ω, Z m ^ 2 - 2 * μs * ∑ m ∈ Ω, Z m + (Ω.card : ℝ) * μs ^ 2 := by
      have hexp : ∀ m ∈ Ω, (Z m - μs) ^ 2 = Z m ^ 2 - 2 * μs * Z m + μs ^ 2 :=
        fun m _ => by ring
      rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have h1 : 2 * μs * (M * μs - ε * (M * νs)) ≤ 2 * μs * ∑ m ∈ Ω, Z m :=
      mul_le_mul_of_nonneg_left hfirst (by linarith)
    have h2 : (Ω.card : ℝ) * μs ^ 2 ≤ (1 + ε) * M * μs ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    have hMD : 0 ≤ (n : ℝ) * (M * teeDiag N₀) :=
      mul_nonneg hn0.le (mul_nonneg hM hD0.le)
    have h3 : (n : ℝ) * ((1 + ε) * M * teeDiag N₀) ≤ 2 * (n : ℝ) * M * teeDiag N₀ := by
      have h31 : ε * ((n : ℝ) * (M * teeDiag N₀)) ≤ 1 * ((n : ℝ) * (M * teeDiag N₀)) :=
        mul_le_mul_of_nonneg_right hε1 hMD
      linarith
    have h4 : ε * M * (μs + νs) ^ 2 ≤ 4 * ε * M * ((n : ℝ) * teeBar N₀) ^ 2 := by
      have h41 : (μs + νs) ^ 2 ≤ (2 * ((n : ℝ) * teeBar N₀)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h42 := mul_le_mul_of_nonneg_left h41 (mul_nonneg hε0 hM)
      linarith
    have hid : (n : ℝ) * ((1 + ε) * M * teeDiag N₀) + M * μs ^ 2 + ε * (M * νs ^ 2) -
        2 * μs * (M * μs - ε * (M * νs)) + (1 + ε) * M * μs ^ 2 =
        (n : ℝ) * ((1 + ε) * M * teeDiag N₀) + ε * M * (μs + νs) ^ 2 := by ring
    rw [e]
    linarith
  -- Chebyshev
  have hthr0 : 0 ≤ β * (n : ℝ) / 2 := div_nonneg (mul_nonneg hβ.le hn0.le) zero_le_two
  have hcheb : ((Ω.filter fun m => ∑ i, tee N₀ (fam i) (u m) < β * (n : ℝ) / 2).card : ℝ) *
      (β * (n : ℝ) / 2) ^ 2 ≤ ∑ m ∈ Ω, (Z m - μs) ^ 2 := by
    calc ((Ω.filter fun m => ∑ i, tee N₀ (fam i) (u m) < β * (n : ℝ) / 2).card : ℝ) *
          (β * (n : ℝ) / 2) ^ 2
        = ∑ _m ∈ Ω.filter fun m => ∑ i, tee N₀ (fam i) (u m) < β * (n : ℝ) / 2,
            (β * (n : ℝ) / 2) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Ω.filter fun m => ∑ i, tee N₀ (fam i) (u m) < β * (n : ℝ) / 2,
            (Z m - μs) ^ 2 := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hlt : Z m < β * (n : ℝ) / 2 := by
            rw [hZ]
            exact (Finset.mem_filter.mp hm).2
          have h1 : β * (n : ℝ) / 2 ≤ μs - Z m := by linarith
          calc (β * (n : ℝ) / 2) ^ 2 ≤ (μs - Z m) ^ 2 := pow_le_pow_left₀ hthr0 h1 2
            _ = (Z m - μs) ^ 2 := by ring
      _ ≤ ∑ m ∈ Ω, (Z m - μs) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => sq_nonneg _
  have hpos : 0 < (β * (n : ℝ) / 2) ^ 2 := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  have hβ0 : β ≠ 0 := hβ.ne'
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  calc ((Ω.filter fun m => ∑ i, tee N₀ (fam i) (u m) < β * (n : ℝ) / 2).card : ℝ) *
        (β * (n : ℝ) / 2) ^ 2
      ≤ ∑ m ∈ Ω, (Z m - μs) ^ 2 := hcheb
    _ ≤ 2 * (n : ℝ) * M * teeDiag N₀ + 4 * ε * M * ((n : ℝ) * teeBar N₀) ^ 2 := hvar
    _ = M * (8 * teeDiag N₀ / (β ^ 2 * (n : ℝ)) + 16 * teeBar N₀ ^ 2 * ε / β ^ 2) *
          (β * (n : ℝ) / 2) ^ 2 := by
        field_simp
        ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin
