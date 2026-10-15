module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinPerBox
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripStructure

/-!
# The coin step: `CoinLink`

`[P-07:0388–0514]`: "outcomes with fewer than `c₂ log L` successes in either family have total
positive weighted mass `o(x/L)` under the coefficient `∏_i ã(m_i)`", and the transfer
`[P-07:0506–0514]`: "A rough product box contains `O(x V(W)^j)` tuples, and
`∏_i ã(m_i) ≪ (L V(W))^{-j}` on its support. Thus its failure mass is `o(x/L^j)` uniformly. There
are `O(L^{j-1})` boxes, proving the claimed `o(x/L)` total."

* `geom_cut`, `sum_dyadic_tuples_le`: `∑_{k ∈ [0, K)^j, 2^{|k|} ≤ N} 2^{|k|} ≤ K^{j-1} · 2N` (the
  boxes with a small product are few *in mass*; no lower cutoff of `Φ` is needed).
* `sum_le_sum_cover`: a sum over tuples is at most the sum over a covering family of boxes.
* `strippedCoeff_le`: `0 ≤ ã(m) ≤ 1/(V(W) log x^γ)`, and `ã(m) ≠ 0` only for rough `m > x^γ`.
* `failure_sum_le`: the transfer at one `x`: the tuples are covered by the rough dyadic boxes
  `k_i = ⌊log₂ m_i⌋`, each of which has failure mass `≤ η' ∏ V(W) 2^{k_i}`.
* `coinFailureMass`: `RoughCounts → MertensReciprocal → MertensProduct → Coin.CoinFailureMass q₀`
  for `0 < q₀ < 1`, with `c₁ = coinC1 q₀`, `c₂ = coinC2 q₀ j`.
* `coinLink : CoinLink q₀`.

The helper declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter

noncomputable section

namespace Coin

/-! ### Dyadic boxes with bounded product -/

/-- `∑_{m < K, 2^m P ≤ N} 2^m P ≤ 2N`. -/
theorem geom_cut (P N : ℕ) : ∀ K : ℕ,
    ∑ m ∈ Finset.range K, (if 2 ^ m * P ≤ N then (2 : ℝ) ^ m * (P : ℝ) else 0) ≤
      2 * (N : ℝ) := by
  intro K
  induction K with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    positivity
  | succ K ih =>
    rw [Finset.sum_range_succ]
    by_cases h : 2 ^ K * P ≤ N
    · rw [if_pos h]
      have hgeom : ∑ m ∈ Finset.range K, (2 : ℝ) ^ m ≤ (2 : ℝ) ^ K := by
        have hnat : ∑ m ∈ Finset.range K, 2 ^ m < 2 ^ K :=
          Nat.geomSum_lt (le_refl 2) fun k hk => Finset.mem_range.mp hk
        have hc : ((∑ m ∈ Finset.range K, 2 ^ m : ℕ) : ℝ) < ((2 ^ K : ℕ) : ℝ) :=
          Nat.cast_lt.mpr hnat
        rw [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at hc
        refine le_of_lt (lt_of_eq_of_lt ?_ hc)
        exact Finset.sum_congr rfl fun m _ => by rw [Nat.cast_pow, Nat.cast_ofNat]
      have hle : ∑ m ∈ Finset.range K,
          (if 2 ^ m * P ≤ N then (2 : ℝ) ^ m * (P : ℝ) else 0) ≤ (2 : ℝ) ^ K * (P : ℝ) :=
        calc ∑ m ∈ Finset.range K, (if 2 ^ m * P ≤ N then (2 : ℝ) ^ m * (P : ℝ) else 0)
            ≤ ∑ m ∈ Finset.range K, (2 : ℝ) ^ m * (P : ℝ) :=
              Finset.sum_le_sum fun m _ => by
                split_ifs
                · exact le_rfl
                · positivity
          _ = (∑ m ∈ Finset.range K, (2 : ℝ) ^ m) * (P : ℝ) := (Finset.sum_mul _ _ _).symm
          _ ≤ (2 : ℝ) ^ K * (P : ℝ) := mul_le_mul_of_nonneg_right hgeom (Nat.cast_nonneg P)
      have hcast : (2 : ℝ) ^ K * (P : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
      linarith
    · rw [if_neg h, add_zero]
      exact ih

/-- `∑_{k ∈ [0, K)^{j'+1}, ∏ 2^{k_i} ≤ N} ∏ 2^{k_i} ≤ K^{j'} · 2N`. -/
theorem sum_dyadic_tuples_le (j' K N : ℕ) :
    ∑ k ∈ Fintype.piFinset (fun _ : Fin (j' + 1) => Finset.range K),
        (if ∏ i, 2 ^ k i ≤ N then ∏ i, (2 : ℝ) ^ k i else 0) ≤
      (K : ℝ) ^ j' * (2 * (N : ℝ)) := by
  rw [Strip.sum_piFinset_succ, Finset.sum_comm]
  have hinner : ∀ k' ∈ Fintype.piFinset (fun _ : Fin j' => Finset.range K),
      ∑ m ∈ Finset.range K,
        (if ∏ i, 2 ^ (Fin.cons m k' : Fin (j' + 1) → ℕ) i ≤ N then
          ∏ i, (2 : ℝ) ^ (Fin.cons m k' : Fin (j' + 1) → ℕ) i else 0) ≤ 2 * (N : ℝ) := by
    intro k' _
    have hcast : ((∏ i, 2 ^ k' i : ℕ) : ℝ) = ∏ i, (2 : ℝ) ^ k' i := by
      rw [Nat.cast_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [Nat.cast_pow, Nat.cast_ofNat]
    have h := geom_cut (∏ i, 2 ^ k' i) N K
    rw [hcast] at h
    refine (le_of_eq ?_).trans h
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  refine (Finset.sum_le_sum hinner).trans (le_of_eq ?_)
  rw [Finset.sum_const, Fintype.card_piFinset, Finset.prod_const, Finset.card_range,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

/-! ### Covering by boxes -/

/-- A sum over `S` is at most the sum over a family of boxes that covers the support, when the
summand is dominated on the boxes by a nonnegative function. -/
theorem sum_le_sum_cover {α κ : Type*} [DecidableEq α] (S : Finset α) (KK : Finset κ)
    (Box : κ → Finset α) (g h : α → ℝ) (hh : ∀ e, 0 ≤ h e)
    (hcov : ∀ e ∈ S, 0 < g e → ∃ k ∈ KK, e ∈ Box k ∧ g e ≤ h e) :
    ∑ e ∈ S, g e ≤ ∑ k ∈ KK, ∑ e ∈ Box k, h e := by
  have h1 : ∀ e ∈ S, g e ≤ ∑ k ∈ KK, (if e ∈ Box k then h e else 0) := by
    intro e he
    have hnn : ∀ k ∈ KK, 0 ≤ (if e ∈ Box k then h e else 0) := fun k _ => by
      split_ifs
      · exact hh e
      · exact le_rfl
    by_cases hg : 0 < g e
    · obtain ⟨k, hk, hek, hle⟩ := hcov e he hg
      calc g e ≤ h e := hle
        _ = (if e ∈ Box k then h e else 0) := (if_pos hek).symm
        _ ≤ ∑ k ∈ KK, (if e ∈ Box k then h e else 0) :=
            Finset.single_le_sum (f := fun k => if e ∈ Box k then h e else 0) hnn hk
    · exact (not_lt.mp hg).trans (Finset.sum_nonneg hnn)
  calc ∑ e ∈ S, g e ≤ ∑ e ∈ S, ∑ k ∈ KK, (if e ∈ Box k then h e else 0) :=
        Finset.sum_le_sum h1
    _ = ∑ k ∈ KK, ∑ e ∈ S, (if e ∈ Box k then h e else 0) := Finset.sum_comm
    _ ≤ ∑ k ∈ KK, ∑ e ∈ Box k, h e := Finset.sum_le_sum fun k _ => by
        rw [← Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun e he => (Finset.mem_filter.mp he).2) (fun e _ _ => hh e)

/-! ### The stripped coefficient -/

/-- `ã(m) ≤ 1/(V(W) ℓ)` with `ℓ = log x^γ`, and `ã(m) ≠ 0` only for `W`-rough `m > x^γ`. -/
theorem strippedCoeff_le {x γ ℓ : ℝ} {P : Finset ℕ} (hA : 1 ≤ x ^ γ) (hℓ : 0 < ℓ)
    (hlog : Real.log (x ^ γ) = ℓ) (m : ℕ) :
    strippedCoeff x γ P m ≤ 1 / (mertensProduct (roughCutoff x) * ℓ) ∧
      (strippedCoeff x γ P m ≠ 0 → IsRough (roughCutoff x) m ∧ x ^ γ < (m : ℝ)) := by
  have hκ0 : 0 ≤ 1 / (mertensProduct (roughCutoff x) * ℓ) :=
    (one_div_pos.mpr (mul_pos (mertensProduct_pos _) hℓ)).le
  by_cases hc : IsRough (roughCutoff x) m ∧ x ^ γ < (freePart P m : ℝ)
  · have hval : strippedCoeff x γ P m = proxyKappa x (freePart P m) := by
      unfold strippedCoeff
      exact if_pos hc
    have hm0 : m ≠ 0 := by
      intro h0
      have h1 : freePart P 0 = 1 := by simp [freePart]
      have h2 := hc.2
      rw [h0, h1, Nat.cast_one] at h2
      linarith
    refine ⟨?_, fun _ =>
      ⟨hc.1, lt_of_lt_of_le hc.2 (Nat.cast_le.mpr (Strip.freePart_le P hm0))⟩⟩
    rw [hval]
    exact (Strip.proxyKappa_facts hA hℓ hlog hc.2).2.2.2
  · have hval : strippedCoeff x γ P m = 0 := by
      unfold strippedCoeff
      exact if_neg hc
    rw [hval]
    exact ⟨hκ0, fun h => absurd rfl h⟩

/-! ### The transfer -/

/-- The final arithmetic: `‖Φ‖_∞ κ₀^j η' V^j K^{j-1} · 2N ≤ η' (2 ‖Φ‖_∞ 5^{j-1} (R+1)/γ^j) x/L`
when `κ₀ = 1/(V γ L)`, `N ≤ (R + 1) x` and `K ≤ 5 L`. -/
theorem transfer_arith {Bφ η' R x L V γ κ₀ : ℝ} {j N K : ℕ} (hj : 1 ≤ j) (hB0 : 0 ≤ Bφ)
    (hL : 0 < L) (hV : 0 < V) (hγ : 0 < γ) (hη' : 0 ≤ η') (hκ : κ₀ = 1 / (V * (γ * L)))
    (hN : (N : ℝ) ≤ (R + 1) * x) (hK : (K : ℝ) ≤ 5 * L) :
    Bφ * (κ₀ ^ j * (η' * (V ^ j * ((K : ℝ) ^ (j - 1) * (2 * (N : ℝ)))))) ≤
      η' * (2 * Bφ * 5 ^ (j - 1) * (R + 1) / γ ^ j) * (x / L) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hVne : V ≠ 0 := hV.ne'
  have hγne : γ ≠ 0 := hγ.ne'
  have hLne : L ≠ 0 := hL.ne'
  have hκV : κ₀ * V = 1 / (γ * L) := by
    rw [hκ]
    field_simp
  have e1 : κ₀ ^ (j' + 1) * V ^ (j' + 1) = (1 / (γ * L)) ^ (j' + 1) := by
    rw [← mul_pow, hκV]
  have hKp : (K : ℝ) ^ j' ≤ (5 * L) ^ j' := pow_le_pow_left₀ (Nat.cast_nonneg K) hK j'
  have hγL : 0 < γ * L := mul_pos hγ hL
  have hc0 : 0 ≤ Bφ * η' * (1 / (γ * L)) ^ (j' + 1) :=
    mul_nonneg (mul_nonneg hB0 hη') (pow_nonneg (one_div_pos.mpr hγL).le _)
  have h1 : (K : ℝ) ^ j' * (2 * (N : ℝ)) ≤ (5 * L) ^ j' * (2 * ((R + 1) * x)) :=
    mul_le_mul hKp (by linarith) (by positivity) (pow_nonneg (by linarith) _)
  calc Bφ * (κ₀ ^ (j' + 1) * (η' * (V ^ (j' + 1) * ((K : ℝ) ^ j' * (2 * (N : ℝ))))))
      = Bφ * η' * (κ₀ ^ (j' + 1) * V ^ (j' + 1)) * ((K : ℝ) ^ j' * (2 * (N : ℝ))) := by ring
    _ = Bφ * η' * (1 / (γ * L)) ^ (j' + 1) * ((K : ℝ) ^ j' * (2 * (N : ℝ))) := by rw [e1]
    _ ≤ Bφ * η' * (1 / (γ * L)) ^ (j' + 1) * ((5 * L) ^ j' * (2 * ((R + 1) * x))) :=
        mul_le_mul_of_nonneg_left h1 hc0
    _ = η' * (2 * Bφ * 5 ^ j' * (R + 1) / γ ^ (j' + 1)) * (x / L) := by
        rw [div_pow, one_pow, mul_pow, mul_pow, pow_succ L j']
        field_simp

/-- **The transfer at one `x`** (`[P-07:0506–0514]`): if every rough dyadic box with
`x^{γ/2} ≤ 2^{k_i} ≤ x²` has failure mass `≤ η' ∏ V(W) 2^{k_i}`, then the weighted failure mass
is `≤ η' (2 ‖Φ‖_∞ 5^{j-1} (R + 1)/γ^j) x/L`. -/
theorem failure_sum_le {Φ : ℝ → ℝ} {R Bφ : ℝ} (hR0 : 0 < R) (hR : ∀ t, R < t → Φ t = 0)
    (hB : ∀ t, Φ t ≤ Bφ) (hB0 : 0 ≤ Bφ) {x γ c₁ c₂ q₀ η' : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hγ : 0 < γ) (hc₁ : 0 ≤ c₁) (hq₀ : 0 ≤ q₀) (hη' : 0 ≤ η') (hxR : R + 1 ≤ x)
    (hL : 1 ≤ Real.log x) (hxγ2 : 2 ≤ x ^ (γ / 2))
    (hprob : ∀ (u : ℕ) (g : (candidateGroups x).Index),
      coinProb (candidateGroups x) c₁ q₀ j u g ≤ 1)
    (hbox : ∀ k : Fin j → ℕ,
      (∀ i, x ^ (γ / 2) ≤ (2 : ℝ) ^ k i ∧ (2 : ℝ) ^ k i ≤ x ^ (2 : ℝ)) →
        ∑ m ∈ roughBox x k, failedMass (candidateGroups x) c₁ c₂ q₀ j x (∏ i, m i - 1) ≤
          η' * ∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i) :
    shiftSum Φ x (fun _ => True)
        (fun u => |convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1) *
          failedMass (candidateGroups x) c₁ c₂ q₀ j x u|) ≤
      η' * (2 * Bφ * 5 ^ (j - 1) * (R + 1) / γ ^ j) * (x / Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hVpos := mertensProduct_pos (roughCutoff x)
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊R * x⌋₊ + 1 := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    rw [hNdef]
    exact Nat.succ_ne_zero _
  have hNle : (N : ℝ) ≤ (R + 1) * x := by
    rw [hNdef, Nat.cast_add, Nat.cast_one]
    have h := Nat.floor_le (mul_nonneg hR0.le hx0.le)
    linarith
  have hNxx : (N : ℝ) ≤ x * x := hNle.trans (mul_le_mul_of_nonneg_right hxR hx0.le)
  obtain ⟨κ₀, hκ₀⟩ :
      ∃ κ₀ : ℝ, κ₀ = 1 / (mertensProduct (roughCutoff x) * (γ * Real.log x)) := ⟨_, rfl⟩
  have hℓ : 0 < γ * Real.log x := mul_pos hγ hL0
  have hκpos : 0 < κ₀ := by
    rw [hκ₀]
    exact one_div_pos.mpr (mul_pos hVpos hℓ)
  have hA : 1 ≤ x ^ γ := Real.one_le_rpow hx1 hγ.le
  have hlog : Real.log (x ^ γ) = γ * Real.log x := Real.log_rpow hx0 γ
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = strippedCoeff x γ (candidatePrimes x) := ⟨_, rfl⟩
  obtain ⟨fm, hfm⟩ : ∃ fm : ℕ → ℝ, fm = failedMass (candidateGroups x) c₁ c₂ q₀ j x :=
    ⟨_, rfl⟩
  rw [← ha, ← hfm]
  have ha0 : ∀ m, 0 ≤ a m := fun m => by
    rw [ha]
    exact strippedCoeff_nonneg _ _ _ _
  have haκ : ∀ m, a m ≤ κ₀ := fun m => by
    rw [ha, hκ₀]
    exact (strippedCoeff_le hA hℓ hlog m).1
  have hasupp : ∀ m, a m ≠ 0 → IsRough (roughCutoff x) m ∧ x ^ γ < (m : ℝ) := fun m => by
    rw [ha]
    exact (strippedCoeff_le hA hℓ hlog m).2
  have hfm0 : ∀ u, 0 ≤ fm u := fun u => by
    rw [hfm]
    exact failedMass_nonneg _ c₂ x (fun g => coinProb_nonneg _ hc₁ hq₀ j u g)
      (fun g => hprob u g)
  -- step 1: from the smooth sum to the sum over `v ≤ N`
  have hstep1 : shiftSum Φ x (fun _ => True) (fun u => |convPow j a (u + 1) * fm u|) ≤
      Bφ * ∑ v ∈ Finset.Icc 1 N, |convPow j a v * fm (v - 1)| := by
    have hcongr : shiftSum Φ x (fun _ => True) (fun u => |convPow j a (u + 1) * fm u|) =
        shiftSum Φ x (fun _ => True)
          (fun u => (fun v => |convPow j a v * fm (v - 1)|) (u + 1)) :=
      shiftSum_congr Φ x _ fun u => by
        show |convPow j a (u + 1) * fm u| = |convPow j a (u + 1) * fm (u + 1 - 1)|
        rw [Nat.add_sub_cancel]
    rw [hcongr, hNdef]
    exact Strip.shiftSum_le_of_tuples hR hB hx0 (fun v => |convPow j a v * fm (v - 1)|)
      (fun v => abs_nonneg _)
  -- step 2: from the ordered factorizations to tuples
  obtain ⟨F, hF⟩ : ∃ F : (Fin j → ℕ) → ℝ,
      ∀ e, F e = (∏ i, a (e i)) * fm (∏ i, e i - 1) := ⟨_, fun _ => rfl⟩
  have hstep2 : ∑ v ∈ Finset.Icc 1 N, |convPow j a v * fm (v - 1)| =
      ∑ e ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
        (if ∏ i, e i ≤ N then F e else 0) := by
    rw [← Strip.sum_orderedFactorizations_eq j N F]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv0 : v ≠ 0 := by
      have := (Finset.mem_Icc.mp hv).1
      omega
    rw [abs_of_nonneg (mul_nonneg (convPow_nonneg ha0 j v) (hfm0 _))]
    unfold convPow
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hF, (mem_orderedFactorizations hv0).mp he]
  -- step 3: the dyadic boxes
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℕ, K₁ = Nat.log 2 N := ⟨_, rfl⟩
  have h2K : 2 ^ K₁ ≤ N := by
    rw [hK₁]
    exact Nat.pow_log_le_self 2 hN0
  obtain ⟨KK, hKK⟩ : ∃ KK : Finset (Fin j → ℕ),
      KK = (Fintype.piFinset (fun _ : Fin j => Finset.range (K₁ + 1))).filter
        (fun k => (∀ i, x ^ (γ / 2) ≤ (2 : ℝ) ^ k i) ∧ ∏ i, 2 ^ k i ≤ N) := ⟨_, rfl⟩
  have hcover : ∑ e ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
      (if ∏ i, e i ≤ N then F e else 0) ≤
      ∑ k ∈ KK, ∑ e ∈ roughBox x k, κ₀ ^ j * fm (∏ i, e i - 1) := by
    refine sum_le_sum_cover _ KK (fun k => roughBox x k) _
      (fun e => κ₀ ^ j * fm (∏ i, e i - 1))
      (fun e => mul_nonneg (pow_nonneg hκpos.le j) (hfm0 _)) ?_
    intro e he hpos
    have he1 : ∀ i, 1 ≤ e i ∧ e i ≤ N := fun i =>
      Finset.mem_Icc.mp (Fintype.mem_piFinset.mp he i)
    have he0 : ∀ i, e i ≠ 0 := fun i => by
      have := (he1 i).1
      omega
    by_cases hprod : ∏ i, e i ≤ N
    · rw [if_pos hprod] at hpos
      have hne : ∀ i, a (e i) ≠ 0 := by
        intro i hi
        have hz : F e = 0 := by
          rw [hF, Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
        rw [hz] at hpos
        exact lt_irrefl 0 hpos
      have hsupp : ∀ i, IsRough (roughCutoff x) (e i) ∧ x ^ γ < (e i : ℝ) := fun i =>
        hasupp _ (hne i)
      have hlt : ∀ i, e i < 2 ^ (Nat.log 2 (e i) + 1) := fun i =>
        Nat.lt_pow_succ_log_self (by norm_num) (e i)
      refine ⟨fun i => Nat.log 2 (e i), ?_, ?_, ?_⟩
      · rw [hKK]
        refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i =>
          Finset.mem_range.mpr ?_, fun i => ?_, ?_⟩
        · rw [hK₁]
          exact Nat.lt_succ_of_le (Nat.log_mono_right (he1 i).2)
        · have h2 : (e i : ℝ) < 2 * (2 : ℝ) ^ Nat.log 2 (e i) := by
            have h3 : ((e i : ℕ) : ℝ) < ((2 ^ (Nat.log 2 (e i) + 1) : ℕ) : ℝ) :=
              Nat.cast_lt.mpr (hlt i)
            rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ] at h3
            linarith
          have h3 : x ^ γ = x ^ (γ / 2) * x ^ (γ / 2) := by
            rw [← Real.rpow_add hx0]
            congr 1
            ring
          have h4 := (hsupp i).2
          have h5 : 0 ≤ x ^ (γ / 2) := by linarith
          have h6 : 2 * x ^ (γ / 2) ≤ x ^ (γ / 2) * x ^ (γ / 2) :=
            mul_le_mul_of_nonneg_right hxγ2 h5
          linarith
        · exact (Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
            fun i _ => Nat.pow_log_le_self 2 (he0 i)).trans hprod
      · exact Fintype.mem_piFinset.mpr fun i =>
          mem_roughDyad.mpr ⟨⟨Nat.pow_log_le_self 2 (he0 i), (hlt i).le⟩, (hsupp i).1⟩
      · rw [if_pos hprod, hF]
        refine mul_le_mul_of_nonneg_right ?_ (hfm0 _)
        calc ∏ i, a (e i) ≤ ∏ _i : Fin j, κ₀ :=
              Finset.prod_le_prod (fun i _ => ha0 _) (fun i _ => haκ _)
          _ = κ₀ ^ j := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · rw [if_neg hprod] at hpos
      exact absurd hpos (lt_irrefl 0)
  -- step 4: each box
  have hKKbox : ∀ k ∈ KK, ∑ e ∈ roughBox x k, κ₀ ^ j * fm (∏ i, e i - 1) ≤
      κ₀ ^ j * (η' * ∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i) := by
    intro k hk
    rw [hKK] at hk
    obtain ⟨hk1, hk2, -⟩ := Finset.mem_filter.mp hk
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hκpos.le j)
    rw [hfm]
    refine hbox k fun i => ⟨hk2 i, ?_⟩
    have hki : k i ≤ K₁ :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hk1 i))
    have h1 : 2 ^ k i ≤ N := (Nat.pow_le_pow_right (by norm_num) hki).trans h2K
    have h2 : ((2 ^ k i : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h1
    rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    calc (2 : ℝ) ^ k i ≤ (N : ℝ) := h2
      _ ≤ x * x := hNxx
      _ = x ^ (2 : ℝ) := by rw [Real.rpow_two, sq]
  -- step 5: the sum over the boxes
  have hsumKK : ∑ k ∈ KK, ∏ i, (2 : ℝ) ^ k i ≤
      ((K₁ + 1 : ℕ) : ℝ) ^ (j - 1) * (2 * (N : ℝ)) := by
    obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    subst hj'
    rw [Nat.add_sub_cancel]
    refine le_trans ?_ (sum_dyadic_tuples_le j' (K₁ + 1) N)
    rw [hKK, Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hc : (∀ i, x ^ (γ / 2) ≤ (2 : ℝ) ^ k i) ∧ ∏ i, 2 ^ k i ≤ N
    · rw [if_pos hc, if_pos hc.2]
    · rw [if_neg hc]
      split_ifs
      · exact Finset.prod_nonneg fun i _ => pow_nonneg zero_le_two _
      · exact le_rfl
  have hK₁le : ((K₁ + 1 : ℕ) : ℝ) ≤ 5 * Real.log x := by
    have h2 : ((2 ^ K₁ : ℕ) : ℝ) ≤ x * x := (Nat.cast_le.mpr h2K).trans hNxx
    rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    have h3 := Real.log_le_log (pow_pos two_pos K₁) h2
    rw [Real.log_pow, Real.log_mul hx0.ne' hx0.ne'] at h3
    have h4 : (K₁ : ℝ) * (1 / 2) ≤ (K₁ : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9]) (Nat.cast_nonneg _)
    push_cast
    linarith
  -- assembly
  have hVj : ∀ k : Fin j → ℕ, ∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i =
      mertensProduct (roughCutoff x) ^ j * ∏ i, (2 : ℝ) ^ k i := fun k => by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hκj0 : 0 ≤ κ₀ ^ j := pow_nonneg hκpos.le j
  have hVj0 : 0 ≤ mertensProduct (roughCutoff x) ^ j := pow_nonneg hVpos.le j
  have htotal : ∑ k ∈ KK, ∑ e ∈ roughBox x k, κ₀ ^ j * fm (∏ i, e i - 1) ≤
      κ₀ ^ j * (η' * (mertensProduct (roughCutoff x) ^ j *
        (((K₁ + 1 : ℕ) : ℝ) ^ (j - 1) * (2 * (N : ℝ))))) := by
    calc ∑ k ∈ KK, ∑ e ∈ roughBox x k, κ₀ ^ j * fm (∏ i, e i - 1)
        ≤ ∑ k ∈ KK, κ₀ ^ j * (η' * ∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i) :=
          Finset.sum_le_sum hKKbox
      _ = κ₀ ^ j * (η' * (mertensProduct (roughCutoff x) ^ j * ∑ k ∈ KK, ∏ i, (2 : ℝ) ^ k i)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [hVj]
      _ ≤ κ₀ ^ j * (η' * (mertensProduct (roughCutoff x) ^ j *
            (((K₁ + 1 : ℕ) : ℝ) ^ (j - 1) * (2 * (N : ℝ))))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumKK hVj0) hη') hκj0
  calc shiftSum Φ x (fun _ => True) (fun u => |convPow j a (u + 1) * fm u|)
      ≤ Bφ * ∑ v ∈ Finset.Icc 1 N, |convPow j a v * fm (v - 1)| := hstep1
    _ ≤ Bφ * (κ₀ ^ j * (η' * (mertensProduct (roughCutoff x) ^ j *
          (((K₁ + 1 : ℕ) : ℝ) ^ (j - 1) * (2 * (N : ℝ)))))) := by
        rw [hstep2]
        exact mul_le_mul_of_nonneg_left (hcover.trans htotal) hB0
    _ ≤ η' * (2 * Bφ * 5 ^ (j - 1) * (R + 1) / γ ^ j) * (x / Real.log x) :=
        transfer_arith hj hB0 hL0 hVpos hγ hη' hκ₀ hNle hK₁le

end Coin

/-! ### The coin step -/

/-- **The failure mass of the coins is `o(x/L)`** (`[P-07:0404–0407, 0506–0514]`): the second
clause of `CoinFailure q₀`, for `0 < q₀ < 1`, with `c₁ = ((1 - q₀)(log 2)/2)²` and
`c₂ = Coin.coinC2 q₀ j`. -/
theorem coinFailureMass {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) :
    RoughCounts → MertensReciprocal → MertensProduct → Coin.CoinFailureMass q₀ := by
  intro hRC hM1 hM2 Φ hΦ γ hγ hγ1 j hj
  have hj1 : 1 ≤ j := by omega
  refine ⟨Coin.coinC1 q₀, Coin.coinC2 q₀ j, Coin.coinC1_pos hq₀1, le_refl _,
    Coin.coinC2_pos hq₀ hq₀1 hj1, fun η hη => ?_⟩
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨Bφ, hB0, hB⟩ := hΦ.exists_bound
  obtain ⟨Cst, hCst⟩ : ∃ Cst : ℝ, Cst = 2 * Bφ * 5 ^ (j - 1) * (R + 1) / γ ^ j := ⟨_, rfl⟩
  have hCst0 : 0 ≤ Cst := by
    rw [hCst]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hB0)
      (pow_nonneg (by norm_num) _)) (by linarith)) (pow_pos hγ j).le
  obtain ⟨η', hη'def⟩ : ∃ η' : ℝ, η' = η / (Cst + 1) := ⟨_, rfl⟩
  have hCst1 : 0 < Cst + 1 := by linarith
  have hη'pos : 0 < η' := by
    rw [hη'def]
    exact div_pos hη hCst1
  have hη'le : η' * Cst ≤ η := by
    rw [hη'def, div_mul_eq_mul_div, div_le_iff₀ hCst1]
    have := mul_nonneg hη.le hCst0
    linarith
  have hbox := Coin.eventually_box_failedMass_le hRC hM1 hM2 hq₀ hq₀1 hj1 (half_pos hγ)
    (two_pos : (0 : ℝ) < 2) hη'pos
  have hprob := Coin.eventually_coinProb_le_one hM1 hq₀.le hq₀1 hj1
    (le_refl (Coin.coinC1 q₀))
  have hx2 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (γ / 2) :=
    (tendsto_rpow_atTop (half_pos hγ)).eventually_ge_atTop 2
  filter_upwards [hbox, hprob, hx2, eventually_ge_atTop (R + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hboxx hprobx hxγ2 hxR hL
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hmain := Coin.failure_sum_le hR0 hR hB hB0 hj1 hγ (Coin.coinC1_pos hq₀1).le hq₀.le
    hη'pos.le hxR hL hxγ2 hprobx hboxx
  rw [← hCst] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_right hη'le (div_pos hx0 hL0).le)

/-- **The coin step** (`[P-07:0388–0514]`): `CoinLink q₀` for `0 < q₀ < 1`. -/
theorem coinLink {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) : CoinLink q₀ :=
  fun hR hM1 hM2 =>
    Coin.coinFailure_of_mass hM1 hq₀.le hq₀1 (coinFailureMass hq₀ hq₀1 hR hM1 hM2)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
