module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.AllocationIdentityProof

/-!
# Sums over tuples with bounded product

Tools for the positive tuple masses of [P] §7 (`[P-07:0347–0386]`): sums
`∑_{m_1 ⋯ m_j ≤ n} ∏_i w_i(m_i)` of nonnegative weights over the `j`-tuples of positive integers
with product at most `n`. The manuscript decomposes the tuples into product dyads; here one
coordinate is counted and the others are summed with the weight `1/m` (the hyperbola method),
which gives the same bounds without boxes.

* `sum_piFinset_succ`: a sum over the tuples `Fin (j+1) → s` is a sum over the first coordinate
  and the remaining tuple (`Fin.cons`).
* `tupleSum j w N n = ∑_{e ∈ [1, N]^j, ∏ e ≤ n} ∏_i w_i(e_i)`; `sum_orderedFactorizations_eq`:
  the sum over `v ≤ N` of the sums over the ordered factorizations of `v` is the sum over the
  tuples with product `≤ N`.
* `tupleSum_le`: **the count**: if the coordinate `i₀` satisfies `∑_{m ≤ t} w_{i₀}(m) ≤ c t` for
  `t ≤ N` and the other coordinates satisfy `∑_{m ≤ N} w_k(m)/m ≤ r_k`, then
  `tupleSum j w N n ≤ c n ∏_{k ≠ i₀} r_k` (stated with `∏_k r_k` and `r_{i₀} ≥ 1`).
* `prod_ite_two`: `∏_k r_k = s r^{j-2}` for the family `r_{i₀} = 1`, `r_{i₁} = s`, `r_k = r`.
* `abs_prod_sub_prod_le`: `|∏ a_i - ∏ b_i| ≤ ∑_i ∏_k (d_k if k = i, c_k otherwise)` when
  `|a_i|, |b_i| ≤ c_i` and `|a_i - b_i| ≤ d_i`.
* `sum_range_succ_eq_sum_Icc`.

The declarations are in the namespace `Extraction.Strip`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip

noncomputable section

/-! ### Tuples -/

/-- A sum over the tuples `Fin (j+1) → s` is a sum over the first coordinate and the rest. -/
theorem sum_piFinset_succ {j : ℕ} (s : Finset ℕ) (G : (Fin (j + 1) → ℕ) → ℝ) :
    ∑ e ∈ Fintype.piFinset (fun _ : Fin (j + 1) => s), G e =
      ∑ m ∈ s, ∑ e' ∈ Fintype.piFinset (fun _ : Fin j => s), G (Fin.cons m e') := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun e => (e 0, Fin.tail e)) (fun p => Fin.cons p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro e he
    have h := Fintype.mem_piFinset.mp he
    exact Finset.mem_product.mpr ⟨h 0, Fintype.mem_piFinset.mpr fun i => h i.succ⟩
  · rintro ⟨m, e'⟩ hp
    obtain ⟨hm, he'⟩ := Finset.mem_product.mp hp
    refine Fintype.mem_piFinset.mpr fun i => ?_
    induction i using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      exact hm
    | succ i' =>
      rw [Fin.cons_succ]
      exact Fintype.mem_piFinset.mp he' i'
  · intro e _
    exact Fin.cons_self_tail e
  · rintro ⟨m, e'⟩ _
    exact Prod.ext (Fin.cons_zero (α := fun _ => ℕ) m e') (Fin.tail_cons (α := fun _ => ℕ) m e')
  · intro e _
    show G e = G (Fin.cons (e 0) (Fin.tail e))
    rw [Fin.cons_self_tail]

/-- `∑_{e ∈ [1, N]^j, ∏ e ≤ n} ∏_i w_i(e_i)`: the sum of a product weight over the `j`-tuples of
positive integers with product at most `n` (`n ≤ N`). -/
def tupleSum (j : ℕ) (w : Fin j → ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ e ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
    if ∏ i, e i ≤ n then ∏ i, w i (e i) else 0

/-- The sum over `v ≤ N` of the sums over the ordered factorizations of `v` is the sum over the
tuples of `[1, N]^j` with product at most `N`. -/
theorem sum_orderedFactorizations_eq (j N : ℕ) (F : (Fin j → ℕ) → ℝ) :
    ∑ v ∈ Finset.Icc 1 N, ∑ e ∈ orderedFactorizations j v, F e =
      ∑ e ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
        if ∏ i, e i ≤ N then F e else 0 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin j → ℕ),
      T = (Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N)).filter
        (fun e => ∏ i, e i ≤ N) := ⟨_, rfl⟩
  have hmem : ∀ e ∈ T, (∀ i, 1 ≤ e i ∧ e i ≤ N) ∧ ∏ i, e i ≤ N := by
    intro e he
    rw [hT] at he
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
    exact ⟨fun i => Finset.mem_Icc.mp (Fintype.mem_piFinset.mp h1 i), h2⟩
  have hmaps : ∀ e ∈ T, (∏ i, e i) ∈ Finset.Icc 1 N := fun e he =>
    Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Finset.prod_pos fun i _ => ((hmem e he).1 i).1),
      (hmem e he).2⟩
  have hfib : ∀ v ∈ Finset.Icc 1 N,
      T.filter (fun e => ∏ i, e i = v) = orderedFactorizations j v := by
    intro v hv
    obtain ⟨hv1, hvN⟩ := Finset.mem_Icc.mp hv
    have hv0 : v ≠ 0 := by omega
    ext e
    rw [Finset.mem_filter, mem_orderedFactorizations hv0]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [hT]
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, by omega⟩
      have hdvd : e i ∣ v := (Finset.dvd_prod_of_mem e (Finset.mem_univ i)).trans (dvd_of_eq h)
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
        (Nat.le_of_dvd (by omega) hdvd).trans hvN⟩
  rw [← Finset.sum_filter, ← hT, ← Finset.sum_fiberwise_of_maps_to hmaps F]
  exact Finset.sum_congr rfl fun v hv => by rw [hfib v hv]

/-- The recursion of the tuple sum on the first coordinate. -/
theorem tupleSum_succ (j : ℕ) (w : Fin (j + 1) → ℕ → ℝ) (N n : ℕ) :
    tupleSum (j + 1) w N n =
      ∑ m ∈ Finset.Icc 1 N, ∑ e' ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
        if m * ∏ i, e' i ≤ n then w 0 m * ∏ i, w i.succ (e' i) else 0 := by
  unfold tupleSum
  rw [sum_piFinset_succ]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun e' _ => ?_
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- **The count of the tuples with bounded product** (the hyperbola method): one coordinate `i₀`
is counted (`∑_{m ≤ t} w_{i₀}(m) ≤ c t`), the others are summed with the weight `1/m`
(`∑_{m ≤ N} w_k(m)/m ≤ r_k`). With `r_{i₀} ≥ 1` (take `r_{i₀} = 1`):
`∑_{e, ∏ e ≤ n} ∏_i w_i(e_i) ≤ c n ∏_k r_k`. -/
theorem tupleSum_le (N : ℕ) : ∀ (j : ℕ) (w : Fin j → ℕ → ℝ) (r : Fin j → ℝ) (i₀ : Fin j)
    (c : ℝ), (∀ i m, 0 ≤ w i m) → 0 ≤ c →
    (∀ t : ℕ, t ≤ N → ∑ m ∈ Finset.Icc 1 t, w i₀ m ≤ c * (t : ℝ)) →
    (∀ k, k ≠ i₀ → ∑ m ∈ Finset.Icc 1 N, w k m / (m : ℝ) ≤ r k) → 1 ≤ r i₀ →
    ∀ n : ℕ, n ≤ N → tupleSum j w N n ≤ c * (n : ℝ) * ∏ k, r k := by
  intro j
  induction j with
  | zero => intro w r i₀; exact i₀.elim0
  | succ j ih =>
    intro w r i₀ c hw hc hcount hrec hr n hn
    have hr0 : ∀ k, 0 ≤ r k := by
      intro k
      by_cases hk : k = i₀
      · rw [hk]
        linarith
      · exact le_trans (Finset.sum_nonneg fun m _ =>
          div_nonneg (hw k m) (Nat.cast_nonneg m)) (hrec k hk)
    have hPr0 : 0 ≤ ∏ k : Fin j, r k.succ := Finset.prod_nonneg fun k _ => hr0 k.succ
    have hcn : 0 ≤ c * (n : ℝ) := mul_nonneg hc (Nat.cast_nonneg n)
    rw [tupleSum_succ, Fin.prod_univ_succ]
    rcases Fin.eq_zero_or_eq_succ i₀ with h0 | ⟨i', hi'⟩
    · -- the first coordinate is counted
      rw [h0] at hcount hrec hr
      rw [Finset.sum_comm]
      have hinner : ∀ e' ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
          ∑ m ∈ Finset.Icc 1 N,
            (if m * ∏ i, e' i ≤ n then w 0 m * ∏ i, w i.succ (e' i) else 0) ≤
          c * (n : ℝ) * ∏ i, (w i.succ (e' i) / (e' i : ℝ)) := by
        intro e' he'
        have he1 : ∀ i, 1 ≤ e' i := fun i =>
          (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp he' i)).1
        obtain ⟨P, hP⟩ : ∃ P : ℕ, P = ∏ i, e' i := ⟨_, rfl⟩
        have hP1 : 1 ≤ P := by
          rw [hP]
          exact Nat.succ_le_of_lt
            (Finset.prod_pos fun i _ => Nat.lt_of_lt_of_le Nat.zero_lt_one (he1 i))
        have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP1
        have hPw : 0 ≤ ∏ i, w i.succ (e' i) := Finset.prod_nonneg fun i _ => hw _ _
        rw [← hP]
        have h1 : ∑ m ∈ Finset.Icc 1 N,
            (if m * P ≤ n then w 0 m * ∏ i, w i.succ (e' i) else 0) =
            (∑ m ∈ (Finset.Icc 1 N).filter (fun m => m * P ≤ n), w 0 m) *
              ∏ i, w i.succ (e' i) := by
          rw [Finset.sum_mul, Finset.sum_filter]
        have hsub : (Finset.Icc 1 N).filter (fun m => m * P ≤ n) ⊆ Finset.Icc 1 (n / P) := by
          intro m hm
          obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm1).1,
            (Nat.le_div_iff_mul_le hP1).mpr hm2⟩
        have h2 : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m * P ≤ n), w 0 m ≤
            c * ((n : ℝ) / (P : ℝ)) :=
          calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m * P ≤ n), w 0 m
              ≤ ∑ m ∈ Finset.Icc 1 (n / P), w 0 m :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hw 0 m
            _ ≤ c * ((n / P : ℕ) : ℝ) := hcount (n / P) ((Nat.div_le_self n P).trans hn)
            _ ≤ c * ((n : ℝ) / (P : ℝ)) := mul_le_mul_of_nonneg_left Nat.cast_div_le hc
        have h3 : ∏ i, (w i.succ (e' i) / (e' i : ℝ)) = (∏ i, w i.succ (e' i)) / (P : ℝ) := by
          rw [Finset.prod_div_distrib, hP, Nat.cast_prod]
        rw [h1, h3]
        calc (∑ m ∈ (Finset.Icc 1 N).filter (fun m => m * P ≤ n), w 0 m) *
              ∏ i, w i.succ (e' i)
            ≤ c * ((n : ℝ) / (P : ℝ)) * ∏ i, w i.succ (e' i) :=
              mul_le_mul_of_nonneg_right h2 hPw
          _ = c * (n : ℝ) * ((∏ i, w i.succ (e' i)) / (P : ℝ)) := by ring
      have hprod : ∑ e' ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
          ∏ i, (w i.succ (e' i) / (e' i : ℝ)) =
          ∏ i : Fin j, ∑ m ∈ Finset.Icc 1 N, w i.succ m / (m : ℝ) :=
        (Finset.prod_univ_sum (fun _ : Fin j => Finset.Icc 1 N)
          (fun i m => w i.succ m / (m : ℝ))).symm
      have hle : ∏ i : Fin j, ∑ m ∈ Finset.Icc 1 N, w i.succ m / (m : ℝ) ≤
          ∏ k : Fin j, r k.succ :=
        Finset.prod_le_prod
          (fun i _ => Finset.sum_nonneg fun m _ => div_nonneg (hw _ m) (Nat.cast_nonneg m))
          (fun i _ => hrec i.succ (Fin.succ_ne_zero i))
      calc ∑ e' ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N), ∑ m ∈ Finset.Icc 1 N,
            (if m * ∏ i, e' i ≤ n then w 0 m * ∏ i, w i.succ (e' i) else 0)
          ≤ ∑ e' ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
              c * (n : ℝ) * ∏ i, (w i.succ (e' i) / (e' i : ℝ)) := Finset.sum_le_sum hinner
        _ = c * (n : ℝ) * ∏ i : Fin j, ∑ m ∈ Finset.Icc 1 N, w i.succ m / (m : ℝ) := by
            rw [← Finset.mul_sum, hprod]
        _ ≤ c * (n : ℝ) * ∏ k : Fin j, r k.succ := mul_le_mul_of_nonneg_left hle hcn
        _ ≤ c * (n : ℝ) * (r 0 * ∏ k : Fin j, r k.succ) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hPr0 hr) hcn
    · -- a later coordinate is counted: induction
      rw [hi'] at hcount hrec hr
      have hih : ∀ n' : ℕ, n' ≤ N → tupleSum j (fun i => w i.succ) N n' ≤
          c * (n' : ℝ) * ∏ k : Fin j, r k.succ :=
        ih (fun i => w i.succ) (fun k => r k.succ) i' c (fun i m => hw i.succ m) hc hcount
          (fun k hk => hrec k.succ fun h => hk (Fin.succ_injective _ h)) hr
      have hinner : ∀ m ∈ Finset.Icc 1 N,
          ∑ e' ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
            (if m * ∏ i, e' i ≤ n then w 0 m * ∏ i, w i.succ (e' i) else 0) ≤
          c * (n : ℝ) * (∏ k : Fin j, r k.succ) * (w 0 m / (m : ℝ)) := by
        intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
        have h1 : ∑ e' ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
            (if m * ∏ i, e' i ≤ n then w 0 m * ∏ i, w i.succ (e' i) else 0) =
            w 0 m * tupleSum j (fun i => w i.succ) N (n / m) := by
          unfold tupleSum
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e' _ => ?_
          by_cases h : m * ∏ i, e' i ≤ n
          · have h' : ∏ i, e' i ≤ n / m :=
              (Nat.le_div_iff_mul_le hm1).mpr (by rwa [mul_comm] at h)
            rw [if_pos h, if_pos h']
          · have h' : ¬ ∏ i, e' i ≤ n / m := fun h'' =>
              h (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hm1).mp h'')
            rw [if_neg h, if_neg h', mul_zero]
        have h2 := hih (n / m) ((Nat.div_le_self n m).trans hn)
        have h3 : c * ((n / m : ℕ) : ℝ) * ∏ k : Fin j, r k.succ ≤
            c * ((n : ℝ) / (m : ℝ)) * ∏ k : Fin j, r k.succ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Nat.cast_div_le hc) hPr0
        rw [h1]
        calc w 0 m * tupleSum j (fun i => w i.succ) N (n / m)
            ≤ w 0 m * (c * ((n : ℝ) / (m : ℝ)) * ∏ k : Fin j, r k.succ) :=
              mul_le_mul_of_nonneg_left (h2.trans h3) (hw 0 m)
          _ = c * (n : ℝ) * (∏ k : Fin j, r k.succ) * (w 0 m / (m : ℝ)) := by ring
      have h0 : (0 : Fin (j + 1)) ≠ i'.succ := (Fin.succ_ne_zero i').symm
      calc ∑ m ∈ Finset.Icc 1 N, ∑ e' ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
            (if m * ∏ i, e' i ≤ n then w 0 m * ∏ i, w i.succ (e' i) else 0)
          ≤ ∑ m ∈ Finset.Icc 1 N,
              c * (n : ℝ) * (∏ k : Fin j, r k.succ) * (w 0 m / (m : ℝ)) :=
            Finset.sum_le_sum hinner
        _ = c * (n : ℝ) * (∏ k : Fin j, r k.succ) * ∑ m ∈ Finset.Icc 1 N, w 0 m / (m : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ c * (n : ℝ) * (∏ k : Fin j, r k.succ) * r 0 :=
            mul_le_mul_of_nonneg_left (hrec 0 h0) (mul_nonneg hcn hPr0)
        _ = c * (n : ℝ) * (r 0 * ∏ k : Fin j, r k.succ) := by ring

/-! ### Products -/

/-- `∏_k r_k = s r^{j-2}` for `r_{i₀} = 1`, `r_{i₁} = s` and `r_k = r` otherwise. -/
theorem prod_ite_two {j : ℕ} {i₀ i₁ : Fin j} (h : i₀ ≠ i₁) (s r : ℝ) :
    ∏ k : Fin j, (if k = i₀ then 1 else if k = i₁ then s else r) = s * r ^ (j - 2) := by
  have hmem : i₁ ∈ (Finset.univ : Finset (Fin j)).erase i₀ :=
    Finset.mem_erase.mpr ⟨h.symm, Finset.mem_univ i₁⟩
  have hcongr : ∀ k ∈ ((Finset.univ : Finset (Fin j)).erase i₀).erase i₁,
      (if k = i₀ then (1 : ℝ) else if k = i₁ then s else r) = r := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_erase.mp hk
    rw [if_neg (Finset.mem_erase.mp hk2).1, if_neg hk1]
  have hcard : (((Finset.univ : Finset (Fin j)).erase i₀).erase i₁).card = j - 2 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, Fintype.card_fin]
    omega
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), if_pos rfl, one_mul,
    ← Finset.mul_prod_erase _ _ hmem, if_neg h.symm, if_pos rfl,
    Finset.prod_congr rfl hcongr, Finset.prod_const, hcard]

/-- `|∏ a_i - ∏ b_i| ≤ ∑_i ∏_k (d_k if k = i, c_k otherwise)` when `|a_i|, |b_i| ≤ c_i` and
`|a_i - b_i| ≤ d_i`. -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b c d : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ c i) (hb : ∀ i ∈ s, |b i| ≤ c i)
    (hd : ∀ i ∈ s, |a i - b i| ≤ d i) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, ∏ k ∈ s, (if k = i then d k else c k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    have hc0 : ∀ i ∈ insert x s, 0 ≤ c i := fun i hi => (abs_nonneg _).trans (ha i hi)
    have ha' : ∀ i ∈ s, |a i| ≤ c i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, |b i| ≤ c i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, |a i - b i| ≤ d i := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hxs := Finset.mem_insert_self x s
    have hA : |∏ i ∈ s, a i| ≤ ∏ i ∈ s, c i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) ha'
    have hPc : 0 ≤ ∏ i ∈ s, c i :=
      Finset.prod_nonneg fun i hi => hc0 i (Finset.mem_insert_of_mem hi)
    have hfirst : ∏ k ∈ s, (if k = x then d k else c k) = ∏ k ∈ s, c k :=
      Finset.prod_congr rfl fun k hk => if_neg fun h : k = x => hx (by rw [← h]; exact hk)
    have hrest : ∀ i ∈ s, ∏ k ∈ insert x s, (if k = i then d k else c k) =
        c x * ∏ k ∈ s, (if k = i then d k else c k) := fun i hi => by
      rw [Finset.prod_insert hx, if_neg fun h : x = i => hx (by rw [h]; exact hi)]
    have hsplit : ∏ i ∈ insert x s, a i - ∏ i ∈ insert x s, b i =
        (a x - b x) * ∏ i ∈ s, a i + b x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      ring
    rw [hsplit, Finset.sum_insert hx, Finset.prod_insert hx, if_pos rfl, hfirst,
      Finset.sum_congr rfl hrest, ← Finset.mul_sum]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (hd x hxs) hA (abs_nonneg _) ((abs_nonneg _).trans (hd x hxs))
    · rw [abs_mul]
      exact mul_le_mul (hb x hxs) (ih ha' hb' hd') (abs_nonneg _) (hc0 x hxs)

/-- `∑_{u < N} F(u + 1) = ∑_{1 ≤ v ≤ N} F(v)`. -/
theorem sum_range_succ_eq_sum_Icc (F : ℕ → ℝ) (N : ℕ) :
    ∑ u ∈ Finset.range N, F (u + 1) = ∑ v ∈ Finset.Icc 1 N, F v := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip
