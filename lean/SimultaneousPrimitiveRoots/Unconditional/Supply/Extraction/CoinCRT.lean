module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinLocal

/-!
# The coin step: pattern counts on a product box

`[P-07:0409–0449]`. Let `R_1, …, R_j` be finite sets of positive integers, each equidistributed in
the residue classes modulo `Q = ∏_{p ∈ A ∪ A'} p`:
`#{n ∈ R_i : n ≡ b (mod Q)} = (C_i / Q)(1 + θ ε)`, `|θ| ≤ 1`, for every `b`. Then the number of
tuples `m ∈ R_1 × ⋯ × R_j` with `p ∣ m_1 ⋯ m_j - 1` for `p ∈ A` and `p ∣ m_1 ⋯ m_j` for `p ∈ A'`
is `(∏ C_i) · ∏_{p ∈ A} a_p · ∏_{p ∈ A'} b_p` up to the relative error `(1 + ε)^j - 1`
(`abs_pattern_count_sub_le`). "Distinct primes are independent in this model."

* `abs_prod_sub_prod_le_pow`: `|∏ x_i - ∏ c_i| ≤ ((1 + ε)^n - 1) ∏ c_i` when
  `|x_i - c_i| ≤ ε c_i`.
* `sum_tuple_prod_cast`: the Chinese remainder theorem for `j`-tuples,
  `∑_{z ∈ (ℤ/M)^j} ∏_k f_k(z mod a_k) = ∏_k ∑_{t ∈ (ℤ/a_k)^j} f_k(t)`.
* `sum_box_residues`: a sum over a product box of a function of the residues modulo `Q` is the sum
  over the residue tuples weighted by the product of the class counts.
* `abs_box_sum_sub_le`: hence it is `(∏ c_i) ∑_z G(z)` up to the relative error `(1 + ε)^j - 1`.
* `localTest`: the test of a pattern at one prime; `abs_pattern_count_sub_le`: the count.

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

noncomputable section

/-! ### Products of nearly equal factors -/

/-- `|∏ x_i - ∏ c_i| ≤ ((1 + ε)^n - 1) ∏ c_i` when `c_i ≥ 0` and `|x_i - c_i| ≤ ε c_i`. -/
theorem abs_prod_sub_prod_le_pow {ι : Type*} [DecidableEq ι] (s : Finset ι) (x c : ι → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hc : ∀ i ∈ s, 0 ≤ c i) (h : ∀ i ∈ s, |x i - c i| ≤ ε * c i) :
    |∏ i ∈ s, x i - ∏ i ∈ s, c i| ≤ ((1 + ε) ^ s.card - 1) * ∏ i ∈ s, c i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hc' : ∀ i ∈ s, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have h' : ∀ i ∈ s, |x i - c i| ≤ ε * c i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ih' := ih hc' h'
    have hca := hc a (Finset.mem_insert_self a s)
    have hxa := h a (Finset.mem_insert_self a s)
    have hPc : 0 ≤ ∏ i ∈ s, c i := Finset.prod_nonneg hc'
    have hPx : |∏ i ∈ s, x i| ≤ (1 + ε) ^ s.card * ∏ i ∈ s, c i := by
      have h1 := abs_add_le (∏ i ∈ s, x i - ∏ i ∈ s, c i) (∏ i ∈ s, c i)
      rw [sub_add_cancel, abs_of_nonneg hPc] at h1
      linarith
    have hsplit : x a * ∏ i ∈ s, x i - c a * ∏ i ∈ s, c i =
        (x a - c a) * ∏ i ∈ s, x i + c a * (∏ i ∈ s, x i - ∏ i ∈ s, c i) := by ring
    have h1 : |x a - c a| * |∏ i ∈ s, x i| ≤ ε * c a * ((1 + ε) ^ s.card * ∏ i ∈ s, c i) :=
      mul_le_mul hxa hPx (abs_nonneg _) (mul_nonneg hε hca)
    have h2 : c a * |∏ i ∈ s, x i - ∏ i ∈ s, c i| ≤
        c a * (((1 + ε) ^ s.card - 1) * ∏ i ∈ s, c i) := mul_le_mul_of_nonneg_left ih' hca
    have e : ε * c a * ((1 + ε) ^ s.card * ∏ i ∈ s, c i) +
        c a * (((1 + ε) ^ s.card - 1) * ∏ i ∈ s, c i) =
        ((1 + ε) ^ (s.card + 1) - 1) * (c a * ∏ i ∈ s, c i) := by ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hca]
    linarith

/-! ### The Chinese remainder theorem for tuples -/

/-- **CRT for tuples**: for pairwise coprime moduli `a_k` with product `M`,
`∑_{z ∈ (ℤ/M)^j} ∏_k f_k(z mod a_k) = ∏_k ∑_{t ∈ (ℤ/a_k)^j} f_k(t)`. -/
theorem sum_tuple_prod_cast {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℕ)
    [∀ k, NeZero (a k)] (hcop : Pairwise (Function.onFun Nat.Coprime a)) (j : ℕ)
    (f : (k : κ) → (Fin j → ZMod (a k)) → ℝ) (M : ℕ) [NeZero M] (hM : M = ∏ k, a k) :
    ∑ z : Fin j → ZMod M, ∏ k, f k (fun i => ZMod.cast (z i)) =
      ∏ k, ∑ t : Fin j → ZMod (a k), f k t := by
  subst hM
  rw [Fintype.prod_sum]
  have e := Equiv.sum_comp
    (((Equiv.refl (Fin j)).arrowCongr (ZMod.prodEquivPi a hcop).toEquiv).trans
      (Equiv.piComm fun (_ : Fin j) (k : κ) => ZMod (a k)))
    (fun x : (k : κ) → Fin j → ZMod (a k) => ∏ k, f k (x k))
  rw [← e]
  refine Finset.sum_congr rfl fun z _ => Finset.prod_congr rfl fun k _ => ?_
  congr 1
  funext i
  show ZMod.cast (z i) = (ZMod.prodEquivPi a hcop) (z i) k
  rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply]

/-! ### A product box and the residues of its coordinates -/

/-- A sum over a product box of a function of the residues modulo `Q` is the sum over the residue
tuples `z`, weighted by `∏_i #{n ∈ R_i : n ≡ z_i (mod Q)}`. -/
theorem sum_box_residues {j : ℕ} (Q : ℕ) [NeZero Q] (R : Fin j → Finset ℕ)
    (G : (Fin j → ZMod Q) → ℝ) :
    ∑ m ∈ Fintype.piFinset R, G (fun i => ((m i : ℕ) : ZMod Q)) =
      ∑ z : Fin j → ZMod Q,
        (∏ i, (((R i).filter fun n => n ≡ (z i).val [MOD Q]).card : ℝ)) * G z := by
  refine (Finset.sum_fiberwise' (Fintype.piFinset R)
    (fun m : Fin j → ℕ => fun i => ((m i : ℕ) : ZMod Q)) G).symm.trans ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  have hfib : (Fintype.piFinset R).filter
      (fun m : Fin j → ℕ => (fun i => ((m i : ℕ) : ZMod Q)) = z) =
      Fintype.piFinset fun i => (R i).filter fun n => n ≡ (z i).val [MOD Q] := by
    ext m
    rw [Finset.mem_filter, Fintype.mem_piFinset, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ i
      refine Finset.mem_filter.mpr ⟨h1 i, ?_⟩
      have h3 : ((m i : ℕ) : ZMod Q) = z i := congrFun h2 i
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
      exact h3
    · intro h
      refine ⟨fun i => (Finset.mem_filter.mp (h i)).1, funext fun i => ?_⟩
      have h3 := (Finset.mem_filter.mp (h i)).2
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at h3
      exact h3
  rw [Finset.sum_const, nsmul_eq_mul, hfib, Fintype.card_piFinset, Nat.cast_prod]

/-- **The count on a product box**: if every class modulo `Q` contains `c_i (1 + θ ε)` elements of
`R_i`, then `∑_{m ∈ ∏ R_i} G(m mod Q) = (∏ c_i) ∑_z G(z)` up to the relative error
`(1 + ε)^j - 1`, for `G ≥ 0`. -/
theorem abs_box_sum_sub_le {j : ℕ} (Q : ℕ) [NeZero Q] (R : Fin j → Finset ℕ) (c : Fin j → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hc : ∀ i, 0 ≤ c i)
    (heq : ∀ i (b : ℕ), |(((R i).filter fun n => n ≡ b [MOD Q]).card : ℝ) - c i| ≤ ε * c i)
    (G : (Fin j → ZMod Q) → ℝ) (hG : ∀ z, 0 ≤ G z) :
    |∑ m ∈ Fintype.piFinset R, G (fun i => ((m i : ℕ) : ZMod Q)) - (∏ i, c i) * ∑ z, G z| ≤
      ((1 + ε) ^ j - 1) * ((∏ i, c i) * ∑ z, G z) := by
  have hterm : ∀ z : Fin j → ZMod Q,
      |(∏ i, (((R i).filter fun n => n ≡ (z i).val [MOD Q]).card : ℝ)) * G z -
          (∏ i, c i) * G z| ≤ ((1 + ε) ^ j - 1) * ((∏ i, c i) * G z) := by
    intro z
    have h := abs_prod_sub_prod_le_pow Finset.univ
      (fun i => (((R i).filter fun n => n ≡ (z i).val [MOD Q]).card : ℝ)) c hε
      (fun i _ => hc i) (fun i _ => heq i (z i).val)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [← sub_mul, abs_mul, abs_of_nonneg (hG z)]
    calc |∏ i, (((R i).filter fun n => n ≡ (z i).val [MOD Q]).card : ℝ) - ∏ i, c i| * G z
        ≤ ((1 + ε) ^ j - 1) * (∏ i, c i) * G z := mul_le_mul_of_nonneg_right h (hG z)
      _ = ((1 + ε) ^ j - 1) * ((∏ i, c i) * G z) := by ring
  rw [sum_box_residues, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun z _ => hterm z).trans (le_of_eq ?_)
  rw [Finset.mul_sum]

/-! ### The test of a pattern at one prime -/

/-- The test of the pattern `(A, A')` at the prime `p`, as a function of the residues of the `j`
coordinates: `1_{∏ t_i = 1}` if `p ∈ A`, `1_{∏ t_i = 0}` otherwise. -/
def localTest (A : Finset ℕ) (j p : ℕ) (t : Fin j → ZMod p) : ℝ :=
  if p ∈ A then (if ∏ i, t i = 1 then 1 else 0) else (if ∏ i, t i = 0 then 1 else 0)

theorem localTest_nonneg (A : Finset ℕ) (j p : ℕ) (t : Fin j → ZMod p) :
    0 ≤ localTest A j p t := by
  unfold localTest
  split_ifs <;> norm_num

/-- At the residues of a tuple `m` with `∏ m_i ≥ 1`, the test is `1_{p ∣ ∏ m_i - 1}` or
`1_{p ∣ ∏ m_i}`. -/
theorem localTest_natCast (A : Finset ℕ) {j : ℕ} (p : ℕ) (m : Fin j → ℕ)
    (hm : 1 ≤ ∏ i, m i) :
    localTest A j p (fun i => ((m i : ℕ) : ZMod p)) =
      if p ∈ A then indU p (∏ i, m i - 1) else indV p (∏ i, m i - 1) := by
  obtain ⟨u, hu⟩ : ∃ u : ℕ, ∏ i, m i = u + 1 := ⟨∏ i, m i - 1, by omega⟩
  have hprod : ∏ i, ((m i : ℕ) : ZMod p) = ((u : ℕ) : ZMod p) + 1 := by
    rw [← Nat.cast_prod, hu, Nat.cast_add, Nat.cast_one]
  have hu' : ∏ i, m i - 1 = u := by omega
  show (if p ∈ A then (if ∏ i, ((m i : ℕ) : ZMod p) = 1 then (1 : ℝ) else 0)
      else (if ∏ i, ((m i : ℕ) : ZMod p) = 0 then (1 : ℝ) else 0)) =
    if p ∈ A then indU p (∏ i, m i - 1) else indV p (∏ i, m i - 1)
  rw [hprod, hu']
  unfold indU indV
  by_cases hpA : p ∈ A
  · rw [if_pos hpA, if_pos hpA]
    by_cases hd : p ∣ u
    · have h0 : ((u : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff u p).mpr hd
      have h1 : ((u : ℕ) : ZMod p) + 1 = 1 := by rw [h0, zero_add]
      rw [if_pos hd, if_pos h1]
    · have hne : ¬ (((u : ℕ) : ZMod p) + 1 = 1) := fun h =>
        hd ((ZMod.natCast_eq_zero_iff u p).mp (add_right_cancel (h.trans (zero_add 1).symm)))
      rw [if_neg hd, if_neg hne]
  · rw [if_neg hpA, if_neg hpA]
    have hiff : ((u : ℕ) : ZMod p) + 1 = 0 ↔ p ∣ u + 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
    by_cases hd : p ∣ u + 1
    · rw [if_pos hd, if_pos (hiff.mpr hd)]
    · rw [if_neg hd, if_neg fun h => hd (hiff.mp h)]

/-- The number of residue tuples passing the test at a prime `p` is `p^j a_p` or `p^j b_p`. -/
theorem sum_localTest (A : Finset ℕ) {j : ℕ} (hj : 1 ≤ j) (p : ℕ) [NeZero p] (hp : p.Prime) :
    ∑ t : Fin j → ZMod p, localTest A j p t =
      (p : ℝ) ^ j * (if p ∈ A then alphaU j p else alphaV j p) := by
  unfold localTest
  by_cases hpA : p ∈ A
  · rw [if_pos hpA, ← sum_ind_prod_eq_one p hp hj]
    exact Finset.sum_congr rfl fun t _ => if_pos hpA
  · rw [if_neg hpA, ← sum_ind_prod_eq_zero p hp j]
    exact Finset.sum_congr rfl fun t _ => if_neg hpA

/-! ### The count of a pattern -/

/-- **The count of a pattern on a product box** (`[P-07:0409–0449]`). -/
theorem abs_pattern_count_sub_le {j : ℕ} (hj : 1 ≤ j) {A A' : Finset ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hA' : ∀ p ∈ A', p.Prime) (hdisj : Disjoint A A')
    (R : Fin j → Finset ℕ) (hR : ∀ i, ∀ n ∈ R i, 1 ≤ n) (C : Fin j → ℝ) (hC : ∀ i, 0 ≤ C i)
    {ε : ℝ} (hε : 0 ≤ ε)
    (heq : ∀ i (b : ℕ), |(((R i).filter fun n => n ≡ b [MOD ∏ p ∈ A ∪ A', p]).card : ℝ) -
        C i / ((∏ p ∈ A ∪ A', p : ℕ) : ℝ)| ≤ ε * (C i / ((∏ p ∈ A ∪ A', p : ℕ) : ℝ))) :
    |∑ m ∈ Fintype.piFinset R, hit A A' (∏ i, m i - 1) - (∏ i, C i) * dens j A A'| ≤
      ((1 + ε) ^ j - 1) * ((∏ i, C i) * dens j A A') := by
  obtain ⟨D, hDdef⟩ : ∃ D : Finset ℕ, D = A ∪ A' := ⟨_, rfl⟩
  rw [← hDdef] at heq
  have hD : ∀ p ∈ D, p.Prime := by
    intro p hp
    rw [hDdef] at hp
    exact (Finset.mem_union.mp hp).elim (hA p) (hA' p)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = ∏ p ∈ D, p := ⟨_, rfl⟩
  rw [← hQdef] at heq
  have hQ0 : Q ≠ 0 := by
    rw [hQdef]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => (hD p hp).ne_zero
  have hQR : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ0)
  have : NeZero Q := ⟨hQ0⟩
  have hne : ∀ k : {p // p ∈ D}, NeZero (k : ℕ) := fun k => ⟨(hD k k.2).ne_zero⟩
  have hcop : Pairwise (Function.onFun Nat.Coprime fun k : {p // p ∈ D} => (k : ℕ)) := by
    intro k k' hkk
    exact (Nat.coprime_primes (hD k k.2) (hD k' k'.2)).mpr fun h => hkk (Subtype.ext h)
  have hQprod : Q = ∏ k : {p // p ∈ D}, (k : ℕ) := by
    rw [hQdef]
    exact (Finset.prod_coe_sort D fun p => p).symm
  -- the test function on the residues modulo `Q`
  obtain ⟨G, hG⟩ : ∃ G : (Fin j → ZMod Q) → ℝ, ∀ z, G z =
      ∏ k : {p // p ∈ D}, localTest A j (k : ℕ) (fun i => ZMod.cast (z i)) :=
    ⟨_, fun _ => rfl⟩
  have hG0 : ∀ z, 0 ≤ G z := fun z => by
    rw [hG]
    exact Finset.prod_nonneg fun k _ => localTest_nonneg _ _ _ _
  -- step 1: on the box the test function is the pattern indicator
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin j → ℕ) → ℕ → ℝ, ∀ m p, φ m p =
      if p ∈ A then indU p (∏ i, m i - 1) else indV p (∏ i, m i - 1) := ⟨_, fun _ _ => rfl⟩
  have hstep1 : ∀ m ∈ Fintype.piFinset R,
      G (fun i => ((m i : ℕ) : ZMod Q)) = hit A A' (∏ i, m i - 1) := by
    intro m hm
    have hm1 : 1 ≤ ∏ i, m i :=
      Nat.succ_le_of_lt (Finset.prod_pos fun i _ =>
        Nat.lt_of_lt_of_le Nat.zero_lt_one (hR i (m i) (Fintype.mem_piFinset.mp hm i)))
    have hk : ∀ k : {p // p ∈ D},
        localTest A j (k : ℕ) (fun i => ZMod.cast (((m i : ℕ) : ZMod Q))) = φ m (k : ℕ) := by
      intro k
      have hdvd : (k : ℕ) ∣ Q := by
        rw [hQdef]
        exact Finset.dvd_prod_of_mem (fun p => p) k.2
      have e : (fun i => (ZMod.cast (((m i : ℕ) : ZMod Q)) : ZMod (k : ℕ))) =
          fun i => ((m i : ℕ) : ZMod (k : ℕ)) :=
        funext fun i => ZMod.cast_natCast hdvd (m i)
      rw [e, hφ]
      exact localTest_natCast A (k : ℕ) m hm1
    have e1 : ∏ k : {p // p ∈ D}, φ m (k : ℕ) = ∏ p ∈ D, φ m p := Finset.prod_coe_sort D (φ m)
    have e2 : ∏ p ∈ A, φ m p = ∏ p ∈ A, indU p (∏ i, m i - 1) :=
      Finset.prod_congr rfl fun p hp => by
        rw [hφ]
        exact if_pos hp
    have e3 : ∏ p ∈ A', φ m p = ∏ p ∈ A', indV p (∏ i, m i - 1) :=
      Finset.prod_congr rfl fun p hp => by
        rw [hφ]
        exact if_neg fun hpA => (Finset.disjoint_left.mp hdisj hpA) hp
    rw [hG, Finset.prod_congr rfl fun k _ => hk k, e1, hDdef, Finset.prod_union hdisj, e2, e3,
      hit_eq_prod]
  -- step 2: the number of residue tuples passing the test
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → ℝ, ∀ p, ψ p =
      (p : ℝ) ^ j * (if p ∈ A then alphaU j p else alphaV j p) := ⟨_, fun _ => rfl⟩
  have hstep2 : ∑ z, G z = (Q : ℝ) ^ j * dens j A A' := by
    have e0 : ∑ z, G z = ∑ z : Fin j → ZMod Q,
        ∏ k : {p // p ∈ D}, localTest A j (k : ℕ) (fun i => ZMod.cast (z i)) :=
      Finset.sum_congr rfl fun z _ => hG z
    have e1 := sum_tuple_prod_cast (fun k : {p // p ∈ D} => (k : ℕ)) hcop j
      (fun k => localTest A j (k : ℕ)) Q hQprod
    have e2 : ∏ k : {p // p ∈ D}, ∑ t : Fin j → ZMod (k : ℕ), localTest A j (k : ℕ) t =
        ∏ k : {p // p ∈ D}, ψ (k : ℕ) :=
      Finset.prod_congr rfl fun k _ => by
        rw [hψ]
        exact sum_localTest A hj (k : ℕ) (hD k k.2)
    have e3 : ∏ k : {p // p ∈ D}, ψ (k : ℕ) = ∏ p ∈ D, ψ p := Finset.prod_coe_sort D ψ
    have e4 : ∏ p ∈ D, ψ p =
        (∏ p ∈ D, (p : ℝ) ^ j) * ∏ p ∈ D, (if p ∈ A then alphaU j p else alphaV j p) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p _ => hψ p
    have e5 : ∏ p ∈ D, (p : ℝ) ^ j = (Q : ℝ) ^ j := by
      rw [Finset.prod_pow, hQdef, Nat.cast_prod]
    have e6 : ∏ p ∈ D, (if p ∈ A then alphaU j p else alphaV j p) = dens j A A' := by
      rw [hDdef, Finset.prod_union hdisj, dens_of hdisj]
      congr 1
      · exact Finset.prod_congr rfl fun p hp => if_pos hp
      · exact Finset.prod_congr rfl fun p hp =>
          if_neg fun hpA => (Finset.disjoint_left.mp hdisj hpA) hp
    rw [e0, e1, e2, e3, e4, e5, e6]
  -- step 3: the count on the box
  have hmain := abs_box_sum_sub_le Q R (fun i => C i / (Q : ℝ)) hε
    (fun i => div_nonneg (hC i) hQpos.le) heq G hG0
  have hprodC : (∏ i, C i / (Q : ℝ)) * ∑ z, G z = (∏ i, C i) * dens j A A' := by
    rw [hstep2, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  rw [hprodC, Finset.sum_congr rfl hstep1] at hmain
  exact hmain

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin
