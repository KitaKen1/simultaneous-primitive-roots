module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements

/-!
# The centered core is invariant under the active primes

`coreInvariance : CoreInvariance d` (`[P-06:0082–0084]`): "`F_x(pn) = F_x(n)` for every active
prime `p`: the active groups are disjoint both from the inert bands and from the long-prime
slots."

* Exact part. For a set `T` of primes and a prime `p ∉ T`, `ω_T(pn) = ω_T(n)`
  (`primeHits_mul_of_notMem`), hence the mark factors and `𝒲` are unchanged
  (`markedWeight_mul_of_notMem`); for slots of primes not containing `p`, a product `ℓ_1 ⋯ ℓ_d` of
  slot primes is coprime to `p`, so it divides `pn` if and only if it divides `n`
  (`slotCount_mul_of_notMem`).
* Disjointness for large `x`. With `L = log x`: a band prime is at most `exp(2 L^a)` with
  `a < 1/5`, an active prime lies in `[exp(L^{0.27}), exp(L^{0.46})]`, a slot prime is at least
  `x^ε = exp(ε L)`. So it suffices that `2 L^{1/5} ≤ L^{0.27}` (`two_mul_rpow_lt`, for
  `L ≥ 2^{15}`) and `L^{0.46} < ε L` (`rpow_lt_mul`, for `L ≥ 1`, `ε² L > 1`). The threshold is
  `x₀ = exp(2^{15} + ε^{-2} + 1)`; it depends on `ε` only.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

/-! ### The exact part -/

/-- `ω_T(pn) = ω_T(n)` for a set `T` of primes and a prime `p ∉ T`. -/
theorem primeHits_mul_of_notMem {T : Finset ℕ} (hT : ∀ ℓ ∈ T, ℓ.Prime) {p : ℕ} (hp : p.Prime)
    (hpT : p ∉ T) (n : ℕ) : primeHits T (p * n) = primeHits T n := by
  unfold primeHits
  refine congrArg Finset.card (Finset.filter_congr fun ℓ hℓ => ?_)
  constructor
  · intro h
    rcases (hT ℓ hℓ).dvd_mul.mp h with h1 | h1
    · exfalso
      rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
      · exact (hT ℓ hℓ).ne_one h2
      · apply hpT
        rw [← h2]
        exact hℓ
    · exact h1
  · intro h
    exact Dvd.dvd.mul_left h p

/-- One mark factor is unchanged by a prime outside its band. -/
theorem markFactor_mul_of_notMem {T : Finset ℕ} (hT : ∀ ℓ ∈ T, ℓ.Prime) {p : ℕ} (hp : p.Prime)
    (hpT : p ∉ T) (q : ℝ) (n : ℕ) : markFactor q T (p * n) = markFactor q T n := by
  unfold markFactor
  rw [primeHits_mul_of_notMem hT hp hpT n]

/-- `𝒲(pn) = 𝒲(n)` for a prime `p` outside all the bands. -/
theorem markedWeight_mul_of_notMem {K : ℕ} {𝔞 : MarkingArray K} {x : ℝ} {p : ℕ} (hp : p.Prime)
    (hband : ∀ i, p ∉ bandPrimes (𝔞.exponent i) x) (q : ℝ) (n : ℕ) :
    markedWeight q 𝔞 x (p * n) = markedWeight q 𝔞 x n := by
  unfold markedWeight
  exact Finset.prod_congr rfl fun i _ =>
    markFactor_mul_of_notMem (fun ℓ hℓ => (mem_bandPrimes.mp hℓ).1) hp (hband i) q n

/-- `f_x(pn) = f_x(n)` for a prime `p` outside all the slots. -/
theorem slotCount_mul_of_notMem {d : ℕ} {S : Fin d → Finset ℕ} (hS : ∀ i, ∀ ℓ ∈ S i, ℓ.Prime)
    {p : ℕ} (hp : p.Prime) (hpS : ∀ i, p ∉ S i) (n : ℕ) :
    slotCount S (p * n) = slotCount S n := by
  unfold slotCount slotTuples
  refine congrArg Finset.card (Finset.filter_congr fun 𝔩 h𝔩 => ?_)
  have hmem : ∀ i, 𝔩 i ∈ S i := Fintype.mem_piFinset.mp (Finset.mem_filter.mp h𝔩).1
  have hcop : Nat.Coprime (∏ i, 𝔩 i) p :=
    Nat.Coprime.prod_left fun i _ =>
      (Nat.coprime_primes (hS i _ (hmem i)) hp).mpr fun e => hpS i (by
        rw [← e]
        exact hmem i)
  constructor
  · intro h
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop h
  · intro h
    exact Dvd.dvd.mul_left h p

/-! ### The two inequalities between powers of `L` -/

/-- `2 L^a < L^{0.27}` for `a < 1/5` and `L ≥ 2^{15}`: `L^{0.27} = L^{1/5} L^{0.07}` and
`L^{0.07} ≥ 2^{1.05} ≥ 2`. -/
theorem two_mul_rpow_lt {L : ℝ} (hL : (2 : ℝ) ^ (15 : ℝ) ≤ L) {a : ℝ} (ha : a < 1 / 5) :
    2 * L ^ a < L ^ (0.27 : ℝ) := by
  have h2 : (1 : ℝ) < (2 : ℝ) ^ (15 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hL1 : 1 < L := lt_of_lt_of_le h2 hL
  have hL0 : 0 < L := lt_trans one_pos hL1
  have hT : (2 : ℝ) ≤ L ^ (0.07 : ℝ) := by
    have h3 : ((2 : ℝ) ^ (15 : ℝ)) ^ (0.07 : ℝ) ≤ L ^ (0.07 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hL (by norm_num)
    have h4 : ((2 : ℝ) ^ (15 : ℝ)) ^ (0.07 : ℝ) = (2 : ℝ) ^ ((15 : ℝ) * (0.07 : ℝ)) :=
      (Real.rpow_mul (by norm_num) _ _).symm
    have h5 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ ((15 : ℝ) * (0.07 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_one] at h5
    rw [h4] at h3
    exact le_trans h5 h3
  have ha' : L ^ a < L ^ ((1 : ℝ) / 5) := Real.rpow_lt_rpow_of_exponent_lt hL1 ha
  have hsplit : L ^ (0.27 : ℝ) = L ^ ((1 : ℝ) / 5) * L ^ (0.07 : ℝ) := by
    rw [← Real.rpow_add hL0]
    congr 1
    norm_num
  have hpos : 0 < L ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hL0 _
  have h6 : L ^ ((1 : ℝ) / 5) * 2 ≤ L ^ ((1 : ℝ) / 5) * L ^ (0.07 : ℝ) :=
    mul_le_mul_of_nonneg_left hT hpos.le
  rw [hsplit]
  linarith

/-- `L^{0.46} < ε L` for `L ≥ 1` and `ε² L > 1`: `L^{0.46} ≤ L^{1/2}` and `ε L^{1/2} > 1`. -/
theorem rpow_lt_mul {ε L : ℝ} (hε : 0 < ε) (hL : 1 ≤ L) (hLε : 1 < ε ^ 2 * L) :
    L ^ (0.46 : ℝ) < ε * L := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hs0 : 0 < L ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hL0 _
  have hss : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = L := by
    have e : (1 : ℝ) / 2 + (1 : ℝ) / 2 = 1 := by norm_num
    rw [← Real.rpow_add hL0, e, Real.rpow_one]
  have h46 : L ^ (0.46 : ℝ) ≤ L ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hεs : 1 < ε * L ^ ((1 : ℝ) / 2) := by
    by_contra hcon
    have hcon' : ε * L ^ ((1 : ℝ) / 2) ≤ 1 := not_lt.mp hcon
    have h1 : ε * L ^ ((1 : ℝ) / 2) * (ε * L ^ ((1 : ℝ) / 2)) ≤ 1 * 1 :=
      mul_le_mul hcon' hcon' (mul_nonneg hε.le hs0.le) zero_le_one
    have h2 : ε * L ^ ((1 : ℝ) / 2) * (ε * L ^ ((1 : ℝ) / 2)) =
        ε ^ 2 * (L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) := by ring
    rw [h2, hss] at h1
    linarith
  have h3 : 1 * L ^ ((1 : ℝ) / 2) < ε * L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) :=
    mul_lt_mul_of_pos_right hεs hs0
  rw [one_mul, mul_assoc, hss] at h3
  exact lt_of_le_of_lt h46 h3

/-! ### The statement -/

/-- **`F_x(pn) = F_x(n)` for every active prime `p`**, for `x ≥ exp(2^{15} + ε^{-2} + 1)`. -/
theorem coreInvariance (d : ℕ) : CoreInvariance d := by
  intro ε hε
  refine ⟨Real.exp ((2 : ℝ) ^ (15 : ℝ) + (ε ^ 2)⁻¹ + 1),
    fun x hx q K 𝔞 P 𝔊 h S hS p hp n => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hLge : (2 : ℝ) ^ (15 : ℝ) + (ε ^ 2)⁻¹ + 1 ≤ Real.log x := by
    have h1 := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h1
  have hT0 : (0 : ℝ) < (2 : ℝ) ^ (15 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hinv : (0 : ℝ) < (ε ^ 2)⁻¹ := inv_pos.mpr hε2
  have hLT : (2 : ℝ) ^ (15 : ℝ) ≤ Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hLε : 1 < ε ^ 2 * Real.log x := by
    have h1 : ε ^ 2 * (ε ^ 2)⁻¹ < ε ^ 2 * Real.log x :=
      mul_lt_mul_of_pos_left (by linarith) hε2
    rwa [mul_inv_cancel₀ hε2.ne'] at h1
  -- the active prime and its range
  have hp' : p ∈ Finset.univ.biUnion 𝔊.group := hp
  obtain ⟨g, -, hpg⟩ := Finset.mem_biUnion.mp hp'
  have hprime : p.Prime := h.prime g p hpg
  have e1 : Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ Real.exp (Real.log x ^ (0.39 : ℝ)) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have e2 : Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hrange : Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) := by
    cases g with
    | inl i =>
      obtain ⟨h1, h2⟩ := h.small_range i p hpg
      exact ⟨h1, le_trans h2 e2⟩
    | inr j =>
      obtain ⟨h1, h2⟩ := h.big_range j p hpg
      exact ⟨le_trans e1 h1, h2⟩
  -- disjointness from the bands
  have hband : ∀ i : Fin K, p ∉ bandPrimes (𝔞.exponent i) x := by
    intro i hmem
    have h1 : (p : ℝ) ≤ Real.exp (2 * Real.log x ^ 𝔞.exponent i) := (mem_bandPrimes.mp hmem).2.2
    have h2 : Real.log x ^ (0.27 : ℝ) ≤ 2 * Real.log x ^ 𝔞.exponent i :=
      Real.exp_le_exp.mp (le_trans hrange.1 h1)
    have h3 := two_mul_rpow_lt hLT (𝔞.lt_fifth i)
    linarith
  -- disjointness from the slots
  have hslot : ∀ i : Fin d, p ∉ S i := by
    intro i hmem
    have h1 : x ^ ε ≤ (p : ℝ) := hS.lower i p hmem
    rw [Real.rpow_def_of_pos hx0] at h1
    have h2 : Real.log x * ε ≤ Real.log x ^ (0.46 : ℝ) :=
      Real.exp_le_exp.mp (le_trans h1 hrange.2)
    have h3 := rpow_lt_mul hε hL1 hLε
    linarith
  unfold centeredCore
  rw [slotCount_mul_of_notMem hS.prime hprime hslot n,
    markedWeight_mul_of_notMem hprime hband q n]

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
