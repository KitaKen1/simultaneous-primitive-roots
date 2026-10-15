module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExtractSmall

/-!
# The extracted coefficients are exact away from squares

`extractedCoefficient d : ExtractSmallIdentity → ExtractedCoefficientIdentity d`
(`[P-06:0692–0715]`): if the groups and the slots consist of primes, the groups are pairwise
disjoint, the slots are disjoint from all marked primes and the bands from the active groups,
`t_{g_s} = 1` and the test depends only on big marks, then for every `w ≥ 1` not divisible by the
square of a prime of `𝒫_{g_s}` or of a slot,

`𝒰(w) = 𝒰_tuple(w) - C_x 𝒰_const(w)`.

With `G = 𝒫_{g_s}`, `V = V_{g_s}` and `W' = W_{𝐭 - 𝐞_{g_s}}^𝐛`:

* (cor:extract-small): `W_𝐭^𝐛(w) = V⁻¹ ∑_{p ∈ G, p ∣ w} W'(w/p)`.
* A prime `p ∈ G` lies in no band, so `𝒲(w/p) = 𝒲(w)` (`markedWeight_div_of_notMem`): the constant
  part is `V⁻¹ ∑_p 𝒲(w/p) W'(w/p) = 𝒲(w) W_𝐭^𝐛(w)`.
* A slot prime `l` is not a marked prime, so `𝒲 W'` is the same at `n/l` and at `n`
  (`hMarks_div_of_notMem`), and "after allowing repeated slots the coefficient on `u` is exactly
  (cor:u-coefficient)": `∑_{l ∈ S_1, l ∣ n} #{(l_2, …) : l_2 ⋯ ∣ n/l} = #{(l_1, l_2, …) :
  l_1 l_2 ⋯ ∣ n}` (`sum_slotCountRep_tail`).
* The count with repeated slot primes is the same at `w/p` and at `w`
  (`slotCountRep_div_of_notMem`), and it is `f_x(w)` when no square of a slot prime divides `w`
  (`slotCount_eq_slotCountRep`). Hence the tuple part is `f_x(w) 𝒲(w) W_𝐭^𝐛(w)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### Removing a prime outside the marked groups -/

/-- The weight with marks removed depends on `n` only through the prime divisors of `n` in the
groups. -/
theorem partialWeight_congr (𝔊 : ActiveGroups) (q₀ : ℝ) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (U : Finset 𝔊.Index) {n n' : ℕ}
    (h : ∀ g : 𝔊.Index,
      (𝔊.group g).filter (fun p => p ∣ n) = (𝔊.group g).filter (fun p => p ∣ n')) :
    partialWeight 𝔊 q₀ t test U n = partialWeight 𝔊 q₀ t test U n' := by
  have hhits : 𝔊.totalHits n = 𝔊.totalHits n' := by
    unfold ActiveGroups.totalHits primeHits
    exact Finset.sum_congr rfl fun g _ => by rw [h g]
  have hlists : partialLists 𝔊 t U n = partialLists 𝔊 t U n' := by
    have hfun : (fun g : 𝔊.Index =>
        if g ∈ U then ({fun _ => 0} : Finset (Fin (t g) → ℕ))
        else (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun q => q ∣ n).filter
          fun 𝔮 => Function.Injective 𝔮) =
        fun g : 𝔊.Index =>
        if g ∈ U then ({fun _ => 0} : Finset (Fin (t g) → ℕ))
        else (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun q => q ∣ n').filter
          fun 𝔮 => Function.Injective 𝔮 := by
      funext g
      rw [h g]
    exact congrArg (fun F : (g : 𝔊.Index) → Finset (Fin (t g) → ℕ) => Fintype.piFinset F) hfun
  unfold partialWeight
  rw [hhits, hlists]

/-- `𝒲(n / p) = 𝒲(n)` for a prime `p ∣ n` that lies in no band. -/
theorem markedWeight_div_of_notMem (q : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) {p n : ℕ}
    (hp : p.Prime) (hband : ∀ i : Fin K, p ∉ bandPrimes (𝔞.exponent i) x) (hpn : p ∣ n) :
    markedWeight q 𝔞 x (n / p) = markedWeight q 𝔞 x n := by
  unfold markedWeight markFactor
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [primeHits_div_of_notMem (fun p' hp' => (mem_bandPrimes.mp hp').1) hp (hband i) hpn]

/-- `H_marks` (with marks removed) is the same at `n / l` and at `n` for a prime `l ∣ n` that is
not a marked prime (`[P-06:0646–0647]`: "All long primes lie outside the marked groups, so
`H_marks(ln) = H_marks(n)`"). -/
theorem hMarks_div_of_notMem (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups)
    (hprime : ∀ g : 𝔊.Index, ∀ p ∈ 𝔊.group g, p.Prime) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (U : Finset 𝔊.Index) {l n : ℕ} (hl : l.Prime)
    (hmark : l ∉ markPrimes 𝔞 x 𝔊) (hln : l ∣ n) :
    hMarks q q₀ 𝔞 x 𝔊 t test U (n / l) = hMarks q q₀ 𝔞 x 𝔊 t test U n := by
  have hmark' : l ∉ (Finset.univ.biUnion fun i : Fin K => bandPrimes (𝔞.exponent i) x) ∪
      Finset.univ.biUnion 𝔊.group := hmark
  have hband : ∀ i : Fin K, l ∉ bandPrimes (𝔞.exponent i) x := fun i hi =>
    hmark' (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩))
  have hgroup : ∀ g : 𝔊.Index, l ∉ 𝔊.group g := fun g hg =>
    hmark' (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hg⟩))
  unfold hMarks
  rw [markedWeight_div_of_notMem q 𝔞 x hl hband hln,
    partialWeight_congr 𝔊 q₀ t test U
      (fun g => filter_dvd_div_of_notMem (hprime g) hl (hgroup g) hln)]

/-! ### The slot statistic with repeated primes -/

/-- If no square of a slot prime divides `u`, a tuple of slot primes whose product divides `u` has
distinct entries: `f_x(u)` is the count with repeated slot primes allowed. -/
theorem slotCount_eq_slotCountRep {d : ℕ} (S : Fin d → Finset ℕ) {u : ℕ}
    (hsq : ∀ i, ∀ l ∈ S i, ¬ l ^ 2 ∣ u) : slotCount S u = slotCountRep S u := by
  unfold slotCount slotCountRep slotTuples
  congr 1
  ext 𝔩
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    intro i j hij
    by_contra hne
    have hdvd : ∏ k ∈ ({i, j} : Finset (Fin d)), 𝔩 k ∣ ∏ k, 𝔩 k :=
      Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
    rw [Finset.prod_pair hne, ← hij, ← pow_two] at hdvd
    exact hsq i (𝔩 i) (Fintype.mem_piFinset.mp h1 i) (hdvd.trans h2)

/-- The count with repeated slot primes is the same at `w / p` and at `w`, for a prime `p ∣ w`
that lies in no slot. -/
theorem slotCountRep_div_of_notMem {d : ℕ} {S : Fin d → Finset ℕ}
    (hS : ∀ i, ∀ l ∈ S i, l.Prime) {p w : ℕ} (hp : p.Prime) (hpS : ∀ i, p ∉ S i) (hpw : p ∣ w) :
    slotCountRep S (w / p) = slotCountRep S w := by
  unfold slotCountRep
  congr 1
  refine Finset.filter_congr fun 𝔩 h𝔩 => ?_
  have hmem : ∀ i, 𝔩 i ∈ S i := Fintype.mem_piFinset.mp h𝔩
  constructor
  · intro h
    exact h.trans (Nat.div_dvd_of_dvd hpw)
  · intro h
    have hcop : Nat.Coprime (∏ i, 𝔩 i) p := by
      refine Nat.Coprime.prod_left fun i _ => ?_
      refine (Nat.coprime_primes (hS i _ (hmem i)) hp).mpr ?_
      intro heq
      have hpi : p ∈ S i := by
        rw [← heq]
        exact hmem i
      exact hpS i hpi
    have h2 : (∏ i, 𝔩 i) ∣ p * (w / p) := by
      rw [Nat.mul_div_cancel' hpw]
      exact h
    exact hcop.dvd_of_dvd_mul_left h2

/-- The first slot prime is split off (`[P-06:0705–0711]`):
`∑_{l ∈ S_1, l ∣ n} #{(l_2, …, l_d) : l_2 ⋯ l_d ∣ n / l} = #{(l_1, …, l_d) : l_1 ⋯ l_d ∣ n}`,
repeated slot primes allowed. -/
theorem sum_slotCountRep_tail {d : ℕ} (S : Fin (d + 1) → Finset ℕ) (n : ℕ) :
    ∑ l ∈ (S 0).filter (fun l => l ∣ n), slotCountRep (tailSlots S) (n / l) =
      slotCountRep S n := by
  have hcard := Finset.card_sigma ((S 0).filter fun l => l ∣ n)
    (fun l : ℕ => (Fintype.piFinset (tailSlots S)).filter
      fun 𝔩 : Fin d → ℕ => (∏ i, 𝔩 i) ∣ n / l)
  unfold slotCountRep
  refine hcard.symm.trans ?_
  refine Finset.card_nbij'
    (fun y : (_ : ℕ) × (Fin d → ℕ) => (Fin.cons y.1 y.2 : Fin (d + 1) → ℕ))
    (fun 𝔩 : Fin (d + 1) → ℕ => (⟨𝔩 0, fun i => 𝔩 i.succ⟩ : (_ : ℕ) × (Fin d → ℕ)))
    ?_ ?_ ?_ ?_
  · -- a first prime and a tuple of the other slots give a tuple
    intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_sigma.mp (Finset.mem_coe.mp hy)
    obtain ⟨hl, hln⟩ := Finset.mem_filter.mp hy1
    obtain ⟨ht, htn⟩ := Finset.mem_filter.mp hy2
    have htail : ∀ j : Fin d, y.2 j ∈ S j.succ := Fintype.mem_piFinset.mp ht
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩)
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact hl
      · simp only [Fin.cons_succ]
        exact htail j
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact Nat.mul_dvd_of_dvd_div hln htn
  · -- a tuple gives its first prime and its tail
    intro 𝔩 h𝔩
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp h𝔩)
    have hmem : ∀ i, 𝔩 i ∈ S i := Fintype.mem_piFinset.mp h1
    rw [Fin.prod_univ_succ] at h2
    refine Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_filter.mpr ⟨hmem 0, dvd_of_mul_right_dvd h2⟩
    · exact Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr fun i => hmem i.succ, Nat.dvd_div_of_mul_dvd h2⟩
  · -- left inverse
    rintro ⟨l, 𝔩'⟩ _
    simp only [Fin.cons_zero, Fin.cons_succ]
  · -- right inverse
    intro 𝔩 _
    exact Fin.cons_self_tail 𝔩

/-! ### The identity -/

/-- **The extracted coefficients are exact away from squares** (`[P-06:0692–0715]`):
`𝒰 = 𝒰_tuple - C_x 𝒰_const` at every `w ≥ 1` not divisible by the square of a prime of the
chosen small group or of a slot. -/
theorem extractedCoefficient (d : ℕ) : ExtractSmallIdentity → ExtractedCoefficientIdentity d := by
  intro hES D x c i₀ hprime hdisj hSprime hSmark hband ht htest w hw hsqG hsqS
  -- (cor:extract-small)
  have hact : c.𝔊.activeWeight D.q₀ c.t c.test w =
      (((reciprocalMass (c.𝔊.group (Sum.inl i₀)))⁻¹ : ℝ) : ℂ) *
        primeConv (c.𝔊.group (Sum.inl i₀))
          (partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀}) w :=
    hES c.𝔊 hprime hdisj D.q₀ c.t c.test i₀ ht
      (fun 𝔭 𝔭' h => htest 𝔭 𝔭' fun j => h (Sum.inr j) Sum.inr_ne_inl) w hw hsqG
  -- a prime of the small group is in no band and in no slot
  have hfacts : ∀ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
      p.Prime ∧ p ∣ w ∧ (∀ j : Fin D.K, p ∉ bandPrimes (D.𝔞.exponent j) x) ∧
        ∀ i, p ∉ c.S i := by
    intro p hp
    obtain ⟨hpG, hpw⟩ := Finset.mem_filter.mp hp
    have hpall : p ∈ c.𝔊.allPrimes := by
      unfold ActiveGroups.allPrimes
      exact Finset.mem_biUnion.mpr ⟨Sum.inl i₀, Finset.mem_univ _, hpG⟩
    have hpmark : p ∈ markPrimes D.𝔞 x c.𝔊 := by
      unfold markPrimes
      exact Finset.mem_union_right _ hpall
    exact ⟨hprime _ p hpG, hpw, fun j => Finset.disjoint_right.mp (hband j) hpall,
      fun i => Finset.disjoint_right.mp (hSmark i) hpmark⟩
  -- the constant coefficient at `w / p`
  have hconst : ∀ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
      c.constCoeff D x i₀ (w / p) = ((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
        partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀} (w / p) := by
    intro p hp
    obtain ⟨hpp, hpw, hpband, -⟩ := hfacts p hp
    unfold EndpointConfig.constCoeff hMarks
    rw [markedWeight_div_of_notMem D.q D.𝔞 x hpp hpband hpw]
  -- the tuple coefficient summed over the first slot prime
  have hterm : ∀ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
      primeConv (c.S 0) (c.tupleCoeff D x i₀) (w / p) =
        (slotCount c.S w : ℂ) * (((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
          partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀} (w / p)) := by
    intro p hp
    obtain ⟨hpp, hpw, -, hpS⟩ := hfacts p hp
    have hl : ∀ l ∈ (c.S 0).filter (fun l => l ∣ w / p),
        c.tupleCoeff D x i₀ (w / p / l) =
          (slotCountRep (tailSlots c.S) (w / p / l) : ℂ) * c.constCoeff D x i₀ (w / p) := by
      intro l hl
      obtain ⟨hlS, hlw⟩ := Finset.mem_filter.mp hl
      have hlmark : l ∉ markPrimes D.𝔞 x c.𝔊 := Finset.disjoint_left.mp (hSmark 0) hlS
      unfold EndpointConfig.tupleCoeff EndpointConfig.constCoeff
      rw [hMarks_div_of_notMem D.q D.q₀ D.𝔞 x c.𝔊 hprime c.t c.test {Sum.inl i₀}
        (hSprime 0 l hlS) hlmark hlw]
    have hcount : slotCountRep c.S (w / p) = slotCount c.S w := by
      rw [slotCountRep_div_of_notMem hSprime hpp hpS hpw, slotCount_eq_slotCountRep c.S hsqS]
    calc primeConv (c.S 0) (c.tupleCoeff D x i₀) (w / p)
        = ∑ l ∈ (c.S 0).filter (fun l => l ∣ w / p), c.tupleCoeff D x i₀ (w / p / l) := rfl
      _ = ∑ l ∈ (c.S 0).filter (fun l => l ∣ w / p),
            (slotCountRep (tailSlots c.S) (w / p / l) : ℂ) * c.constCoeff D x i₀ (w / p) :=
          Finset.sum_congr rfl hl
      _ = ((∑ l ∈ (c.S 0).filter (fun l => l ∣ w / p),
            slotCountRep (tailSlots c.S) (w / p / l) : ℕ) : ℂ) *
              c.constCoeff D x i₀ (w / p) := by
          rw [Nat.cast_sum, Finset.sum_mul]
      _ = (slotCount c.S w : ℂ) * (((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
            partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀} (w / p)) := by
          rw [sum_slotCountRep_tail c.S (w / p), hcount, hconst p hp]
  -- the tuple part
  have hT : primeConv (c.𝔊.group (Sum.inl i₀))
        (primeConv (c.S 0) (c.tupleCoeff D x i₀)) w =
      (slotCount c.S w : ℂ) * (((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
        primeConv (c.𝔊.group (Sum.inl i₀))
          (partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀}) w) :=
    calc primeConv (c.𝔊.group (Sum.inl i₀)) (primeConv (c.S 0) (c.tupleCoeff D x i₀)) w
        = ∑ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
            primeConv (c.S 0) (c.tupleCoeff D x i₀) (w / p) := rfl
      _ = ∑ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
            (slotCount c.S w : ℂ) * (((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
              partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀} (w / p)) :=
          Finset.sum_congr rfl hterm
      _ = (slotCount c.S w : ℂ) * ∑ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
            ((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
              partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀} (w / p) :=
          (Finset.mul_sum _ _ _).symm
      _ = (slotCount c.S w : ℂ) * (((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
            ∑ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
              partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀} (w / p)) :=
          congrArg (fun z : ℂ => (slotCount c.S w : ℂ) * z) (Finset.mul_sum _ _ _).symm
      _ = (slotCount c.S w : ℂ) * (((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
            primeConv (c.𝔊.group (Sum.inl i₀))
              (partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀}) w) := rfl
  -- the constant part
  have hC : primeConv (c.𝔊.group (Sum.inl i₀)) (c.constCoeff D x i₀) w =
      ((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
        primeConv (c.𝔊.group (Sum.inl i₀))
          (partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀}) w :=
    calc primeConv (c.𝔊.group (Sum.inl i₀)) (c.constCoeff D x i₀) w
        = ∑ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
            c.constCoeff D x i₀ (w / p) := rfl
      _ = ∑ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
            ((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
              partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀} (w / p) :=
          Finset.sum_congr rfl hconst
      _ = ((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
            ∑ p ∈ (c.𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
              partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀} (w / p) :=
          (Finset.mul_sum _ _ _).symm
      _ = ((markedWeight D.q D.𝔞 x w : ℝ) : ℂ) *
            primeConv (c.𝔊.group (Sum.inl i₀))
              (partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀}) w := rfl
  -- `𝒰 - 𝒰_tuple + C_x 𝒰_const = 0`
  unfold EndpointConfig.errEndpoint EndpointConfig.endpoint EndpointConfig.tupleEndpoint
    EndpointConfig.constEndpoint EndpointConfig.smallGroup comparisonEndpoint centeredCore
  rw [hact, hT, hC]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast]
  ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
