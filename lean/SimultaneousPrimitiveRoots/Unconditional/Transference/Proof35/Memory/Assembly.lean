module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Bridge
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Scalars
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# [S] Lemma 3.7 from its intermediate statements

Source: `verification/stage7-sources/S-02.tex`, lines 316–582 (`[S-02:0316–0582]`).

`memoryIdentity_of_parts` proves `MemoryIdentity` (`Proof35/Statements.lean`) from the eight
statements of `Memory/Statements.lean`:

```
MemoryIdentity
└─ memoryIdentity_of_raw            threshold: for large x the hypotheses `RawHyp` hold
   └─ memoryIdentityRaw_of_parts    phaseSum = (∏ b_p) · distinctSum for raw families
      ├─ PhaseSkeleton (A), DistinctSkeleton (B)
      ├─ Skel.common_eq_zero_of_not_bigValid       skeletons without `BigValid` do not contribute
      └─ Skel.bigPhys_eq            bigPhys = (∏ b_p) · memSum for a skeleton with `BigValid`
         ├─ BigResidueProduct (C1), OnePrimeLifespan (C2)
         └─ Skel.memSum_eq_lifeSum  memSum = 1_inj · norm · ∏_p lifeSum p
            ├─ BornSetRecursion (M1), ChainLifespan (M4)
            └─ Skel.fut_eq_chain    backward induction over the operations
               └─ GhostStepFactor (M2), EdgeStepFactor (M3)
```

The threshold [S-02:0318–0325, 0376]: for large `x`, `N = 2R` with `R ≥ 1`, `b_p > 0` for every
big prime (`eventually_big_tilt`) and no group prime divides `k` ("for large `x` every group prime
exceeds `|k|`": `|k| ≤ L^{C₂} < exp(L^a) ≤ p`, `memId_eventually_rpow_lt_exp_rpow`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

open Filter

noncomputable section

section Core

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {D : MemData 𝒢 J ℓ N}

/-! ### Skeletons without `BigValid` -/

omit [Fintype N] in
/-- A skeleton which violates one of the conditions `BigValid` has common part zero. -/
theorem Skel.common_eq_zero_of_not_bigValid (sk : Skel D) (θ : ℝ)
    (y : ResVec (smallPrimes 𝒢)) (h : ¬sk.BigValid) : sk.common θ y = 0 := by
  have h' : ∃ i : Fin D.n, ¬(SharedBig (sk.Cset i) (sk.src i).2 (sk.tgt i).2 ∧
      AuxAvoids (sk.Cset i) (sk.aux i) (sk.src i) ∧
      AuxAvoids (sk.Cset i) (sk.aux i) (sk.tgt i)) := by
    by_contra hcon
    exact h fun i => not_not.mp fun hi => hcon ⟨i, hi⟩
  obtain ⟨i, hi⟩ := h'
  have h0 : sk.edgeCommon θ y i = 0 := by
    unfold Skel.edgeCommon
    exact if_neg fun hc => hi ⟨hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩
  have hprod : (∏ i : Fin D.n, ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
      sk.edgeCommon θ y i * (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0, mul_zero, zero_mul])
  unfold Skel.common
  rw [hprod, mul_zero]

/-! ### The final values and the initial state -/

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- The product of the final values is `𝟏_∅`: one if all memories are empty, zero otherwise. -/
theorem finalVals_eval {Bc : ℕ} (xb : LabelList 𝒢.big J ℓ) (mem : (g : B) → Mem 𝒢 Bc g)
    (U : Finset ℕ) :
    (finalVals 𝒢).eval xb mem U = if (∑ g, (mem g).1.val) = 0 then 1 else 0 := by
  unfold PrimeVals.eval
  simp only [finalVals, Finset.prod_const_one, ite_self, one_mul, mul_one]
  by_cases h : (∑ g, (mem g).1.val) = 0
  · rw [if_pos h]
    refine Finset.prod_eq_one fun g _ => ?_
    have hg : (mem g).1.val = 0 := Finset.sum_eq_zero_iff.mp h g (Finset.mem_univ g)
    exact Finset.prod_eq_one fun j _ => absurd j.isLt (by omega)
  · rw [if_neg h]
    obtain ⟨g, hg⟩ : ∃ g, (mem g).1.val ≠ 0 := by
      by_contra hcon
      exact h (Finset.sum_eq_zero fun g _ => not_not.mp fun hg => hcon ⟨g, hg⟩)
    refine Finset.prod_eq_zero (Finset.mem_univ g) ?_
    exact Finset.prod_eq_zero
      (Finset.mem_univ (⟨0, Nat.pos_of_ne_zero hg⟩ : Fin (mem g).1.val)) rfl

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- The initial state (empty memories, the set of the initial labels) is consistent if the initial
labels are pairwise distinct. -/
theorem memConsistent_init {Bc : ℕ} (xb : LabelList 𝒢.big J ℓ)
    (hinj : Function.Injective fun a : B × Slot J ℓ => (xb a.1 a.2 : ℕ)) :
    MemConsistent xb (fun g => emptyMem 𝒢 Bc g)
      (Finset.univ.image fun a : B × Slot J ℓ => (xb a.1 a.2 : ℕ)) := by
  refine ⟨fun g sl sl' h => ?_, fun g j => ?_, fun g sl j => ?_, fun g sl => ?_, fun g j => ?_,
    fun p hp => ?_⟩
  · have h' := @hinj (g, sl) (g, sl') (congrArg Subtype.val h)
    exact (Prod.mk.inj h').2
  · exact absurd j.isLt (Nat.not_lt_zero _)
  · exact absurd j.isLt (Nat.not_lt_zero _)
  · exact Finset.mem_image.mpr ⟨(g, sl), Finset.mem_univ _, rfl⟩
  · exact absurd j.isLt (Nat.not_lt_zero _)
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    exact mem_bigPrimes.mpr ⟨a.1, (xb a.1 a.2).2⟩

/-! ### The recursion -/

omit [DecidableEq S] [Fintype N] in
theorem Skel.fut_zero {Bc : ℕ} (sk : Skel D) :
    sk.fut Bc 0 =
      sk.ghostSum Bc D.n fun mem _ => if (∑ g, (mem g).1.val) = 0 then 1 else 0 := by
  rw [Skel.fut]

omit [DecidableEq S] [Fintype N] in
theorem Skel.fut_succ {Bc : ℕ} (sk : Skel D) (m : ℕ) (h : m < D.n) :
    sk.fut Bc (m + 1) =
      sk.ghostSum Bc (D.n - (m + 1))
        (sk.edgeSum Bc ⟨D.n - (m + 1), Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le m) h)
          (Nat.succ_pos m)⟩ (sk.fut Bc m)) := by
  rw [Skel.fut]
  exact dif_pos h

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.chain_zero (sk : Skel D) : sk.chain 0 = ghostStepVals D D.n (finalVals 𝒢) := by
  rw [Skel.chain]

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.chain_succ (sk : Skel D) (m : ℕ) (h : m < D.n) :
    sk.chain (m + 1) =
      ghostStepVals D (D.n - (m + 1))
        (sk.edgeStepVals ⟨D.n - (m + 1), Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le m) h)
          (Nat.succ_pos m)⟩ (sk.chain m)) := by
  rw [Skel.chain]
  exact dif_pos h

/-- **The future of the memory part is the product of the chain values** on the states in which
every big prime occurs at most once: backward induction over the operations
`G_N, ℰ_{N-1}, G_{N-1}, …`, one step being (M3) followed by (M2). -/
theorem Skel.fut_eq_chain (hG : GhostStepFactor) (hE : EdgeStepFactor) (Bc : ℕ) (sk : Skel D)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (hBc : (bigPrimes 𝒢).card ≤ Bc)
    (hsh : ∀ i : Fin D.n, SharedBig (sk.Cset i) (sk.src i).2 (sk.tgt i).2) :
    ∀ m : ℕ, m ≤ D.n → ∀ (mem : (g : B) → Mem 𝒢 Bc g) (U : Finset ℕ),
      MemConsistent (sk.lists (D.n - m)).2 mem U →
      sk.fut Bc m mem U = (sk.chain m).eval (sk.lists (D.n - m)).2 mem U := by
  intro m
  induction m with
  | zero =>
    intro _ mem U hc
    rw [Nat.sub_zero] at hc ⊢
    rw [sk.fut_zero, sk.chain_zero]
    exact hG S B 𝒢 J ℓ N D Bc sk hdisj hBc D.n le_rfl
      (fun mem _ => if (∑ g, (mem g).1.val) = 0 then 1 else 0) (finalVals 𝒢)
      (fun mem' U' _ => (finalVals_eval (sk.lists D.n).2 mem' U').symm) mem U hc
  | succ m ih =>
    intro hm mem U hc
    have hlt : m < D.n := hm
    have hidx : D.n - (m + 1) + 1 = D.n - m := by omega
    rw [sk.fut_succ m hlt, sk.chain_succ m hlt]
    refine hG S B 𝒢 J ℓ N D Bc sk hdisj hBc (D.n - (m + 1)) (Nat.sub_le _ _) _ _ ?_ mem U hc
    intro mem' U' hc'
    refine hE S B 𝒢 J ℓ N D Bc sk hdisj hBc ⟨D.n - (m + 1), _⟩ (hsh _) (sk.fut Bc m)
      (sk.chain m) ?_ mem' U' hc'
    intro mem'' U'' hc''
    have hc3 : MemConsistent (sk.lists (D.n - (m + 1) + 1)).2 mem'' U'' := hc''
    rw [hidx] at hc3
    show sk.fut Bc m mem'' U'' = (sk.chain m).eval (sk.lists (D.n - (m + 1) + 1)).2 mem'' U''
    rw [hidx]
    exact ih (Nat.le_of_succ_le hm) mem'' U'' hc3

/-! ### The identity for one skeleton -/

open _root_.Classical in
/-- **The memory sum of a skeleton is the product of the lifespan sums** [S-02:0537–0582]: for a
skeleton with `BigValid`, `memSum = 1_{big lists injective} · (label normalization) ·
∏_{p big} lifeSum p`. From (M1), the recursion (M2), (M3), and (M4). -/
theorem Skel.memSum_eq_lifeSum (h1 : BornSetRecursion) (h2 : GhostStepFactor)
    (h3 : EdgeStepFactor) (h4 : ChainLifespan) (Bc : ℕ) (sk : Skel D) (hraw : RawHyp D)
    (hBc : (bigPrimes 𝒢).card ≤ Bc) (hv : sk.BigValid) :
    sk.memSum Bc =
      (if sk.BigInj then 1 else 0) * sk.bigNormAll * ∏ p ∈ bigPrimes 𝒢, sk.lifeSum p := by
  refine (h1 S B 𝒢 J ℓ N D Bc sk).trans (Eq.trans ?_ (h4 S B 𝒢 J ℓ N D Bc sk hraw hv))
  by_cases hinj : Function.Injective fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)
  · rw [if_pos hinj, if_pos hinj]
    have e : (sk.lists (D.n - D.n)).2 = sk.xb₀ := by
      rw [Nat.sub_self]
      rfl
    have hcons := memConsistent_init (Bc := Bc) sk.xb₀ hinj
    have hfut := sk.fut_eq_chain h2 h3 Bc hraw.disjoint_big hBc (fun i => (hv i).1) D.n le_rfl
      (fun g => emptyMem 𝒢 Bc g)
      (Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ))
      (by rw [e]; exact hcons)
    rw [e] at hfut
    rw [hfut]
  · rw [if_neg hinj, if_neg hinj]

/-- **The core identity for one skeleton**: for a skeleton with `BigValid`, the expectation of the
big part of the physical weight is the baseline `∏_{p big} b_p` times the memory sum. From (C1),
(C2) and `Skel.memSum_eq_lifeSum`. -/
theorem Skel.bigPhys_eq (hC1 : BigResidueProduct) (hC2 : OnePrimeLifespan)
    (h1 : BornSetRecursion) (h2 : GhostStepFactor) (h3 : EdgeStepFactor) (h4 : ChainLifespan)
    (Bc : ℕ) (sk : Skel D) (hraw : RawHyp D) (hn : 1 ≤ D.n) (hBc : (bigPrimes 𝒢).card ≤ Bc)
    (hv : sk.BigValid) :
    sk.bigPhys = baselineProd (bigPrimes 𝒢) D.q D.n * sk.memSum Bc := by
  have hpos : ∀ p ∈ bigPrimes 𝒢, 0 < p := by
    intro p hp
    obtain ⟨g, hg⟩ := mem_bigPrimes.mp hp
    exact (hraw.prime_big g p hg).pos
  have hprod : ∏ p ∈ bigPrimes 𝒢, sk.onePrimeExp p =
      baselineProd (bigPrimes 𝒢) D.q D.n * ∏ p ∈ bigPrimes 𝒢, sk.lifeSum p := by
    unfold baselineProd
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp =>
      hC2 S B 𝒢 J ℓ N D sk p (hpos p hp) (hraw.baseline_ne p hp)
  rw [hC1 S B 𝒢 J ℓ N D sk hn hraw.q_pos hraw.disjoint_big hpos, hprod,
    sk.memSum_eq_lifeSum h1 h2 h3 h4 Bc hraw hBc hv]
  ring

end Core

/-! ### The identity for raw families -/

/-- **The memory identity for raw families from the eight statements.** -/
theorem memoryIdentityRaw_of_parts (hA : PhaseSkeleton) (hB : DistinctSkeleton)
    (hC1 : BigResidueProduct) (hC2 : OnePrimeLifespan) (hM1 : BornSetRecursion)
    (hM2 : GhostStepFactor) (hM3 : EdgeStepFactor) (hM4 : ChainLifespan) :
    MemoryIdentityRaw := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D Bc R θ hn hR hraw hBc
  have hsb : Disjoint (smallPrimes 𝒢) (bigPrimes 𝒢) := by
    unfold smallPrimes bigPrimes
    rw [Finset.disjoint_biUnion_left]
    intro g _
    rw [Finset.disjoint_biUnion_right]
    intro g' _
    exact hraw.disjoint_small_big g g'
  have hn1 : 1 ≤ D.n := by omega
  have key : ∀ (y : ResVec (smallPrimes 𝒢)) (sk : Skel D),
      sk.common θ y * ((sk.bigPhys : ℝ) : ℂ) =
        ((baselineProd (bigPrimes 𝒢) D.q D.n : ℝ) : ℂ) *
          (sk.common θ y * ((sk.memSum Bc : ℝ) : ℂ)) := by
    intro y sk
    by_cases hv : sk.BigValid
    · rw [sk.bigPhys_eq hC1 hC2 hM1 hM2 hM3 hM4 Bc hraw hn1 hBc hv, Complex.ofReal_mul]
      ring
    · rw [sk.common_eq_zero_of_not_bigValid θ y hv, zero_mul, zero_mul, mul_zero]
  have hsum : (∑ y : ResVec (smallPrimes 𝒢), ∑ sk : Skel D,
        sk.common θ y * ((sk.bigPhys : ℝ) : ℂ)) =
      ((baselineProd (bigPrimes 𝒢) D.q D.n : ℝ) : ℂ) *
        ∑ y : ResVec (smallPrimes 𝒢), ∑ sk : Skel D,
          sk.common θ y * ((sk.memSum Bc : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun sk _ => key y sk
  rw [hA S B 𝒢 J ℓ N D R θ hn hraw.q_pos hsb, hB S B 𝒢 J ℓ N D Bc θ, hsum]
  ring

/-! ### The threshold -/

/-- `L^C < exp(L^c)` for large `x` (`L = log x`, `c > 0`): a power of `L` is smaller than every
group prime. -/
theorem memId_eventually_rpow_lt_exp_rpow (c C : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ C < Real.exp (Real.log x ^ c) := by
  have hC : 0 ≤ |C| := abs_nonneg C
  have hC1 : 0 < |C| + 1 := by linarith
  filter_upwards [eventually_loglog_le c (1 / (|C| + 1)) hc (one_div_pos.mpr hC1),
    eventually_log_ge 1] with x h1 h2
  have hL : 0 < Real.log x := by linarith
  have hLc : 0 < Real.log x ^ c := Real.rpow_pos_of_pos hL c
  have hlog : 0 ≤ Real.log (Real.log x) := Real.log_nonneg h2
  have e1 : Real.log (Real.log x) * C ≤ Real.log (Real.log x) * |C| :=
    mul_le_mul_of_nonneg_left (le_abs_self C) hlog
  have e2 : Real.log (Real.log x) * |C| ≤ 1 / (|C| + 1) * Real.log x ^ c * |C| :=
    mul_le_mul_of_nonneg_right h1 hC
  have e3 : 1 / (|C| + 1) * Real.log x ^ c * |C| < Real.log x ^ c := by
    have h4 : |C| / (|C| + 1) < 1 := (div_lt_one hC1).mpr (by linarith)
    have h5 : 1 / (|C| + 1) * Real.log x ^ c * |C| = Real.log x ^ c * (|C| / (|C| + 1)) := by
      ring
    rw [h5]
    calc Real.log x ^ c * (|C| / (|C| + 1)) < Real.log x ^ c * 1 :=
          mul_lt_mul_of_pos_left h4 hLc
      _ = Real.log x ^ c := mul_one _
  have e4 : Real.log (Real.log x) * C < Real.log x ^ c := by linarith
  calc Real.log x ^ C = Real.exp (Real.log (Real.log x) * C) := Real.rpow_def_of_pos hL C
    _ < Real.exp (Real.log x ^ c) := Real.exp_lt_exp.mpr e4

/-- **Lemma 3.7 from the identity for raw families**: for large `x` the prime groups of
Definition 3.1 and an admissible `k` satisfy `RawHyp`, and `N = 2R` with `R ≥ 1`. -/
theorem memoryIdentity_of_raw (hraw : MemoryIdentityRaw) : MemoryIdentity := by
  intro P m C₁ J C₂
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((((eventually_log_ge 1).and (memId_eventually_rpow_lt_exp_rpow P.a C₂ P.a_pos)).and
      (memId_eventually_rpow_lt_exp_rpow P.c C₂ P.c_pos)).and (eventually_big_tilt P one_pos))
  refine ⟨x₀, fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm θ Bc hBc => ?_⟩
  obtain ⟨⟨⟨hL1, ha⟩, hc⟩, htilt⟩ := hx₀ x hx
  have hL : 0 < Real.log x := by linarith
  obtain ⟨_, _, hk0, hkle⟩ := hadm
  -- a natural number larger than `L^{C₂}` does not divide `k`
  have hnd : ∀ p : ℕ, Real.log x ^ C₂ < (p : ℝ) → ¬((p : ℤ) ∣ k) := by
    intro p hp hdvd
    have h1 : p ∣ k.natAbs := by
      have h := Int.natAbs_dvd_natAbs.mpr hdvd
      rwa [Int.natAbs_natCast] at h
    have h2 : p ≤ k.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hk0) h1
    have h4 : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have h3 : (p : ℝ) ≤ |(k : ℝ)| := by
      rw [← h4]
      exact_mod_cast h2
    linarith
  have hsmall : ∀ g, ∀ p ∈ 𝔊.small g, Real.log x ^ C₂ < (p : ℝ) :=
    fun g p hg => lt_of_lt_of_le ha (𝔊.small_ge g p hg)
  have hbig : ∀ g, ∀ p ∈ 𝔊.big g, Real.log x ^ C₂ < (p : ℝ) :=
    fun g p hg => lt_of_lt_of_le hc (𝔊.big_ge g p hg)
  have hrawH : RawHyp (memData 𝔊 𝔉 k ζ) :=
    { prime_small := 𝔊.prime_small
      prime_big := 𝔊.prime_big
      disjoint_big := 𝔊.disjoint_big
      disjoint_small_big := 𝔊.disjoint_small_big
      not_dvd := by
        intro p hp
        have hp' : p ∈ (Finset.univ.biUnion 𝔊.small) ∪ (Finset.univ.biUnion 𝔊.big) := hp
        rcases Finset.mem_union.mp hp' with hs | hb
        · obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp hs
          exact hnd p (hsmall g p hg)
        · obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp hb
          exact hnd p (hbig g p hg)
      baseline_ne := by
        intro p hp
        obtain ⟨g, hg⟩ := mem_bigPrimes.mp hp
        exact (htilt S B 𝔊 g p hg).1.ne'
      q_pos := P.q_pos
      ρ_ne := (memRho_pos P).ne' }
  have hR : 0 < transferR (Real.log x) := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hL _)
  exact hraw S B 𝔊.toGroupFamily J P.ℓ N (memData 𝔊 𝔉 k ζ) Bc (transferR (Real.log x)) θ
    (sourceMemoryLength_eq_two_mul _) hR hrawH hBc

/-- **[S] Lemma 3.7 from its eight intermediate statements** (`Memory/Statements.lean`): the
physical and the memory path expansions by skeletons (A), (B), the product over the big primes of
the residue expectation (C1), the one-prime lifespan expansion (C2), the distinct-birth rule as a
running set (M1), the factorization of a visit and of an edge operation over the big primes (M2),
(M3), and the evaluation of the per-prime transfer chain (M4). -/
theorem memoryIdentity_of_parts (hA : PhaseSkeleton) (hB : DistinctSkeleton)
    (hC1 : BigResidueProduct) (hC2 : OnePrimeLifespan) (hM1 : BornSetRecursion)
    (hM2 : GhostStepFactor) (hM3 : EdgeStepFactor) (hM4 : ChainLifespan) : MemoryIdentity :=
  memoryIdentity_of_raw (memoryIdentityRaw_of_parts hA hB hC1 hC2 hM1 hM2 hM3 hM4)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
