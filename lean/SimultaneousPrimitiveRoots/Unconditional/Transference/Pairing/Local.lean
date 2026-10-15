module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing.Adjoint
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Corollary 3.11: integer positions, the maximal displacement and supports in intervals

Source: `verification/stage7-sources/S-02.tex`, lines 1285–1290 (`[S-02:1285–1290]`):
"Let `H ≥ 1` bound every displacement `|kD|`. Since `D` has `Js` factors, all at most
`exp(L^d)`, `log H = O_J(T L^d)`."

* `maxPrime`, `dilBound`, `stepBound` — a bound `P ≥ 1` for all group primes, the bound
  `P^{J|𝒮| + 2J|ℬ|}` for every dilation `D` (`dil_le_dilBound`), and the bound
  `H = |k| P^{J|𝒮| + 2J|ℬ|}` for every displacement `|kD|` (`abs_mul_dil_le`). The exponent `2J`
  for a big group (instead of the paper's `J`) is the crude count "at most `J` shared labels and
  at most `J` auxiliary labels"; it only changes the implied constant in `log H = O_J(T L^d)`.
* `SuppIcc u a b` — `u` vanishes at all positions outside `[a, b]`. `𝒜` and `𝒜*` enlarge such an
  interval by `H` on both sides (`suppIcc_physOp`, `suppIcc_physAdj`).
* For such functions the inner product and the norm are sums over the interval
  (`gp_Icc_left`, `gsq_Icc`), `⟨u, 𝒜 v⟩ = ⟨𝒜* u, v⟩` (`gp_physOp_int`), and the Cauchy–Schwarz
  inequality holds (`norm_gp_sq_le`, `norm_gp_sq_le_window`, `gsq_sum_smul_le`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing

open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-! ### The maximal displacement -/

section DilBound

variable (𝒢 : GroupFamily S B) (J : ℕ)

/-- A bound for all group primes, at least `1`. -/
def maxPrime : ℕ := max 1 (𝒢.allPrimes.sup id)

/-- A bound for every dilation `D` of the family: `P^{J|𝒮| + 2J|ℬ|}`. -/
def dilBound : ℕ := maxPrime 𝒢 ^ (J * Fintype.card S + 2 * J * Fintype.card B)

/-- **A bound `H` for every displacement `|kD|`** [S-02:1286]. -/
def stepBound (k : ℤ) : ℕ := k.natAbs * dilBound 𝒢 J

omit [DecidableEq S] [DecidableEq B] in
theorem one_le_maxPrime : 1 ≤ maxPrime 𝒢 := le_max_left _ _

variable {𝒢 J}

omit [DecidableEq S] [DecidableEq B] in
theorem small_label_le {ℓ : ℕ} (p : LabelList 𝒢.small J ℓ) (g : S) (s : Slot J ℓ) :
    (p g s : ℕ) ≤ maxPrime 𝒢 := by
  have hmem : (p g s : ℕ) ∈ 𝒢.allPrimes := by
    unfold GroupFamily.allPrimes
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (p g s).2⟩)
  exact (Finset.le_sup (f := id) hmem).trans (le_max_right _ _)

omit [DecidableEq S] [DecidableEq B] in
theorem big_label_le {ℓ : ℕ} (p : LabelList 𝒢.big J ℓ) (g : B) (s : Slot J ℓ) :
    (p g s : ℕ) ≤ maxPrime 𝒢 := by
  have hmem : (p g s : ℕ) ∈ 𝒢.allPrimes := by
    unfold GroupFamily.allPrimes
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (p g s).2⟩)
  exact (Finset.le_sup (f := id) hmem).trans (le_max_right _ _)

omit [DecidableEq S] [DecidableEq B] in
theorem aux_label_le (C : B → Finset (Fin J)) (r : AuxList 𝒢.big C) (g : B)
    (i : {i : Fin J // i ∈ C g}) : (r g i : ℕ) ≤ maxPrime 𝒢 := by
  have hmem : (r g i : ℕ) ∈ 𝒢.allPrimes := by
    unfold GroupFamily.allPrimes
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (r g i).2⟩)
  exact (Finset.le_sup (f := id) hmem).trans (le_max_right _ _)

omit [DecidableEq S] [DecidableEq B] in
/-- `D_𝒮` has `J` factors from each small group. -/
theorem smallDil_le {ℓ : ℕ} (p : LabelList 𝒢.small J ℓ) :
    smallDil p ≤ maxPrime 𝒢 ^ (J * Fintype.card S) := by
  unfold smallDil
  calc ∏ g : S, ∏ i : Fin J, (p g (Sum.inl i) : ℕ)
      ≤ ∏ _g : S, ∏ _i : Fin J, maxPrime 𝒢 :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun g _ =>
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ =>
            small_label_le p g (Sum.inl i)
    _ = maxPrime 𝒢 ^ (J * Fintype.card S) := by
        rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, ← pow_mul]

omit [DecidableEq S] [DecidableEq B] in
/-- `D_ℬ` has at most `2J` factors from each big group (shared labels and auxiliary labels). -/
theorem bigDil_le {ℓ : ℕ} (C : B → Finset (Fin J)) (p : LabelList 𝒢.big J ℓ)
    (r : AuxList 𝒢.big C) : bigDil C p r ≤ maxPrime 𝒢 ^ (2 * J * Fintype.card B) := by
  have hM : 0 < maxPrime 𝒢 := one_le_maxPrime 𝒢
  have h1 : ∀ g : B,
      (∏ i : Fin J, if i ∈ C g then 1 else (p g (Sum.inl i) : ℕ)) ≤ maxPrime 𝒢 ^ J := by
    intro g
    calc (∏ i : Fin J, if i ∈ C g then 1 else (p g (Sum.inl i) : ℕ))
        ≤ ∏ _i : Fin J, maxPrime 𝒢 :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => by
            split_ifs
            · exact one_le_maxPrime 𝒢
            · exact big_label_le p g (Sum.inl i)
      _ = maxPrime 𝒢 ^ J := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ∀ g : B, (∏ i : {i : Fin J // i ∈ C g}, (r g i : ℕ)) ≤ maxPrime 𝒢 ^ J := by
    intro g
    calc (∏ i : {i : Fin J // i ∈ C g}, (r g i : ℕ))
        ≤ ∏ _i : {i : Fin J // i ∈ C g}, maxPrime 𝒢 :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => aux_label_le C r g i
      _ = maxPrime 𝒢 ^ Fintype.card {i : Fin J // i ∈ C g} := by
          rw [Finset.prod_const, Finset.card_univ]
      _ ≤ maxPrime 𝒢 ^ J := Nat.pow_le_pow_right hM (by
          rw [Fintype.card_coe]
          exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin J))
  unfold bigDil
  calc ∏ g : B, ((∏ i : Fin J, if i ∈ C g then 1 else (p g (Sum.inl i) : ℕ)) *
        ∏ i : {i : Fin J // i ∈ C g}, (r g i : ℕ))
      ≤ ∏ _g : B, (maxPrime 𝒢 ^ J * maxPrime 𝒢 ^ J) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun g _ => Nat.mul_le_mul (h1 g) (h2 g)
    _ = maxPrime 𝒢 ^ (2 * J * Fintype.card B) := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_add, ← two_mul, ← pow_mul]

omit [DecidableEq S] [DecidableEq B] in
/-- Every dilation is at most `dilBound`. -/
theorem dil_le_dilBound {ℓ : ℕ} (C : B → Finset (Fin J)) (x : Lists 𝒢 J ℓ)
    (r : AuxList 𝒢.big C) : dil C x r ≤ dilBound 𝒢 J := by
  unfold dil dilBound
  rw [pow_add]
  exact Nat.mul_le_mul (smallDil_le x.1) (bigDil_le C x.2 r)

omit [DecidableEq S] [DecidableEq B] in
/-- **Every displacement `|kD|` is at most `H`** [S-02:1286]. -/
theorem abs_mul_dil_le {ℓ : ℕ} (k : ℤ) (C : B → Finset (Fin J)) (x : Lists 𝒢 J ℓ)
    (r : AuxList 𝒢.big C) : |k * (dil C x r : ℤ)| ≤ (stepBound 𝒢 J k : ℤ) := by
  unfold stepBound
  rw [abs_mul, Nat.cast_mul, Int.natCast_natAbs, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast dil_le_dilBound C x r) (abs_nonneg k)

end DilBound

/-! ### Functions supported on an interval of positions -/

section Int

variable {𝒢 : GroupFamily S B} {q : ℝ} {J ℓ : ℕ} {N : Type} [Fintype N]

/-- `u` vanishes at all states whose position is outside `[a, b]`. -/
def SuppIcc (u : PState intPos 𝒢 J ℓ → ℂ) (a b : ℤ) : Prop :=
  PosSupp intPos 𝒢 J ℓ u (Set.Icc a b : Set ℤ)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem suppIcc_mono {u : PState intPos 𝒢 J ℓ → ℂ} {a b a' b' : ℤ} (h : SuppIcc u a b)
    (ha : a' ≤ a) (hb : b ≤ b') : SuppIcc u a' b' := by
  unfold SuppIcc at h ⊢
  exact posSupp_mono h (Set.Icc_subset_Icc ha hb)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem suppIcc_coe {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b) :
    PosSupp intPos 𝒢 J ℓ u (↑(Finset.Icc a b : Finset ℤ) : Set ℤ) := by
  rw [Finset.coe_Icc]
  exact h

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem suppIcc_sum {ι : Type*} (s : Finset ι) {w : ι → PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ}
    (h : ∀ i ∈ s, SuppIcc (w i) a b) : SuppIcc (∑ i ∈ s, w i) a b := by
  unfold SuppIcc at h ⊢
  exact posSupp_sum s h

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem suppIcc_smul (c : ℂ) {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b) :
    SuppIcc (c • u) a b := by
  unfold SuppIcc at h ⊢
  exact posSupp_smul c h

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- `u_n` is supported on the position `n`. -/
theorem suppIcc_physUnit (n : ℤ) : SuppIcc (physUnit intPos 𝒢 J ℓ n) n n := by
  unfold SuppIcc
  intro (m : ℤ) x hm
  refine physUnit_apply_of_ne (fun h => hm ?_) x
  rw [h]
  exact ⟨le_rfl, le_rfl⟩

/-- **`𝒜` moves the position by at most `H`**. -/
theorem suppIcc_physOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b) :
    SuppIcc (physOp intPos 𝒢 q 𝔉 k ζ u) (a - stepBound 𝒢 J k) (b + stepBound 𝒢 J k) := by
  unfold SuppIcc at h ⊢
  refine posSupp_physOp 𝔉 k ζ h fun ν (n : ℤ) x r hmem => ?_
  have hstep := abs_le.mp (abs_mul_dil_le k (𝔉 ν).C x r)
  have h1 : a ≤ n + k * (dil (𝔉 ν).C x r : ℤ) := hmem.1
  have h2 : n + k * (dil (𝔉 ν).C x r : ℤ) ≤ b := hmem.2
  exact ⟨by linarith [hstep.1, hstep.2], by linarith [hstep.1, hstep.2]⟩

/-- **`𝒜*` moves the position by at most `H`**. -/
theorem suppIcc_physAdj (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b) :
    SuppIcc (physAdj intPos 𝒢 q 𝔉 k ζ u) (a - stepBound 𝒢 J k) (b + stepBound 𝒢 J k) := by
  unfold SuppIcc at h ⊢
  refine posSupp_physAdj 𝔉 k ζ h fun ν (n : ℤ) x r hmem => ?_
  have hstep := abs_le.mp (abs_mul_dil_le k (𝔉 ν).C x r)
  have h1 : a ≤ n + -(k * (dil (𝔉 ν).C x r : ℤ)) := hmem.1
  have h2 : n + -(k * (dil (𝔉 ν).C x r : ℤ)) ≤ b := hmem.2
  exact ⟨by linarith [hstep.1, hstep.2], by linarith [hstep.1, hstep.2]⟩

/-! ### The inner product of functions supported on an interval -/

theorem gp_Icc_left {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b)
    (v : PState intPos 𝒢 J ℓ → ℂ) :
    gp intPos 𝒢 J ℓ u v = ∑ n ∈ Finset.Icc a b, fib intPos 𝒢 J ℓ n u v :=
  gp_eq_sum_left (𝔭 := intPos) (Finset.Icc a b : Finset ℤ) (suppIcc_coe h) v

theorem gp_Icc_right {v : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc v a b)
    (u : PState intPos 𝒢 J ℓ → ℂ) :
    gp intPos 𝒢 J ℓ u v = ∑ n ∈ Finset.Icc a b, fib intPos 𝒢 J ℓ n u v :=
  gp_eq_sum_right (𝔭 := intPos) (Finset.Icc a b : Finset ℤ) (suppIcc_coe h) u

theorem gsq_Icc {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b) :
    gsq intPos 𝒢 J ℓ u = ∑ n ∈ Finset.Icc a b, fibSq intPos 𝒢 J ℓ n u :=
  gsq_eq_sum (𝔭 := intPos) (Finset.Icc a b : Finset ℤ) (suppIcc_coe h)

theorem gsq_nonneg_int {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b) :
    0 ≤ gsq intPos 𝒢 J ℓ u :=
  gsq_nonneg (𝔭 := intPos) (Finset.Icc a b : Finset ℤ) (suppIcc_coe h)

/-- `⟨u, u⟩ = ‖u‖²`. -/
theorem gp_self_int {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b) :
    gp intPos 𝒢 J ℓ u u = (gsq intPos 𝒢 J ℓ u : ℂ) :=
  gp_self (𝔭 := intPos) (Finset.Icc a b : Finset ℤ) (suppIcc_coe h)

/-- **`⟨u, 𝒜 v⟩ = ⟨𝒜* u, v⟩`** for `u` supported on an interval of positions. -/
theorem gp_physOp_int (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b)
    (v : PState intPos 𝒢 J ℓ → ℂ) :
    gp intPos 𝒢 J ℓ u (physOp intPos 𝒢 q 𝔉 k ζ v) =
      gp intPos 𝒢 J ℓ (physAdj intPos 𝒢 q 𝔉 k ζ u) v :=
  gp_physOp (𝔭 := intPos) 𝔉 k ζ (Set.finite_Icc a b) h v

/-- **`⟨𝒜 w, v⟩ = ⟨w, 𝒜* v⟩`** for `v` supported on an interval of positions. -/
theorem gp_physOp_left_int (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    {v : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc v a b)
    (w : PState intPos 𝒢 J ℓ → ℂ) :
    gp intPos 𝒢 J ℓ (physOp intPos 𝒢 q 𝔉 k ζ w) v =
      gp intPos 𝒢 J ℓ w (physAdj intPos 𝒢 q 𝔉 k ζ v) :=
  gp_physOp_left (𝔭 := intPos) 𝔉 k ζ (Set.finite_Icc a b) h w

/-- **Cauchy–Schwarz** `|⟨u, v⟩|² ≤ ‖u‖² ‖v‖²` for functions supported on intervals. -/
theorem norm_gp_sq_le {u v : PState intPos 𝒢 J ℓ → ℂ} {a b a' b' : ℤ} (hu : SuppIcc u a b)
    (hv : SuppIcc v a' b') :
    ‖gp intPos 𝒢 J ℓ u v‖ ^ 2 ≤ gsq intPos 𝒢 J ℓ u * gsq intPos 𝒢 J ℓ v := by
  have hu' : SuppIcc u (min a a') (max b b') :=
    suppIcc_mono hu (min_le_left _ _) (le_max_left _ _)
  have hv' : SuppIcc v (min a a') (max b b') :=
    suppIcc_mono hv (min_le_right _ _) (le_max_right _ _)
  rw [gp_Icc_left hu', gsq_Icc hu', gsq_Icc hv']
  exact norm_sum_fib_sq_le (𝔭 := intPos) (Finset.Icc (min a a') (max b b') : Finset ℤ) u v

/-- **Cauchy–Schwarz against an arbitrary function**: if `u` is supported on `[a, b]` then
`|⟨u, v⟩|² ≤ ‖u‖² · (the part of ‖v‖² on [a, b])`. -/
theorem norm_gp_sq_le_window {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (hu : SuppIcc u a b)
    (v : PState intPos 𝒢 J ℓ → ℂ) :
    ‖gp intPos 𝒢 J ℓ u v‖ ^ 2 ≤
      gsq intPos 𝒢 J ℓ u * ∑ n ∈ Finset.Icc a b, fibSq intPos 𝒢 J ℓ n v := by
  rw [gp_Icc_left hu, gsq_Icc hu]
  exact norm_sum_fib_sq_le (𝔭 := intPos) (Finset.Icc a b : Finset ℤ) u v

/-- **The norm of a finite linear combination**:
`‖∑ c_i w_i‖² ≤ (∑ |c_i|²) (∑ ‖w_i‖²)`. -/
theorem gsq_sum_smul_le {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {w : ι → PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (hw : ∀ i ∈ s, SuppIcc (w i) a b) :
    gsq intPos 𝒢 J ℓ (∑ i ∈ s, c i • w i) ≤
      (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, gsq intPos 𝒢 J ℓ (w i) := by
  have hsum : SuppIcc (∑ i ∈ s, c i • w i) a b :=
    suppIcc_sum s fun i hi => suppIcc_smul (c i) (hw i hi)
  calc gsq intPos 𝒢 J ℓ (∑ i ∈ s, c i • w i)
      = ∑ n ∈ Finset.Icc a b, fibSq intPos 𝒢 J ℓ n (∑ i ∈ s, c i • w i) := gsq_Icc hsum
    _ ≤ ∑ n ∈ Finset.Icc a b, (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, fibSq intPos 𝒢 J ℓ n (w i) :=
        Finset.sum_le_sum fun n _ => fibSq_sum_smul_le s n c w
    _ = (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, ∑ n ∈ Finset.Icc a b, fibSq intPos 𝒢 J ℓ n (w i) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, gsq intPos 𝒢 J ℓ (w i) := by
        rw [Finset.sum_congr rfl fun i hi => (gsq_Icc (hw i hi)).symm]

end Int

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing
