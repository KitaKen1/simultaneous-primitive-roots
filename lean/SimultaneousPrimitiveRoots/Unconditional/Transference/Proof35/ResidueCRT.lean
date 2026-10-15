module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The proof of [S] Lemma 3.6, part 1: CRT counts on an interval of integers

Source: `verification/stage7-sources/S-02.tex`, lines 277–280 (`[S-02:0277–0280]`): "Each truncated
term specifies one residue at each of at most `h` additional primes. Its CRT count on `I` differs
from its independent density by `O(|I ∩ ℤ|^{-1})`, also when the active congruence is imposed."

Everything here is about a family of pairwise coprime moduli `m i ≠ 0` and functions
`f i : ZMod (m i) → ℝ`; no prime groups occur.

* `abs_card_filter_intCast_sub_le` — a residue class modulo `N` has `(b - a)/N + O(1)` elements in
  `[a, b)`, with `|O(1)| ≤ 1`.
* `abs_sum_Ico_intCast_sub_le` — hence `∑_{a ≤ n < b} H(n mod N) = ((b - a)/N) ∑_u H(u) + θ ∑_u H(u)`
  with `|θ| ≤ 1`, for `H ≥ 0`.
* `sum_zmod_prod_cast`, `sum_zmod_prod_cast_finset` — the Chinese remainder theorem in the form
  `∑_{z mod ∏ m_i} ∏_i f_i(z mod m_i) = ∏_i ∑_u f_i(u)`.
* `abs_sum_Ico_prod_sub_le` — **the weighted CRT count**: for nonnegative `f_i`,
  `|∑_{a ≤ n < b} ∏_{i ∈ T} f_i(n) - (b - a) ∏_{i ∈ T} (∑_u f_i(u))/m_i| ≤ ∏_{i ∈ T} ∑_u f_i(u)`.
  For indicator functions of residues this is the count of the manuscript; the weighted form
  avoids the expansion of the factors `X_p` into residues.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl

open scoped BigOperators

noncomputable section

/-! ### One modulus -/

/-- A residue class modulo `N` has `(b - a)/N + θ` elements in `[a, b)`, `|θ| ≤ 1`. -/
theorem abs_card_filter_intCast_sub_le (N : ℕ) [NeZero N] {a b : ℤ} (hab : a ≤ b) (u : ZMod N) :
    |(((Finset.Ico a b).filter fun n : ℤ => (n : ZMod N) = u).card : ℝ) - ((b : ℝ) - a) / N| ≤
      1 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN : (0 : ℤ) < (N : ℤ) := Int.natCast_pos.mpr hN0
  have hNq : (0 : ℚ) < ((N : ℤ) : ℚ) := by exact_mod_cast hN0
  have hu : (((u.val : ℤ) : ℤ) : ZMod N) = u := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hfilter : ((Finset.Ico a b).filter fun n : ℤ => (n : ZMod N) = u) =
      (Finset.Ico a b).filter fun n : ℤ => n ≡ (u.val : ℤ) [ZMOD (N : ℤ)] := by
    refine Finset.filter_congr fun n _ => ?_
    rw [← ZMod.intCast_eq_intCast_iff, hu]
  have hcard := Int.Ico_filter_modEq_card a b hN (u.val : ℤ)
  have hle : ((a : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ) ≤
      ((b : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ) := by
    have hab' : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
    exact div_le_div_of_nonneg_right (by linarith) hNq.le
  rw [max_eq_left (sub_nonneg.mpr (Int.ceil_mono hle))] at hcard
  rw [hfilter]
  have hcq : ((((Finset.Ico a b).filter fun n : ℤ => n ≡ (u.val : ℤ) [ZMOD (N : ℤ)]).card : ℤ) : ℚ) =
      ((⌈((b : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ)⌉ : ℤ) : ℚ) -
        ((⌈((a : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ)⌉ : ℤ) : ℚ) := by
    rw [hcard, Int.cast_sub]
  have hb1 := Int.le_ceil (((b : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ))
  have hb2 := Int.ceil_lt_add_one (((b : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ))
  have ha1 := Int.le_ceil (((a : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ))
  have ha2 := Int.ceil_lt_add_one (((a : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ))
  have hdiff : ((b : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ) -
      ((a : ℚ) - ((u.val : ℤ) : ℚ)) / ((N : ℤ) : ℚ) = ((b : ℚ) - a) / ((N : ℤ) : ℚ) := by
    ring
  have hq : |((((Finset.Ico a b).filter fun n : ℤ => n ≡ (u.val : ℤ) [ZMOD (N : ℤ)]).card : ℤ) : ℚ) -
      ((b : ℚ) - a) / ((N : ℤ) : ℚ)| ≤ 1 := by
    rw [hcq, abs_le]
    constructor <;> linarith
  have hreal := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hreal
  exact hreal

/-- The sum over `[a, b)` of a nonnegative function of the residue modulo `N` is
`((b - a)/N + θ) ∑_u H(u)` with `|θ| ≤ 1`. -/
theorem abs_sum_Ico_intCast_sub_le (N : ℕ) [NeZero N] {a b : ℤ} (hab : a ≤ b) (H : ZMod N → ℝ)
    (hH : ∀ u, 0 ≤ H u) :
    |∑ n ∈ Finset.Ico a b, H (n : ZMod N) - ((b : ℝ) - a) / N * ∑ u, H u| ≤ ∑ u, H u := by
  have h1 : ∑ n ∈ Finset.Ico a b, H (n : ZMod N) =
      ∑ u : ZMod N, (((Finset.Ico a b).filter fun n : ℤ => (n : ZMod N) = u).card : ℝ) * H u := by
    rw [← Finset.sum_fiberwise' (Finset.Ico a b) (fun n : ℤ => (n : ZMod N)) H]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  rw [← sub_mul, abs_mul, abs_of_nonneg (hH u)]
  exact mul_le_of_le_one_left (hH u) (abs_card_filter_intCast_sub_le N hab u)

/-! ### The Chinese remainder theorem for sums -/

/-- **CRT for sums**, for a family indexed by a finite type: the sum over the residues modulo
`M = ∏_k a_k` of `∏_k f_k(z mod a_k)` is `∏_k ∑_u f_k(u)`. -/
theorem sum_zmod_prod_cast {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℕ)
    [∀ k, NeZero (a k)] (hcop : Pairwise (Function.onFun Nat.Coprime a))
    (f : (k : κ) → ZMod (a k) → ℝ) (M : ℕ) [NeZero M] (hM : M = ∏ k, a k) :
    ∑ z : ZMod M, ∏ k, f k (ZMod.cast z) = ∏ k, ∑ u : ZMod (a k), f k u := by
  subst hM
  rw [Fintype.prod_sum,
    ← Equiv.sum_comp (ZMod.prodEquivPi a hcop).toEquiv fun x => ∏ k, f k (x k)]
  refine Finset.sum_congr rfl fun z _ => Finset.prod_congr rfl fun k _ => ?_
  have h : (ZMod.prodEquivPi a hcop).toEquiv z k = ZMod.cast z := by
    show (ZMod.prodEquivPi a hcop) z k = ZMod.cast z
    rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply]
  rw [h]

variable {ι : Type*} [DecidableEq ι] (m : ι → ℕ) [∀ i, NeZero (m i)]

/-- **CRT for sums**, for a finite set of indices. -/
theorem sum_zmod_prod_cast_finset (hm : Pairwise (Function.onFun Nat.Coprime m)) (T : Finset ι)
    (f : (i : ι) → ZMod (m i) → ℝ) [NeZero (∏ i ∈ T, m i)] :
    ∑ z : ZMod (∏ i ∈ T, m i), ∏ i ∈ T, f i (ZMod.cast z) =
      ∏ i ∈ T, ∑ u : ZMod (m i), f i u := by
  have hcop : Pairwise (Function.onFun Nat.Coprime fun k : {i // i ∈ T} => m k.1) :=
    fun i j hij => hm fun h => hij (Subtype.ext h)
  have h := sum_zmod_prod_cast (fun k : {i // i ∈ T} => m k.1) hcop (fun k => f k.1)
    (∏ i ∈ T, m i) (Finset.prod_coe_sort T m).symm
  rw [Finset.prod_coe_sort T fun i => ∑ u : ZMod (m i), f i u] at h
  rw [← h]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (Finset.prod_coe_sort T fun i => f i (ZMod.cast z)).symm

/-- **The weighted CRT count** [S-02:0277–0280]: for pairwise coprime moduli and nonnegative
functions `f_i` of the residue modulo `m_i`,
`∑_{a ≤ n < b} ∏_{i ∈ T} f_i(n) = (b - a) ∏_{i ∈ T} (∑_u f_i(u))/m_i + θ ∏_{i ∈ T} ∑_u f_i(u)`,
`|θ| ≤ 1`. -/
theorem abs_sum_Ico_prod_sub_le (hm : Pairwise (Function.onFun Nat.Coprime m)) (T : Finset ι)
    (f : (i : ι) → ZMod (m i) → ℝ) (hf : ∀ i ∈ T, ∀ u, 0 ≤ f i u) {a b : ℤ} (hab : a ≤ b) :
    |∑ n ∈ Finset.Ico a b, ∏ i ∈ T, f i (n : ZMod (m i)) -
        ((b : ℝ) - a) * ∏ i ∈ T, ((∑ u, f i u) / (m i : ℝ))| ≤ ∏ i ∈ T, ∑ u, f i u := by
  have : NeZero (∏ i ∈ T, m i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (m i)⟩
  have hH := abs_sum_Ico_intCast_sub_le (∏ i ∈ T, m i) hab
    (fun z => ∏ i ∈ T, f i (ZMod.cast z)) fun z => Finset.prod_nonneg fun i hi => hf i hi _
  rw [sum_zmod_prod_cast_finset m hm T f] at hH
  have hcast : ∀ n : ℤ, ∏ i ∈ T, f i (ZMod.cast (n : ZMod (∏ i ∈ T, m i))) =
      ∏ i ∈ T, f i (n : ZMod (m i)) := by
    intro n
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [ZMod.cast_intCast (Finset.dvd_prod_of_mem m hi)]
  rw [Finset.sum_congr rfl fun n _ => hcast n] at hH
  have hprod : ((b : ℝ) - a) / ((∏ i ∈ T, m i : ℕ) : ℝ) * ∏ i ∈ T, ∑ u, f i u =
      ((b : ℝ) - a) * ∏ i ∈ T, ((∑ u, f i u) / (m i : ℝ)) := by
    rw [Finset.prod_div_distrib, Nat.cast_prod]
    ring
  rw [hprod] at hH
  exact hH

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl
