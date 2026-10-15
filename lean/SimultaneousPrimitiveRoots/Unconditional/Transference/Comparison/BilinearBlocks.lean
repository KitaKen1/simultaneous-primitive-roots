module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.BilinearKernel
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The blocks of the integer bilinear estimate

Source: `verification/stage7-sources/S-03.tex`, lines 144–158 (`[S-03:0144–0158]`), the proof of
[S] Lemma 4.2.

* `Bilinear.sep_of_coprime` — "If `h ≠ h'` belong to a block, their difference is nonzero and has
  magnitude less than `r`, so `‖α(h - h')‖ ≥ ‖u(h - h')/r‖ - |h - h'|/r² ≥ 1/(2r)`": for an
  integer `d ≠ 0` with `2|d| ≤ r` and every integer `z`, `2 r |α d - z| ≥ 1`.
* `Bilinear.sum_le_of_sep` — "the phases in a block are `1/(2r)`-separated on the circle. Ordering
  them by distance from zero bounds their contribution": separated phases lie in distinct arcs
  (`bin_ne_of_sep`), so the sum over a block is at most twice the sum of all arc weights.
* `Bilinear.sum_geomKernel_le` — a row sum `∑_k |∑_n e(α (k - c) n)|` over `k` in an interval of
  length `D`, split into the `⌊D/q⌋ + 1` blocks of `q` consecutive integers, `2(q - 1) ≤ r`
  ("consecutive blocks, each of diameter at most `r/2`"). For `r = 1` the blocks are single
  points, so that the trivial bound of the paper for `r = 1` is the same argument.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Bilinear

/-! ### Separation of the phases of a block -/

/-- **Separation.** If `α = u/r + β` with `(u, r) = 1` and `|β| ≤ r⁻²`, then for every integer
`d ≠ 0` with `2|d| ≤ r` the number `α d` has distance at least `1/(2r)` from every integer. -/
theorem sep_of_coprime {α β : ℝ} {u : ℤ} {r : ℕ} (hr : 0 < r) (hcop : IsCoprime u (r : ℤ))
    (hα : α = (u : ℝ) / (r : ℝ) + β) (hβ : |β| ≤ ((r : ℝ) ^ 2)⁻¹) {d : ℤ} (hd : d ≠ 0)
    (hdr : 2 * |d| ≤ (r : ℤ)) (z : ℤ) :
    1 ≤ 2 * (r : ℝ) * |α * (d : ℝ) - (z : ℝ)| := by
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  -- the integer `u d - z r` is not zero, because `r` does not divide `d`
  have he : u * d - z * (r : ℤ) ≠ 0 := by
    intro h0
    have hdvd : (r : ℤ) ∣ u * d := Dvd.intro z (by linear_combination (-1 : ℤ) * h0)
    have hdvd' : (r : ℤ) ∣ |d| := (dvd_abs _ _).mpr (hcop.symm.dvd_of_dvd_mul_left hdvd)
    have hpos : 0 < |d| := abs_pos.mpr hd
    have hle : (r : ℤ) ≤ |d| := Int.le_of_dvd hpos hdvd'
    linarith
  have he1 : (1 : ℝ) ≤ |((u * d - z * (r : ℤ) : ℤ) : ℝ)| := by
    have h : ((1 : ℤ) : ℝ) ≤ ((|u * d - z * (r : ℤ)| : ℤ) : ℝ) :=
      Int.cast_le.mpr (Int.one_le_abs he)
    rw [Int.cast_one, Int.cast_abs] at h
    exact h
  -- `u d - z r = r (α d - z) - r β d`
  have hur : (u : ℝ) / (r : ℝ) * (r : ℝ) = (u : ℝ) := div_mul_cancel₀ _ hrpos.ne'
  have hid : ((u * d - z * (r : ℤ) : ℤ) : ℝ) =
      (r : ℝ) * (α * (d : ℝ) - (z : ℝ)) - (r : ℝ) * (β * (d : ℝ)) := by
    rw [hα]
    push_cast
    linear_combination (-(d : ℝ)) * hur
  -- `2 r |β d| ≤ 1`
  have hβ' : |β| * (r : ℝ) ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hβ (sq_nonneg (r : ℝ))
    rwa [inv_mul_cancel₀ (pow_ne_zero 2 hrpos.ne')] at h
  have hd' : 2 * |(d : ℝ)| ≤ (r : ℝ) := by
    have h : ((2 * |d| : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) := Int.cast_le.mpr hdr
    push_cast at h
    exact h
  have hβd : 2 * ((r : ℝ) * (|β| * |(d : ℝ)|)) ≤ 1 := by
    have h1 : (r : ℝ) * |β| * (2 * |(d : ℝ)|) ≤ (r : ℝ) * |β| * (r : ℝ) :=
      mul_le_mul_of_nonneg_left hd' (mul_nonneg hrpos.le (abs_nonneg β))
    nlinarith
  by_contra hcon
  rw [not_le] at hcon
  have habs1 : |(r : ℝ) * (α * (d : ℝ) - (z : ℝ))| = (r : ℝ) * |α * (d : ℝ) - (z : ℝ)| := by
    rw [abs_mul, abs_of_pos hrpos]
  have habs2 : |(r : ℝ) * (β * (d : ℝ))| = (r : ℝ) * (|β| * |(d : ℝ)|) := by
    rw [abs_mul, abs_mul, abs_of_pos hrpos]
  have h1 : |((u * d - z * (r : ℤ) : ℤ) : ℝ)| ≤
      |(r : ℝ) * (α * (d : ℝ) - (z : ℝ))| + |(r : ℝ) * (β * (d : ℝ))| := by
    rw [hid]
    exact abs_sub _ _
  rw [habs1, habs2] at h1
  linarith

/-! ### Separated phases lie in distinct arcs -/

/-- The arc of a phase `θ` among the `2r` arcs of length `1/(2r)`: `⌊2 r {θ}⌋`. -/
def bin (r : ℕ) (θ : ℝ) : ℕ := ⌊2 * (r : ℝ) * Int.fract θ⌋₊

theorem bin_le (r : ℕ) (θ : ℝ) : (bin r θ : ℝ) ≤ 2 * (r : ℝ) * Int.fract θ := by
  unfold bin
  exact Nat.floor_le
    (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg r)) (Int.fract_nonneg θ))

theorem lt_bin_add_one (r : ℕ) (θ : ℝ) : 2 * (r : ℝ) * Int.fract θ < (bin r θ : ℝ) + 1 := by
  unfold bin
  exact Nat.lt_floor_add_one _

/-- Two phases which are `1/(2r)`-separated modulo `1` lie in different arcs. -/
theorem bin_ne_of_sep {r : ℕ} {θ θ' : ℝ}
    (hsep : ∀ z : ℤ, 1 ≤ 2 * (r : ℝ) * |θ - θ' - (z : ℝ)|) : bin r θ ≠ bin r θ' := by
  intro heq
  have h1 := bin_le r θ
  have h2 := lt_bin_add_one r θ
  have h3 := bin_le r θ'
  have h4 := lt_bin_add_one r θ'
  rw [heq] at h1 h2
  have hz := hsep (⌊θ⌋ - ⌊θ'⌋)
  have hfr : θ - θ' - ((⌊θ⌋ - ⌊θ'⌋ : ℤ) : ℝ) = Int.fract θ - Int.fract θ' := by
    rw [← Int.self_sub_floor θ, ← Int.self_sub_floor θ']
    push_cast
    ring
  rw [hfr] at hz
  have h5 : |2 * (r : ℝ) * Int.fract θ - 2 * (r : ℝ) * Int.fract θ'| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have h6 : 2 * (r : ℝ) * Int.fract θ - 2 * (r : ℝ) * Int.fract θ' =
      2 * (r : ℝ) * (Int.fract θ - Int.fract θ') := by ring
  rw [h6, abs_mul, abs_of_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg r))] at h5
  linarith

/-- **The contribution of a block.** If the phases `θ j`, `j ∈ P`, are pairwise
`1/(2r)`-separated modulo `1`, then values `Φ j ≤ L` with `Φ j ≤ 1 / (2 x_j (1 - x_j))`, `x_j` the
fractional part of `θ j`, add up to at most twice the sum of the weights of all `2r` arcs. -/
theorem sum_le_of_sep {r : ℕ} (hr : 0 < r) {L : ℝ} (hL : 0 ≤ L) (P : Finset ℕ) (θ Φ : ℕ → ℝ)
    (hΦ0 : ∀ j ∈ P, 0 ≤ Φ j) (hΦL : ∀ j ∈ P, Φ j ≤ L)
    (hΦx : ∀ j ∈ P, Φ j * (2 * (Int.fract (θ j) * (1 - Int.fract (θ j)))) ≤ 1)
    (hsep : ∀ j ∈ P, ∀ j' ∈ P, j ≠ j' →
      ∀ z : ℤ, 1 ≤ 2 * (r : ℝ) * |θ j - θ j' - (z : ℝ)|) :
    ∑ j ∈ P, Φ j ≤ 2 * ∑ m ∈ Finset.range (2 * r), binWeight L r m := by
  have hinj : Set.InjOn (fun j => bin r (θ j)) (P : Set ℕ) := by
    intro j hj j' hj' heq
    by_contra hne
    exact bin_ne_of_sep (hsep j (Finset.mem_coe.mp hj) j' (Finset.mem_coe.mp hj') hne) heq
  have hpt : ∀ j ∈ P, bin r (θ j) < 2 * r ∧
      Φ j ≤ binWeight L r (bin r (θ j)) + binWeight L r (2 * r - 1 - bin r (θ j)) :=
    fun j hj => le_binWeight_add hr (hΦ0 j hj) (hΦL j hj) (Int.fract_lt_one (θ j)) (hΦx j hj)
      (bin_le r (θ j)) (lt_bin_add_one r (θ j))
  have hsub : P.image (fun j => bin r (θ j)) ⊆ Finset.range (2 * r) := by
    rw [Finset.image_subset_iff]
    intro j hj
    exact Finset.mem_range.mpr (hpt j hj).1
  have hw0 : ∀ m : ℕ, 0 ≤ binWeight L r m := fun m => binWeight_nonneg hL r m
  have hA : ∑ j ∈ P, binWeight L r (bin r (θ j)) ≤
      ∑ m ∈ Finset.range (2 * r), binWeight L r m := by
    calc ∑ j ∈ P, binWeight L r (bin r (θ j))
        = ∑ m ∈ P.image (fun j => bin r (θ j)), binWeight L r m :=
          (Finset.sum_image (f := fun m => binWeight L r m) hinj).symm
      _ ≤ ∑ m ∈ Finset.range (2 * r), binWeight L r m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hw0 m
  have hB : ∑ j ∈ P, binWeight L r (2 * r - 1 - bin r (θ j)) ≤
      ∑ m ∈ Finset.range (2 * r), binWeight L r m := by
    calc ∑ j ∈ P, binWeight L r (2 * r - 1 - bin r (θ j))
        = ∑ m ∈ P.image (fun j => bin r (θ j)), binWeight L r (2 * r - 1 - m) :=
          (Finset.sum_image (f := fun m => binWeight L r (2 * r - 1 - m)) hinj).symm
      _ ≤ ∑ m ∈ Finset.range (2 * r), binWeight L r (2 * r - 1 - m) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hw0 _
      _ = ∑ m ∈ Finset.range (2 * r), binWeight L r m :=
          Finset.sum_range_reflect (fun m => binWeight L r m) (2 * r)
  calc ∑ j ∈ P, Φ j
      ≤ ∑ j ∈ P, (binWeight L r (bin r (θ j)) + binWeight L r (2 * r - 1 - bin r (θ j))) :=
        Finset.sum_le_sum fun j hj => (hpt j hj).2
    _ = ∑ j ∈ P, binWeight L r (bin r (θ j)) +
          ∑ j ∈ P, binWeight L r (2 * r - 1 - bin r (θ j)) := Finset.sum_add_distrib
    _ ≤ 2 * ∑ m ∈ Finset.range (2 * r), binWeight L r m := by linarith

/-! ### Row sums -/

/-- **Row sums of the geometric kernel.** For `α = u/r + β` as in Lemma 4.2, a set `t` of integers
in `[T, T + D]`, a block length `q` with `2(q - 1) ≤ r`, and any real `c`,
`∑_{k ∈ t} |∑_{N ≤ n < N + L} e(α (k - c) n)|` is at most the number `⌊D/q⌋ + 1` of blocks times
twice the sum of all arc weights. -/
theorem sum_geomKernel_le {α β : ℝ} {u : ℤ} {r : ℕ} (hr : 0 < r) (hcop : IsCoprime u (r : ℤ))
    (hα : α = (u : ℝ) / (r : ℝ) + β) (hβ : |β| ≤ ((r : ℝ) ^ 2)⁻¹) {q : ℕ} (hq0 : 0 < q)
    (hqr : 2 * (q - 1) ≤ r) (N L T D : ℕ) (t : Finset ℕ)
    (ht : ∀ k ∈ t, T ≤ k ∧ k ≤ T + D) (c : ℝ) :
    ∑ k ∈ t, geomKernel N L (α * ((k : ℝ) - c)) ≤
      ((D / q + 1 : ℕ) : ℝ) * (2 * ∑ m ∈ Finset.range (2 * r), binWeight (L : ℝ) r m) := by
  have hmaps : ∀ k ∈ t, (k - T) / q ∈ Finset.range (D / q + 1) := by
    intro k hk
    have h1 : k - T ≤ D := by
      have h := (ht k hk).2
      omega
    exact Finset.mem_range.mpr (Nat.lt_add_one_of_le (Nat.div_le_div_right h1))
  have hblock : ∀ j ∈ Finset.range (D / q + 1),
      ∑ k ∈ t.filter (fun k => (k - T) / q = j), geomKernel N L (α * ((k : ℝ) - c)) ≤
        2 * ∑ m ∈ Finset.range (2 * r), binWeight (L : ℝ) r m := by
    intro j _
    refine sum_le_of_sep hr (Nat.cast_nonneg L) (t.filter (fun k => (k - T) / q = j))
      (fun k => α * ((k : ℝ) - c)) (fun k => geomKernel N L (α * ((k : ℝ) - c)))
      (fun k _ => geomKernel_nonneg N L _) (fun k _ => geomKernel_le N L _)
      (fun k _ => geomKernel_mul_fract_le N L _) ?_
    intro k hk k' hk' hne z
    obtain ⟨hkt, hkj⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkt', hkj'⟩ := Finset.mem_filter.mp hk'
    have hT := (ht k hkt).1
    have hT' := (ht k' hkt').1
    have e1 := Nat.div_add_mod (k - T) q
    have e2 := Nat.mod_lt (k - T) hq0
    have e1' := Nat.div_add_mod (k' - T) q
    have e2' := Nat.mod_lt (k' - T) hq0
    rw [hkj] at e1
    rw [hkj'] at e1'
    have hd : (k : ℤ) - (k' : ℤ) ≠ 0 := by omega
    have h1 : 2 * ((k : ℤ) - (k' : ℤ)) ≤ (r : ℤ) := by omega
    have h2 : 2 * ((k' : ℤ) - (k : ℤ)) ≤ (r : ℤ) := by omega
    have hdr : 2 * |(k : ℤ) - (k' : ℤ)| ≤ (r : ℤ) := by
      have h3 : |2 * ((k : ℤ) - (k' : ℤ))| ≤ (r : ℤ) := abs_le.mpr ⟨by linarith, h1⟩
      rwa [abs_mul, abs_two] at h3
    have hsep := sep_of_coprime hr hcop hα hβ hd hdr z
    have hθ : α * (((k : ℤ) - (k' : ℤ) : ℤ) : ℝ) - (z : ℝ) =
        α * ((k : ℝ) - c) - α * ((k' : ℝ) - c) - (z : ℝ) := by
      push_cast
      ring
    rw [hθ] at hsep
    exact hsep
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine (Finset.sum_le_sum hblock).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Bilinear

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
