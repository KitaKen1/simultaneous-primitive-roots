module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.ChainSteps
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.HistorySkeleton
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The residue factors of one prime from a visit on

Source: `verification/stage7-sources/S-02.tex`, lines 327–334 and 538–567
(`[S-02:0327–0334, 0538–0567]`).

Tools for the proof of (M4) `ChainLifespan`. For a skeleton `sk`, a natural number `p` and a
residue `t ∈ ℤ/pℤ` at the visit `0`:

* `Skel.resF sk p i t` — the factor of the visit `i` in the residue expectation `Skel.onePrimeExp`:
  `1_{t + h_i = 0}` if `p` is active at the visit `i`, and `q_i^{1_{t + h_i = 0}}` otherwise;
* `Skel.tailF sk p i t` — the product of these factors over the visits `i, …, N`
  (`Skel.onePrimeExp_eq_tail`: `onePrimeExp p = p⁻¹ ∑_t tailF p 0 t`);
* `Skel.tailF_act`, `Skel.sum_tailF_act`, `Skel.tailF_inact`, `Skel.sum_tailF_inact` — one step of
  the product, for an active and for an inactive visit;
* `Skel.nv sk p i` — `1` if `p` is not active at any visit `≥ i`, `0` otherwise;
* `chnEta D i = ∑_{j < i} η_j`;
* `chn_alg_*` — the identities between real numbers which the backward induction uses.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### A sum over the residues -/

/-- `∑_t 1_{t + h = 0} c = c`. -/
theorem chn_sum_ite_add {p : ℕ} (h : Res p) (c : ℝ) :
    ∑ t : Res p, (if t + h = 0 then c else 0) = c := by
  rw [Finset.sum_eq_single (-h)]
  · exact if_pos (neg_add_cancel h)
  · intro t _ ht
    exact if_neg fun h0 => ht (eq_neg_of_add_eq_zero_left h0)
  · intro h0
    exact absurd (Finset.mem_univ _) h0

/-! ### Identities between real numbers -/

/-- A pending zero at a visit: it terminates (`-η/ρ`) or continues (`q/ρ²`). -/
theorem chn_alg_pend_zero {ρ q Z T n : ℝ} (hρ : ρ ≠ 0) :
    Graph.sourceGhostD q ρ * n + Graph.sourceGhostA q ρ * (ρ * (Z * T - n)) =
      ρ⁻¹ * (Z * (q * T) - n) := by
  have h : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ
  unfold Graph.sourceGhostD Graph.sourceGhostA
  linear_combination (q * ρ⁻¹ * (Z * T - n)) * h

/-- The last visit: a pending zero must terminate. -/
theorem chn_alg_pend_last (ρ q : ℝ) :
    Graph.sourceGhostD q ρ * 1 + Graph.sourceGhostA q ρ * 0 = ρ⁻¹ * (1 * (q * 1) - 1) := by
  unfold Graph.sourceGhostD Graph.sourceGhostA
  ring

/-- An unborn prime at a visit: it stays unborn or has a ghost birth. -/
theorem chn_alg_unborn {ρ q η V pp b μ Z Sg T n s : ℝ} (hρ : ρ ≠ 0) (hV : V ≠ 0)
    (hη : η = 1 - q) (hμ : μ = 1 / (V * pp * b)) :
    (Z * Sg - n * (s + η)) / (pp * b) + Graph.sourceGhostC V q ρ * μ * (ρ * (Z * T - n)) =
      (Z * (Sg - η * T) - n * s) / (pp * b) := by
  have h : V * V⁻¹ * (ρ⁻¹ * ρ) = 1 := by
    rw [mul_inv_cancel₀ hV, inv_mul_cancel₀ hρ, one_mul]
  subst hη hμ
  unfold Graph.sourceGhostC Graph.sourceGhostD
  linear_combination (-(1 - q) * (Z * T - n) * (pp * b)⁻¹) * h

/-- An unborn prime which is born in an unshared target slot of the next edge. -/
theorem chn_alg_unborn_birth {V pp b μ Z Sg η s c : ℝ} (hμ : μ = 1 / (V * pp * b)) :
    μ * (Z * Sg) + c * μ * 0 = (V⁻¹ * Z * (Sg - η * 0) - 0 * s) / (pp * b) := by
  subst hμ
  ring

/-- The last visit: an unborn prime has the value `1`. -/
theorem chn_alg_base {pp b η s : ℝ} (hp : pp ≠ 0) (hb : b ≠ 0) (hbdef : b = 1 - (s + η) / pp) :
    (1 * (pp - η * 1) - 1 * s) / (pp * b) = 1 := by
  have hpp : pp * pp⁻¹ = 1 := mul_inv_cancel₀ hp
  rw [div_eq_one_iff_eq (mul_ne_zero hp hb)]
  subst hbdef
  linear_combination (s + η) * hpp

/-- The visit `0`, an initial label: `μ̃ · act = V⁻¹ · Z · lifeSum`. -/
theorem chn_alg_final_act {V pp b Z L : ℝ} (hp : pp ≠ 0) (hb : b ≠ 0) :
    1 / (V * pp * b) * (Z * (pp * (b * L))) = V⁻¹ * Z * L := by
  have h : pp⁻¹ * pp * (b⁻¹ * b) = 1 := by
    rw [inv_mul_cancel₀ hp, inv_mul_cancel₀ hb, one_mul]
  linear_combination (V⁻¹ * Z * L) * h

/-- The visit `0`, an unborn prime: `unborn = Z · lifeSum`. -/
theorem chn_alg_final_unborn {pp b Z L n : ℝ} (hp : pp ≠ 0) (hb : b ≠ 0) :
    (Z * (pp * (b * L)) - n * 0) / (pp * b) = Z * L := by
  have h : pp * b * (pp * b)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero hp hb)
  linear_combination (Z * L) * h

variable {S B : Type} [Fintype S] [Fintype B] {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type}
  {D : MemData 𝒢 J ℓ N}

/-! ### The sums of the coefficients `η` -/

/-- `∑_{j < i} η_j`. -/
def chnEta (D : MemData 𝒢 J ℓ N) (i : ℕ) : ℝ := ∑ j ∈ Finset.range i, visitEta D.q D.n j

omit [Fintype S] [Fintype B] in
theorem chnEta_zero (D : MemData 𝒢 J ℓ N) : chnEta D 0 = 0 := Finset.sum_range_zero _

omit [Fintype S] [Fintype B] in
theorem chnEta_succ (D : MemData 𝒢 J ℓ N) (i : ℕ) :
    chnEta D (i + 1) = chnEta D i + visitEta D.q D.n i := Finset.sum_range_succ _ _

omit [Fintype S] [Fintype B] in
theorem lifeBaseline_eq_chnEta (D : MemData 𝒢 J ℓ N) (p : ℕ) :
    lifeBaseline D.q D.n p = 1 - (chnEta D D.n + visitEta D.q D.n D.n) / (p : ℝ) := by
  rw [← chnEta_succ]
  rfl

/-! ### The factors of the visits -/

/-- The factor of the visit `i` in the residue expectation of `p`, for the residue `t` at the
visit `0`: `1_{t + h_i = 0}` if `p` is active at the visit `i`, `q_i^{1_{t + h_i = 0}}`
otherwise. -/
def Skel.resF (sk : Skel D) (p i : ℕ) (t : Res p) : ℝ :=
  if i ∈ sk.activeVisits p then
    (if t + ((sk.off i : ℤ) : Res p) = 0 then (1 : ℝ) else 0)
  else (if t + ((sk.off i : ℤ) : Res p) = 0 then visitQ D.q D.n i else 1)

/-- The product of the factors of the visits `i, …, N`. -/
def Skel.tailF (sk : Skel D) (p i : ℕ) (t : Res p) : ℝ :=
  ∏ j ∈ Finset.Ico i (D.n + 1), sk.resF p j t

/-- The residue expectation of one prime is the mean of the product of all factors. -/
theorem Skel.onePrimeExp_eq_tail (sk : Skel D) (p : ℕ) :
    sk.onePrimeExp p = (p : ℝ)⁻¹ * ∑ t : Res p, sk.tailF p 0 t := by
  have h : ∀ t : Res p, (∏ i ∈ Finset.range (D.n + 1), sk.resF p i t) = sk.tailF p 0 t := by
    intro t
    unfold Skel.tailF
    rw [Finset.range_eq_Ico]
  exact congrArg (fun x => (p : ℝ)⁻¹ * x) (Finset.sum_congr rfl fun t _ => h t)

theorem Skel.tailF_succ (sk : Skel D) (p i : ℕ) (hi : i ≤ D.n) (t : Res p) :
    sk.tailF p i t = sk.resF p i t * sk.tailF p (i + 1) t := by
  unfold Skel.tailF
  exact Finset.prod_eq_prod_Ico_succ_bot (Nat.lt_succ_of_le hi) _

theorem Skel.tailF_last (sk : Skel D) (p : ℕ) (t : Res p) : sk.tailF p (D.n + 1) t = 1 := by
  unfold Skel.tailF
  rw [Finset.Ico_self, Finset.prod_empty]

/-- An active visit: the product vanishes unless `t = -h_i`. -/
theorem Skel.tailF_act (sk : Skel D) (p i : ℕ) (hi : i ≤ D.n) (h : i ∈ sk.activeVisits p)
    (t : Res p) :
    sk.tailF p i t =
      if t + ((sk.off i : ℤ) : Res p) = 0 then
        sk.tailF p (i + 1) (-((sk.off i : ℤ) : Res p))
      else 0 := by
  rw [sk.tailF_succ p i hi t]
  unfold Skel.resF
  rw [if_pos h]
  by_cases ht : t + ((sk.off i : ℤ) : Res p) = 0
  · rw [if_pos ht, if_pos ht, one_mul, eq_neg_of_add_eq_zero_left ht]
  · rw [if_neg ht, if_neg ht, zero_mul]

/-- An active visit: the sum over the residues is the product from the next visit on at
`t = -h_i`. -/
theorem Skel.sum_tailF_act (sk : Skel D) (p i : ℕ) (hi : i ≤ D.n)
    (h : i ∈ sk.activeVisits p) :
    ∑ t : Res p, sk.tailF p i t = sk.tailF p (i + 1) (-((sk.off i : ℤ) : Res p)) := by
  rw [Finset.sum_congr rfl fun t _ => sk.tailF_act p i hi h t]
  exact chn_sum_ite_add _ _

/-- An inactive visit: the factor `q_i^{1_{t + h_i = 0}}`. -/
theorem Skel.tailF_inact (sk : Skel D) (p i : ℕ) (hi : i ≤ D.n) (h : i ∉ sk.activeVisits p)
    (t : Res p) :
    sk.tailF p i t =
      (if t + ((sk.off i : ℤ) : Res p) = 0 then visitQ D.q D.n i else 1) *
        sk.tailF p (i + 1) t := by
  rw [sk.tailF_succ p i hi t]
  unfold Skel.resF
  rw [if_neg h]

/-- An inactive visit: `∑_t ∏_{j ≥ i} = ∑_t ∏_{j > i} - η_i ∏_{j > i}(-h_i)`. -/
theorem Skel.sum_tailF_inact (sk : Skel D) (p i : ℕ) (hi : i ≤ D.n)
    (h : i ∉ sk.activeVisits p) :
    ∑ t : Res p, sk.tailF p i t =
      ∑ t : Res p, sk.tailF p (i + 1) t -
        visitEta D.q D.n i * sk.tailF p (i + 1) (-((sk.off i : ℤ) : Res p)) := by
  have hpt : ∀ t : Res p, sk.tailF p i t = sk.tailF p (i + 1) t -
      (if t + ((sk.off i : ℤ) : Res p) = 0 then
        visitEta D.q D.n i * sk.tailF p (i + 1) (-((sk.off i : ℤ) : Res p)) else 0) := by
    intro t
    rw [sk.tailF_inact p i hi h t]
    by_cases ht : t + ((sk.off i : ℤ) : Res p) = 0
    · rw [if_pos ht, if_pos ht, ← eq_neg_of_add_eq_zero_left ht]
      unfold visitEta
      ring
    · rw [if_neg ht, if_neg ht, one_mul, sub_zero]
  rw [Finset.sum_congr rfl fun t _ => hpt t, Finset.sum_sub_distrib, chn_sum_ite_add]

/-! ### The active visits -/

omit [Fintype S] in
theorem Skel.mem_activeVisits (sk : Skel D) (p i : ℕ) :
    i ∈ sk.activeVisits p ↔ i < D.n + 1 ∧ ∃ g sl, ((sk.lists i).2 g sl : ℕ) = p := by
  unfold Skel.activeVisits
  rw [Finset.mem_filter, Finset.mem_range]

open _root_.Classical in
/-- `1` if `p` is not active at any visit `t ≥ i`, and `0` otherwise. -/
def Skel.nv (sk : Skel D) (p i : ℕ) : ℝ := if ∀ t, i ≤ t → t ∉ sk.activeVisits p then 1 else 0

omit [Fintype S] in
theorem Skel.nv_of_mem (sk : Skel D) (p i j : ℕ) (hij : i ≤ j) (h : j ∈ sk.activeVisits p) :
    sk.nv p i = 0 :=
  if_neg fun hall => hall j hij h

omit [Fintype S] in
theorem Skel.nv_succ (sk : Skel D) (p i : ℕ) (h : i ∉ sk.activeVisits p) :
    sk.nv p i = sk.nv p (i + 1) := by
  by_cases hall : ∀ t, i + 1 ≤ t → t ∉ sk.activeVisits p
  · have hall' : ∀ t, i ≤ t → t ∉ sk.activeVisits p := by
      intro t ht
      rcases Nat.eq_or_lt_of_le ht with rfl | hlt
      · exact h
      · exact hall t hlt
    exact (if_pos hall').trans (if_pos hall).symm
  · have hall' : ¬∀ t, i ≤ t → t ∉ sk.activeVisits p := fun h' =>
      hall fun t ht => h' t (Nat.le_of_succ_le ht)
    exact (if_neg hall').trans (if_neg hall).symm

omit [Fintype S] in
theorem Skel.nv_last (sk : Skel D) (p : ℕ) (h : D.n ∉ sk.activeVisits p) : sk.nv p D.n = 1 := by
  refine if_pos fun t ht hmem => ?_
  have hlt : t < D.n + 1 := ((sk.mem_activeVisits p t).mp hmem).1
  have ht' : t = D.n := le_antisymm (Nat.lt_succ_iff.mp hlt) ht
  rw [ht'] at hmem
  exact h hmem

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
