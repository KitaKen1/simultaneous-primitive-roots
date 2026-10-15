module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.History
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ReturnFourier
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemPerm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Fourier representation of the block constraints

Source: `verification/stage7-sources/S-02.tex`, lines 1172–1191 (`[S-02:1172–1191]`).

"For a block with pivot `β₀` and other addresses `β₁, …, β_{h-1}`, equality of the integer prime
values has the exact representation
`1_{p_{β_j} = p_{β_0} (1 ≤ j < h)} = ∫_{[0,1]^{h-1}} e(∑_j τ_j (p_{β_j} - p_{β_0})) dτ`
on paths performing all these addresses. For fixed Fourier parameters, collect the factors by their
birth operation. Each affected operation is multiplied, on its individual local choices, by
`1_{designated local births are performed} e(∑_{β local} c_β p_β)`, of modulus at most one."

This file proves the representation in a finite form, for an arbitrary finite set `A` of
addresses, a collection `π` of blocks and an assignment `birth : A → Option ℕ` whose performed
values are smaller than `Q`:

`∑_t ∏_β m^t_β(birth β) = #{t} · 1_{𝒞_π}` (`sum_prod_addrMult`),

where `t` runs over the Fourier parameters `t_{β β'} ∈ ℤ/Q`, one for every ordered pair of
addresses, and `m^t_β` (`addrMult`) is a function of the birth at the single address `β`, of
modulus at most one (`norm_addrMult_le`), which is `1` when `β` is in no block
(`addrMult_of_notMem`):

* `m^t_β(not performed) = 0` for `β` in a block, and
* `m^t_β(p) = ∏_{β' in the block of β} e((t_{ββ'} - t_{β'β}) p / Q)`.

Instead of a pivot in each block, every ordered pair `(β, β')` of addresses of a common block
carries the factor `1_{p_β = p_{β'}} = Q⁻¹ ∑_{t < Q} e(t (p_β - p_{β'}) / Q)`
(`sum_expUnit_range`, for integers `|p_β - p_{β'}| < Q`); the product over all pairs is the
indicator that the values are constant on every block. The average over the parameters `t` is a
finite average in place of the integral over `[0,1]^{h-1}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

theorem expUnit_mul' (a b : ℝ) : expUnit a * expUnit b = expUnit (a + b) := by
  unfold expUnit
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `∑_{j < Q} e(j v / Q) e(-j v' / Q) = Q · 1_{v = v'}` for natural numbers `v, v' < Q`, with a
condition `R` under which the two phases are present. -/
theorem sum_fin_expUnit_pair (Q : ℕ) (hQ : 0 < Q) (R : Prop) [Decidable R] (v v' : ℕ)
    (hv : v < Q) (hv' : v' < Q) :
    ∑ j : Fin Q, (if R then expUnit ((j.val : ℝ) / (Q : ℝ) * (v : ℝ)) else 1) *
        (if R then expUnit (-((j.val : ℝ) / (Q : ℝ) * (v' : ℝ))) else 1) =
      (Q : ℂ) * (if R → v = v' then 1 else 0) := by
  by_cases hR : R
  · have hterm : ∀ j : Fin Q,
        (if R then expUnit ((j.val : ℝ) / (Q : ℝ) * (v : ℝ)) else 1) *
            (if R then expUnit (-((j.val : ℝ) / (Q : ℝ) * (v' : ℝ))) else 1) =
          expUnit ((j.val : ℝ) / (Q : ℝ) * (((v : ℤ) - (v' : ℤ) : ℤ) : ℝ)) := by
      intro j
      rw [if_pos hR, if_pos hR, expUnit_mul']
      congr 1
      push_cast
      ring
    have hrange := sum_expUnit_range Q hQ ((v : ℤ) - (v' : ℤ))
      (fun h0 hdvd => h0 (Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by omega, by omega⟩)))
    have hfin : ∑ j : Fin Q, expUnit ((j.val : ℝ) / (Q : ℝ) * (((v : ℤ) - (v' : ℤ) : ℤ) : ℝ)) =
        ∑ j ∈ Finset.range Q, expUnit ((j : ℝ) / (Q : ℝ) * (((v : ℤ) - (v' : ℤ) : ℤ) : ℝ)) :=
      (Finset.sum_range
        (fun j : ℕ => expUnit ((j : ℝ) / (Q : ℝ) * (((v : ℤ) - (v' : ℤ) : ℤ) : ℝ)))).symm
    rw [Finset.sum_congr rfl fun j _ => hterm j, hfin, hrange]
    by_cases hvv : v = v'
    · have h1 : (v : ℤ) - (v' : ℤ) = 0 := by omega
      have h2 : R → v = v' := fun _ => hvv
      rw [if_pos h1, if_pos h2, mul_one]
    · have h1 : ¬((v : ℤ) - (v' : ℤ) = 0) := by omega
      have h2 : ¬(R → v = v') := fun h => hvv (h hR)
      rw [if_neg h1, if_neg h2, mul_zero]
  · have hterm : ∀ j : Fin Q,
        (if R then expUnit ((j.val : ℝ) / (Q : ℝ) * (v : ℝ)) else 1) *
            (if R then expUnit (-((j.val : ℝ) / (Q : ℝ) * (v' : ℝ))) else 1) = 1 := by
      intro j
      rw [if_neg hR, if_neg hR, one_mul]
    have h2 : R → v = v' := fun h => absurd h hR
    rw [Finset.sum_congr rfl fun j _ => hterm j, if_pos h2, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

section Fourier

variable {A : Type}

/-- Two addresses lie in a common block of the collection `π`. -/
def SameBlock (π : Finset (Finset A)) (β β' : A) : Prop := ∃ b ∈ π, β ∈ b ∧ β' ∈ b

variable [DecidableEq A]

instance SameBlock.instDecidable (π : Finset (Finset A)) (β β' : A) :
    Decidable (SameBlock π β β') :=
  inferInstanceAs (Decidable (∃ b ∈ π, β ∈ b ∧ β' ∈ b))

theorem not_sameBlock_left {π : Finset (Finset A)} {β : A} (hβ : β ∉ π.biUnion id) (β' : A) :
    ¬SameBlock π β β' := by
  intro h
  obtain ⟨b, hb, hβb, -⟩ := h
  exact hβ (Finset.mem_biUnion.mpr ⟨b, hb, hβb⟩)

theorem not_sameBlock_right {π : Finset (Finset A)} {β : A} (hβ : β ∉ π.biUnion id) (β' : A) :
    ¬SameBlock π β' β := by
  intro h
  obtain ⟨b, hb, -, hβb⟩ := h
  exact hβ (Finset.mem_biUnion.mpr ⟨b, hb, hβb⟩)

/-- A collection of rank `r` involves at most `2r` addresses [S-02:1095]. -/
theorem card_biUnion_le_two_mul_blockRank [Fintype A] {π : Finset (Finset A)}
    (hπ : π ∈ blockCollections A) : (π.biUnion id).card ≤ 2 * blockRank π := by
  have h2 := (mem_blockCollections.mp hπ).1
  calc (π.biUnion id).card ≤ ∑ b ∈ π, b.card := Finset.card_biUnion_le
    _ ≤ ∑ b ∈ π, 2 * (b.card - 1) := Finset.sum_le_sum fun b hb => by
        have := h2 b hb
        omega
    _ = 2 * blockRank π := by
        unfold blockRank
        rw [Finset.mul_sum]

variable [Fintype A]

/-- **The Fourier multiplier of the address `β`**, for the parameters `t`: a function of the birth
at `β` (the prime `p` if the address is performed). For a performed address it is the product of
the phases `e(t_{ββ'} p / Q) e(-t_{β'β} p / Q)` over the addresses `β'` of the block of `β`; for an
address which is not performed it is `0` if `β` is in a block and `1` otherwise. -/
def addrMult (π : Finset (Finset A)) (Q : ℕ) (t : A × A → Fin Q) (β : A) : Option ℕ → ℂ
  | some p => ∏ β' : A,
      (if SameBlock π β β' then expUnit (((t (β, β')).val : ℝ) / (Q : ℝ) * (p : ℝ)) else 1) *
        (if SameBlock π β' β then expUnit (-(((t (β', β)).val : ℝ) / (Q : ℝ) * (p : ℝ)))
          else 1)
  | none => if β ∈ π.biUnion id then 0 else 1

theorem addrMult_some (π : Finset (Finset A)) (Q : ℕ) (t : A × A → Fin Q) (β : A) (p : ℕ) :
    addrMult π Q t β (some p) = ∏ β' : A,
      (if SameBlock π β β' then expUnit (((t (β, β')).val : ℝ) / (Q : ℝ) * (p : ℝ)) else 1) *
        (if SameBlock π β' β then expUnit (-(((t (β', β)).val : ℝ) / (Q : ℝ) * (p : ℝ)))
          else 1) := rfl

theorem addrMult_none (π : Finset (Finset A)) (Q : ℕ) (t : A × A → Fin Q) (β : A) :
    addrMult π Q t β none = if β ∈ π.biUnion id then 0 else 1 := rfl

/-- The Fourier multipliers have modulus at most one. -/
theorem norm_addrMult_le (π : Finset (Finset A)) (Q : ℕ) (t : A × A → Fin Q) (β : A)
    (o : Option ℕ) : ‖addrMult π Q t β o‖ ≤ 1 := by
  cases o with
  | none =>
    rw [addrMult_none]
    split_ifs
    · exact (norm_zero : ‖(0 : ℂ)‖ = 0).trans_le zero_le_one
    · exact le_of_eq norm_one
  | some p =>
    rw [addrMult_some, norm_prod]
    refine Finset.prod_le_one (fun β' _ => norm_nonneg _) (fun β' _ => ?_)
    rw [norm_mul]
    have h1 : ‖(if SameBlock π β β' then
        expUnit (((t (β, β')).val : ℝ) / (Q : ℝ) * (p : ℝ)) else (1 : ℂ))‖ ≤ 1 := by
      split_ifs
      · exact le_of_eq (norm_expUnit _)
      · exact le_of_eq norm_one
    have h2 : ‖(if SameBlock π β' β then
        expUnit (-(((t (β', β)).val : ℝ) / (Q : ℝ) * (p : ℝ))) else (1 : ℂ))‖ ≤ 1 := by
      split_ifs
      · exact le_of_eq (norm_expUnit _)
      · exact le_of_eq norm_one
    exact (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The Fourier multiplier of an address which is in no block is `1`. -/
theorem addrMult_of_notMem (π : Finset (Finset A)) (Q : ℕ) (t : A × A → Fin Q) {β : A}
    (hβ : β ∉ π.biUnion id) (o : Option ℕ) : addrMult π Q t β o = 1 := by
  cases o with
  | none =>
    rw [addrMult_none]
    exact if_neg hβ
  | some p =>
    rw [addrMult_some]
    refine Finset.prod_eq_one fun β' _ => ?_
    rw [if_neg (not_sameBlock_left hβ β'), if_neg (not_sameBlock_right hβ β'),
      one_mul]

omit [DecidableEq A] in
/-- Regrouping a double product: the factor `g β' β` of the pair `(β, β')` is moved to the pair
`(β', β)`. -/
theorem prod_prod_swap_mul (f g : A → A → ℂ) :
    ∏ β, ∏ β', (f β β' * g β' β) = ∏ x : A × A, (f x.1 x.2 * g x.1 x.2) := by
  have h1 : ∏ β, ∏ β', (f β β' * g β' β) = (∏ β, ∏ β', f β β') * ∏ β, ∏ β', g β' β := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun β _ => Finset.prod_mul_distrib
  have h2 : ∏ β, ∏ β', g β' β = ∏ β, ∏ β', g β β' := Finset.prod_comm
  have h3 : ∏ x : A × A, (f x.1 x.2 * g x.1 x.2) = ∏ β, ∏ β', (f β β' * g β β') :=
    Fintype.prod_prod_type' fun β β' => f β β' * g β β'
  have h4 : ∏ β, ∏ β', (f β β' * g β β') = (∏ β, ∏ β', f β β') * ∏ β, ∏ β', g β β' := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun β _ => Finset.prod_mul_distrib
  rw [h1, h2, h3, h4]

/-- **The Fourier representation of the constraint `𝒞_π`** (eq:birth-equality-fourier)
[S-02:1172–1178]: for an assignment `birth` whose performed values are smaller than `Q`, the sum
over the Fourier parameters `t` of the products of the multipliers of all addresses is the number
of parameters times the indicator of `𝒞_π` (for an arbitrary decidability instance of
`𝒞_π`). -/
theorem sum_prod_addrMult (π : Finset (Finset A)) (hπ : π ∈ blockCollections A) (Q : ℕ)
    (hQ : 0 < Q) (birth : A → Option ℕ) (hlt : ∀ β p, birth β = some p → p < Q)
    [Decidable (BlockConstraint birth π)] :
    ∑ t : A × A → Fin Q, ∏ β, addrMult π Q t β (birth β) =
      (Fintype.card (A × A → Fin Q) : ℂ) * (if BlockConstraint birth π then 1 else 0) := by
  by_cases hperf : ∀ β ∈ π.biUnion id, ∃ p, birth β = some p
  · -- all addresses of the blocks are performed
    obtain ⟨val, hvaldef⟩ : ∃ val : A → ℕ, val = fun β => (birth β).getD 0 := ⟨_, rfl⟩
    have hval : ∀ β p, birth β = some p → val β = p := by
      intro β p h
      subst hvaldef
      simp only [h, Option.getD_some]
    have hvlt : ∀ β, val β < Q := by
      intro β
      cases hb : birth β with
      | none =>
        have h0 : val β = 0 := by
          subst hvaldef
          simp only [hb, Option.getD_none]
        rw [h0]
        exact hQ
      | some p =>
        rw [hval β p hb]
        exact hlt β p hb
    -- the multiplier of every address in terms of the values
    have h1 : ∀ (t : A × A → Fin Q) (β : A), addrMult π Q t β (birth β) =
        ∏ β' : A,
          (if SameBlock π β β' then
              expUnit (((t (β, β')).val : ℝ) / (Q : ℝ) * (val β : ℝ)) else 1) *
            (if SameBlock π β' β then
              expUnit (-(((t (β', β)).val : ℝ) / (Q : ℝ) * (val β : ℝ))) else 1) := by
      intro t β
      cases hb : birth β with
      | none =>
        have hβ : β ∉ π.biUnion id := by
          intro hmem
          obtain ⟨p, hp⟩ := hperf β hmem
          exact Option.some_ne_none p (hp.symm.trans hb)
        rw [addrMult_of_notMem π Q t hβ]
        symm
        refine Finset.prod_eq_one fun β' _ => ?_
        rw [if_neg (not_sameBlock_left hβ β'), if_neg (not_sameBlock_right hβ β'),
          one_mul]
      | some p =>
        rw [addrMult_some, hval β p hb]
    -- regrouping by pairs
    have h2 : ∀ t : A × A → Fin Q, ∏ β, addrMult π Q t β (birth β) =
        ∏ x : A × A,
          (if SameBlock π x.1 x.2 then
              expUnit (((t x).val : ℝ) / (Q : ℝ) * (val x.1 : ℝ)) else 1) *
            (if SameBlock π x.1 x.2 then
              expUnit (-(((t x).val : ℝ) / (Q : ℝ) * (val x.2 : ℝ))) else 1) := by
      intro t
      rw [Finset.prod_congr rfl fun β _ => h1 t β]
      exact prod_prod_swap_mul
        (fun β β' => if SameBlock π β β' then
          expUnit (((t (β, β')).val : ℝ) / (Q : ℝ) * (val β : ℝ)) else 1)
        (fun β' β => if SameBlock π β' β then
          expUnit (-(((t (β', β)).val : ℝ) / (Q : ℝ) * (val β : ℝ))) else 1)
    -- the sum over the parameters factorizes over the pairs
    have hLHS : ∑ t : A × A → Fin Q, ∏ β, addrMult π Q t β (birth β) =
        ∏ x : A × A,
          ((Q : ℂ) * (if SameBlock π x.1 x.2 → val x.1 = val x.2 then 1 else 0)) := by
      rw [Finset.sum_congr rfl fun t _ => h2 t]
      exact ((Fintype.prod_sum (fun (x : A × A) (j : Fin Q) =>
          (if SameBlock π x.1 x.2 then
              expUnit ((j.val : ℝ) / (Q : ℝ) * (val x.1 : ℝ)) else 1) *
            (if SameBlock π x.1 x.2 then
              expUnit (-((j.val : ℝ) / (Q : ℝ) * (val x.2 : ℝ))) else 1))).symm).trans
        (Finset.prod_congr rfl fun x _ =>
          sum_fin_expUnit_pair Q hQ (SameBlock π x.1 x.2) (val x.1) (val x.2) (hvlt _)
            (hvlt _))
    have hcard : (Fintype.card (A × A → Fin Q) : ℂ) = (Q : ℂ) ^ Fintype.card (A × A) := by
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    -- the values are constant on the blocks exactly when `𝒞_π` holds
    have h8 : (∀ x : A × A, (SameBlock π x.1 x.2 → val x.1 = val x.2)) ↔
        BlockConstraint birth π := by
      constructor
      · intro hall b hb
        have hb2 := (mem_blockCollections.mp hπ).1 b hb
        obtain ⟨β₀, hβ₀⟩ := Finset.card_pos.mp (by omega : 0 < b.card)
        obtain ⟨p₀, hp₀⟩ := hperf β₀ (Finset.mem_biUnion.mpr ⟨b, hb, hβ₀⟩)
        refine ⟨p₀, fun i hi => ?_⟩
        obtain ⟨p, hp⟩ := hperf i (Finset.mem_biUnion.mpr ⟨b, hb, hi⟩)
        have hv : val i = val β₀ := hall (i, β₀) ⟨b, hb, hi, hβ₀⟩
        rw [hval i p hp, hval β₀ p₀ hp₀] at hv
        rw [hp, hv]
      · intro hC x hx
        obtain ⟨b, hb, hx1, hx2⟩ := hx
        obtain ⟨z, hz⟩ := hC b hb
        rw [hval x.1 z (hz x.1 hx1), hval x.2 z (hz x.2 hx2)]
    rw [hLHS, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_boole,
      hcard]
    refine congrArg (fun z : ℂ => (Q : ℂ) ^ Fintype.card (A × A) * z) ?_
    exact ite_congr_of_iff h8 rfl rfl
  · -- an address of a block is not performed: both sides vanish
    have hex : ∃ β ∈ π.biUnion id, birth β = none := by
      by_contra hne
      apply hperf
      intro β hβ
      cases hb : birth β with
      | none => exact (hne ⟨β, hβ, hb⟩).elim
      | some p => exact ⟨p, rfl⟩
    obtain ⟨β, hβU, hβn⟩ := hex
    have hzero : ∀ t : A × A → Fin Q, ∏ β', addrMult π Q t β' (birth β') = 0 := by
      intro t
      refine Finset.prod_eq_zero (Finset.mem_univ β) ?_
      show addrMult π Q t β (birth β) = 0
      rw [hβn, addrMult_none]
      exact if_pos hβU
    have hnotC : ¬BlockConstraint birth π := by
      intro hC
      obtain ⟨b, hb, hβb⟩ := Finset.mem_biUnion.mp hβU
      obtain ⟨z, hz⟩ := hC b hb
      exact Option.some_ne_none z ((hz β hβb).symm.trans hβn)
    rw [Finset.sum_congr rfl fun t _ => hzero t, Finset.sum_const_zero, if_neg hnotC,
      mul_zero]

end Fourier

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
