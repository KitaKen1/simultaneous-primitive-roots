module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.History
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Large rank: from pinned births to equality blocks

Source: `verification/stage7-sources/S-02.tex`, lines 1107–1155 (`[S-02:1107–1155]`), the
paragraph "Large rank: chronological fresh integrations".

"Fix `π`. Order birth addresses chronologically … and call the first address in each block its
pivot. Every other address is a dependent birth. When such an address is performed, its fresh
prime integration is constrained to the already determined pivot value. Since
`sup_{g, p} μ̃_g(p) ≪ P_*^{-1}`, this improves the weighted absolute row bound by `O(P_*^{-1})` per
dependent birth. … Retain all pivot values in the conditioning."

This file contains the combinatorial half of that argument, for an arbitrary finite family of
terms `h` with weights `m h ≥ 0` and birth assignments `β h : I → Option ℕ`.

* `HrPinned pv birth` — the partial assignment `pv` of values to addresses is realized by `birth`:
  every address with a prescribed value is performed with that value.
* `hrW ω o` — the weight of an address: `1` if no value is prescribed, the point mass `ω z` if the
  value `z` is prescribed.
* `hr_block_sum_le` — **pinned bounds give block bounds**: if for every partial assignment `pv`
  the total weight of the terms realizing `pv` is at most `K ∏_a hrW (ω a) (pv a)`, where the
  point masses satisfy `ω a z ≤ μ` and `∑_z ω a z ≤ M`, then for every collection `π` of disjoint
  nonempty blocks the total weight of the terms satisfying `𝒞_π` is at most
  `K ∏_{b ∈ π} M μ^{|b| - 1}`.
* `hr_prod_block_le` — `∏_{b ∈ π} M μ^{|b| - 1} ≤ (M μ)^{r(π)}` when every block has at least two
  addresses and `M ≥ 1`.

## The relation to the text

The text conditions on the value of the pivot of each block and bounds the fresh integration of
every dependent birth, uniformly in that value. Here the common value `ζ_b` of each block is
summed first: `1_{𝒞_π} ≤ ∑_ζ ∏_{b ∈ π} ∏_{a ∈ b} 1[birth a = ζ_b]`. For a fixed `ζ` every address
of every block is pinned to a constant, each pinned address costs its point mass at `ζ_b`, and
`∑_z ∏_{a ∈ b} ω_a(z) ≤ μ^{|b| - 1} ∑_z ω_{a₀}(z) ≤ M μ^{|b| - 1}`: one address of the block keeps
its total mass (the pivot of the text), every other one contributes the single-point bound. This
is the same estimate with the two summations interchanged; no order on the addresses is needed.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section HrBlocks

variable {I : Type}

/-- **A partial assignment of prime values to birth addresses is realized**: every address `a`
with a prescribed value `z` is performed and has the value `z`. -/
def HrPinned (pv birth : I → Option ℕ) : Prop := ∀ a z, pv a = some z → birth a = some z

/-- The weight of an address in a pinned sum: `1` if no value is prescribed, the point mass `ω z`
if the value `z` is prescribed ("replace the total fresh mass in each constrained slot by its
single-point bound", [S-02:1127–1129]). -/
def hrW (ω : ℕ → ℝ) (o : Option ℕ) : ℝ := o.elim 1 ω

theorem hrW_none (ω : ℕ → ℝ) : hrW ω none = 1 := rfl

theorem hrW_some (ω : ℕ → ℝ) (z : ℕ) : hrW ω (some z) = ω z := rfl

theorem hrW_nonneg {ω : ℕ → ℝ} (hω : ∀ z, 0 ≤ ω z) (o : Option ℕ) : 0 ≤ hrW ω o := by
  cases o with
  | none => exact zero_le_one
  | some z => exact hω z

theorem hrPinned_none (birth : I → Option ℕ) : HrPinned (fun _ => none) birth :=
  fun _ z (h : (none : Option ℕ) = some z) => absurd h (Option.some_ne_none z).symm

/-- The sum over the common value of one block: one address keeps its total mass, the others
contribute the single-point bound. -/
theorem hr_sum_block_le [DecidableEq I] (V : Finset ℕ) (ω : I → ℕ → ℝ)
    (hω0 : ∀ a z, 0 ≤ ω a z) {μ M : ℝ} (hω : ∀ a z, ω a z ≤ μ) (hM : ∀ a, ∑ z ∈ V, ω a z ≤ M)
    (hμ0 : 0 ≤ μ) (b : Finset I) (hb : b.Nonempty) :
    ∑ z ∈ V, ∏ a ∈ b, ω a z ≤ M * μ ^ (b.card - 1) := by
  obtain ⟨a₀, ha₀⟩ := hb
  have hterm : ∀ z ∈ V, ∏ a ∈ b, ω a z ≤ ω a₀ z * μ ^ (b.card - 1) := by
    intro z _
    have h1 : ∏ a ∈ b.erase a₀, ω a z ≤ ∏ _a ∈ b.erase a₀, μ :=
      Finset.prod_le_prod (fun a _ => hω0 a z) (fun a _ => hω a z)
    have h2 : ∏ _a ∈ b.erase a₀, μ = μ ^ (b.card - 1) := by
      rw [Finset.prod_const, Finset.card_erase_of_mem ha₀]
    calc ∏ a ∈ b, ω a z = ω a₀ z * ∏ a ∈ b.erase a₀, ω a z :=
          (Finset.mul_prod_erase b (fun a => ω a z) ha₀).symm
      _ ≤ ω a₀ z * μ ^ (b.card - 1) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 (hω0 a₀ z)
  calc ∑ z ∈ V, ∏ a ∈ b, ω a z ≤ ∑ z ∈ V, ω a₀ z * μ ^ (b.card - 1) :=
        Finset.sum_le_sum hterm
    _ = (∑ z ∈ V, ω a₀ z) * μ ^ (b.card - 1) := (Finset.sum_mul _ _ _).symm
    _ ≤ M * μ ^ (b.card - 1) := mul_le_mul_of_nonneg_right (hM a₀) (pow_nonneg hμ0 _)

open _root_.Classical in
/-- The induction behind `hr_block_sum_le`: the blocks are pinned one at a time, the common value
of the new block being summed over `V`. -/
theorem hr_block_sum_aux {H : Type} [Fintype I] [Fintype H] (m : H → ℝ) (hm : ∀ h, 0 ≤ m h)
    (β : H → I → Option ℕ) (V : Finset ℕ) (hV : ∀ h a z, β h a = some z → z ∈ V)
    (ω : I → ℕ → ℝ) (hω0 : ∀ a z, 0 ≤ ω a z) {μ M K : ℝ} (hμ0 : 0 ≤ μ) (hM0 : 0 ≤ M)
    (hK : 0 ≤ K) (hω : ∀ a z, ω a z ≤ μ) (hM : ∀ a, ∑ z ∈ V, ω a z ≤ M)
    (hpin : ∀ pv : I → Option ℕ,
      ∑ h, (if HrPinned pv (β h) then m h else 0) ≤ K * ∏ a, hrW (ω a) (pv a))
    (π : Finset (Finset I)) :
    (∀ b ∈ π, b.Nonempty) → (∀ b ∈ π, ∀ b' ∈ π, b ≠ b' → Disjoint b b') →
      ∀ pv : I → Option ℕ, (∀ b ∈ π, ∀ a ∈ b, pv a = none) →
        ∑ h, (if HrPinned pv (β h) ∧ BlockConstraint (β h) π then m h else 0) ≤
          K * (∏ a, hrW (ω a) (pv a)) * ∏ b ∈ π, (M * μ ^ (b.card - 1)) := by
  refine Finset.induction_on π ?_ ?_
  · intro _ _ pv _
    rw [Finset.prod_empty, mul_one]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun h _ => ?_)) (hpin pv)
    exact if_congr (and_iff_left fun b hb => absurd hb (Finset.notMem_empty b)) rfl rfl
  · intro b π' hb ih hne hdisj pv hpv
    have hne' : ∀ b₁ ∈ π', b₁.Nonempty := fun b₁ h₁ => hne b₁ (Finset.mem_insert_of_mem h₁)
    have hdisj' : ∀ b₁ ∈ π', ∀ b₂ ∈ π', b₁ ≠ b₂ → Disjoint b₁ b₂ := fun b₁ h₁ b₂ h₂ =>
      hdisj b₁ (Finset.mem_insert_of_mem h₁) b₂ (Finset.mem_insert_of_mem h₂)
    have hbne : b.Nonempty := hne b (Finset.mem_insert_self b π')
    have hpvb : ∀ a ∈ b, pv a = none := hpv b (Finset.mem_insert_self b π')
    -- the assignment with the block `b` pinned to `z`
    obtain ⟨pvz, hpvz⟩ : ∃ pvz : ℕ → I → Option ℕ,
        ∀ z a, pvz z a = if a ∈ b then some z else pv a := ⟨_, fun _ _ => rfl⟩
    have hpvz' : ∀ z, ∀ b₁ ∈ π', ∀ a ∈ b₁, pvz z a = none := by
      intro z b₁ h₁ a ha
      have hab : a ∉ b := fun hab =>
        Finset.disjoint_left.mp
          (hdisj b (Finset.mem_insert_self b π') b₁ (Finset.mem_insert_of_mem h₁)
            (fun e => hb (e ▸ h₁))) hab ha
      rw [hpvz, if_neg hab]
      exact hpv b₁ (Finset.mem_insert_of_mem h₁) a ha
    -- one term: the common value of the block is one of the values of `V`
    have hterm : ∀ h : H,
        (if HrPinned pv (β h) ∧ BlockConstraint (β h) (insert b π') then m h else 0) ≤
          ∑ z ∈ V, (if HrPinned (pvz z) (β h) ∧ BlockConstraint (β h) π' then m h else 0) := by
      intro h
      have hnn : ∀ z ∈ V,
          (0 : ℝ) ≤ (if HrPinned (pvz z) (β h) ∧ BlockConstraint (β h) π' then m h else 0) := by
        intro z _
        split_ifs
        · exact hm h
        · exact le_rfl
      by_cases hc : HrPinned pv (β h) ∧ BlockConstraint (β h) (insert b π')
      · obtain ⟨hP, hBC⟩ := hc
        obtain ⟨z, hz⟩ := hBC b (Finset.mem_insert_self b π')
        obtain ⟨a₀, ha₀⟩ := hbne
        have hzV : z ∈ V := hV h a₀ z (hz a₀ ha₀)
        have hc' : HrPinned (pvz z) (β h) ∧ BlockConstraint (β h) π' := by
          refine ⟨fun a z' hz' => ?_, fun b₁ h₁ => hBC b₁ (Finset.mem_insert_of_mem h₁)⟩
          rw [hpvz] at hz'
          by_cases hab : a ∈ b
          · rw [if_pos hab] at hz'
            rw [← Option.some.inj hz']
            exact hz a hab
          · rw [if_neg hab] at hz'
            exact hP a z' hz'
        rw [if_pos (And.intro hP hBC)]
        calc m h = (if HrPinned (pvz z) (β h) ∧ BlockConstraint (β h) π' then m h else 0) :=
              (if_pos hc').symm
          _ ≤ ∑ z ∈ V,
                (if HrPinned (pvz z) (β h) ∧ BlockConstraint (β h) π' then m h else 0) :=
              Finset.single_le_sum
                (f := fun z => if HrPinned (pvz z) (β h) ∧ BlockConstraint (β h) π' then m h
                  else 0) hnn hzV
      · rw [if_neg hc]
        exact Finset.sum_nonneg hnn
    -- the weights of the pinned assignment
    have hprod : ∀ z, ∏ a, hrW (ω a) (pvz z a) = (∏ a, hrW (ω a) (pv a)) * ∏ a ∈ b, ω a z := by
      intro z
      have h1 : ∀ a : I, hrW (ω a) (pvz z a) =
          hrW (ω a) (pv a) * (if a ∈ b then ω a z else 1) := by
        intro a
        rw [hpvz]
        by_cases hab : a ∈ b
        · rw [if_pos hab, if_pos hab, hpvb a hab, hrW_none, one_mul, hrW_some]
        · rw [if_neg hab, if_neg hab, mul_one]
      rw [Finset.prod_congr rfl fun a _ => h1 a, Finset.prod_mul_distrib, Finset.prod_ite_mem,
        Finset.univ_inter]
    have hW0 : 0 ≤ ∏ a, hrW (ω a) (pv a) :=
      Finset.prod_nonneg fun a _ => hrW_nonneg (hω0 a) _
    have hP0 : 0 ≤ ∏ b₁ ∈ π', (M * μ ^ (b₁.card - 1)) :=
      Finset.prod_nonneg fun b₁ _ => mul_nonneg hM0 (pow_nonneg hμ0 _)
    calc ∑ h, (if HrPinned pv (β h) ∧ BlockConstraint (β h) (insert b π') then m h else 0)
        ≤ ∑ h, ∑ z ∈ V,
            (if HrPinned (pvz z) (β h) ∧ BlockConstraint (β h) π' then m h else 0) :=
          Finset.sum_le_sum fun h _ => hterm h
      _ = ∑ z ∈ V, ∑ h,
            (if HrPinned (pvz z) (β h) ∧ BlockConstraint (β h) π' then m h else 0) :=
          Finset.sum_comm
      _ ≤ ∑ z ∈ V, K * (∏ a, hrW (ω a) (pvz z a)) * ∏ b₁ ∈ π', (M * μ ^ (b₁.card - 1)) :=
          Finset.sum_le_sum fun z _ => ih hne' hdisj' (pvz z) (hpvz' z)
      _ = (K * (∏ a, hrW (ω a) (pv a)) * ∏ b₁ ∈ π', (M * μ ^ (b₁.card - 1))) *
            ∑ z ∈ V, ∏ a ∈ b, ω a z := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [hprod z]
          ring
      _ ≤ (K * (∏ a, hrW (ω a) (pv a)) * ∏ b₁ ∈ π', (M * μ ^ (b₁.card - 1))) *
            (M * μ ^ (b.card - 1)) :=
          mul_le_mul_of_nonneg_left (hr_sum_block_le V ω hω0 hω hM hμ0 b hbne)
            (mul_nonneg (mul_nonneg hK hW0) hP0)
      _ = K * (∏ a, hrW (ω a) (pv a)) * ∏ b₁ ∈ insert b π', (M * μ ^ (b₁.card - 1)) := by
          rw [Finset.prod_insert hb]
          ring

open _root_.Classical in
/-- **Pinned bounds give block bounds** [S-02:1107–1151]. Let `m h ≥ 0` be the weights and `β h`
the birth assignments of a finite family of terms, with values in the finite set `V`. Suppose that
for every partial assignment `pv` of values to addresses

`∑_{h realizing pv} m h ≤ K ∏_a W_a(pv a)`,  `W_a(none) = 1`, `W_a(some z) = ω a z`,

with point masses `0 ≤ ω a z ≤ μ` and total masses `∑_{z ∈ V} ω a z ≤ M`. Then for every collection
`π` of pairwise disjoint nonempty blocks of addresses

`∑_{h satisfying 𝒞_π} m h ≤ K ∏_{b ∈ π} M μ^{|b| - 1}`:

every block has one address with its total mass and `|b| - 1` addresses with the single-point
bound. -/
theorem hr_block_sum_le {H : Type} [Fintype I] [Fintype H] (m : H → ℝ) (hm : ∀ h, 0 ≤ m h)
    (β : H → I → Option ℕ) (V : Finset ℕ) (hV : ∀ h a z, β h a = some z → z ∈ V)
    (ω : I → ℕ → ℝ) (hω0 : ∀ a z, 0 ≤ ω a z) {μ M K : ℝ} (hμ0 : 0 ≤ μ) (hM0 : 0 ≤ M)
    (hK : 0 ≤ K) (hω : ∀ a z, ω a z ≤ μ) (hM : ∀ a, ∑ z ∈ V, ω a z ≤ M)
    (hpin : ∀ pv : I → Option ℕ,
      ∑ h, (if HrPinned pv (β h) then m h else 0) ≤ K * ∏ a, hrW (ω a) (pv a))
    (π : Finset (Finset I)) (hne : ∀ b ∈ π, b.Nonempty)
    (hdisj : ∀ b ∈ π, ∀ b' ∈ π, b ≠ b' → Disjoint b b') :
    ∑ h, (if BlockConstraint (β h) π then m h else 0) ≤
      K * ∏ b ∈ π, (M * μ ^ (b.card - 1)) := by
  have h := hr_block_sum_aux m hm β V hV ω hω0 hμ0 hM0 hK hω hM hpin π hne hdisj
    (fun _ => none) (fun _ _ _ _ => rfl)
  have h1 : ∏ a : I, hrW (ω a) ((fun _ => none : I → Option ℕ) a) = 1 :=
    Finset.prod_eq_one fun a _ => hrW_none (ω a)
  rw [h1, mul_one] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun h' _ => ?_)) h
  exact if_congr (and_iff_right (hrPinned_none (β h'))).symm rfl rfl

/-- `∏_{b ∈ π} M μ^{|b| - 1} ≤ (M μ)^{r(π)}` when every block has at least two addresses and
`M ≥ 1`: a block of size `h` has `h - 1 ≥ 1` dependent births. -/
theorem hr_prod_block_le [Fintype I] {μ M : ℝ} (hμ0 : 0 ≤ μ) (hM1 : 1 ≤ M)
    {π : Finset (Finset I)} (hπ : π ∈ blockCollections I) :
    ∏ b ∈ π, (M * μ ^ (b.card - 1)) ≤ (M * μ) ^ blockRank π := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hcard := (mem_blockCollections.mp hπ).1
  have h1 : ∀ b ∈ π, M * μ ^ (b.card - 1) ≤ (M * μ) ^ (b.card - 1) := by
    intro b hb
    have hk : b.card - 1 ≠ 0 := by
      have := hcard b hb
      omega
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hM1 hk) (pow_nonneg hμ0 _)
  calc ∏ b ∈ π, (M * μ ^ (b.card - 1)) ≤ ∏ b ∈ π, (M * μ) ^ (b.card - 1) :=
        Finset.prod_le_prod (fun b _ => mul_nonneg hM0 (pow_nonneg hμ0 _)) h1
    _ = (M * μ) ^ blockRank π := Finset.prod_pow_eq_pow_sum π _ _

end HrBlocks

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
