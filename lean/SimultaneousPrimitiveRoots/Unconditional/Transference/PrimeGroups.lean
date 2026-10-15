module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.PrimeGroupMass
public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourcePrimeGrowth
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Prime groups, slots, patterns and dilations ([S] Definition 3.1 and the text after it)

Source: `verification/stage7-sources/S-02.tex`, lines 18–77 (cited as `[S-02:0018–0077]`).

* `GroupParams` — the fixed constants `0 < a < b < c < d < 0.47`, `c₀, C₀, v₋, v₊ > 0`,
  `0 < q < 1`, `ℓ ≥ 1` of Definition 3.1.
* `GroupFamily S B` — a raw family of finite sets of natural numbers indexed by the small groups
  `S` and the big groups `B`; `PrimeGroups P x S B` — Definition 3.1 for one value of `x`: the
  family together with all its constraints.
* `Slot J ℓ`, `LabelList`, `permuteSlots` — the `M = J + ℓ` slots, ordered label lists and slot
  permutations [S-02:0051–0052, 0072–0075].
* `Pattern`, `Pattern.t`, `SharedSmall`, `SharedBig`, `smallDil`, `bigDil`, `auxWeight` — patterns
  `ν`, shared slots, the dilation `D = D_𝒮 D_ℬ` and the law of the auxiliary free labels
  [S-02:0052–0063].
* `Pattern.supNorm`, `patternMass` — `sup |K_ν|` and the left side of (eq:pattern-mass)
  [S-02:0065–0072].

## Reuse of `Graph/`

`V_g` is `Graph.primeGroupReciprocalMass (𝒫_g)` and `μ_g(p)` is `Graph.primeGroupLaw (𝒫_g) p`
(`Graph/PrimeGroupMass.lean`); `exp(L^a)`, `exp(L^c)` are `Graph.sourcePrimeLowerBound a L`,
`Graph.sourcePrimeLowerBound c L`, and `N = 2⌈L^{13/25}⌉` is `Graph.sourceMemoryLength L`
(`Graph/SourcePrimeGrowth.lean`). These are the same real numbers as in the paper, so the
`Graph/` lemmas about them apply to the groups of a `PrimeGroups` structure verbatim.

## Choices

* The index sets `𝒮`, `ℬ` are arbitrary finite types `S`, `B` (parameters of the structure).
* The slots `{1, …, M}`, `M = J + ℓ`, are the sum type `Fin J ⊕ Fin ℓ`: `Sum.inl i` is one of the
  first `J` slots (the only ones a pattern may free), `Sum.inr j` one of the last `ℓ`.
* The paper's `ℕ ∋ ℓ` must be positive ([S-03:0535–0540] uses `ℓ ≥ 1`): `GroupParams.ℓ_pos`.
* `T = log L = log log x`, `L = log x` [S-01:0020–0023].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators NNReal

noncomputable section

/-! ### Definition 3.1 -/

/-- **The fixed constants of Definition 3.1** [S-02:0021–0025]:
`0 < a < b < c < d < 0.47`, `c₀, C₀, v₋, v₊ > 0`, `0 < q < 1`, `ℓ ∈ ℕ`.
The paper writes `ℓ ∈ ℕ`; its proofs need `ℓ ≥ 1` ([S-03:0535–0540], and the rare-transfer count
`𝒟 = C(M, ℓ)^{|𝒮|}` of [S-02:0834–0836] grows with `J` only for `ℓ ≥ 1`), so positivity is a
field. -/
structure GroupParams where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  c₀ : ℝ
  C₀ : ℝ
  vMinus : ℝ
  vPlus : ℝ
  q : ℝ
  ℓ : ℕ
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_c : b < c
  c_lt_d : c < d
  d_lt : d < 47 / 100
  c₀_pos : 0 < c₀
  C₀_pos : 0 < C₀
  vMinus_pos : 0 < vMinus
  vPlus_pos : 0 < vPlus
  q_pos : 0 < q
  q_lt_one : q < 1
  ℓ_pos : 0 < ℓ

/-- A raw family of groups: finite sets of natural numbers `small g` (`g ∈ 𝒮`) and `big g`
(`g ∈ ℬ`). All operators of Definitions 3.2 and 3.3 are defined for a raw family; the constraints
of Definition 3.1 are the structure `PrimeGroups`. -/
structure GroupFamily (S B : Type) where
  /-- the small groups `𝒫_g`, `g ∈ 𝒮` -/
  small : S → Finset ℕ
  /-- the big groups `𝒫_g`, `g ∈ ℬ` -/
  big : B → Finset ℕ

open Classical in
/-- `#{p ∈ s : hit p}`. With `hit p ↔ p ∣ n` this is `ω_g(n) = ∑_{p ∈ 𝒫_g} 1_{p ∣ n}`
[S-02:0043]. -/
def countHits (hit : ℕ → Prop) (s : Finset ℕ) : ℕ := (s.filter hit).card

namespace GroupFamily

variable {S B : Type} [Fintype S] [Fintype B] (𝒢 : GroupFamily S B)

/-- `∑_g #{p ∈ 𝒫_g : hit p}` over all small and big groups; `ω(n)` when `hit p ↔ p ∣ n`. -/
def omegaOf (hit : ℕ → Prop) : ℕ :=
  ∑ g, countHits hit (𝒢.small g) + ∑ g, countHits hit (𝒢.big g)

/-- `ω(n) = ∑_g ω_g(n)` for `n ∈ ℤ` [S-02:0043–0045]: the number of group primes dividing `n`
(each counted once; "divisibility at `n = 0` has its usual meaning"). -/
def omega (n : ℤ) : ℕ := 𝒢.omegaOf fun p => (p : ℤ) ∣ n

end GroupFamily

/-- `s = |𝒮| + |ℬ|`, the number of groups [S-02:0041]. -/
def groupCount (S B : Type) [Fintype S] [Fintype B] : ℕ := Fintype.card S + Fintype.card B

/-- At `n = 0` every prime of a group divides `n` [S-02:0047]. -/
theorem countHits_dvd_zero (s : Finset ℕ) : countHits (fun p => (p : ℤ) ∣ 0) s = s.card := by
  simp [countHits]

/-- **Definition 3.1** [S-02:0020–0049] for one value of `x`: finite, pairwise disjoint sets of
primes `𝒫_g` indexed by the disjoint sets `𝒮 = S` and `ℬ = B`, with
`c₀ T ≤ |𝒮|, |ℬ| ≤ C₀ T` (`T = log log x`), the ranges (eq:prime-group-ranges)
`exp(L^a) ≤ p ≤ exp(L^b)` (small), `exp(L^c) ≤ p ≤ exp(L^d)` (big) with `L = log x`, and
`v₋ ≤ V_g ≤ v₊` for `V_g = ∑_{p ∈ 𝒫_g} 1/p`.

`V_g` is `Graph.primeGroupReciprocalMass`, the lower range bounds are
`Graph.sourcePrimeLowerBound`. Disjointness of a small group from a big group is stated as a
field although it follows from the ranges when `L > 1`. The paper considers "each sufficiently
large `x`"; the structure makes sense for every real `x`, and the theorems quantify over
`x ≥ x₀`. -/
structure PrimeGroups (P : GroupParams) (x : ℝ) (S B : Type) [Fintype S] [Fintype B]
    extends GroupFamily S B where
  prime_small : ∀ g, ∀ p ∈ small g, Nat.Prime p
  prime_big : ∀ g, ∀ p ∈ big g, Nat.Prime p
  disjoint_small : ∀ g g', g ≠ g' → Disjoint (small g) (small g')
  disjoint_big : ∀ g g', g ≠ g' → Disjoint (big g) (big g')
  disjoint_small_big : ∀ g g', Disjoint (small g) (big g')
  card_small_ge : P.c₀ * Real.log (Real.log x) ≤ (Fintype.card S : ℝ)
  card_small_le : (Fintype.card S : ℝ) ≤ P.C₀ * Real.log (Real.log x)
  card_big_ge : P.c₀ * Real.log (Real.log x) ≤ (Fintype.card B : ℝ)
  card_big_le : (Fintype.card B : ℝ) ≤ P.C₀ * Real.log (Real.log x)
  small_ge : ∀ g, ∀ p ∈ small g, Graph.sourcePrimeLowerBound P.a (Real.log x) ≤ (p : ℝ)
  small_le : ∀ g, ∀ p ∈ small g, (p : ℝ) ≤ Real.exp (Real.log x ^ P.b)
  big_ge : ∀ g, ∀ p ∈ big g, Graph.sourcePrimeLowerBound P.c (Real.log x) ≤ (p : ℝ)
  big_le : ∀ g, ∀ p ∈ big g, (p : ℝ) ≤ Real.exp (Real.log x ^ P.d)
  mass_small_ge : ∀ g, P.vMinus ≤ Graph.primeGroupReciprocalMass (small g)
  mass_small_le : ∀ g, Graph.primeGroupReciprocalMass (small g) ≤ P.vPlus
  mass_big_ge : ∀ g, P.vMinus ≤ Graph.primeGroupReciprocalMass (big g)
  mass_big_le : ∀ g, Graph.primeGroupReciprocalMass (big g) ≤ P.vPlus

/-- `s` is the set of all primes in an interval. In [S] §4 every big group has this form
[S-03:0004–0009]; so do the big active groups of [P] §6 [P-06:0023]. -/
def IsPrimeInterval (s : Finset ℕ) : Prop :=
  ∃ lo hi : ℕ, ∀ p : ℕ, p ∈ s ↔ (p.Prime ∧ lo ≤ p ∧ p ≤ hi)

namespace PrimeGroups

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B]
  (𝔊 : PrimeGroups P x S B)

theorem mass_pos_of_ge {s : Finset ℕ} (h : P.vMinus ≤ Graph.primeGroupReciprocalMass s) :
    0 < Graph.primeGroupReciprocalMass s := lt_of_lt_of_le P.vMinus_pos h

theorem nonempty_of_mass {s : Finset ℕ} (h : P.vMinus ≤ Graph.primeGroupReciprocalMass s) :
    s.Nonempty := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have h0 : Graph.primeGroupReciprocalMass (∅ : Finset ℕ) = 0 := by
      unfold Graph.primeGroupReciprocalMass
      exact Finset.sum_empty
    linarith [P.vMinus_pos]
  · exact hne

/-- Every small group is nonempty (since `V_g ≥ v₋ > 0`). -/
theorem small_nonempty (g : S) : (𝔊.small g).Nonempty := nonempty_of_mass (𝔊.mass_small_ge g)

/-- Every big group is nonempty (since `V_g ≥ v₋ > 0`). -/
theorem big_nonempty (g : B) : (𝔊.big g).Nonempty := nonempty_of_mass (𝔊.mass_big_ge g)

/-- `μ_g` is a probability law on a big group: `∑_{p ∈ 𝒫_g} μ_g(p) = 1` [S-02:0039]. -/
theorem big_law_sum (g : B) : ∑ p ∈ 𝔊.big g, Graph.primeGroupLaw (𝔊.big g) p = 1 :=
  Graph.prime_group_law_sum _ (𝔊.big_nonempty g) (𝔊.prime_big g)

/-- `μ_g` is a probability law on a small group. -/
theorem small_law_sum (g : S) : ∑ p ∈ 𝔊.small g, Graph.primeGroupLaw (𝔊.small g) p = 1 :=
  Graph.prime_group_law_sum _ (𝔊.small_nonempty g) (𝔊.prime_small g)

/-- `μ_g(p) > 0` on a big group. -/
theorem big_law_pos (g : B) (p : ℕ) (hp : p ∈ 𝔊.big g) :
    0 < Graph.primeGroupLaw (𝔊.big g) p :=
  Graph.prime_group_law_pos _ (𝔊.big_nonempty g) (𝔊.prime_big g) p hp

end PrimeGroups

/-! ### Slots, label lists and slot permutations -/

/-- The `M = J + ℓ` slots of one group [S-02:0051–0052]: `Sum.inl i` (`i : Fin J`) is one of the
first `J` slots, `Sum.inr j` (`j : Fin ℓ`) one of the last `ℓ`. -/
abbrev Slot (J ℓ : ℕ) : Type := Fin J ⊕ Fin ℓ

/-- The number of slots is `M = J + ℓ`. -/
theorem card_slot (J ℓ : ℕ) : Fintype.card (Slot J ℓ) = J + ℓ := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

/-- Ordered label lists `𝐩 = (p_{g,i})` of a family `𝒬`: `M` slots in every group, the label of a
slot of group `g` lies in `𝒬 g`, repetitions allowed [S-02:0052, 0083–0086]. -/
abbrev LabelList {ι : Type} (𝒬 : ι → Finset ℕ) (J ℓ : ℕ) : Type :=
  (g : ι) → Slot J ℓ → {p : ℕ // p ∈ 𝒬 g}

/-- One permutation of the `M` slots for every group of the family: the group over which
symmetrization averages [S-02:0072–0075]. -/
abbrev SlotPerms (ι : Type) (J ℓ : ℕ) : Type := ι → Equiv.Perm (Slot J ℓ)

section Lists

variable {ι : Type} {𝒬 : ι → Finset ℕ} {J ℓ : ℕ}

/-- Permute the slots of every group: `(p · σ)_{g,i} = p_{g, σ_g(i)}`. -/
def permuteSlots (σ : SlotPerms ι J ℓ) (p : LabelList 𝒬 J ℓ) : LabelList 𝒬 J ℓ :=
  fun g i => p g (σ g i)

theorem permuteSlots_one (p : LabelList 𝒬 J ℓ) : permuteSlots (1 : SlotPerms ι J ℓ) p = p := rfl

theorem permuteSlots_mul (σ τ : SlotPerms ι J ℓ) (p : LabelList 𝒬 J ℓ) :
    permuteSlots (σ * τ) p = permuteSlots τ (permuteSlots σ p) := rfl

/-- `permuteSlots σ` as a bijection of the label lists. -/
def permuteEquiv (σ : SlotPerms ι J ℓ) : LabelList 𝒬 J ℓ ≃ LabelList 𝒬 J ℓ where
  toFun := permuteSlots σ
  invFun := permuteSlots σ⁻¹
  left_inv p := by rw [← permuteSlots_mul, mul_inv_cancel, permuteSlots_one]
  right_inv p := by rw [← permuteSlots_mul, inv_mul_cancel, permuteSlots_one]

theorem permuteEquiv_apply (σ : SlotPerms ι J ℓ) (p : LabelList 𝒬 J ℓ) :
    permuteEquiv σ p = permuteSlots σ p := rfl

theorem permuteSlots_inv_cancel (σ : SlotPerms ι J ℓ) (p : LabelList 𝒬 J ℓ) :
    permuteSlots σ⁻¹ (permuteSlots σ p) = p := (permuteEquiv σ).left_inv p

theorem permuteSlots_cancel_inv (σ : SlotPerms ι J ℓ) (p : LabelList 𝒬 J ℓ) :
    permuteSlots σ (permuteSlots σ⁻¹ p) = p := (permuteEquiv σ).right_inv p

/-- `p · σ = p'` if and only if `p = p' · σ⁻¹`. -/
theorem permuteSlots_eq_iff (σ : SlotPerms ι J ℓ) (p p' : LabelList 𝒬 J ℓ) :
    permuteSlots σ p = p' ↔ p = permuteSlots σ⁻¹ p' := by
  constructor
  · rintro rfl
    exact (permuteSlots_inv_cancel σ p).symm
  · rintro rfl
    exact permuteSlots_cancel_inv σ p'

end Lists

/-- The number of elements of the symmetrization group is `(M!)^{#groups}`, `M = J + ℓ`:
"averaging all `M!` slot permutations independently in each relevant group" [S-02:0072–0074]. -/
theorem card_slotPerms (ι : Type) [Fintype ι] [DecidableEq ι] (J ℓ : ℕ) :
    Fintype.card (SlotPerms ι J ℓ) = (J + ℓ).factorial ^ Fintype.card ι := by
  rw [Fintype.card_fun, Fintype.card_perm, card_slot]

/-! ### Patterns, dilations and coefficients -/

/-- The auxiliary free labels of a pattern with sets `C_g`: one label of the big group `g` for
every slot of `C_g` [S-02:0060–0062]. -/
abbrev AuxList {B : Type} (big : B → Finset ℕ) {J : ℕ} (C : B → Finset (Fin J)) : Type :=
  (g : B) → {i : Fin J // i ∈ C g} → {p : ℕ // p ∈ big g}

/-- **A pattern `ν` with its coefficient `K_ν`** [S-02:0052–0068].

`C g ⊆ {1, …, J}` is the set `C_g` of a big group `g` (for small groups `C_g = ∅`, so no field is
needed). The slots of `{1, …, J} ∖ C_g` are *shared*; the other `t_g = ℓ + |C_g|` slots of each
endpoint list are *unshared*. The coefficient `K_ν` depends "only on the ordered big-group source
labels, target labels, and the auxiliary free labels used in `D_ℬ`": its arguments are the source
list, the target list and the auxiliary labels, in this order.

The bound `|C_g| ≤ m` is a hypothesis on a family of patterns, not a field. -/
structure Pattern {B : Type} (big : B → Finset ℕ) (J ℓ : ℕ) where
  /-- the sets `C_g ⊆ {1, …, J}`, `g ∈ ℬ` -/
  C : B → Finset (Fin J)
  /-- the coefficient `K_ν (source big labels) (target big labels) (auxiliary free labels)` -/
  K : LabelList big J ℓ → LabelList big J ℓ → AuxList big C → ℂ

namespace Pattern

variable {B : Type} {big : B → Finset ℕ} {J ℓ : ℕ}

/-- `t_g = ℓ + |C_g|`, the number of unshared slots of the big group `g` [S-02:0056]. For a small
group `t_g = ℓ`. -/
def t (ν : Pattern big J ℓ) (g : B) : ℕ := ℓ + (ν.C g).card

/-- `sup |K_ν|`, the supremum over source lists, target lists and auxiliary labels. -/
def supNorm [Fintype B] [DecidableEq B] (ν : Pattern big J ℓ) : ℝ≥0 :=
  Finset.univ.sup fun a : LabelList big J ℓ × LabelList big J ℓ × AuxList big ν.C =>
    ‖ν.K a.1 a.2.1 a.2.2‖₊

theorem norm_K_le [Fintype B] [DecidableEq B] (ν : Pattern big J ℓ)
    (p p' : LabelList big J ℓ) (r : AuxList big ν.C) : ‖ν.K p p' r‖ ≤ (ν.supNorm : ℝ) := by
  have h := Finset.le_sup
    (f := fun a : LabelList big J ℓ × LabelList big J ℓ × AuxList big ν.C =>
      ‖ν.K a.1 a.2.1 a.2.2‖₊) (Finset.mem_univ (p, p', r))
  exact NNReal.coe_le_coe.mpr h

/-- The raw pattern: `C_g = ∅` for every `g`, `K_0 = 1` [S-03:0017–0020]. -/
def raw (big : B → Finset ℕ) (J ℓ : ℕ) : Pattern big J ℓ where
  C := fun _ => ∅
  K := fun _ _ _ => 1

theorem supNorm_raw_le [Fintype B] [DecidableEq B] : (raw big J ℓ).supNorm ≤ 1 := by
  unfold supNorm
  refine Finset.sup_le fun a _ => ?_
  show ‖(1 : ℂ)‖₊ ≤ 1
  rw [nnnorm_one]

/-- `sup |K_0| = 1` for the raw pattern, as soon as a label list exists. -/
theorem supNorm_raw [Fintype B] [DecidableEq B] (p : LabelList big J ℓ) :
    (raw big J ℓ).supNorm = 1 := by
  apply le_antisymm supNorm_raw_le
  have r : AuxList big (raw big J ℓ).C := fun g i => (Finset.notMem_empty _ i.2).elim
  have h := norm_K_le (raw big J ℓ) p p r
  have h1 : ‖(raw big J ℓ).K p p r‖ = 1 := by
    show ‖(1 : ℂ)‖ = 1
    exact norm_one
  rw [h1] at h
  exact_mod_cast h

end Pattern

section Mass

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- **The left side of (eq:pattern-mass)** [S-02:0069–0071]: `∑_ν sup |K_ν|` for a finite family
of patterns indexed by a finite type `N`. The paper requires `patternMass 𝔉 ≤ L^{C₁}`. -/
def patternMass {N : Type} [Fintype N] (𝔉 : N → Pattern big J ℓ) : ℝ :=
  ∑ ν, ((𝔉 ν).supNorm : ℝ)

theorem patternMass_nonneg {N : Type} [Fintype N] (𝔉 : N → Pattern big J ℓ) :
    0 ≤ patternMass 𝔉 := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _

/-- Every coefficient of a family is bounded by the pattern mass. -/
theorem norm_K_le_patternMass {N : Type} [Fintype N] (𝔉 : N → Pattern big J ℓ) (ν : N)
    (p p' : LabelList big J ℓ) (r : AuxList big (𝔉 ν).C) :
    ‖(𝔉 ν).K p p' r‖ ≤ patternMass 𝔉 :=
  ((𝔉 ν).norm_K_le p p' r).trans
    (Finset.single_le_sum (f := fun ν => ((𝔉 ν).supNorm : ℝ))
      (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ ν))

/-- The family consisting of the raw pattern alone has pattern mass `1`. -/
theorem patternMass_raw (p : LabelList big J ℓ) :
    patternMass (fun _ : Unit => Pattern.raw big J ℓ) = 1 := by
  unfold patternMass
  rw [Fintype.sum_unique, Pattern.supNorm_raw p]
  rfl

end Mass

section Dilation

variable {S B : Type} [Fintype S] [Fintype B] {small : S → Finset ℕ} {big : B → Finset ℕ}
  {J ℓ : ℕ}

/-- `D_𝒮`: the product of the `J` shared labels of every small group (for a small group
`C_g = ∅`, so all of its first `J` slots are shared) [S-02:0058–0063]. -/
def smallDil (p : LabelList small J ℓ) : ℕ := ∏ g, ∏ i : Fin J, (p g (Sum.inl i) : ℕ)

/-- `D_ℬ`: in every big group the product of the shared labels (slots of `{1, …, J} ∖ C_g`) of the
list `p` and of the auxiliary free labels `r` (one for each slot of `C_g`) [S-02:0060–0063]. It
has `J` prime factors from each big group, counted with multiplicity. -/
def bigDil (C : B → Finset (Fin J)) (p : LabelList big J ℓ) (r : AuxList big C) : ℕ :=
  ∏ g, ((∏ i : Fin J, if i ∈ C g then 1 else (p g (Sum.inl i) : ℕ)) *
    ∏ i : {i : Fin J // i ∈ C g}, (r g i : ℕ))

/-- The shared labels of two small lists agree: all the first `J` slots [S-02:0058–0059]. -/
def SharedSmall (p p' : LabelList small J ℓ) : Prop :=
  ∀ (g : S) (i : Fin J), p' g (Sum.inl i) = p g (Sum.inl i)

/-- The shared labels of two big lists agree: the slots of `{1, …, J} ∖ C_g` [S-02:0058–0059]. -/
def SharedBig (C : B → Finset (Fin J)) (p p' : LabelList big J ℓ) : Prop :=
  ∀ (g : B) (i : Fin J), i ∉ C g → p' g (Sum.inl i) = p g (Sum.inl i)

/-- "The shared product and hence `D` are unchanged on reversal" [S-02:0122–0123], small part. -/
theorem smallDil_eq_of_shared {p p' : LabelList small J ℓ} (h : SharedSmall p p') :
    smallDil p' = smallDil p := by
  unfold smallDil
  exact Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => by rw [h g i]

/-- "The shared product and hence `D` are unchanged on reversal" [S-02:0122–0123], big part. -/
theorem bigDil_eq_of_shared {C : B → Finset (Fin J)} {p p' : LabelList big J ℓ}
    (h : SharedBig C p p') (r : AuxList big C) : bigDil C p' r = bigDil C p r := by
  unfold bigDil
  refine Finset.prod_congr rfl fun g _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rfl
  · rw [h g i hi]

/-- The law of the auxiliary free labels: independent, of law `μ_g` in the slots of `C_g`
[S-02:0060–0062]. -/
def auxWeight (big : B → Finset ℕ) (C : B → Finset (Fin J)) (r : AuxList big C) : ℝ :=
  ∏ g, ∏ i : {i : Fin J // i ∈ C g}, Graph.primeGroupLaw (big g) (r g i)

end Dilation

/-! ### The length of the moment -/

/-- `R = ⌈L^{0.52}⌉` [S-02:0172–0174]. The length `N = 2R` is `Graph.sourceMemoryLength L`. -/
def transferR (L : ℝ) : ℕ := Nat.ceil (L ^ ((13 : ℝ) / 25))

theorem sourceMemoryLength_eq_two_mul (L : ℝ) :
    Graph.sourceMemoryLength L = 2 * transferR L := rfl

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
