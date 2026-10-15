module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemoryAbsoluteProof
public import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# [S] Lemma 3.9 (rare transfer): the count of the omission choices

Source: `verification/stage7-sources/S-02.tex`, lines 847–872 (`[S-02:0847–0872]`).

"For some one of its at most `B` old pending particles `(p, r)`, promotion requires
`r + σ_i k D_ℬ D_𝒮 ≡ 0 (mod p)`, `p ∤ D`. In each small group the source symmetrization omits an
independent uniformly chosen `ℓ`-subset of its `M` distinct labels. If `F` is the full product of
all small source labels and `U` the product of the omitted labels, then `D_𝒮 = F/U`. Unique
factorization and disjointness of groups show that the `𝒟` choices give distinct positive integers
`U`. Moreover `U ≤ exp(ℓ|𝒮|L^b) < exp(L^c) ≤ p` for sufficiently large `x`. They are therefore
distinct modulo `p`. The quantities `F, k, D_ℬ` are invertible modulo every `p` eligible in
(eq:promotion-congruence). Hence each pending particle allows at most one omission choice. At most
`B` of the `𝒟` equally likely choices allow any promotion."

* `rare_card_coset_le` — a set of families of slot permutations any two of which omit the same
  slots (the last `ℓ` slots have the same image) has at most `(J! ℓ!)^{|𝒮|}` elements
  (it lies in one coset of `(𝔖_J × 𝔖_ℓ)^{𝒮}`).
* `rareOmit`, `smallDil_mul_rareOmit_permute` — `U`, and `D_𝒮 U = F`.
* `rare_slots_of_omit_eq` — "unique factorization and disjointness of groups": `U` determines the
  omitted labels of every small group.
* `rare_omit_eq` — the congruence: two omission choices which are compatible with the same pending
  particle have the same `U`.
* `RareArith` — the arithmetic hypotheses (primes, disjoint small groups, `p ∤ σ_i k`, `U < p`).
* `RareElig` — some pending particle `(p, r)` of the state satisfies a congruence `Q` for the
  step `Δ = e D` of the state, with `p ∤ D` (and the total memory is at most the cutoff, the small
  labels of each group are distinct). `rare_count`: for a fixed permutation of the big lists, at
  most `B (J! ℓ!)^{|𝒮|}` permutations of the small lists lead to such a state.
* `rareFrac`, `rareFrac_le`, `rare_sum_frac_le` — the proportion of the slot permutations is at
  most `B/𝒟`.
* `rareElig_permMem`, `rare_ind_mul_memSymmetric` — the condition is symmetric in the particle
  indices.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Slot permutations which preserve the last `ℓ` slots -/

/-- A set of permutations of the slots which map the last `ℓ` slots to the last `ℓ` slots has at
most `J! ℓ!` elements. -/
theorem rare_card_perm_le {J ℓ : ℕ} (A : Finset (Equiv.Perm (Slot J ℓ)))
    (hA : ∀ σ ∈ A, ∀ j : Fin ℓ, ∃ j' : Fin ℓ, σ (Sum.inr j) = Sum.inr j') :
    A.card ≤ J.factorial * ℓ.factorial := by
  classical
  have hsub : A ⊆ Finset.univ.image (Equiv.Perm.sumCongrHom (Fin J) (Fin ℓ)) := by
    intro σ hσ
    have hr : Set.MapsTo σ (Set.range Sum.inr) (Set.range Sum.inr) := by
      rintro _ ⟨j, rfl⟩
      obtain ⟨j', hj'⟩ := hA σ hσ j
      exact ⟨j', hj'.symm⟩
    have hl := (Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr σ).mpr hr
    obtain ⟨ab, hab⟩ := MonoidHom.mem_range.mp
      (Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hl)
    exact Finset.mem_image.mpr ⟨ab, Finset.mem_univ _, hab⟩
  calc A.card ≤ (Finset.univ.image (Equiv.Perm.sumCongrHom (Fin J) (Fin ℓ))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin J) × Equiv.Perm (Fin ℓ))).card :=
        Finset.card_image_le
    _ = J.factorial * ℓ.factorial := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
          Fintype.card_fin, Fintype.card_fin]

/-- A set of families of slot permutations which map the last `ℓ` slots to the last `ℓ` slots has
at most `(J! ℓ!)^{|𝒮|}` elements. -/
theorem rare_card_slotPerms_le {S : Type} [Fintype S] [DecidableEq S] {J ℓ : ℕ}
    (A : Finset (SlotPerms S J ℓ))
    (hA : ∀ σ ∈ A, ∀ (g : S) (j : Fin ℓ), ∃ j' : Fin ℓ, σ g (Sum.inr j) = Sum.inr j') :
    A.card ≤ (J.factorial * ℓ.factorial) ^ Fintype.card S := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (Equiv.Perm (Slot J ℓ)),
      T = Finset.univ.filter fun σ : Equiv.Perm (Slot J ℓ) =>
        ∀ j : Fin ℓ, ∃ j' : Fin ℓ, σ (Sum.inr j) = Sum.inr j' := ⟨_, rfl⟩
  have hTcard : T.card ≤ J.factorial * ℓ.factorial :=
    rare_card_perm_le T fun σ hσ => by
      rw [hT] at hσ
      exact (Finset.mem_filter.mp hσ).2
  have hsub : A ⊆ Fintype.piFinset fun _ : S => T := by
    intro σ hσ
    refine Fintype.mem_piFinset.mpr fun g => ?_
    rw [hT]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA σ hσ g⟩
  calc A.card ≤ (Fintype.piFinset fun _ : S => T).card := Finset.card_le_card hsub
    _ = T.card ^ Fintype.card S := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
    _ ≤ (J.factorial * ℓ.factorial) ^ Fintype.card S := Nat.pow_le_pow_left hTcard _

/-- **One coset of `(𝔖_J × 𝔖_ℓ)^{𝒮}`**: a set of families of slot permutations any two of which
have the same image of the last `ℓ` slots in every group has at most `(J! ℓ!)^{|𝒮|}` elements. -/
theorem rare_card_coset_le {S : Type} [Fintype S] [DecidableEq S] {J ℓ : ℕ}
    (A : Finset (SlotPerms S J ℓ))
    (hA : ∀ σ ∈ A, ∀ τ ∈ A, ∀ (g : S) (j : Fin ℓ),
      ∃ j' : Fin ℓ, σ g (Sum.inr j) = τ g (Sum.inr j')) :
    A.card ≤ (J.factorial * ℓ.factorial) ^ Fintype.card S := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | ⟨τ, hτ⟩
  · rw [Finset.card_empty]
    exact Nat.zero_le _
  · have hinj : Function.Injective fun σ : SlotPerms S J ℓ => τ⁻¹ * σ :=
      fun a b h => mul_left_cancel h
    rw [← Finset.card_image_of_injective A hinj]
    refine rare_card_slotPerms_le _ fun ρ hρ g j => ?_
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨j', hj'⟩ := hA σ hσ τ hτ g j
    refine ⟨j', ?_⟩
    show (τ g)⁻¹ (σ g (Sum.inr j)) = Sum.inr j'
    rw [hj']
    exact (τ g).symm_apply_apply _

/-! ### The omitted small labels -/

section Omit

variable {S : Type} [Fintype S] {small : S → Finset ℕ} {J ℓ : ℕ}

/-- **`U`, the product of the omitted small labels** [S-02:0858–0860]: the labels of the last `ℓ`
slots of every small group. -/
def rareOmit (p : LabelList small J ℓ) : ℕ := ∏ g, ∏ j : Fin ℓ, (p g (Sum.inr j) : ℕ)

/-- `D_𝒮 · U = F`, the product of all small labels. -/
theorem smallDil_mul_rareOmit (p : LabelList small J ℓ) :
    smallDil p * rareOmit p = ∏ g, ∏ sl : Slot J ℓ, (p g sl : ℕ) := by
  unfold smallDil rareOmit
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun g _ =>
    (Fintype.prod_sum_type fun sl : Slot J ℓ => (p g sl : ℕ)).symm

/-- "`D_𝒮 = F/U`" [S-02:0858–0860]: the product `D_𝒮 U` does not depend on the permutation of the
slots. -/
theorem smallDil_mul_rareOmit_permute (σ τ : SlotPerms S J ℓ) (p : LabelList small J ℓ) :
    smallDil (permuteSlots σ p) * rareOmit (permuteSlots σ p) =
      smallDil (permuteSlots τ p) * rareOmit (permuteSlots τ p) := by
  have h : ∀ ρ : SlotPerms S J ℓ,
      ∏ g, ∏ sl : Slot J ℓ, (permuteSlots ρ p g sl : ℕ) = ∏ g, ∏ sl : Slot J ℓ, (p g sl : ℕ) :=
    fun ρ => Finset.prod_congr rfl fun g _ =>
      Equiv.prod_comp (ρ g) (fun sl : Slot J ℓ => (p g sl : ℕ))
  rw [smallDil_mul_rareOmit, smallDil_mul_rareOmit, h σ, h τ]

/-- **"Unique factorization and disjointness of groups show that the `𝒟` choices give distinct
positive integers `U`"** [S-02:0860–0862]: if two permutations of the slots of a list of distinct
primes of disjoint groups have the same product `U` of the omitted labels, they omit the same
slots in every group. -/
theorem rare_slots_of_omit_eq (hprime : ∀ g, ∀ p ∈ small g, Nat.Prime p)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (small g) (small g'))
    (xs : LabelList small J ℓ) (hinj : ∀ g, Function.Injective (xs g)) (σ τ : SlotPerms S J ℓ)
    (h : rareOmit (permuteSlots σ xs) = rareOmit (permuteSlots τ xs)) (g : S) (j : Fin ℓ) :
    ∃ j' : Fin ℓ, σ g (Sum.inr j) = τ g (Sum.inr j') := by
  have hq : Nat.Prime (xs g (σ g (Sum.inr j)) : ℕ) := hprime g _ (xs g (σ g (Sum.inr j))).2
  have hdvd1 : (xs g (σ g (Sum.inr j)) : ℕ) ∣ rareOmit (permuteSlots σ xs) :=
    Dvd.dvd.trans
      (Finset.dvd_prod_of_mem (fun j' : Fin ℓ => (permuteSlots σ xs g (Sum.inr j') : ℕ))
        (Finset.mem_univ j))
      (Finset.dvd_prod_of_mem
        (fun g' : S => ∏ j' : Fin ℓ, (permuteSlots σ xs g' (Sum.inr j') : ℕ)) (Finset.mem_univ g))
  have hdvd : (xs g (σ g (Sum.inr j)) : ℕ) ∣
      ∏ g' : S, ∏ j' : Fin ℓ, (permuteSlots τ xs g' (Sum.inr j') : ℕ) := by
    rw [h] at hdvd1
    exact hdvd1
  obtain ⟨g', _, hg'⟩ := (hq.prime.dvd_finsetProd_iff _).mp hdvd
  obtain ⟨j', _, hj'⟩ := (hq.prime.dvd_finsetProd_iff _).mp hg'
  have hq' : Nat.Prime (xs g' (τ g' (Sum.inr j')) : ℕ) :=
    hprime g' _ (xs g' (τ g' (Sum.inr j'))).2
  have heq : (xs g (σ g (Sum.inr j)) : ℕ) = (xs g' (τ g' (Sum.inr j')) : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hq hq').mp hj'
  have hgg : g = g' := by
    by_contra hne
    have hm : (xs g (σ g (Sum.inr j)) : ℕ) ∈ small g' := by
      rw [heq]
      exact (xs g' (τ g' (Sum.inr j'))).2
    exact Finset.disjoint_left.mp (hdisj g g' hne) (xs g (σ g (Sum.inr j))).2 hm
  subst hgg
  exact ⟨j', hinj g (Subtype.ext heq)⟩

end Omit

/-- **"They are therefore distinct modulo `p`. The quantities `F, k, D_ℬ` are invertible modulo
every eligible `p`. Hence each pending particle allows at most one omission choice"**
[S-02:0863–0871]: if `e D₁ D_ℬ ≡ e D₂ D_ℬ (mod p)` with `p ∤ e`, `p ∤ D₁ D_ℬ`, and
`D₁ U₁ = D₂ U₂` with `U₁, U₂ < p`, then `U₁ = U₂`. -/
theorem rare_omit_eq {p : ℕ} (hp : p.Prime) {e : ℤ} (he : ¬(p : ℤ) ∣ e) {DB D1 D2 U1 U2 : ℕ}
    (hF : D1 * U1 = D2 * U2) (hU1 : U1 < p) (hU2 : U2 < p) (hnd : ¬p ∣ D1 * DB)
    (hcong : (p : ℤ) ∣ e * ((D1 * DB : ℕ) : ℤ) - e * ((D2 * DB : ℕ) : ℤ)) : U1 = U2 := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hD1 : ¬(p : ℤ) ∣ (D1 : ℤ) := fun h =>
    hnd (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mp h) DB)
  have hDB : ¬(p : ℤ) ∣ (DB : ℤ) := fun h =>
    hnd (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mp h) D1)
  have e1 : e * ((D1 * DB : ℕ) : ℤ) - e * ((D2 * DB : ℕ) : ℤ) =
      e * ((DB : ℤ) * ((D1 : ℤ) - (D2 : ℤ))) := by
    push_cast
    ring
  have h1 : (p : ℤ) ∣ e * ((DB : ℤ) * ((D1 : ℤ) - (D2 : ℤ))) := by
    rw [← e1]
    exact hcong
  have h2 : (p : ℤ) ∣ (D1 : ℤ) - (D2 : ℤ) :=
    (hp'.dvd_or_dvd ((hp'.dvd_or_dvd h1).resolve_left he)).resolve_left hDB
  have hF' : (D1 : ℤ) * (U1 : ℤ) = (D2 : ℤ) * (U2 : ℤ) := by exact_mod_cast hF
  have e2 : (D1 : ℤ) * ((U1 : ℤ) - (U2 : ℤ)) = -(((D1 : ℤ) - (D2 : ℤ)) * (U2 : ℤ)) := by
    have e3 : (D1 : ℤ) * ((U1 : ℤ) - (U2 : ℤ)) = (D1 : ℤ) * (U1 : ℤ) - (D1 : ℤ) * (U2 : ℤ) := by
      ring
    rw [e3, hF']
    ring
  have h3 : (p : ℤ) ∣ (D1 : ℤ) * ((U1 : ℤ) - (U2 : ℤ)) := by
    rw [e2]
    exact dvd_neg.mpr (Dvd.dvd.mul_right h2 _)
  have h4 : (p : ℤ) ∣ (U1 : ℤ) - (U2 : ℤ) := (hp'.dvd_or_dvd h3).resolve_left hD1
  have h5 : (U1 : ℤ) - (U2 : ℤ) = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h4 ?_
    rw [abs_lt]
    constructor <;> omega
  omega

/-! ### Eligible particles -/

section Elig

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ}

/-- **The arithmetic hypotheses of the count of the omission choices** [S-02:0860–0868], for the
multiplier `e = σ_i k` of the step: the group primes are primes, the small groups are disjoint, no
big prime divides `e` ("`k` is invertible modulo every eligible `p`"), and every product of `ℓ`
labels from each small group is smaller than every big prime
("`U ≤ exp(ℓ|𝒮|L^b) < exp(L^c) ≤ p`"). -/
structure RareArith (𝒢 : GroupFamily S B) (ℓ : ℕ) (e : ℤ) : Prop where
  prime_small : ∀ g, ∀ p ∈ 𝒢.small g, Nat.Prime p
  prime_big : ∀ g, ∀ p ∈ 𝒢.big g, Nat.Prime p
  disjoint_small : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g')
  not_dvd : ∀ g, ∀ p ∈ 𝒢.big g, ¬((p : ℤ) ∣ e)
  omit_lt : ∀ (u : (g : S) → Fin ℓ → {p : ℕ // p ∈ 𝒢.small g}) (g : B), ∀ p ∈ 𝒢.big g,
    ∏ g', ∏ j, (u g' j : ℕ) < p

/-- **A pending particle of the state is eligible for a transfer** [S-02:0851–0855]: the total
memory is at most the cutoff, the small labels of every group are distinct, and some pending
particle `(p, r)` satisfies the congruence `Q` for the step `Δ = e D` of the state, with `p ∤ D`.
Here `D` is the dilation of the lists of the state for the pattern sets `C` and the free labels
`r`; `Q` is the congruence of a promotion (`r + Δ ≡ 0`) or of a store (`r ≡ Δ`). -/
def RareElig (Q : (g : B) → Particle 𝒢 g → ℤ → Prop) (e : ℤ) (C : B → Finset (Fin J))
    (r : AuxList 𝒢.big C) (s : MState 𝒢 J ℓ Bc) : Prop :=
  memTotal s ≤ Bc ∧ (∀ g, Function.Injective (s.xs g)) ∧
    ∃ (g : B) (j : Fin Bc) (pr : Particle 𝒢 g), memAt (s.mem g) j = some pr ∧
      Q g pr (e * ((dil C ((s.xs, s.xb) : Lists 𝒢 J ℓ) r : ℕ) : ℤ)) ∧
      ¬((pr.1 : ℕ) ∣ dil C ((s.xs, s.xb) : Lists 𝒢 J ℓ) r)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- A particle read through `memAt` is a particle of the memory. -/
theorem rare_of_memAt {g : B} {z : Mem 𝒢 Bc g} {j : Fin Bc} {pr : Particle 𝒢 g}
    (h : memAt z j = some pr) : ∃ j' : Fin z.1.val, z.2 j' = pr := by
  by_cases hj : j.val < z.1.val
  · have e : memAt z j = some (z.2 ⟨j.val, hj⟩) := dif_pos hj
    rw [e] at h
    exact ⟨⟨j.val, hj⟩, Option.some.inj h⟩
  · have e : memAt z j = none := dif_neg hj
    rw [e] at h
    exact absurd h.symm (Option.some_ne_none pr)

omit [DecidableEq B] in
/-- **"Each pending particle allows at most one omission choice. At most `B` of the `𝒟` equally
likely choices allow any promotion"** [S-02:0869–0872], as a count of permutations: for a fixed
permutation of the slots of the big lists, at most `B (J! ℓ!)^{|𝒮|}` permutations of the slots of
the small lists lead to a state with an eligible pending particle. The congruence `Q` only needs
to determine the step modulo the prime of the particle. -/
theorem rare_count {e : ℤ} (hA : RareArith 𝒢 ℓ e) (Q : (g : B) → Particle 𝒢 g → ℤ → Prop)
    (hQ : ∀ (g : B) (pr : Particle 𝒢 g) (Δ₁ Δ₂ : ℤ), 0 < (pr.1 : ℕ) → Q g pr Δ₁ → Q g pr Δ₂ →
      ((pr.1 : ℕ) : ℤ) ∣ Δ₁ - Δ₂)
    (C : B → Finset (Fin J)) (r : AuxList 𝒢.big C) (s : MState 𝒢 J ℓ Bc)
    (πB : SlotPerms B J ℓ) (A : Finset (SlotPerms S J ℓ))
    (hmem : ∀ πS ∈ A, RareElig Q e C r (s.permLists (πS, πB))) :
    A.card ≤ Bc * (J.factorial * ℓ.factorial) ^ Fintype.card S := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | ⟨π₀, hπ₀⟩
  · rw [Finset.card_empty]
    exact Nat.zero_le _
  have hBc : memTotal s ≤ Bc := (hmem π₀ hπ₀).1
  have hinj : ∀ g, Function.Injective (s.xs g) := fun g =>
    (Equiv.injective_comp (π₀ g) (s.xs g)).mp ((hmem π₀ hπ₀).2.1 g)
  obtain ⟨Af, hAf⟩ : ∃ Af : (Σ g : B, Fin (s.mem g).1.val) → Finset (SlotPerms S J ℓ), ∀ a,
      Af a = A.filter fun πS =>
        Q a.1 ((s.mem a.1).2 a.2)
            (e * ((smallDil (permuteSlots πS s.xs) *
              bigDil C (permuteSlots πB s.xb) r : ℕ) : ℤ)) ∧
          ¬((((s.mem a.1).2 a.2).1 : ℕ) ∣
            smallDil (permuteSlots πS s.xs) * bigDil C (permuteSlots πB s.xb) r) :=
    ⟨_, fun _ => rfl⟩
  have hsub : A ⊆ Finset.univ.biUnion Af := by
    intro πS hπS
    obtain ⟨_, _, g, j, pr, hpr, hQ1, hnd⟩ := hmem πS hπS
    obtain ⟨j', hj'⟩ := rare_of_memAt (z := s.mem g) hpr
    refine Finset.mem_biUnion.mpr ⟨⟨g, j'⟩, Finset.mem_univ _, ?_⟩
    rw [hAf]
    refine Finset.mem_filter.mpr ⟨hπS, ?_⟩
    show Q g ((s.mem g).2 j')
          (e * ((smallDil (permuteSlots πS s.xs) *
            bigDil C (permuteSlots πB s.xb) r : ℕ) : ℤ)) ∧
        ¬((((s.mem g).2 j').1 : ℕ) ∣
          smallDil (permuteSlots πS s.xs) * bigDil C (permuteSlots πB s.xb) r)
    rw [hj']
    exact ⟨hQ1, hnd⟩
  have hcard : ∀ a, (Af a).card ≤ (J.factorial * ℓ.factorial) ^ Fintype.card S := by
    intro a
    refine rare_card_coset_le (Af a) fun σ hσ τ hτ g j => ?_
    rw [hAf] at hσ hτ
    obtain ⟨_, hσQ, hσnd⟩ := Finset.mem_filter.mp hσ
    obtain ⟨_, hτQ, _⟩ := Finset.mem_filter.mp hτ
    have hp : Nat.Prime (((s.mem a.1).2 a.2).1 : ℕ) :=
      hA.prime_big a.1 _ ((s.mem a.1).2 a.2).1.2
    have hcong := hQ a.1 _ _ _ hp.pos hσQ hτQ
    have hU : rareOmit (permuteSlots σ s.xs) = rareOmit (permuteSlots τ s.xs) :=
      rare_omit_eq hp (hA.not_dvd a.1 _ ((s.mem a.1).2 a.2).1.2)
        (smallDil_mul_rareOmit_permute σ τ s.xs)
        (hA.omit_lt (fun g' j' => permuteSlots σ s.xs g' (Sum.inr j')) a.1 _
          ((s.mem a.1).2 a.2).1.2)
        (hA.omit_lt (fun g' j' => permuteSlots τ s.xs g' (Sum.inr j')) a.1 _
          ((s.mem a.1).2 a.2).1.2)
        hσnd hcong
    exact rare_slots_of_omit_eq hA.prime_small hA.disjoint_small s.xs hinj σ τ hU g j
  have hI : Fintype.card (Σ g : B, Fin (s.mem g).1.val) = memTotal s := by
    rw [Fintype.card_sigma]
    unfold memTotal
    exact Finset.sum_congr rfl fun g _ => Fintype.card_fin _
  calc A.card ≤ (Finset.univ.biUnion Af).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Σ g : B, Fin (s.mem g).1.val)).card *
          (J.factorial * ℓ.factorial) ^ Fintype.card S :=
        Finset.card_biUnion_le_card_mul _ _ _ fun a _ => hcard a
    _ = memTotal s * (J.factorial * ℓ.factorial) ^ Fintype.card S := by
        rw [Finset.card_univ, hI]
    _ ≤ Bc * (J.factorial * ℓ.factorial) ^ Fintype.card S := Nat.mul_le_mul_right _ hBc

open _root_.Classical in
/-- **The proportion of the slot permutations after which a pending particle is eligible**: the
average over the permutations `π` of the slots of the active lists of the indicator of
`RareElig` at the permuted state. -/
def rareFrac (Q : (g : B) → Particle 𝒢 g → ℤ → Prop) (e : ℤ) (C : B → Finset (Fin J))
    (r : AuxList 𝒢.big C) (s : MState 𝒢 J ℓ Bc) : ℝ :=
  (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ *
    ∑ π : ListPerms S B J ℓ, (if RareElig Q e C r (s.permLists π) then (1 : ℝ) else 0)

/-- `|𝔖_M|^{|𝒮|} = 𝒟 · (J! ℓ!)^{|𝒮|}`. -/
theorem rare_card_slotPerms (S : Type) [Fintype S] [DecidableEq S] (J ℓ : ℕ) :
    Fintype.card (SlotPerms S J ℓ) =
      omissionNumber S J ℓ * (J.factorial * ℓ.factorial) ^ Fintype.card S := by
  have h3 : (J + ℓ).factorial = (J + ℓ).choose ℓ * (J.factorial * ℓ.factorial) := by
    rw [← mul_assoc]
    exact (Nat.add_choose_mul_factorial_mul_factorial J ℓ).symm
  rw [card_slotPerms, h3, mul_pow]
  rfl

open _root_.Classical in
/-- **"At most `B` of the `𝒟` equally likely choices allow any promotion"** [S-02:0871–0872]: the
proportion of the slot permutations after which a pending particle is eligible is at most
`B/𝒟`. -/
theorem rareFrac_le {e : ℤ} (hA : RareArith 𝒢 ℓ e) (Q : (g : B) → Particle 𝒢 g → ℤ → Prop)
    (hQ : ∀ (g : B) (pr : Particle 𝒢 g) (Δ₁ Δ₂ : ℤ), 0 < (pr.1 : ℕ) → Q g pr Δ₁ → Q g pr Δ₂ →
      ((pr.1 : ℕ) : ℤ) ∣ Δ₁ - Δ₂)
    (C : B → Finset (Fin J)) (r : AuxList 𝒢.big C) (s : MState 𝒢 J ℓ Bc) :
    rareFrac Q e C r s ≤ (Bc : ℝ) / (omissionNumber S J ℓ : ℝ) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (((J.factorial * ℓ.factorial) ^ Fintype.card S : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (omissionNumber S J ℓ : ℝ) := ⟨_, rfl⟩
  obtain ⟨cB, hcB⟩ : ∃ cB : ℝ, cB = (Fintype.card (SlotPerms B J ℓ) : ℝ) := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    exact Nat.cast_pos.mpr
      (pow_pos (Nat.mul_pos (Nat.factorial_pos J) (Nat.factorial_pos ℓ)) _)
  have hd0 : 0 < d := by
    rw [hd]
    exact Nat.cast_pos.mpr (omissionNumber_pos S J ℓ)
  have hcB0 : 0 < cB := by
    rw [hcB]
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hsum : ∑ π : ListPerms S B J ℓ,
        (if RareElig Q e C r (s.permLists π) then (1 : ℝ) else 0) ≤ cB * ((Bc : ℝ) * a) := by
    have h1 : ∑ π : ListPerms S B J ℓ,
          (if RareElig Q e C r (s.permLists π) then (1 : ℝ) else 0) =
        ∑ πB : SlotPerms B J ℓ, ∑ πS : SlotPerms S J ℓ,
          (if RareElig Q e C r (s.permLists (πS, πB)) then (1 : ℝ) else 0) :=
      (Fintype.sum_prod_type _).trans Finset.sum_comm
    rw [h1]
    calc ∑ πB : SlotPerms B J ℓ, ∑ πS : SlotPerms S J ℓ,
          (if RareElig Q e C r (s.permLists (πS, πB)) then (1 : ℝ) else 0)
        ≤ ∑ _πB : SlotPerms B J ℓ, (Bc : ℝ) * a := by
          refine Finset.sum_le_sum fun πB _ => ?_
          rw [Finset.sum_boole, ha]
          have h := rare_count hA Q hQ C r s πB
            (Finset.univ.filter fun πS : SlotPerms S J ℓ =>
              RareElig Q e C r (s.permLists (πS, πB)))
            (fun πS hπS => (Finset.mem_filter.mp hπS).2)
          exact_mod_cast h
      _ = cB * ((Bc : ℝ) * a) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcB]
  have hcard : (Fintype.card (ListPerms S B J ℓ) : ℝ) = d * a * cB := by
    have h1 : Fintype.card (ListPerms S B J ℓ) =
        Fintype.card (SlotPerms S J ℓ) * Fintype.card (SlotPerms B J ℓ) := Fintype.card_prod _ _
    rw [h1, rare_card_slotPerms S J ℓ, ha, hd, hcB, Nat.cast_mul, Nat.cast_mul]
  unfold rareFrac
  rw [hcard, ← hd]
  calc (d * a * cB)⁻¹ * ∑ π : ListPerms S B J ℓ,
        (if RareElig Q e C r (s.permLists π) then (1 : ℝ) else 0)
      ≤ (d * a * cB)⁻¹ * (cB * ((Bc : ℝ) * a)) :=
        mul_le_mul_of_nonneg_left hsum
          (inv_nonneg.mpr (mul_nonneg (mul_nonneg hd0.le ha0.le) hcB0.le))
    _ = (Bc : ℝ) * d⁻¹ * (a⁻¹ * a) * (cB⁻¹ * cB) := by
        rw [mul_inv, mul_inv]
        ring
    _ = (Bc : ℝ) / d := by
        rw [inv_mul_cancel₀ ha0.ne', inv_mul_cancel₀ hcB0.ne', mul_one, mul_one, div_eq_mul_inv]

open _root_.Classical in
theorem rareFrac_nonneg (Q : (g : B) → Particle 𝒢 g → ℤ → Prop) (e : ℤ)
    (C : B → Finset (Fin J)) (r : AuxList 𝒢.big C) (s : MState 𝒢 J ℓ Bc) :
    0 ≤ rareFrac Q e C r s := by
  unfold rareFrac
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun π _ => ?_)
  split_ifs
  · exact zero_le_one
  · exact le_rfl

open _root_.Classical in
/-- **The average over the slot permutations of an integral of the indicator of eligibility** is
at most `B/𝒟` times the integral: for a nonnegative function `g` of the states,
`|𝔖|⁻¹ ∑_π ∑_s g(s) 1[eligible at s·π] ≤ (B/𝒟) ∑_s g(s)`. -/
theorem rare_sum_frac_le {e : ℤ} (hA : RareArith 𝒢 ℓ e)
    (Q : (g : B) → Particle 𝒢 g → ℤ → Prop)
    (hQ : ∀ (g : B) (pr : Particle 𝒢 g) (Δ₁ Δ₂ : ℤ), 0 < (pr.1 : ℕ) → Q g pr Δ₁ → Q g pr Δ₂ →
      ((pr.1 : ℕ) : ℤ) ∣ Δ₁ - Δ₂)
    (C : B → Finset (Fin J)) (r : AuxList 𝒢.big C) (g : MState 𝒢 J ℓ Bc → ℝ)
    (hg : ∀ s, 0 ≤ g s) :
    ∑ π : ListPerms S B J ℓ, (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ *
        ∑ s : MState 𝒢 J ℓ Bc,
          g s * (if RareElig Q e C r (s.permLists π) then (1 : ℝ) else 0) ≤
      (Bc : ℝ) / (omissionNumber S J ℓ : ℝ) * ∑ s : MState 𝒢 J ℓ Bc, g s := by
  have h2 : ∀ s : MState 𝒢 J ℓ Bc, g s * rareFrac Q e C r s =
      ∑ π : ListPerms S B J ℓ, (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ *
        (g s * (if RareElig Q e C r (s.permLists π) then (1 : ℝ) else 0)) := by
    intro s
    unfold rareFrac
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun π _ => by ring
  calc ∑ π : ListPerms S B J ℓ, (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ *
        ∑ s : MState 𝒢 J ℓ Bc,
          g s * (if RareElig Q e C r (s.permLists π) then (1 : ℝ) else 0)
      = ∑ π : ListPerms S B J ℓ, ∑ s : MState 𝒢 J ℓ Bc,
          (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ *
            (g s * (if RareElig Q e C r (s.permLists π) then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl fun π _ => Finset.mul_sum _ _ _
    _ = ∑ s : MState 𝒢 J ℓ Bc, ∑ π : ListPerms S B J ℓ,
          (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ *
            (g s * (if RareElig Q e C r (s.permLists π) then (1 : ℝ) else 0)) :=
        Finset.sum_comm
    _ = ∑ s : MState 𝒢 J ℓ Bc, g s * rareFrac Q e C r s :=
        Finset.sum_congr rfl fun s _ => (h2 s).symm
    _ ≤ ∑ s : MState 𝒢 J ℓ Bc, g s * ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ)) :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (rareFrac_le hA Q hQ C r s) (hg s)
    _ = (Bc : ℝ) / (omissionNumber S J ℓ : ℝ) * ∑ s : MState 𝒢 J ℓ Bc, g s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => mul_comm _ _

/-! ### Symmetry in the particle indices -/

omit [Fintype B] [DecidableEq S] in
/-- The particles of the memory of the group whose particle indices are permuted. -/
theorem rare_memAt_permMem_self (s : MState 𝒢 J ℓ Bc) (g₀ : B)
    (σ : Equiv.Perm (Fin (s.mem g₀).1.val)) (j : Fin Bc) :
    memAt ((s.permMem g₀ σ).mem g₀) j = memAt (s.mem g₀) (extPerm (s.mem g₀).1 σ j) := by
  have e : (s.permMem g₀ σ).mem g₀ = ⟨(s.mem g₀).1, (s.mem g₀).2 ∘ σ⟩ :=
    Function.update_self _ _ _
  rw [e]
  exact memAt_comp_extPerm (s.mem g₀).1 (s.mem g₀).2 σ j

omit [DecidableEq S] in
/-- **The eligibility of a pending particle is symmetric in the particle indices.** -/
theorem rareElig_permMem (Q : (g : B) → Particle 𝒢 g → ℤ → Prop) (e : ℤ)
    (C : B → Finset (Fin J)) (r : AuxList 𝒢.big C) (s : MState 𝒢 J ℓ Bc) (g₀ : B)
    (σ : Equiv.Perm (Fin (s.mem g₀).1.val)) :
    RareElig Q e C r (s.permMem g₀ σ) ↔ RareElig Q e C r s := by
  have hfw : ∀ (g : B) (j : Fin Bc), ∃ j' : Fin Bc,
      memAt ((s.permMem g₀ σ).mem g) j = memAt (s.mem g) j' := by
    intro g j
    by_cases hg : g₀ = g
    · subst hg
      exact ⟨extPerm (s.mem g₀).1 σ j, rare_memAt_permMem_self s g₀ σ j⟩
    · refine ⟨j, ?_⟩
      have e1 : (s.permMem g₀ σ).mem g = s.mem g :=
        Function.update_of_ne (fun h => hg h.symm) _ _
      rw [e1]
  have hbw : ∀ (g : B) (j : Fin Bc), ∃ j' : Fin Bc,
      memAt (s.mem g) j = memAt ((s.permMem g₀ σ).mem g) j' := by
    intro g j
    by_cases hg : g₀ = g
    · subst hg
      refine ⟨(extPerm (s.mem g₀).1 σ).symm j, ?_⟩
      rw [rare_memAt_permMem_self, Equiv.apply_symm_apply]
    · refine ⟨j, ?_⟩
      have e1 : (s.permMem g₀ σ).mem g = s.mem g :=
        Function.update_of_ne (fun h => hg h.symm) _ _
      rw [e1]
  constructor
  · rintro ⟨h1, h2, g, j, pr, hpr, hQ, hnd⟩
    obtain ⟨j', hj'⟩ := hfw g j
    have h1' : memTotal s ≤ Bc := by
      rw [← memTotal_permMem s g₀ σ]
      exact h1
    have hpr' : memAt (s.mem g) j' = some pr := by
      rw [← hj']
      exact hpr
    exact ⟨h1', h2, g, j', pr, hpr', hQ, hnd⟩
  · rintro ⟨h1, h2, g, j, pr, hpr, hQ, hnd⟩
    obtain ⟨j', hj'⟩ := hbw g j
    have h1' : memTotal (s.permMem g₀ σ) ≤ Bc := by
      rw [memTotal_permMem s g₀ σ]
      exact h1
    have hpr' : memAt ((s.permMem g₀ σ).mem g) j' = some pr := by
      rw [← hj']
      exact hpr
    exact ⟨h1', h2, g, j', pr, hpr', hQ, hnd⟩

open _root_.Classical in
omit [DecidableEq S] in
/-- The indicator of eligibility times a function which is symmetric in the particle indices is
symmetric in the particle indices. -/
theorem rare_ind_mul_memSymmetric (Q : (g : B) → Particle 𝒢 g → ℤ → Prop) (e : ℤ)
    (C : B → Finset (Fin J)) (r : AuxList 𝒢.big C) {f : MState 𝒢 J ℓ Bc → ℝ}
    (hf : MemSymmetric f) :
    MemSymmetric fun s : MState 𝒢 J ℓ Bc =>
      (if RareElig Q e C r s then (1 : ℝ) else 0) * f s := by
  intro s g σ
  have e1 : (if RareElig Q e C r (s.permMem g σ) then (1 : ℝ) else 0) =
      (if RareElig Q e C r s then (1 : ℝ) else 0) :=
    ite_congr_of_iff (rareElig_permMem Q e C r s g σ) rfl rfl
  show (if RareElig Q e C r (s.permMem g σ) then (1 : ℝ) else 0) * f (s.permMem g σ) =
    (if RareElig Q e C r s then (1 : ℝ) else 0) * f s
  rw [e1, hf s g σ]

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- Undoing a permutation of the slots of the active lists. -/
theorem rare_permLists_inv (π : ListPerms S B J ℓ) (s : MState 𝒢 J ℓ Bc) :
    (s.permLists π).permLists π⁻¹ = s :=
  (l38_permListsEquiv π).left_inv s

end Elig

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
