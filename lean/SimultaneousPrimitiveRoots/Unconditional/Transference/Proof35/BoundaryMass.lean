module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemPerm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The mass of the boundary vector `𝟏_∅`

Source: `verification/stage7-sources/S-02.tex`, lines 296–302 and 812–819
(`[S-02:0296–0302, 0812–0819]`).

"The empty-memory boundary vector has bounded norm: the small part has mass at most one by
(eq:initial-factorial-mass), and the big part has mass `∏_{g ∈ ℬ} μ̃_g(𝒫_g)^M`."

* `boundary_wNormSq_eq` — `‖𝟏_∅‖² = (small part) · ∑_{xb} ∏_g ∏_i μ̃_g(xb_{g,i})`: only the empty
  memories contribute, with mass `1` (`boundary_sum_mem`).
* `boundary_sum_bigListMass` — the big part is `∏_g μ̃_g(𝒫_g)^M`.
* `boundary_smallPart_le_one` — (eq:initial-factorial-mass): the expected total mass of the small
  states is at most one,
  `V_g^{-M} ∑_{p_1, …, p_M ∈ 𝒫_g distinct} 1/(p_1 ⋯ p_M) ≤ 1` in every small group. The Haar
  probability that the residues at distinct primes vanish is the product of the `1/p`
  (`boundary_haar_card`); labels of different small groups are distinct because the groups are
  disjoint.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Independent uniform residues -/

/-- **The Haar probability that the residues at distinct primes vanish**: for an injective family
`e` of primes of `Q`, `#{y : y_{e a} = 0 for all a} / #(∏_{p ∈ Q} ℤ/pℤ) = ∏_a 1/e(a)`. -/
theorem boundary_haar_card (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 0 < p) {ι : Type*} [Fintype ι]
    (e : ι → {p : ℕ // p ∈ Q}) (he : Function.Injective e)
    [DecidablePred fun y : ResVec Q => ∀ a, y (e a) = 0] :
    haarMass Q * ((Finset.univ.filter fun y : ResVec Q => ∀ a, y (e a) = 0).card : ℝ) =
      ∏ a, (1 / ((e a : ℕ) : ℝ)) := by
  have hc0 : ∀ p : {p : ℕ // p ∈ Q}, ((p : ℕ) : ℝ) ≠ 0 :=
    fun p => Nat.cast_ne_zero.mpr (hQ p.1 p.2).ne'
  have hfilter : (Finset.univ.filter fun y : ResVec Q => ∀ a, y (e a) = 0) =
      Fintype.piFinset (fun p : {p : ℕ // p ∈ Q} =>
        if p ∈ Finset.univ.image e then ({0} : Finset (Res p.1)) else Finset.univ) := by
    ext y
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨_, h⟩ p
      by_cases hp : p ∈ Finset.univ.image e
      · rw [if_pos hp]
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_singleton.mpr (h a)
      · rw [if_neg hp]
        exact Finset.mem_univ _
    · intro h
      refine ⟨Finset.mem_univ _, fun a => ?_⟩
      have h1 := h (e a)
      rw [if_pos (Finset.mem_image_of_mem e (Finset.mem_univ a))] at h1
      exact Finset.mem_singleton.mp h1
  have hcard : ((Finset.univ.filter fun y : ResVec Q => ∀ a, y (e a) = 0).card : ℝ) =
      ∏ p : {p : ℕ // p ∈ Q}, if p ∈ Finset.univ.image e then (1 : ℝ) else ((p : ℕ) : ℝ) := by
    rw [hfilter, Fintype.card_piFinset, Nat.cast_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases hp : p ∈ Finset.univ.image e
    · rw [if_pos hp, if_pos hp, Finset.card_singleton, Nat.cast_one]
    · rw [if_neg hp, if_neg hp, Finset.card_univ, Res.card p.1 (hQ p.1 p.2)]
  have hhaar : haarMass Q = (∏ p : {p : ℕ // p ∈ Q}, ((p : ℕ) : ℝ))⁻¹ := by
    unfold haarMass
    rw [Fintype.card_pi, Nat.cast_prod]
    refine congrArg (fun t : ℝ => t⁻¹) (Finset.prod_congr rfl fun p _ => ?_)
    rw [Res.card p.1 (hQ p.1 p.2)]
  have hsplit : (∏ p : {p : ℕ // p ∈ Q},
        if p ∈ Finset.univ.image e then (1 : ℝ) else ((p : ℕ) : ℝ)) *
      ∏ a, ((e a : ℕ) : ℝ) = ∏ p : {p : ℕ // p ∈ Q}, ((p : ℕ) : ℝ) := by
    have h1 : ∏ a, ((e a : ℕ) : ℝ) = ∏ p : {p : ℕ // p ∈ Q},
        if p ∈ Finset.univ.image e then ((p : ℕ) : ℝ) else 1 := by
      rw [Finset.prod_ite_mem, Finset.univ_inter]
      exact Eq.symm (Finset.prod_image he.injOn)
    rw [h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases hp : p ∈ Finset.univ.image e
    · rw [if_pos hp, if_pos hp, one_mul]
    · rw [if_neg hp, if_neg hp, mul_one]
  have hC0 : (∏ p : {p : ℕ // p ∈ Q}, ((p : ℕ) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => hc0 p
  have key : ∀ A D C : ℝ, A * D = C → C ≠ 0 → C⁻¹ * A = D⁻¹ := by
    intro A D C h hC
    have hA : A ≠ 0 := fun h0 => hC (by rw [← h, h0, zero_mul])
    rw [← h, mul_inv, mul_comm A⁻¹ D⁻¹, mul_assoc, inv_mul_cancel₀ hA, mul_one]
  have e1 : (∏ a, (1 / ((e a : ℕ) : ℝ))) = (∏ a, ((e a : ℕ) : ℝ))⁻¹ := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, one_div]
  rw [hhaar, hcard, e1]
  exact key _ _ _ hsplit hC0

section States

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ}

/-! ### The small part: (eq:initial-factorial-mass) -/

omit [Fintype B] [DecidableEq B] in
/-- The Haar probability that a small list is a small state is at most the product of the
reciprocals of its labels. -/
theorem boundary_smallState_card_le (𝒢 : GroupFamily S B) (hpos : ∀ g, ∀ p ∈ 𝒢.small g, 0 < p)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g'))
    (xs : LabelList 𝒢.small J ℓ)
    [DecidablePred fun y : ResVec (smallPrimes 𝒢) => IsSmallState 𝒢 y xs] :
    haarMass (smallPrimes 𝒢) *
        ((Finset.univ.filter fun y : ResVec (smallPrimes 𝒢) => IsSmallState 𝒢 y xs).card : ℝ) ≤
      ∏ g, ∏ i : Slot J ℓ, (1 / ((xs g i : ℕ) : ℝ)) := by
  by_cases hinj : ∀ g, Function.Injective (xs g)
  · have hQpos : ∀ p ∈ smallPrimes 𝒢, 0 < p := by
      intro p hp
      obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp hp
      exact hpos g p hg
    have hmem : ∀ (g : S) (i : Slot J ℓ), (xs g i : ℕ) ∈ smallPrimes 𝒢 :=
      fun g i => Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (xs g i).2⟩
    obtain ⟨e, he⟩ : ∃ e : S × Slot J ℓ → {p : ℕ // p ∈ smallPrimes 𝒢},
        ∀ a, e a = ⟨(xs a.1 a.2 : ℕ), hmem a.1 a.2⟩ := ⟨_, fun _ => rfl⟩
    have heinj : Function.Injective e := by
      rintro ⟨g, i⟩ ⟨g', i'⟩ h
      rw [he, he] at h
      have hval : (xs g i : ℕ) = (xs g' i' : ℕ) := congrArg Subtype.val h
      have hg : g = g' := by
        by_contra hne
        have h1 : (xs g i : ℕ) ∈ 𝒢.small g' := by
          rw [hval]
          exact (xs g' i').2
        exact Finset.disjoint_left.mp (hdisj g g' hne) (xs g i).2 h1
      subst hg
      have hi : i = i' := hinj g (Subtype.ext hval)
      rw [hi]
    have hfilter : (Finset.univ.filter fun y : ResVec (smallPrimes 𝒢) => IsSmallState 𝒢 y xs) =
        Finset.univ.filter fun y : ResVec (smallPrimes 𝒢) => ∀ a, y (e a) = 0 := by
      refine Finset.filter_congr fun y _ => ?_
      constructor
      · intro h a
        obtain ⟨h', hy⟩ := h.2 a.1 a.2
        rw [he]
        exact hy
      · intro h
        refine And.intro hinj fun g i => ?_
        show ∃ h' : (xs g i : ℕ) ∈ smallPrimes 𝒢, y ⟨(xs g i : ℕ), h'⟩ = 0
        refine ⟨hmem g i, ?_⟩
        have h1 := h (g, i)
        rw [he] at h1
        exact h1
    rw [hfilter, boundary_haar_card (smallPrimes 𝒢) hQpos e heinj, Fintype.prod_prod_type]
    refine le_of_eq (Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => ?_)
    exact congrArg (fun t : {p : ℕ // p ∈ smallPrimes 𝒢} => 1 / ((t : ℕ) : ℝ)) (he (g, i))
  · have hempty : (Finset.univ.filter fun y : ResVec (smallPrimes 𝒢) => IsSmallState 𝒢 y xs) =
        ∅ := Finset.filter_eq_empty_iff.mpr fun y _ h => hinj h.1
    rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ =>
      div_nonneg zero_le_one (Nat.cast_nonneg _)

omit [Fintype B] [DecidableEq B] in
/-- **(eq:initial-factorial-mass)** [S-02:0296–0302]: "the expected total mass of all initial
lists is at most one". -/
theorem boundary_smallPart_le_one (𝒢 : GroupFamily S B) (hpos : ∀ g, ∀ p ∈ 𝒢.small g, 0 < p)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g'))
    (hV : ∀ g, 0 < Graph.primeGroupReciprocalMass (𝒢.small g)) (J ℓ : ℕ)
    [∀ (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ),
      Decidable (IsSmallState 𝒢 y xs)] :
    ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
      (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ else 0) ≤
        1 := by
  have hsmall0 : 0 ≤ smallListMass 𝒢 J ℓ :=
    Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (hV g).le _)
  have hxs : ∀ xs : LabelList 𝒢.small J ℓ,
      ∑ y : ResVec (smallPrimes 𝒢),
        (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ else 0) ≤
      smallListMass 𝒢 J ℓ * ∏ g, ∏ i : Slot J ℓ, (1 / ((xs g i : ℕ) : ℝ)) := by
    intro xs
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    refine le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left
      (boundary_smallState_card_le 𝒢 hpos hdisj xs) hsmall0)
    ring
  have hW : ∑ xs : LabelList 𝒢.small J ℓ, ∏ g, ∏ i : Slot J ℓ, (1 / ((xs g i : ℕ) : ℝ)) =
      ∏ g, Graph.primeGroupReciprocalMass (𝒢.small g) ^ (J + ℓ) := by
    have h1 : ∑ xs : LabelList 𝒢.small J ℓ, ∏ g, ∏ i : Slot J ℓ, (1 / ((xs g i : ℕ) : ℝ)) =
        ∏ g : S, ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.small g},
          ∏ i : Slot J ℓ, (1 / ((w i : ℕ) : ℝ)) :=
      (Fintype.prod_sum fun (g : S) (w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.small g}) =>
        ∏ i : Slot J ℓ, (1 / ((w i : ℕ) : ℝ))).symm
    have h2 : ∀ g : S, ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.small g},
        ∏ i : Slot J ℓ, (1 / ((w i : ℕ) : ℝ)) =
          Graph.primeGroupReciprocalMass (𝒢.small g) ^ (J + ℓ) := by
      intro g
      have h3 : ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.small g},
          ∏ i : Slot J ℓ, (1 / ((w i : ℕ) : ℝ)) =
            ∏ _i : Slot J ℓ, ∑ p : {p : ℕ // p ∈ 𝒢.small g}, (1 / ((p : ℕ) : ℝ)) :=
        (Fintype.prod_sum fun (_ : Slot J ℓ) (p : {p : ℕ // p ∈ 𝒢.small g}) =>
          (1 / ((p : ℕ) : ℝ))).symm
      have h4 : ∑ p : {p : ℕ // p ∈ 𝒢.small g}, (1 / ((p : ℕ) : ℝ)) =
          Graph.primeGroupReciprocalMass (𝒢.small g) :=
        Finset.sum_coe_sort (𝒢.small g) fun p => (1 / (p : ℝ))
      rw [h3, Finset.prod_const, Finset.card_univ, card_slot, h4]
    rw [h1]
    exact Finset.prod_congr rfl fun g _ => h2 g
  calc ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
        (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ else 0)
      = ∑ xs : LabelList 𝒢.small J ℓ, ∑ y : ResVec (smallPrimes 𝒢),
          (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ else 0) :=
        Finset.sum_comm
    _ ≤ ∑ xs : LabelList 𝒢.small J ℓ,
          smallListMass 𝒢 J ℓ * ∏ g, ∏ i : Slot J ℓ, (1 / ((xs g i : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun xs _ => hxs xs
    _ = smallListMass 𝒢 J ℓ * ∏ g, Graph.primeGroupReciprocalMass (𝒢.small g) ^ (J + ℓ) := by
        rw [← Finset.mul_sum, hW]
    _ = 1 := by
        unfold smallListMass
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun g _ => inv_mul_cancel₀ (pow_ne_zero _ (hV g).ne')

/-! ### The big part -/

omit [Fintype S] [DecidableEq S] in
/-- The total mass of the big active lists is `∏_g μ̃_g(𝒫_g)^M`. -/
theorem boundary_sum_bigListMass (𝒢 : GroupFamily S B) (q : ℝ) (n J ℓ : ℕ) :
    ∑ xb : LabelList 𝒢.big J ℓ, bigListMass 𝒢 q n xb =
      ∏ g, (∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p) ^ (J + ℓ) := by
  have h1 : ∑ xb : LabelList 𝒢.big J ℓ, bigListMass 𝒢 q n xb =
      ∏ g : B, ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
        ∏ i : Slot J ℓ, tiltLaw (𝒢.big g) q n (w i) :=
    (Fintype.prod_sum fun (g : B) (w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) =>
      ∏ i : Slot J ℓ, tiltLaw (𝒢.big g) q n (w i)).symm
  have h2 : ∀ g : B, ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
      ∏ i : Slot J ℓ, tiltLaw (𝒢.big g) q n (w i) =
        (∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p) ^ (J + ℓ) := by
    intro g
    have h3 : ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
        ∏ i : Slot J ℓ, tiltLaw (𝒢.big g) q n (w i) =
          ∏ _i : Slot J ℓ, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) q n p :=
      (Fintype.prod_sum fun (_ : Slot J ℓ) (p : {p : ℕ // p ∈ 𝒢.big g}) =>
        tiltLaw (𝒢.big g) q n p).symm
    have h4 : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) q n p =
        ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p :=
      Finset.sum_coe_sort (𝒢.big g) fun p => tiltLaw (𝒢.big g) q n p
    rw [h3, Finset.prod_const, Finset.card_univ, card_slot, h4]
  rw [h1]
  exact Finset.prod_congr rfl fun g _ => h2 g

/-! ### The empty memories -/

/-- The point mass of the empty tuple is `1`. -/
theorem boundary_pointMass_zero {Z : Type*} (w : Z → ℝ) (x : Fin 0 → Z) :
    Graph.factorialMemoryPointMass w x = 1 := by
  unfold Graph.factorialMemoryPointMass
  simp

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- A memory of size zero is the empty memory. -/
theorem boundary_mem_eq_empty {g : B} (z : Mem 𝒢 Bc g) (h : z.1.val = 0) :
    z = emptyMem 𝒢 Bc g := by
  refine mem_ext_ofFn z (emptyMem 𝒢 Bc g) ?_
  have h1 : List.ofFn z.2 = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn]; exact h)
  rw [h1]
  exact List.ofFn_zero.symm

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- The measure of `ℋ` as the product of its small part, the measure of the big active list and
the measure of the memories. -/
theorem boundary_memWeight_factor (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ)
    (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ)
    (mem : (g : B) → Mem 𝒢 Bc g) :
    memWeight 𝒢 q n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) =
      (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ else 0) *
        bigListMass 𝒢 q n xb * memMass 𝒢 q n mem := by
  by_cases h : IsSmallState 𝒢 y xs
  · rw [if_pos h]
    unfold memWeight
    exact if_pos h
  · rw [if_neg h, zero_mul, zero_mul]
    unfold memWeight
    exact if_neg h

omit [DecidableEq S] in
open _root_.Classical in
/-- For fixed residues and active lists, only the empty memories contribute to `‖𝟏_∅‖²`, with
mass `1`. -/
theorem boundary_sum_mem (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ) (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ) :
    ∑ mem : (g : B) → Mem 𝒢 Bc g,
        memWeight 𝒢 q n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
          ‖emptyVec 𝒢 J ℓ Bc ⟨y, xs, xb, mem⟩‖ ^ 2 =
      (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ else 0) *
        bigListMass 𝒢 q n xb := by
  rw [Finset.sum_eq_single_of_mem (fun g => emptyMem 𝒢 Bc g) (Finset.mem_univ _)]
  · have h1 : emptyVec 𝒢 J ℓ Bc (⟨y, xs, xb, fun g => emptyMem 𝒢 Bc g⟩ : MState 𝒢 J ℓ Bc) =
        1 := by
      unfold emptyVec
      exact if_pos (Finset.sum_eq_zero fun g _ => rfl)
    have h2 : memMass 𝒢 q n (fun g => emptyMem 𝒢 Bc g) = 1 :=
      Finset.prod_eq_one fun g _ => boundary_pointMass_zero _ _
    rw [h1, boundary_memWeight_factor, h2, norm_one, one_pow, mul_one, mul_one]
  · intro mem _ hne
    have hpos : memTotal (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) ≠ 0 := by
      intro h0
      refine hne (funext fun g => boundary_mem_eq_empty (mem g) ?_)
      exact Finset.sum_eq_zero_iff.mp h0 g (Finset.mem_univ g)
    have h1 : emptyVec 𝒢 J ℓ Bc (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) = 0 := by
      unfold emptyVec
      exact if_neg hpos
    rw [h1, norm_zero, zero_pow two_ne_zero, mul_zero]

open _root_.Classical in
/-- **`‖𝟏_∅‖²` is the product of the small part and of the total mass of the big active
lists.** -/
theorem boundary_wNormSq_eq (𝒢 : GroupFamily S B) (q : ℝ) (n J ℓ Bc : ℕ) :
    wNormSq (memWeight 𝒢 q n) (emptyVec 𝒢 J ℓ Bc) =
      (∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
        if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ else 0) *
        ∑ xb : LabelList 𝒢.big J ℓ, bigListMass 𝒢 q n xb := by
  have e : wNormSq (memWeight 𝒢 q n) (emptyVec 𝒢 J ℓ Bc) =
      ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
        ∑ xb : LabelList 𝒢.big J ℓ, ∑ mem : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 q n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
            ‖emptyVec 𝒢 J ℓ Bc ⟨y, xs, xb, mem⟩‖ ^ 2 := by
    unfold wNormSq
    refine (Fintype.sum_equiv MState.equivProd _
      (fun t => memWeight 𝒢 q n (⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ : MState 𝒢 J ℓ Bc) *
        ‖emptyVec 𝒢 J ℓ Bc ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩‖ ^ 2) (fun s => rfl)).trans ?_
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun y _ => ?_)
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun xs _ => ?_)
    exact Fintype.sum_prod_type _
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun xs _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun xb _ => boundary_sum_mem 𝒢 q n y xs xb

end States

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
