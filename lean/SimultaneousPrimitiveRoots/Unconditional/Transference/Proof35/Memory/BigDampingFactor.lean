module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.Statements
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The big endpoint damping of a big state as a product over the big primes

Source: `verification/stage7-sources/S-02.tex`, lines 226–234 (`[S-02:0226–0234]`),
(eq:path-residue-factor).

Tools for `BigResidueProductProof.lean` (part (C1) of the proof of [S] Lemma 3.7). Nothing here
involves a skeleton.

* `bigRes_ite_congr`, `bigRes_ite_and`, `bigRes_ite_prod`, `bigRes_ite_cases`, `bigRes_phi_mul` —
  lemmas on `if … then … else …` with arbitrary decidability instances.
* `bigRes_prod_adjacent` — `∏_{i<n} a_i a_{i+1}` as a product over `i ≤ n`: every `a_i` occurs
  once as a left factor (`i < n`) and once as a right factor (`0 < i`).
* `isBigState_permuteSlots` — `IsBigState` is invariant under slot permutations.
* `bigRes_countHits_eq`, `bigRes_group_damping` — in a group whose `M` labels are distinct hits,
  `q^{(ω_g - M)/2} = ∏_{p ∈ 𝒫_g} (√q)^{[p hit, p not a label]}`.
* `bigRes_bigDamping_eq`, `bigRes_state_damping` — for pairwise disjoint big groups,
  `1_{big state at y} · bigDamping y = 1_{lists injective} · ∏_{p big} F_p(y_p)`, where `F_p(t)` is
  `1_{t = 0}` if `p` is a label and `(√q)^{1_{t = 0}}` otherwise.
* `bigRes_resAvg_prod` — the mean over a residue vector of a product over its coordinates is the
  product of the one-coordinate means ("independent uniform residues", [S-02:0238–0240]).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### `if … then … else …` with arbitrary decidability instances -/

/-- `if` with equivalent conditions and equal branches. -/
theorem bigRes_ite_congr {α : Sort*} {P Q : Prop} {hP : Decidable P} {hQ : Decidable Q}
    {x y u v : α} (hc : P ↔ Q) (ht : x = u) (he : y = v) :
    @ite α P hP x y = @ite α Q hQ u v := by
  subst ht
  subst he
  by_cases h : P
  · exact (if_pos h).trans (if_pos (hc.mp h)).symm
  · exact (if_neg h).trans (if_neg (fun hq => h (hc.mpr hq))).symm

/-- An `if` over a conjunction, with a product as value, is the product of the two `if`s. -/
theorem bigRes_ite_and {P Q P' Q' : Prop} {hPQ : Decidable (P ∧ Q)} {hP : Decidable P'}
    {hQ : Decidable Q'} (hp : P ↔ P') (hq : Q ↔ Q') (c a b : ℝ) :
    @ite ℝ (P ∧ Q) hPQ (c * (a * b)) 0 = c * (@ite ℝ P' hP a 0 * @ite ℝ Q' hQ b 0) := by
  by_cases h1 : P'
  · by_cases h2 : Q'
    · rw [if_pos (And.intro (hp.mpr h1) (hq.mpr h2)), if_pos h1, if_pos h2]
    · rw [if_neg (fun h : P ∧ Q => h2 (hq.mp h.2)), if_neg h2, mul_zero, mul_zero]
  · rw [if_neg (fun h : P ∧ Q => h1 (hp.mp h.1)), if_neg h1, zero_mul, mul_zero]

/-- An `if` with default value `1` commutes with a product. -/
theorem bigRes_ite_prod {ι : Type*} {c : Prop} {hc : Decidable c} (s : Finset ι) (f : ι → ℝ) :
    @ite ℝ c hc (∏ x ∈ s, f x) 1 = ∏ x ∈ s, @ite ℝ c hc (f x) 1 := by
  by_cases h : c
  · rw [if_pos h]
    exact Finset.prod_congr rfl fun x _ => (if_pos h).symm
  · rw [if_neg h]
    exact (Finset.prod_eq_one fun x _ => if_neg h).symm

/-- The factor of a prime which is hit (`H ↔ Z`): `s` if it is hit and not active, in the form
"indicator if active, `s^{[hit]}` otherwise". An active prime is hit (`A → Z`). -/
theorem bigRes_ite_cases {A Z H : Prop} {hA : Decidable A} {hZ : Decidable Z}
    {hHA : Decidable (H ∧ ¬A)} (s : ℝ) (hHZ : H ↔ Z) (hAZ : A → Z) :
    @ite ℝ (H ∧ ¬A) hHA s 1 = @ite ℝ A hA (@ite ℝ Z hZ 1 0) (@ite ℝ Z hZ s 1) := by
  by_cases hA' : A
  · rw [if_neg (fun h : H ∧ ¬A => h.2 hA'), if_pos hA', if_pos (hAZ hA')]
  · by_cases hZ' : Z
    · rw [if_pos (And.intro (hHZ.mpr hZ') hA'), if_neg hA', if_pos hZ']
    · rw [if_neg (fun h : H ∧ ¬A => hZ' (hHZ.mp h.1)), if_neg hA', if_neg hZ']

/-- The factors "indicator if active, `c^{[hit]}` otherwise" are multiplicative in `c`. -/
theorem bigRes_phi_mul {A Z : Prop} {hA : Decidable A} {hZ : Decidable Z} (a b : ℝ) :
    @ite ℝ A hA (@ite ℝ Z hZ 1 0) (@ite ℝ Z hZ a 1) *
        @ite ℝ A hA (@ite ℝ Z hZ 1 0) (@ite ℝ Z hZ b 1) =
      @ite ℝ A hA (@ite ℝ Z hZ 1 0) (@ite ℝ Z hZ (a * b) 1) := by
  by_cases h1 : A <;> by_cases h2 : Z <;> simp [h1, h2]

/-! ### Products of adjacent factors -/

/-- `∏_{i<n} a_i a_{i+1} = ∏_{i≤n} a_i^{[i<n]} a_i^{[0<i]}`: every `a_i` occurs once as a left
factor (for `i < n`) and once as a right factor (for `0 < i`). -/
theorem bigRes_prod_adjacent {M : Type*} [CommMonoid M] (a : ℕ → M) (n : ℕ) :
    ∏ i ∈ Finset.range n, (a i * a (i + 1)) =
      ∏ i ∈ Finset.range (n + 1),
        ((if i < n then a i else 1) * (if 0 < i then a i else 1)) := by
  have hL : ∏ i ∈ Finset.range (n + 1), (if i < n then a i else 1) =
      ∏ i ∈ Finset.range n, a i := by
    rw [Finset.prod_range_succ, if_neg (Nat.lt_irrefl n), mul_one]
    exact Finset.prod_congr rfl fun i hi => if_pos (Finset.mem_range.mp hi)
  have hR : ∏ i ∈ Finset.range (n + 1), (if 0 < i then a i else 1) =
      ∏ i ∈ Finset.range n, a (i + 1) := by
    rw [Finset.prod_range_succ', if_neg (Nat.lt_irrefl 0), mul_one]
    exact Finset.prod_congr rfl fun i _ => if_pos (Nat.succ_pos i)
  calc ∏ i ∈ Finset.range n, (a i * a (i + 1))
      = (∏ i ∈ Finset.range n, a i) * ∏ i ∈ Finset.range n, a (i + 1) :=
        Finset.prod_mul_distrib
    _ = (∏ i ∈ Finset.range (n + 1), (if i < n then a i else 1)) *
          ∏ i ∈ Finset.range (n + 1), (if 0 < i then a i else 1) := by rw [hL, hR]
    _ = ∏ i ∈ Finset.range (n + 1),
          ((if i < n then a i else 1) * (if 0 < i then a i else 1)) :=
        Finset.prod_mul_distrib.symm

/-! ### One group: the hits which are not labels -/

open _root_.Classical in
/-- In a group whose `M = J + ℓ` labels are distinct hits, the number of hits is `M` plus the
number of the hits which are not labels. -/
theorem bigRes_countHits_eq {Q : Finset ℕ} {J ℓ : ℕ} (hit : ℕ → Prop)
    (f : Slot J ℓ → {p : ℕ // p ∈ Q}) (hinj : Function.Injective f) (hhit : ∀ s, hit (f s)) :
    countHits hit Q = (J + ℓ) + (Q.filter fun p => hit p ∧ ¬∃ s, (f s : ℕ) = p).card := by
  have hinj' : Function.Injective (fun s : Slot J ℓ => (f s : ℕ)) :=
    fun a b h => hinj (Subtype.ext h)
  have hcard : (Finset.univ.image fun s : Slot J ℓ => (f s : ℕ)).card = J + ℓ := by
    rw [Finset.card_image_of_injective _ hinj', Finset.card_univ, card_slot]
  have hsub : (Finset.univ.image fun s : Slot J ℓ => (f s : ℕ)) ⊆ Q.filter hit := by
    intro p hp
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨(f s).2, hhit s⟩
  have hsd : (Q.filter hit) \ (Finset.univ.image fun s : Slot J ℓ => (f s : ℕ)) =
      Q.filter fun p => hit p ∧ ¬∃ s, (f s : ℕ) = p := by
    ext p
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨hpQ, hph⟩, hnot⟩
      exact ⟨hpQ, hph, fun ⟨s, hs⟩ => hnot ⟨s, Finset.mem_univ s, hs⟩⟩
    · rintro ⟨hpQ, hph, hnot⟩
      exact ⟨⟨hpQ, hph⟩, fun ⟨s, _, hs⟩ => hnot ⟨s, hs⟩⟩
  have h := Finset.card_sdiff_add_card_eq_card hsub
  rw [hsd, hcard] at h
  exact h.symm.trans (Nat.add_comm _ _)

/-- `q^{((M + e) - M)/2} = (√q)^e`. -/
theorem bigRes_rpow_half {q : ℝ} (hq : 0 < q) (M e : ℕ) :
    q ^ ((((M + e : ℕ) : ℝ) - ((M : ℕ) : ℝ)) / 2) = Real.sqrt q ^ e := by
  have h : (((M + e : ℕ) : ℝ) - ((M : ℕ) : ℝ)) / 2 = (e : ℝ) / 2 := by
    push_cast
    ring
  rw [h, Real.rpow_div_two_eq_sqrt _ hq.le, Real.rpow_natCast]

open _root_.Classical in
/-- **The endpoint damping of one group**: if the `M` labels of the group are distinct hits, then
`q^{(ω_g - M)/2}` is the product over the primes of the group of `√q` for every hit which is not a
label. -/
theorem bigRes_group_damping {Q : Finset ℕ} {J ℓ : ℕ} {q : ℝ} (hq : 0 < q) (hit : ℕ → Prop)
    (f : Slot J ℓ → {p : ℕ // p ∈ Q}) (hinj : Function.Injective f) (hhit : ∀ s, hit (f s)) :
    q ^ ((((countHits hit Q : ℕ) : ℝ) - ((J + ℓ : ℕ) : ℝ)) / 2) =
      ∏ p ∈ Q, if hit p ∧ ¬∃ s, (f s : ℕ) = p then Real.sqrt q else 1 := by
  rw [bigRes_countHits_eq hit f hinj hhit, bigRes_rpow_half hq, ← Finset.prod_const,
    Finset.prod_filter]

/-! ### The mean over a residue vector of a product over its coordinates -/

/-- **Independent uniform residues**: the mean over the residue vector `y` of a product of
functions of the single coordinates `y_p` is the product of the one-coordinate means. -/
theorem bigRes_resAvg_prod (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 0 < p)
    (G : (p : {p : ℕ // p ∈ Q}) → Res p.1 → ℝ) :
    (Fintype.card (ResVec Q) : ℝ)⁻¹ * ∑ y : ResVec Q, ∏ p, G p (y p) =
      ∏ p : {p : ℕ // p ∈ Q}, ((p.1 : ℝ)⁻¹ * ∑ t : Res p.1, G p t) := by
  have hcard : (Fintype.card (ResVec Q) : ℝ) = ∏ p : {p : ℕ // p ∈ Q}, (p.1 : ℝ) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    exact Finset.prod_congr rfl fun p _ => by rw [Res.card p.1 (hQ p.1 p.2)]
  calc (Fintype.card (ResVec Q) : ℝ)⁻¹ * ∑ y : ResVec Q, ∏ p, G p (y p)
      = (∏ p : {p : ℕ // p ∈ Q}, (p.1 : ℝ))⁻¹ *
          ∏ p : {p : ℕ // p ∈ Q}, ∑ t : Res p.1, G p t :=
        congrArg₂ (· * ·) (congrArg (fun t : ℝ => t⁻¹) hcard) (Fintype.prod_sum G).symm
    _ = ∏ p : {p : ℕ // p ∈ Q}, ((p.1 : ℝ)⁻¹ * ∑ t : Res p.1, G p t) := by
        rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

/-! ### Big states -/

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ}

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- **`IsBigState` is invariant under slot permutations**: the labels of a group are distinct
zero coordinates in every order. -/
theorem isBigState_permuteSlots (σ : SlotPerms B J ℓ) (y : ResVec (bigPrimes 𝒢))
    (xb : LabelList 𝒢.big J ℓ) :
    IsBigState 𝒢 y (permuteSlots σ xb) ↔ IsBigState 𝒢 y xb := by
  unfold IsBigState
  constructor
  · intro h
    refine ⟨fun g a b hab => ?_, fun g i => ?_⟩
    · have h1 : permuteSlots σ xb g ((σ g).symm a) = permuteSlots σ xb g ((σ g).symm b) := by
        show xb g (σ g ((σ g).symm a)) = xb g (σ g ((σ g).symm b))
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hab
      exact (σ g).symm.injective (h.1 g h1)
    · have h2 : (resModel (bigPrimes 𝒢)).hit (xb g (σ g ((σ g).symm i))) y :=
        h.2 g ((σ g).symm i)
      rwa [Equiv.apply_symm_apply] at h2
  · intro h
    exact ⟨fun g a b hab => (σ g).injective (h.1 g hab), fun g i => h.2 g (σ g i)⟩

omit [Fintype S] [DecidableEq S] in
open _root_.Classical in
/-- **The big endpoint damping at a big state**: for pairwise disjoint big groups, the damping
`∏_g q^{(ω_g(y) - M)/2}` at a big state is the product over the big primes of `√q` for every zero
coordinate which is not a label ("`q_i^{#{p ∉ Λ_i : n + h_i ≡ 0 (p)}}`", [S-02:0226–0231]). -/
theorem bigRes_bigDamping_eq {q : ℝ} (hq : 0 < q)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (y : ResVec (bigPrimes 𝒢))
    (xb : LabelList 𝒢.big J ℓ) (hst : IsBigState 𝒢 y xb) :
    bigDamping 𝒢 J ℓ q y =
      ∏ p ∈ bigPrimes 𝒢,
        if (resModel (bigPrimes 𝒢)).hit p y ∧ ¬∃ g sl, (xb g sl : ℕ) = p then Real.sqrt q
        else 1 := by
  have hexp : ((((∑ g, countHits (fun p => (resModel (bigPrimes 𝒢)).hit p y) (𝒢.big g) : ℕ) :
        ℝ) - ((J + ℓ : ℕ) : ℝ) * (Fintype.card B : ℝ)) / 2) =
      ∑ g : B, (((countHits (fun p => (resModel (bigPrimes 𝒢)).hit p y) (𝒢.big g) : ℕ) : ℝ) -
        ((J + ℓ : ℕ) : ℝ)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    push_cast
    ring
  have hlab : ∀ (g : B) (p : ℕ), p ∈ 𝒢.big g →
      ((∃ sl, (xb g sl : ℕ) = p) ↔ ∃ g' sl, (xb g' sl : ℕ) = p) := by
    intro g p hp
    constructor
    · rintro ⟨sl, h⟩
      exact ⟨g, sl, h⟩
    · rintro ⟨g', sl, h⟩
      have hg : g' = g := by
        by_contra hne
        have hp' : p ∈ 𝒢.big g' := by
          rw [← h]
          exact (xb g' sl).2
        exact Finset.disjoint_left.mp (hdisj g' g hne) hp' hp
      subst hg
      exact ⟨sl, h⟩
  calc bigDamping 𝒢 J ℓ q y
      = q ^ (∑ g : B,
          (((countHits (fun p => (resModel (bigPrimes 𝒢)).hit p y) (𝒢.big g) : ℕ) : ℝ) -
            ((J + ℓ : ℕ) : ℝ)) / 2) := congrArg (fun t : ℝ => q ^ t) hexp
    _ = ∏ g : B, q ^
          ((((countHits (fun p => (resModel (bigPrimes 𝒢)).hit p y) (𝒢.big g) : ℕ) : ℝ) -
            ((J + ℓ : ℕ) : ℝ)) / 2) := Real.rpow_sum_of_pos hq _ _
    _ = ∏ g : B, ∏ p ∈ 𝒢.big g,
          (if (resModel (bigPrimes 𝒢)).hit p y ∧ ¬∃ g' sl, (xb g' sl : ℕ) = p then
            Real.sqrt q else 1) :=
        Finset.prod_congr rfl fun g _ =>
          (bigRes_group_damping hq (fun p => (resModel (bigPrimes 𝒢)).hit p y) (xb g)
            (hst.1 g) (hst.2 g)).trans
            (Finset.prod_congr rfl fun p hp =>
              bigRes_ite_congr (and_congr Iff.rfl (not_congr (hlab g p hp))) rfl rfl)
    _ = ∏ p ∈ bigPrimes 𝒢,
          (if (resModel (bigPrimes 𝒢)).hit p y ∧ ¬∃ g sl, (xb g sl : ℕ) = p then
            Real.sqrt q else 1) :=
        (Finset.prod_biUnion fun g _ g' _ hne => hdisj g g' hne).symm

omit [Fintype S] [DecidableEq S] in
open _root_.Classical in
/-- **The factor of a visit as a product over the big primes** [S-02:0226–0231]: for pairwise
disjoint big groups, the indicator of a big state at `y` times the big endpoint damping is the
indicator that the lists are injective times the product over the big primes `p` of
`1_{y_p = 0}` if `p` is a label and of `(√q)^{1_{y_p = 0}}` otherwise. -/
theorem bigRes_state_damping {q : ℝ} (hq : 0 < q)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (y : ResVec (bigPrimes 𝒢))
    (xb : LabelList 𝒢.big J ℓ) :
    (if IsBigState 𝒢 y xb then bigDamping 𝒢 J ℓ q y else 0) =
      (if ∀ g, Function.Injective (xb g) then (1 : ℝ) else 0) *
        ∏ p : {p : ℕ // p ∈ bigPrimes 𝒢},
          if ∃ g sl, (xb g sl : ℕ) = p.1 then (if y p = 0 then (1 : ℝ) else 0)
          else (if y p = 0 then Real.sqrt q else 1) := by
  have hhit_iff : ∀ p : {p : ℕ // p ∈ bigPrimes 𝒢},
      (resModel (bigPrimes 𝒢)).hit p.1 y ↔ y p = 0 := by
    intro p
    constructor
    · intro h
      obtain ⟨_, hz⟩ : ∃ h' : p.1 ∈ bigPrimes 𝒢, y ⟨p.1, h'⟩ = 0 := h
      exact hz
    · intro hz
      exact (⟨p.2, hz⟩ : ∃ h' : p.1 ∈ bigPrimes 𝒢, y ⟨p.1, h'⟩ = 0)
  by_cases hinj : ∀ g, Function.Injective (xb g)
  · rw [if_pos hinj, one_mul]
    by_cases hhit : ∀ g sl, (resModel (bigPrimes 𝒢)).hit (xb g sl) y
    · have hst : IsBigState 𝒢 y xb := ⟨hinj, hhit⟩
      have key : ∏ p : {p : ℕ // p ∈ bigPrimes 𝒢},
            (if (resModel (bigPrimes 𝒢)).hit p.1 y ∧ ¬∃ g sl, (xb g sl : ℕ) = p.1 then
              Real.sqrt q else 1) =
          ∏ p ∈ bigPrimes 𝒢,
            (if (resModel (bigPrimes 𝒢)).hit p y ∧ ¬∃ g sl, (xb g sl : ℕ) = p then
              Real.sqrt q else 1) :=
        (Finset.prod_subtype (bigPrimes 𝒢) (fun _ => Iff.rfl)
          (fun p : ℕ =>
            if (resModel (bigPrimes 𝒢)).hit p y ∧ ¬∃ g sl, (xb g sl : ℕ) = p then
              Real.sqrt q else 1)).symm
      rw [if_pos hst]
      refine ((bigRes_bigDamping_eq hq hdisj y xb hst).trans key.symm).trans ?_
      refine Finset.prod_congr rfl fun p _ => ?_
      refine bigRes_ite_cases (Real.sqrt q) (hhit_iff p) ?_
      rintro ⟨g, sl, hgs⟩
      have h := hhit g sl
      rw [hgs] at h
      exact (hhit_iff p).mp h
    · rw [if_neg (fun h : IsBigState 𝒢 y xb => hhit h.2)]
      obtain ⟨g, sl, hns⟩ : ∃ g sl, ¬(resModel (bigPrimes 𝒢)).hit (xb g sl) y := by
        by_contra hcon
        exact hhit fun g sl => not_not.mp fun h => hcon ⟨g, sl, h⟩
      have hpQ : (xb g sl : ℕ) ∈ bigPrimes 𝒢 := mem_bigPrimes.mpr ⟨g, (xb g sl).2⟩
      obtain ⟨p₀, hp₀⟩ : ∃ p₀ : {p : ℕ // p ∈ bigPrimes 𝒢}, (xb g sl : ℕ) = p₀.1 :=
        ⟨⟨_, hpQ⟩, rfl⟩
      rw [hp₀] at hns
      have hz : ¬y p₀ = 0 := fun hz => hns ((hhit_iff p₀).mpr hz)
      refine (Finset.prod_eq_zero (Finset.mem_univ p₀) ?_).symm
      rw [if_pos (⟨g, sl, hp₀⟩ : ∃ g' sl', (xb g' sl' : ℕ) = p₀.1), if_neg hz]
  · rw [if_neg (fun h : IsBigState 𝒢 y xb => hinj h.1), if_neg hinj, zero_mul]

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
