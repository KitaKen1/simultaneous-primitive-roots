module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.EdgeListTools
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The factor of one big group as a product over its primes

Source: `verification/stage7-sources/S-02.tex`, lines 569–581 (`[S-02:0569–0581]`): "A numerical
prime occupies at most one active slot or pending particle, because it has only one birth."

Tools for the proof of (M3) `EdgeStepFactor`. For one big group `g`, an active list `x`, a list
`L` of pending particles and the set `U` of the primes born so far:

* `edgEval a b d u x L U` — the factor `PrimeVals.evalL` of the group, for arbitrary functions
  `a` (active), `b` (pending), `d` (dead), `u` (unborn) (`PrimeVals.evalL_eq_edgEval`);
* `edgPF a b d u x L U p` — the factor of the prime `p`: `a p` if `p` is a label, the product
  `edgMid b L p` of `b` over the particles with prime `p`, and the third factor `edgThird`;
  `edgEval_eq_prod`: for an injective list the factor of the group is the product of the factors
  of its primes;
* `edgPF_act`, `edgPF_pend`, `edgPF_dead`, `edgPF_unborn` — the factor of a prime in each of its
  four conditions;
* `edgMid_ofFn`, `edgMid_newList` — the product over the particles with prime `p`, for the list of
  a memory and for the new memory after an edge;
* `edgEval_mul`, `edgEval_eq_zero`, `PrimeVals.evalL_comp_perm`;
* `edg_prod_inj`, `edg_prod_split`, `edg_sum_subsets` — products over the values of an injective
  map, and the sum over all subsets of a product of two alternatives.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Products and sums over finite types -/

/-- A product over the values of an injective map, for arbitrary decidability instances. -/
theorem edg_prod_inj {ι α : Type*} [Fintype ι] [Fintype α] {f : ι → α}
    (hf : Function.Injective f) (F : α → ℝ) {inst : ∀ a, Decidable (∃ i, f i = a)} :
    ∏ a, @ite ℝ (∃ i, f i = a) (inst a) (F a) 1 = ∏ i, F (f i) := by
  classical
  have h2 : ∏ a, (if a ∈ Finset.univ.image f then F a else 1) = ∏ i, F (f i) :=
    (Fintype.prod_ite_mem (Finset.univ.image f) F).trans
      (Finset.prod_image fun i _ j _ h => hf h)
  refine Eq.trans (Finset.prod_congr rfl fun a _ => ?_) h2
  refine bigRes_ite_congr ?_ rfl rfl
  rw [Finset.mem_image]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, Finset.mem_univ i, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩

/-- A product over a finite type, split into the values of an injective map on a set of indices
and the other elements. -/
theorem edg_prod_split {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] (x : ι → α)
    (hx : Function.Injective x) (P : ι → Prop) [DecidablePred P] (F : α → ℝ) :
    ∏ p, F p =
      (∏ i, if P i then F (x i) else 1) * ∏ p ∈ ((Finset.univ.filter P).image x)ᶜ, F p := by
  rw [← Finset.prod_mul_prod_compl ((Finset.univ.filter P).image x) F,
    Finset.prod_image (fun i _ j _ h => hx h), Finset.prod_filter]

/-- A product of two alternatives, chosen by a set. -/
theorem edg_prod_piecewise {ι : Type*} [Fintype ι] [DecidableEq ι] (st : Finset ι)
    (f g : ι → ℝ) :
    (∏ i ∈ st, f i) * ∏ i ∈ stᶜ, g i = ∏ i, if i ∈ st then f i else g i := by
  rw [← Finset.prod_mul_prod_compl st fun i => if i ∈ st then f i else g i]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => (if_pos hi).symm
  · exact Finset.prod_congr rfl fun i hi => (if_neg (Finset.mem_compl.mp hi)).symm

/-- **The sum over all subsets** of the product of the two alternatives is the product of the
sums: every element is in the subset or not. -/
theorem edg_sum_subsets {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ) :
    ∑ st : Finset ι, ∏ i, (if i ∈ st then f i else g i) = ∏ i, (f i + g i) := by
  rw [Fintype.prod_add]
  exact Finset.sum_congr rfl fun st _ => (edg_prod_piecewise st f g).symm

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {g : B}

/-! ### The factor of a group for arbitrary functions -/

open _root_.Classical in
/-- The third factor of the prime `p`: `d p` if it was born and is not present, `u p` if it was
not born, `1` if it is present. -/
def edgThird (d u : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (L : List (Particle 𝒢 g)) (U : Finset ℕ) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  if (p : ℕ) ∈ U then (if (∃ sl, x sl = p) ∨ (∃ w ∈ L, w.1 = p) then 1 else d p) else u p

/-- The product of `b` over the particles of the list with the prime `p`. -/
def edgMid (b : Particle 𝒢 g → ℝ) (L : List (Particle 𝒢 g)) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  (L.map fun w => if w.1 = p then b w else 1).prod

/-- The factor of a big group for arbitrary functions of the active primes (`a`), the pending
particles (`b`), the dead (`d`) and the unborn primes (`u`). -/
def edgEval (a : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (b : Particle 𝒢 g → ℝ)
    (d u : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (L : List (Particle 𝒢 g)) (U : Finset ℕ) : ℝ :=
  (∏ sl : Slot J ℓ, a (x sl)) * (L.map b).prod *
    ∏ p : {p : ℕ // p ∈ 𝒢.big g}, edgThird d u x L U p

open _root_.Classical in
/-- **The factor of the prime `p`** in the factor of its group. -/
def edgPF (a : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (b : Particle 𝒢 g → ℝ)
    (d u : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (L : List (Particle 𝒢 g)) (U : Finset ℕ) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  (if ∃ sl, x sl = p then a p else 1) * edgMid b L p * edgThird d u x L U p

/-- The factor `PrimeVals.evalL` of a group is `edgEval` for the four values of the group. -/
theorem PrimeVals.evalL_eq_edgEval (v : PrimeVals 𝒢) (g : B)
    (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (L : List (Particle 𝒢 g)) (U : Finset ℕ) :
    v.evalL g x L U = edgEval (v.act g) (v.pend g) (v.dead g) (v.unborn g) x L U := by
  unfold PrimeVals.evalL edgEval
  refine congrArg (fun t => (∏ sl : Slot J ℓ, v.act g (x sl)) * (L.map (v.pend g)).prod * t)
    (Finset.prod_congr rfl fun p _ => ?_)
  unfold PrimeVals.thirdL edgThird
  exact bigRes_ite_congr Iff.rfl (bigRes_ite_congr Iff.rfl rfl rfl) rfl

/-- **For an injective list, the factor of a group is the product of the factors of its primes.**
-/
theorem edgEval_eq_prod (a : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (b : Particle 𝒢 g → ℝ)
    (d u : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (hx : Function.Injective x) (L : List (Particle 𝒢 g)) (U : Finset ℕ) :
    edgEval a b d u x L U = ∏ p : {p : ℕ // p ∈ 𝒢.big g}, edgPF a b d u x L U p := by
  unfold edgEval edgPF edgMid
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, edg_prod_inj hx a,
    ← edg_prod_by_key (fun w : Particle 𝒢 g => w.1) b L]

/-- Factors of the active primes and of the pending particles can be taken out. -/
theorem edgEval_mul (κ a : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (c b : Particle 𝒢 g → ℝ)
    (d u : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (L : List (Particle 𝒢 g)) (U : Finset ℕ) :
    edgEval (fun p => κ p * a p) (fun w => c w * b w) d u x L U =
      (∏ sl : Slot J ℓ, κ (x sl)) * (L.map c).prod * edgEval a b d u x L U := by
  unfold edgEval
  rw [Finset.prod_mul_distrib, List.prod_map_mul]
  ring

/-- The factor of a group vanishes if the value of some prime vanishes in each of its possible
conditions. -/
theorem edgEval_eq_zero (a : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (b : Particle 𝒢 g → ℝ)
    (d u : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (L : List (Particle 𝒢 g)) (U : Finset ℕ) (p : {p : ℕ // p ∈ 𝒢.big g})
    (ha : ∀ sl, x sl = p → a p = 0) (hb : ∀ w ∈ L, w.1 = p → b w = 0)
    (hd : (p : ℕ) ∈ U → d p = 0) (hu : (p : ℕ) ∉ U → u p = 0) :
    edgEval a b d u x L U = 0 := by
  unfold edgEval
  by_cases h1 : ∃ sl, x sl = p
  · obtain ⟨sl, hsl⟩ := h1
    have h0 : ∏ sl : Slot J ℓ, a (x sl) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ sl) (by
        rw [hsl]
        exact ha sl hsl)
    rw [h0, zero_mul, zero_mul]
  · by_cases h2 : ∃ w ∈ L, w.1 = p
    · obtain ⟨w, hw, hwp⟩ := h2
      have h0 : (L.map b).prod = 0 :=
        List.prod_eq_zero (List.mem_map.mpr ⟨w, hw, hb w hw hwp⟩)
      rw [h0, mul_zero, zero_mul]
    · have h0 : edgThird d u x L U p = 0 := by
        unfold edgThird
        by_cases hU : (p : ℕ) ∈ U
        · rw [if_pos hU,
            if_neg (fun h : (∃ sl, x sl = p) ∨ ∃ w ∈ L, w.1 = p => h.elim h1 h2)]
          exact hd hU
        · rw [if_neg hU]
          exact hu hU
      rw [Finset.prod_eq_zero (Finset.mem_univ p) h0, mul_zero]

/-! ### The factor of a prime in each of its conditions -/

section PF

variable (a : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (b : Particle 𝒢 g → ℝ)
  (d u : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
  (L : List (Particle 𝒢 g)) (U : Finset ℕ) (p : {p : ℕ // p ∈ 𝒢.big g})

/-- An active prime. -/
theorem edgPF_act (hx : ∃ sl, x sl = p) (hmid : edgMid b L p = 1) (hU : (p : ℕ) ∈ U) :
    edgPF a b d u x L U p = a p := by
  unfold edgPF edgThird
  rw [if_pos hx, hmid, if_pos hU,
    if_pos (show (∃ sl, x sl = p) ∨ ∃ w ∈ L, w.1 = p from Or.inl hx), mul_one, mul_one]

/-- A pending prime. -/
theorem edgPF_pend (hx : ¬∃ sl, x sl = p) (hL : ∃ w ∈ L, w.1 = p) (hU : (p : ℕ) ∈ U) :
    edgPF a b d u x L U p = edgMid b L p := by
  unfold edgPF edgThird
  rw [if_neg hx, if_pos hU,
    if_pos (show (∃ sl, x sl = p) ∨ ∃ w ∈ L, w.1 = p from Or.inr hL), one_mul, mul_one]

/-- A prime which was born and is not present. -/
theorem edgPF_dead (hx : ¬∃ sl, x sl = p) (hmid : edgMid b L p = 1)
    (hL : ¬∃ w ∈ L, w.1 = p) (hU : (p : ℕ) ∈ U) : edgPF a b d u x L U p = d p := by
  unfold edgPF edgThird
  rw [if_neg hx, hmid, if_pos hU,
    if_neg (show ¬((∃ sl, x sl = p) ∨ ∃ w ∈ L, w.1 = p) from fun h => h.elim hx hL),
    one_mul, one_mul]

/-- A prime which was not born. -/
theorem edgPF_unborn (hx : ¬∃ sl, x sl = p) (hmid : edgMid b L p = 1) (hU : (p : ℕ) ∉ U) :
    edgPF a b d u x L U p = u p := by
  unfold edgPF edgThird
  rw [if_neg hx, hmid, if_neg hU, one_mul, one_mul]

end PF

/-! ### The particles with a given prime -/

/-- The product over the particles of a memory with the prime `p`. -/
theorem edgMid_ofFn (b : Particle 𝒢 g → ℝ) {n : ℕ} (zf : Fin n → Particle 𝒢 g)
    (p : {p : ℕ // p ∈ 𝒢.big g}) :
    edgMid b (List.ofFn zf) p = ∏ j : Fin n, if (zf j).1 = p then b (zf j) else 1 := by
  unfold edgMid
  exact ghStep_prod_map_ofFn zf fun w => if w.1 = p then b w else 1

/-- The product over the particles of the new memory after an edge with the prime `p`. -/
theorem edgMid_newList (b : Particle 𝒢 g → ℝ) {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (zf : Fin n → Particle 𝒢 g) (Δ : ℤ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (st : Finset (Slot J ℓ)) (pm : Slot J ℓ → Option (Fin Bc)) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    edgMid b (edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm) p =
      (∏ j : Fin n, if ∃ sl, pm sl = some (Fin.castLE hnB j) then 1
        else (if (zf j).1 = p then b (shiftParticle Δ (zf j)) else 1)) *
        ∏ sl ∈ st, if x sl = p then b (shiftParticle Δ ⟨x sl, 0⟩) else 1 := by
  unfold edgMid
  exact edg_prod_newList hn hnB zf Δ x st pm fun w => if w.1 = p then b w else 1

/-- No particle of the new memory has the prime `p`. -/
theorem edgMid_newList_none (b : Particle 𝒢 g → ℝ) {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (zf : Fin n → Particle 𝒢 g) (Δ : ℤ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (st : Finset (Slot J ℓ)) (pm : Slot J ℓ → Option (Fin Bc)) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hk : ∀ j : Fin n, (¬∃ sl, pm sl = some (Fin.castLE hnB j)) → (zf j).1 ≠ p)
    (hs : ∀ sl ∈ st, x sl ≠ p) :
    edgMid b (edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm) p = 1 ∧
      ¬∃ w ∈ edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm, w.1 = p := by
  refine ⟨?_, ?_⟩
  · rw [edgMid_newList b hn hnB zf Δ x st pm p,
      Finset.prod_eq_one fun sl hsl => if_neg (hs sl hsl), mul_one]
    refine Finset.prod_eq_one fun j _ => ?_
    by_cases hc : ∃ sl, pm sl = some (Fin.castLE hnB j)
    · exact if_pos hc
    · exact (if_neg hc).trans (if_neg (hk j hc))
  · rw [edg_exists_newList hn hnB zf Δ x st pm p]
    rintro (⟨j, hj, hp⟩ | ⟨sl, hsl, hp⟩)
    · exact hk j hj hp
    · exact hs sl hsl hp

/-- The particle of the new memory with the prime `p` is an old particle which is kept. -/
theorem edgMid_newList_kept (b : Particle 𝒢 g → ℝ) {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (zf : Fin n → Particle 𝒢 g) (hz : Function.Injective fun j : Fin n => (zf j).1) (Δ : ℤ)
    (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (st : Finset (Slot J ℓ))
    (pm : Slot J ℓ → Option (Fin Bc)) (j₀ : Fin n)
    (hk : ¬∃ sl, pm sl = some (Fin.castLE hnB j₀)) (hs : ∀ sl ∈ st, x sl ≠ (zf j₀).1) :
    edgMid b (edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm) (zf j₀).1 =
        b (shiftParticle Δ (zf j₀)) ∧
      ∃ w ∈ edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm, w.1 = (zf j₀).1 := by
  refine ⟨?_, ?_⟩
  · rw [edgMid_newList b hn hnB zf Δ x st pm (zf j₀).1,
      Finset.prod_eq_one fun sl hsl => if_neg (hs sl hsl), mul_one]
    refine (Fintype.prod_eq_single j₀ fun j hj => ?_).trans ?_
    · by_cases hc : ∃ sl, pm sl = some (Fin.castLE hnB j)
      · exact if_pos hc
      · exact (if_neg hc).trans (if_neg fun h => hj (hz h))
    · exact (if_neg hk).trans (if_pos rfl)
  · rw [edg_exists_newList hn hnB zf Δ x st pm (zf j₀).1]
    exact Or.inl ⟨j₀, hk, rfl⟩

/-- The particle of the new memory with the prime `p` is a stored particle. -/
theorem edgMid_newList_stored (b : Particle 𝒢 g → ℝ) {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (zf : Fin n → Particle 𝒢 g) (Δ : ℤ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (hx : Function.Injective x) (st : Finset (Slot J ℓ)) (pm : Slot J ℓ → Option (Fin Bc))
    (sl₀ : Slot J ℓ) (hsl₀ : sl₀ ∈ st) (hne : ∀ j : Fin n, (zf j).1 ≠ x sl₀) :
    edgMid b (edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm) (x sl₀) =
        b (shiftParticle Δ ⟨x sl₀, 0⟩) ∧
      ∃ w ∈ edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm, w.1 = x sl₀ := by
  refine ⟨?_, ?_⟩
  · have h1 : ∏ j : Fin n, (if ∃ sl, pm sl = some (Fin.castLE hnB j) then (1 : ℝ)
        else (if (zf j).1 = x sl₀ then b (shiftParticle Δ (zf j)) else 1)) = 1 := by
      refine Finset.prod_eq_one fun j _ => ?_
      by_cases hc : ∃ sl, pm sl = some (Fin.castLE hnB j)
      · exact if_pos hc
      · exact (if_neg hc).trans (if_neg (hne j))
    rw [edgMid_newList b hn hnB zf Δ x st pm (x sl₀), h1, one_mul]
    refine (Finset.prod_eq_single sl₀ (fun sl _ hsl => ?_) fun h => absurd hsl₀ h).trans ?_
    · exact if_neg fun h => hsl (hx h)
    · exact if_pos rfl
  · rw [edg_exists_newList hn hnB zf Δ x st pm (x sl₀)]
    exact Or.inr ⟨sl₀, hsl₀, rfl⟩

/-! ### Permutations of the slots -/

/-- The factor of a group does not depend on the order of the slots. -/
theorem PrimeVals.evalL_comp_perm (v : PrimeVals 𝒢) (g : B)
    (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (σ : Equiv.Perm (Slot J ℓ))
    (L : List (Particle 𝒢 g)) (U : Finset ℕ) :
    v.evalL g (fun sl => x (σ sl)) L U = v.evalL g x L U := by
  have h1 : ∏ sl : Slot J ℓ, v.act g (x (σ sl)) = ∏ sl : Slot J ℓ, v.act g (x sl) :=
    Equiv.prod_comp σ fun sl => v.act g (x sl)
  have h2 : ∀ p : {p : ℕ // p ∈ 𝒢.big g},
      v.thirdL g (fun sl => x (σ sl)) L U p = v.thirdL g x L U p := by
    intro p
    unfold PrimeVals.thirdL
    refine bigRes_ite_congr Iff.rfl (bigRes_ite_congr (or_congr ?_ Iff.rfl) rfl rfl) rfl
    constructor
    · rintro ⟨sl, h⟩
      exact ⟨σ sl, h⟩
    · rintro ⟨sl, h⟩
      refine ⟨σ.symm sl, ?_⟩
      show x (σ (σ.symm sl)) = p
      rw [Equiv.apply_symm_apply]
      exact h
  unfold PrimeVals.evalL
  rw [h1, Finset.prod_congr rfl fun p _ => h2 p]

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
