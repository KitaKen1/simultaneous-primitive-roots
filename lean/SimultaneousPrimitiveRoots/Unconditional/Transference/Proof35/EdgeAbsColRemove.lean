module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsColTools
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The column bound of the absolute edge: removing the promoted particles

Source: `verification/stage7-sources/S-02.tex`, lines 704–737 (`[S-02:0704–0737]`),
(eq:edge-joint-memory), (eq:edge-joint-measure), (eq:edge-factorial-reversal).

"Suppose `a` target slots are promotions … Let the source memory have size `j`, and write `u` for
its `j - a` surviving particles. … The factorial accounting is `(j)_a / j! = 1/(j - a)!`. The first
equality selects old memory indices into the `a` specified ordered target slots."

For one big group, one target list `τ` and fixed promotions `pm`:

* `edgeAbsSurv`, `edgeAbsProm`, `edgeAbsStored` — the surviving and the promoted particles of the
  old memory (before translation) and the stored particles;
  `edgeAbsNewList_eq_surv`: the new memory is `T_Δ u ⊔ ((s_h, Δ))_h`.
* `EdgeAbsPromoValid` — the promotions are admissible for the memory `z` and produce the target
  labels `τ`: unshared slots, distinct indices, zero translated residue, label `τ(sl)`.
* `edgeAbs_lw_valid`, `edgeAbs_size_valid` — for admissible promotions the weight `λ^{⊗j}` of the
  memory is the weight of the survivors times `∏ μ̃(τ(sl))` over the promoting slots, and
  `j = (j - a) + a`.
* `edgeAbs_surv_injective` — "each required residue … selects exactly one point of counting
  measure": for fixed promotions the memory is determined by its survivors.
* `edgeAbs_remove_le` — hence the sum over the memories `z` with admissible promotions `pm` is at
  most the sum over the memories `u` of the survivors, with `λ^{⊗(j-a)}(u) v^j / j!`.
* `edgeAbs_promoShape_sum_le` — the number of promotion maps with `a` promotions into `j` indices
  is at most `j^a` and `k! (k+1)^a ≤ (k+a)!`: summed over the promotion maps, the factors
  `V_g^{-a} v^{k+a}/(k+a)!` are at most `(1 + T v / V_g)^T v^k / k!`.
* `edgeAbs_remove_sum_le` — **the removal step**: the sum over the source memories and the
  promotions is at most `(1 + T v / V_g)^T ∏_{sl unshared} μ̃(τ(sl))` times the sum over the
  memories of the survivors with their own measure `λ^{⊗k} v^k / k!`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- The scalar inequality behind `edgeAbs_remove_le`. -/
theorem l38_remove_scalar {lws PA Fr nfac vn r1 r2 Gs LU : ℝ} (hP : PA * Fr = LU) (hr : r1 ≤ r2)
    (hLU : 0 ≤ LU) (hl : 0 ≤ lws) (hv : 0 ≤ vn) (hn : 0 ≤ nfac) (hG : 0 ≤ Gs) :
    lws * PA / nfac * vn * r1 * Fr * Gs ≤ LU * (lws * (vn / nfac) * r2 * Gs) := by
  have h0 : 0 ≤ LU * (lws * (vn / nfac) * Gs) :=
    mul_nonneg hLU (mul_nonneg (mul_nonneg hl (div_nonneg hv hn)) hG)
  calc lws * PA / nfac * vn * r1 * Fr * Gs
      = (PA * Fr) * (lws * (vn / nfac) * Gs) * r1 := by ring
    _ = LU * (lws * (vn / nfac) * Gs) * r1 := by rw [hP]
    _ ≤ LU * (lws * (vn / nfac) * Gs) * r2 := mul_le_mul_of_nonneg_left hr h0
    _ = LU * (lws * (vn / nfac) * r2 * Gs) := by ring

/-- `V^{-a} v^{n+a}/(n+a)! ≤ (v^n/n!) (v/(V(n+1)))^a`, from `n! (n+1)^a ≤ (n+a)!`
(eq:edge-factorial-reversal, in the form of an inequality). -/
theorem l38_fact_scalar {v V : ℝ} (hv : 0 ≤ v) (hV : 0 < V) (n a : ℕ) :
    (V ^ a)⁻¹ * (v ^ (n + a) / ((n + a).factorial : ℝ)) ≤
      v ^ n / (n.factorial : ℝ) * (v / (V * ((n : ℝ) + 1))) ^ a := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_pos
  have hfn : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hVa : (0 : ℝ) < V ^ a := pow_pos hV a
  have hf : (n.factorial : ℝ) * ((n : ℝ) + 1) ^ a ≤ ((n + a).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_pow_le_factorial (m := n) (n := a)
  have hden : 0 < V ^ a * ((n.factorial : ℝ) * ((n : ℝ) + 1) ^ a) :=
    mul_pos hVa (mul_pos hfn (pow_pos hn1 a))
  have e1 : (V ^ a)⁻¹ * (v ^ (n + a) / ((n + a).factorial : ℝ)) =
      v ^ (n + a) / (V ^ a * ((n + a).factorial : ℝ)) := by ring
  have e2 : v ^ n / (n.factorial : ℝ) * (v / (V * ((n : ℝ) + 1))) ^ a =
      v ^ (n + a) / (V ^ a * ((n.factorial : ℝ) * ((n : ℝ) + 1) ^ a)) := by
    rw [div_pow, mul_pow, pow_add]
    ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_left (pow_nonneg hv _) hden (mul_le_mul_of_nonneg_left hf hVa.le)

section OneGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {g : B}

/-! ### Survivors, promoted and stored particles -/

/-- The old pending particles which are not promoted, in the order of their indices (before the
translation): `u` of (eq:edge-joint-memory). -/
def edgeAbsSurv (z : Mem 𝒢 Bc g) (pm : Slot J ℓ → Option (Fin Bc)) : List (Particle 𝒢 g) :=
  (List.finRange Bc).filterMap fun j => if ∃ sl, pm sl = some j then none else memAt z j

/-- The promoted particles, in the order of their indices. -/
def edgeAbsProm (z : Mem 𝒢 Bc g) (pm : Slot J ℓ → Option (Fin Bc)) : List (Particle 𝒢 g) :=
  (List.finRange Bc).filterMap fun j => if ∃ sl, pm sl = some j then memAt z j else none

/-- The stored particles after the translation, `((s_h, Δ mod s_h))_h` of
(eq:edge-joint-memory), in the canonical order of their slots. -/
def edgeAbsStored (Δ : ℤ) (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (st : Finset (Slot J ℓ)) :
    List (Particle 𝒢 g) :=
  ((slotList J ℓ).filter fun sl => decide (sl ∈ st)).map fun sl => shiftParticle Δ ⟨xg sl, 0⟩

/-- The number of promotions of a promotion map. -/
def edgeAbsPromoNum (pm : Slot J ℓ → Option (Fin Bc)) : ℕ :=
  (Finset.univ.filter fun sl : Slot J ℓ => pm sl ≠ none).card

/-- **(eq:edge-joint-memory)**: the new memory is `Y = T_Δ u ⊔ ((s_h, Δ mod s_h))_h`. -/
theorem edgeAbsNewList_eq_surv (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (st : Finset (Slot J ℓ))
    (pm : Slot J ℓ → Option (Fin Bc)) :
    edgeAbsNewList Δ z xg st pm =
      (edgeAbsSurv z pm).map (shiftParticle Δ) ++ edgeAbsStored Δ xg st := by
  have h : (edgeAbsSurv z pm).map (shiftParticle Δ) =
      (List.finRange Bc).filterMap fun j =>
        if ∃ sl, pm sl = some j then none else (memAt z j).map (shiftParticle Δ) := by
    unfold edgeAbsSurv
    rw [List.map_filterMap]
    refine congrArg (fun φ => (List.finRange Bc).filterMap φ) (funext fun j => ?_)
    show (if ∃ sl, pm sl = some j then none else memAt z j).map (shiftParticle Δ) =
      if ∃ sl, pm sl = some j then none else (memAt z j).map (shiftParticle Δ)
    by_cases hc : ∃ sl, pm sl = some j
    · rw [if_pos hc, if_pos hc, Option.map_none]
    · rw [if_neg hc, if_neg hc]
  rw [h]
  rfl

theorem edgeAbsSurv_length_le (z : Mem 𝒢 Bc g) (pm : Slot J ℓ → Option (Fin Bc)) :
    (edgeAbsSurv z pm).length ≤ Bc :=
  (List.length_filterMap_le _ _).trans (le_of_eq List.length_finRange)

/-- The particles of a memory are its survivors and its promoted particles. -/
theorem edgeAbs_perm_surv_prom (z : Mem 𝒢 Bc g) (pm : Slot J ℓ → Option (Fin Bc)) :
    (List.ofFn z.2).Perm (edgeAbsSurv z pm ++ edgeAbsProm z pm) :=
  (l38_filterMap_memAt_perm z).symm.trans
    (l38_filterMap_split (fun j => ∃ sl, pm sl = some j) (memAt z) (List.finRange Bc))

/-- The survivors have at most as many zeros as the memory. -/
theorem edgeAbs_zeros_surv_le (z : Mem 𝒢 Bc g) (pm : Slot J ℓ → Option (Fin Bc)) :
    (edgeAbsSurv z pm).countP (fun pr => decide (pr.2 = 0)) ≤ memZeroCount z := by
  rw [l38_memZeroCount_eq,
    (edgeAbs_perm_surv_prom z pm).countP_eq (fun pr => decide (pr.2 = 0)), List.countP_append]
  exact Nat.le_add_right _ _

/-! ### Weights of lists of optional particles -/

/-- The weight of an optional particle. -/
def l38_ow (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) : Option (Particle 𝒢 g) → ℝ
  | none => 1
  | some pr => μ pr.1

/-- The weight of the list of the present values of a family. -/
theorem l38_lw_filterMap (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) {α : Type*}
    (φ : α → Option (Particle 𝒢 g)) (l : List α) :
    l38_lw μ (l.filterMap φ) = (l.map fun a => l38_ow μ (φ a)).prod := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨o, ho⟩ : ∃ o, φ a = o := ⟨_, rfl⟩
    cases o with
    | none =>
      rw [List.filterMap_cons_none ho, List.map_cons, List.prod_cons, ih, ho]
      exact (one_mul _).symm
    | some pr =>
      have e : l38_lw μ (pr :: t.filterMap φ) = μ pr.1 * l38_lw μ (t.filterMap φ) := by
        unfold l38_lw
        rw [List.map_cons, List.prod_cons]
      rw [List.filterMap_cons_some ho, e, ih, List.map_cons, List.prod_cons, ho]
      rfl

/-- The weight of a list for a constant weight. -/
theorem l38_lw_const (c : ℝ) (l : List (Particle 𝒢 g)) :
    l38_lw (fun _ => c) l = c ^ l.length := by
  induction l with
  | nil =>
    rw [List.length_nil, pow_zero]
    rfl
  | cons a t ih =>
    have e : l38_lw (fun _ => c) (a :: t) = c * l38_lw (fun _ => c) t := by
      unfold l38_lw
      rw [List.map_cons, List.prod_cons]
    rw [e, ih, List.length_cons, pow_succ']

/-! ### Admissible promotions -/

/-- **The promotions `pm` are admissible for the memory `z` and produce the target labels `τ`**
(step 3 of [S-02:0494–0501], for one big group): every promoting slot is unshared, different
slots promote different indices, and the promoted particle has zero translated residue and the
label of its target slot. -/
def EdgeAbsPromoValid (Cg : Finset (Fin J)) (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (pm : Slot J ℓ → Option (Fin Bc)) (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) : Prop :=
  ∀ sl j, pm sl = some j → Unshared Cg sl ∧ (∀ sl', pm sl' = some j → sl' = sl) ∧
    ∃ pr : Particle 𝒢 g, memAt z j = some pr ∧ (shiftParticle Δ pr).2 = 0 ∧ τ sl = pr.1

/-- **The weight of a memory with admissible promotions**: the weight of the survivors times
`μ̃(τ(sl))` for every promoting slot. -/
theorem edgeAbs_lw_valid (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) {Cg : Finset (Fin J)} {Δ : ℤ}
    {z : Mem 𝒢 Bc g} {pm : Slot J ℓ → Option (Fin Bc)} {τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}}
    (hv : EdgeAbsPromoValid Cg Δ z pm τ) :
    l38_lw μ (List.ofFn z.2) =
      l38_lw μ (edgeAbsSurv z pm) * ∏ sl, (if pm sl ≠ none then μ (τ sl) else 1) := by
  have h1 : l38_lw μ (List.ofFn z.2) =
      l38_lw μ (edgeAbsSurv z pm) * l38_lw μ (edgeAbsProm z pm) := by
    rw [← l38_lw_append]
    exact l38_lw_perm μ (edgeAbs_perm_surv_prom z pm)
  have h2 : l38_lw μ (edgeAbsProm z pm) =
      ∏ j : Fin Bc, ∏ sl : Slot J ℓ, (if pm sl = some j then μ (τ sl) else 1) := by
    unfold edgeAbsProm
    rw [l38_lw_filterMap, ← Fin.prod_univ_def]
    refine Finset.prod_congr rfl fun j _ => ?_
    show l38_ow μ (if ∃ sl, pm sl = some j then memAt z j else none) = _
    by_cases hc : ∃ sl, pm sl = some j
    · rw [if_pos hc]
      obtain ⟨sl₀, h₀⟩ := hc
      obtain ⟨_, hinj, pr, hpr, _, hτ⟩ := hv sl₀ j h₀
      rw [hpr]
      exact ((Finset.prod_eq_single_of_mem
        (f := fun sl : Slot J ℓ => if pm sl = some j then μ (τ sl) else 1) sl₀
        (Finset.mem_univ _)
        (fun sl _ hne => if_neg (fun h => hne (hinj sl h)))).trans
          ((if_pos h₀).trans (congrArg μ hτ))).symm
    · rw [if_neg hc]
      exact (Finset.prod_eq_one fun sl _ => if_neg (fun h => hc ⟨sl, h⟩)).symm
  have h3 : ∏ j : Fin Bc, ∏ sl : Slot J ℓ, (if pm sl = some j then μ (τ sl) else 1) =
      ∏ sl, (if pm sl ≠ none then μ (τ sl) else 1) := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun sl _ => ?_
    obtain ⟨o, ho⟩ : ∃ o, pm sl = o := ⟨_, rfl⟩
    cases o with
    | none =>
      rw [if_neg (fun hne : pm sl ≠ none => hne ho)]
      exact Finset.prod_eq_one fun j _ =>
        if_neg (fun h : pm sl = some j => Option.some_ne_none j (h.symm.trans ho))
    | some j₀ =>
      rw [if_pos (fun hn : pm sl = none => Option.some_ne_none j₀ (ho.symm.trans hn))]
      exact (Finset.prod_eq_single_of_mem
        (f := fun j : Fin Bc => if pm sl = some j then μ (τ sl) else 1) j₀ (Finset.mem_univ _)
        (fun j _ hj => if_neg
          (fun h : pm sl = some j => hj (Option.some.inj (h.symm.trans ho))))).trans
          (if_pos ho)
  rw [h1, h2, h3]

/-- **`j = (j - a) + a`**: the size of a memory with admissible promotions. -/
theorem edgeAbs_size_valid {Cg : Finset (Fin J)} {Δ : ℤ} {z : Mem 𝒢 Bc g}
    {pm : Slot J ℓ → Option (Fin Bc)} {τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}}
    (hv : EdgeAbsPromoValid Cg Δ z pm τ) :
    z.1.val = (edgeAbsSurv z pm).length + edgeAbsPromoNum pm := by
  have h := edgeAbs_lw_valid (fun _ => (2 : ℝ)) hv
  have hp : (∏ sl : Slot J ℓ, if pm sl ≠ none then (2 : ℝ) else 1) = 2 ^ edgeAbsPromoNum pm :=
    l38_prod_ite_const (fun sl : Slot J ℓ => pm sl ≠ none) 2
  rw [l38_lw_const, l38_lw_const, List.length_ofFn, hp, ← pow_add] at h
  exact pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) h

/-- **For fixed promotions a memory is determined by its survivors**: "each required residue …
selects exactly one point of counting measure" [S-02:0735–0737]. -/
theorem edgeAbs_surv_injective {Cg : Finset (Fin J)} {Δ : ℤ} {z z' : Mem 𝒢 Bc g}
    {pm : Slot J ℓ → Option (Fin Bc)} {τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}}
    (h : EdgeAbsPromoValid Cg Δ z pm τ) (h' : EdgeAbsPromoValid Cg Δ z' pm τ)
    (hs : edgeAbsSurv z pm = edgeAbsSurv z' pm) : z = z' := by
  have hsize : z.1.val = z'.1.val := by
    rw [edgeAbs_size_valid h, edgeAbs_size_valid h', hs]
  have hpat : ∀ k ∈ List.finRange Bc,
      ((if ∃ sl, pm sl = some k then none else memAt z k) = none ↔
        (if ∃ sl, pm sl = some k then none else memAt z' k) = none) := by
    intro k _
    by_cases hc : ∃ sl, pm sl = some k
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, l38_memAt_eq_none_iff, l38_memAt_eq_none_iff, hsize]
  have hall : ∀ k ∈ List.finRange Bc,
      (if ∃ sl, pm sl = some k then none else memAt z k) =
        (if ∃ sl, pm sl = some k then none else memAt z' k) :=
    l38_filterMap_inj (fun k => if ∃ sl, pm sl = some k then none else memAt z k)
      (fun k => if ∃ sl, pm sl = some k then none else memAt z' k) (List.finRange Bc) hpat hs
  refine l38_mem_ext_memAt z z' fun j => ?_
  by_cases hc : ∃ sl, pm sl = some j
  · obtain ⟨sl, hsl⟩ := hc
    obtain ⟨_, _, pr, hpr, h0, hτ⟩ := h sl j hsl
    obtain ⟨_, _, pr', hpr', h0', hτ'⟩ := h' sl j hsl
    rw [hpr, hpr', l38_promoted_eq hτ h0, l38_promoted_eq hτ' h0']
  · have e1 : (if ∃ sl, pm sl = some j then none else memAt z j) = memAt z j := if_neg hc
    have e2 : (if ∃ sl, pm sl = some j then none else memAt z' j) = memAt z' j :=
      if_neg hc
    exact e1.symm.trans ((hall j (List.mem_finRange j)).trans e2)

/-! ### The removal step for fixed promotions -/

open _root_.Classical in
/-- The weight of a memory `u` of survivors for the promotions `pm`: zero unless every promoting
slot is unshared and every promoted index is smaller than `|u| + a`, and then
`λ^{⊗k}(u) v^{k+a}/(k+a)! ρ^{#zeros} G(u)`. -/
def edgeAbsRemW (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (v ρ : ℝ) (Cg : Finset (Fin J))
    (pm : Slot J ℓ → Option (Fin Bc)) (G : List (Particle 𝒢 g) → ℝ) (u : Mem 𝒢 Bc g) : ℝ :=
  if ∀ sl j, pm sl = some j → Unshared Cg sl ∧ j.val < u.1.val + edgeAbsPromoNum pm then
    l38_lw μ (List.ofFn u.2) *
        (v ^ (u.1.val + edgeAbsPromoNum pm) /
          ((u.1.val + edgeAbsPromoNum pm).factorial : ℝ)) *
        ρ ^ memZeroCount u * G (List.ofFn u.2)
  else 0

open _root_.Classical in
/-- **The removal step for fixed promotions** (eq:edge-factorial-reversal), first equality: the
sum over the memories `z` for which the promotions `pm` are admissible, of
`λ^{⊗j}(z)/j! · v^j ρ^{#zeros} ∏_{fresh} μ̃(τ) · G(survivors)`, is at most
`∏_{sl unshared} μ̃(τ(sl))` times the sum over the memories `u` of the survivors of `edgeAbsRemW`.
The map `z ↦ survivors` is injective, the promoted particles carry the weights `μ̃(τ(sl))`, and
the survivors have at most as many zeros as `z`. -/
theorem edgeAbs_remove_le (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (hμ : ∀ p, 0 ≤ μ p) {v ρ : ℝ}
    (hv : 0 ≤ v) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (Cg : Finset (Fin J)) (Δ : ℤ)
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (pm : Slot J ℓ → Option (Fin Bc))
    (G : List (Particle 𝒢 g) → ℝ) (hG : ∀ l, 0 ≤ G l) :
    ∑ z : Mem 𝒢 Bc g,
        (if EdgeAbsPromoValid Cg Δ z pm τ then
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z * v ^ z.1.val *
            ρ ^ memZeroCount z *
            (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
            G (edgeAbsSurv z pm)
        else 0) ≤
      (∏ sl, if Unshared Cg sl then μ (τ sl) else 1) *
        ∑ u : Mem 𝒢 Bc g, edgeAbsRemW μ v ρ Cg pm G u := by
  obtain ⟨LU, hLU⟩ : ∃ LU : ℝ, LU = ∏ sl, (if Unshared Cg sl then μ (τ sl) else 1) :=
    ⟨_, rfl⟩
  rw [← hLU]
  have hLU0 : 0 ≤ LU := by
    rw [hLU]
    refine Finset.prod_nonneg fun sl _ => ?_
    split_ifs
    · exact hμ _
    · exact zero_le_one
  have hH0 : ∀ u : Mem 𝒢 Bc g, 0 ≤ edgeAbsRemW μ v ρ Cg pm G u := by
    intro u
    unfold edgeAbsRemW
    split_ifs
    · exact mul_nonneg (mul_nonneg (mul_nonneg (l38_lw_nonneg hμ _)
        (div_nonneg (pow_nonneg hv _) (Nat.cast_nonneg _))) (pow_nonneg hρ0 _)) (hG _)
    · exact le_rfl
  -- one memory
  have hterm : ∀ z : Mem 𝒢 Bc g,
      (if EdgeAbsPromoValid Cg Δ z pm τ then
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z * v ^ z.1.val *
            ρ ^ memZeroCount z *
            (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
            G (edgeAbsSurv z pm)
        else 0) ≤
        LU * (if EdgeAbsPromoValid Cg Δ z pm τ then
          edgeAbsRemW μ v ρ Cg pm G (memOfList (Bc := Bc) (edgeAbsSurv z pm)) else 0) := by
    intro z
    by_cases hval : EdgeAbsPromoValid Cg Δ z pm τ
    · rw [if_pos hval, if_pos hval]
      have hlen : (edgeAbsSurv z pm).length ≤ Bc := edgeAbsSurv_length_le z pm
      have hofn : List.ofFn (memOfList (Bc := Bc) (edgeAbsSurv z pm)).2 = edgeAbsSurv z pm :=
        ofFn_memOfList hlen
      have hsz : (memOfList (Bc := Bc) (edgeAbsSurv z pm)).1.val = (edgeAbsSurv z pm).length :=
        memOfList_size hlen
      have hzs := edgeAbs_size_valid hval
      have hlw := edgeAbs_lw_valid μ hval
      have hz0 : memZeroCount (memOfList (Bc := Bc) (edgeAbsSurv z pm)) ≤ memZeroCount z := by
        rw [l38_memZeroCount_memOfList hlen]
        exact edgeAbs_zeros_surv_le z pm
      have hshape : ∀ sl j, pm sl = some j → Unshared Cg sl ∧
          j.val < (memOfList (Bc := Bc) (edgeAbsSurv z pm)).1.val + edgeAbsPromoNum pm := by
        intro sl j hj
        obtain ⟨hU, _, pr, hpr, _, _⟩ := hval sl j hj
        refine ⟨hU, ?_⟩
        rw [hsz, ← hzs]
        exact l38_memAt_lt hpr
      have hprodU : (∏ sl, (if pm sl ≠ none then μ (τ sl) else 1)) *
          (∏ sl, (if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1)) = LU := by
        rw [hLU, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun sl _ => ?_
        obtain ⟨o, ho⟩ : ∃ o, pm sl = o := ⟨_, rfl⟩
        cases o with
        | none =>
          rw [if_neg (fun hne : pm sl ≠ none => hne ho), one_mul]
          exact ite_congr_of_iff (and_iff_left ho) rfl rfl
        | some j =>
          have hU : Unshared Cg sl := (hval sl j ho).1
          rw [if_pos (fun hn : pm sl = none => Option.some_ne_none j (ho.symm.trans hn)),
            if_neg (fun h : Unshared Cg sl ∧ pm sl = none =>
              Option.some_ne_none j (ho.symm.trans h.2)),
            mul_one, if_pos hU]
      have hρ : ρ ^ memZeroCount z ≤
          ρ ^ memZeroCount (memOfList (Bc := Bc) (edgeAbsSurv z pm)) :=
        pow_le_pow_of_le_one hρ0 hρ1 hz0
      unfold edgeAbsRemW
      rw [if_pos hshape, hofn, hsz, l38_pointMass_eq, hlw, hzs]
      exact l38_remove_scalar hprodU hρ hLU0 (l38_lw_nonneg hμ _) (pow_nonneg hv _)
        (Nat.cast_nonneg _) (hG _)
    · rw [if_neg hval, if_neg hval, mul_zero]
  -- the map to the survivors is injective
  have himg : ∑ z : Mem 𝒢 Bc g, (if EdgeAbsPromoValid Cg Δ z pm τ then
        edgeAbsRemW μ v ρ Cg pm G (memOfList (Bc := Bc) (edgeAbsSurv z pm)) else 0) ≤
      ∑ u : Mem 𝒢 Bc g, edgeAbsRemW μ v ρ Cg pm G u := by
    rw [← Finset.sum_filter]
    have hinj : Set.InjOn (fun z : Mem 𝒢 Bc g => memOfList (Bc := Bc) (edgeAbsSurv z pm))
        ↑(Finset.univ.filter fun z : Mem 𝒢 Bc g => EdgeAbsPromoValid Cg Δ z pm τ) := by
      intro z hz z' hz' hzz
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hz')).2
      refine edgeAbs_surv_injective h1 h2 ?_
      have e : List.ofFn (memOfList (Bc := Bc) (edgeAbsSurv z pm)).2 =
          List.ofFn (memOfList (Bc := Bc) (edgeAbsSurv z' pm)).2 :=
        congrArg (fun m : Mem 𝒢 Bc g => List.ofFn m.2) hzz
      exact (ofFn_memOfList (edgeAbsSurv_length_le z pm)).symm.trans
        (e.trans (ofFn_memOfList (edgeAbsSurv_length_le z' pm)))
    have e := Finset.sum_image (f := edgeAbsRemW μ v ρ Cg pm G) hinj
    refine (le_of_eq e.symm).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun u _ _ => hH0 u
  calc ∑ z : Mem 𝒢 Bc g,
        (if EdgeAbsPromoValid Cg Δ z pm τ then
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z * v ^ z.1.val *
            ρ ^ memZeroCount z *
            (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
            G (edgeAbsSurv z pm)
        else 0)
      ≤ ∑ z : Mem 𝒢 Bc g, LU * (if EdgeAbsPromoValid Cg Δ z pm τ then
          edgeAbsRemW μ v ρ Cg pm G (memOfList (Bc := Bc) (edgeAbsSurv z pm)) else 0) :=
        Finset.sum_le_sum fun z _ => hterm z
    _ = LU * ∑ z : Mem 𝒢 Bc g, (if EdgeAbsPromoValid Cg Δ z pm τ then
          edgeAbsRemW μ v ρ Cg pm G (memOfList (Bc := Bc) (edgeAbsSurv z pm)) else 0) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ LU * ∑ u : Mem 𝒢 Bc g, edgeAbsRemW μ v ρ Cg pm G u :=
        mul_le_mul_of_nonneg_left himg hLU0

/-! ### The sum over the promotion maps -/

open _root_.Classical in
/-- **The count of the promotion maps** (eq:edge-factorial-reversal, eq:promotion-count for the
reversed edge is not needed here): summed over all promotion maps of unshared slots into the
indices below `n + a`, the factors `V^{-a} v^{n+a}/(n+a)!` are at most
`(1 + T v / V)^T · v^n / n!`. There are at most `(n + a)^a` such maps with `a` promotions, and
`n! (n+1)^a ≤ (n+a)!`. -/
theorem edgeAbs_promoShape_sum_le {v V : ℝ} (hv : 0 ≤ v) (hV : 0 < V) (Cg : Finset (Fin J))
    {T : ℕ} (hT : 0 < T) (hC : ℓ + Cg.card ≤ T) (n : ℕ) :
    ∑ pm : Slot J ℓ → Option (Fin Bc),
        (if ∀ sl j, pm sl = some j → Unshared Cg sl ∧ j.val < n + edgeAbsPromoNum pm then
          (V ^ edgeAbsPromoNum pm)⁻¹ *
            (v ^ (n + edgeAbsPromoNum pm) / ((n + edgeAbsPromoNum pm).factorial : ℝ))
        else 0) ≤
      (1 + (T : ℝ) * v / V) ^ T * (v ^ n / (n.factorial : ℝ)) := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = v / (V * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_pos
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    exact div_nonneg hv (mul_pos hV hn1).le
  have hvn : 0 ≤ v ^ n / (n.factorial : ℝ) := div_nonneg (pow_nonneg hv n) (Nat.cast_nonneg _)
  have hUcard : (Finset.univ.filter fun sl : Slot J ℓ => Unshared Cg sl).card = ℓ + Cg.card :=
    l38_card_unshared Cg
  -- one promotion map
  have hterm : ∀ pm : Slot J ℓ → Option (Fin Bc),
      (if ∀ sl j, pm sl = some j → Unshared Cg sl ∧ j.val < n + edgeAbsPromoNum pm then
          (V ^ edgeAbsPromoNum pm)⁻¹ *
            (v ^ (n + edgeAbsPromoNum pm) / ((n + edgeAbsPromoNum pm).factorial : ℝ))
        else 0) ≤
        v ^ n / (n.factorial : ℝ) *
          ∏ sl, l38_slotW κ (fun sl : Slot J ℓ => Unshared Cg sl)
            (fun j : Fin Bc => j.val < n + T) sl (pm sl) := by
    intro pm
    have hnn : 0 ≤ v ^ n / (n.factorial : ℝ) *
        ∏ sl, l38_slotW κ (fun sl : Slot J ℓ => Unshared Cg sl)
          (fun j : Fin Bc => j.val < n + T) sl (pm sl) :=
      mul_nonneg hvn (Finset.prod_nonneg fun sl _ => l38_slotW_nonneg hκ0 _ _ sl _)
    by_cases hsh : ∀ sl j, pm sl = some j →
        Unshared Cg sl ∧ j.val < n + edgeAbsPromoNum pm
    · rw [if_pos hsh]
      have ha : edgeAbsPromoNum pm ≤ T := by
        have hsub : (Finset.univ.filter fun sl : Slot J ℓ => pm sl ≠ none) ⊆
            Finset.univ.filter fun sl : Slot J ℓ => Unshared Cg sl := by
          intro sl hsl
          have hne : pm sl ≠ none := (Finset.mem_filter.mp hsl).2
          obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ sl, (hsh sl j hj).1⟩
        exact (Finset.card_le_card hsub).trans (hUcard.le.trans hC)
      have hval : ∀ sl j, pm sl = some j → Unshared Cg sl ∧ j.val < n + T := fun sl j hj =>
        ⟨(hsh sl j hj).1, lt_of_lt_of_le (hsh sl j hj).2 (Nat.add_le_add_left ha n)⟩
      have hprod : ∏ sl, l38_slotW κ (fun sl : Slot J ℓ => Unshared Cg sl)
            (fun j : Fin Bc => j.val < n + T) sl (pm sl) = κ ^ edgeAbsPromoNum pm :=
        l38_prod_slotW_of_valid κ _ _ pm hval
      rw [hprod, hκ]
      exact l38_fact_scalar hv hV n _
    · rw [if_neg hsh]
      exact hnn
  have hsum : ∑ pm : Slot J ℓ → Option (Fin Bc),
        ∏ sl, l38_slotW κ (fun sl : Slot J ℓ => Unshared Cg sl)
          (fun j : Fin Bc => j.val < n + T) sl (pm sl) =
      (1 + ((Finset.univ.filter fun j : Fin Bc => j.val < n + T).card : ℝ) * κ) ^
        (Finset.univ.filter fun sl : Slot J ℓ => Unshared Cg sl).card :=
    l38_sum_prod_slotW κ _ _
  have hE : ((Finset.univ.filter fun j : Fin Bc => j.val < n + T).card : ℝ) ≤ (n : ℝ) + T := by
    exact_mod_cast l38_card_fin_lt_le (n := Bc) (n + T)
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have h3 : (n : ℝ) + T ≤ (T : ℝ) * ((n : ℝ) + 1) := by
    have h4 := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hT1)
    linarith
  have h2 : ((n : ℝ) + T) * κ ≤ (T : ℝ) * v / V := by
    calc ((n : ℝ) + T) * κ ≤ ((T : ℝ) * ((n : ℝ) + 1)) * κ :=
          mul_le_mul_of_nonneg_right h3 hκ0
      _ = ((T : ℝ) * v) * ((n : ℝ) + 1) / (V * ((n : ℝ) + 1)) := by
          rw [hκ]
          ring
      _ = (T : ℝ) * v / V := mul_div_mul_right _ _ hn1.ne'
  have hbase : 1 + ((Finset.univ.filter fun j : Fin Bc => j.val < n + T).card : ℝ) * κ ≤
      1 + (T : ℝ) * v / V := by
    have h1 : ((Finset.univ.filter fun j : Fin Bc => j.val < n + T).card : ℝ) * κ ≤
        ((n : ℝ) + T) * κ := mul_le_mul_of_nonneg_right hE hκ0
    linarith
  have hb0 : 0 ≤ 1 + ((Finset.univ.filter fun j : Fin Bc => j.val < n + T).card : ℝ) * κ :=
    add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hκ0)
  have hb1 : (1 : ℝ) ≤ 1 + (T : ℝ) * v / V :=
    le_add_of_nonneg_right (div_nonneg (mul_nonneg (Nat.cast_nonneg T) hv) hV.le)
  calc ∑ pm : Slot J ℓ → Option (Fin Bc),
        (if ∀ sl j, pm sl = some j → Unshared Cg sl ∧ j.val < n + edgeAbsPromoNum pm then
          (V ^ edgeAbsPromoNum pm)⁻¹ *
            (v ^ (n + edgeAbsPromoNum pm) / ((n + edgeAbsPromoNum pm).factorial : ℝ))
        else 0)
      ≤ ∑ pm : Slot J ℓ → Option (Fin Bc), v ^ n / (n.factorial : ℝ) *
          ∏ sl, l38_slotW κ (fun sl : Slot J ℓ => Unshared Cg sl)
            (fun j : Fin Bc => j.val < n + T) sl (pm sl) :=
        Finset.sum_le_sum fun pm _ => hterm pm
    _ = v ^ n / (n.factorial : ℝ) *
          (1 + ((Finset.univ.filter fun j : Fin Bc => j.val < n + T).card : ℝ) * κ) ^
            (Finset.univ.filter fun sl : Slot J ℓ => Unshared Cg sl).card := by
        rw [← Finset.mul_sum, hsum]
    _ ≤ v ^ n / (n.factorial : ℝ) * (1 + (T : ℝ) * v / V) ^ T := by
        refine mul_le_mul_of_nonneg_left ?_ hvn
        rw [hUcard]
        exact (pow_le_pow_left₀ hb0 hbase _).trans (pow_le_pow_right₀ hb1 hC)
    _ = (1 + (T : ℝ) * v / V) ^ T * (v ^ n / (n.factorial : ℝ)) := mul_comm _ _

/-! ### The removal step -/

open _root_.Classical in
/-- **The removal step** [S-02:0704–0737]: the sum over the source memories `z` and over the
promotions which are admissible for `z` and produce the target labels `τ`, of

`V_g^{-a} · λ^{⊗j}(z)/j! · v^j · ρ^{#zeros(z)} · ∏_{fresh sl} μ̃(τ(sl)) · G(survivors)`,

is at most `(1 + T v / V_g)^T ∏_{sl unshared} μ̃(τ(sl))` times the sum over the memories `u` of
`λ^{⊗k}(u)/k! · v^k · ρ^{#zeros(u)} · G(u)`. -/
theorem edgeAbs_remove_sum_le (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    {v ρ V : ℝ} (hv : 0 ≤ v) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hV : 0 < V) (Cg : Finset (Fin J))
    {T : ℕ} (hT : 0 < T) (hC : ℓ + Cg.card ≤ T) (Δ : ℤ)
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (G : List (Particle 𝒢 g) → ℝ)
    (hG : ∀ l, 0 ≤ G l) :
    ∑ z : Mem 𝒢 Bc g, ∑ pm : Slot J ℓ → Option (Fin Bc),
        (if EdgeAbsPromoValid Cg Δ z pm τ then
          (V ^ edgeAbsPromoNum pm)⁻¹ *
            (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z * v ^ z.1.val *
              ρ ^ memZeroCount z *
              (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
              G (edgeAbsSurv z pm))
        else 0) ≤
      (1 + (T : ℝ) * v / V) ^ T * (∏ sl, if Unshared Cg sl then μ (τ sl) else 1) *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            ρ ^ memZeroCount u * G (List.ofFn u.2) := by
  obtain ⟨LU, hLU⟩ : ∃ LU : ℝ, LU = ∏ sl, (if Unshared Cg sl then μ (τ sl) else 1) :=
    ⟨_, rfl⟩
  have hLU0 : 0 ≤ LU := by
    rw [hLU]
    refine Finset.prod_nonneg fun sl _ => ?_
    split_ifs
    · exact hμ _
    · exact zero_le_one
  obtain ⟨A, hA⟩ : ∃ A : Mem 𝒢 Bc g → ℝ, ∀ u,
      A u = l38_lw μ (List.ofFn u.2) * ρ ^ memZeroCount u * G (List.ofFn u.2) :=
    ⟨_, fun _ => rfl⟩
  have hA0 : ∀ u, 0 ≤ A u := by
    intro u
    rw [hA]
    exact mul_nonneg (mul_nonneg (l38_lw_nonneg hμ _) (pow_nonneg hρ0 _)) (hG _)
  obtain ⟨W, hW⟩ : ∃ W : (Slot J ℓ → Option (Fin Bc)) → Mem 𝒢 Bc g → ℝ, ∀ pm u,
      W pm u = if ∀ sl j, pm sl = some j →
          Unshared Cg sl ∧ j.val < u.1.val + edgeAbsPromoNum pm then
        (V ^ edgeAbsPromoNum pm)⁻¹ *
          (v ^ (u.1.val + edgeAbsPromoNum pm) /
            ((u.1.val + edgeAbsPromoNum pm).factorial : ℝ))
      else 0 := ⟨_, fun _ _ => rfl⟩
  -- fixed promotions
  have hpm : ∀ pm : Slot J ℓ → Option (Fin Bc),
      ∑ z : Mem 𝒢 Bc g,
        (if EdgeAbsPromoValid Cg Δ z pm τ then
          (V ^ edgeAbsPromoNum pm)⁻¹ *
            (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z * v ^ z.1.val *
              ρ ^ memZeroCount z *
              (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
              G (edgeAbsSurv z pm))
        else 0) ≤
        ∑ u : Mem 𝒢 Bc g, LU * (A u * W pm u) := by
    intro pm
    have h := edgeAbs_remove_le μ hμ hv hρ0 hρ1 Cg Δ τ pm G hG
    rw [← hLU] at h
    have e : ∑ z : Mem 𝒢 Bc g,
        (if EdgeAbsPromoValid Cg Δ z pm τ then
          (V ^ edgeAbsPromoNum pm)⁻¹ *
            (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z * v ^ z.1.val *
              ρ ^ memZeroCount z *
              (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
              G (edgeAbsSurv z pm))
        else 0) =
        (V ^ edgeAbsPromoNum pm)⁻¹ * ∑ z : Mem 𝒢 Bc g,
          (if EdgeAbsPromoValid Cg Δ z pm τ then
            Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z * v ^ z.1.val *
              ρ ^ memZeroCount z *
              (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
              G (edgeAbsSurv z pm)
          else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs
      · rfl
      · exact (mul_zero _).symm
    have e2 : (V ^ edgeAbsPromoNum pm)⁻¹ * (LU * ∑ u : Mem 𝒢 Bc g, edgeAbsRemW μ v ρ Cg pm G u) =
        ∑ u : Mem 𝒢 Bc g, LU * (A u * W pm u) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hA, hW]
      unfold edgeAbsRemW
      split_ifs
      · ring
      · ring
    rw [e, ← e2]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (pow_nonneg hV.le _))
  have hswap : ∑ pm : Slot J ℓ → Option (Fin Bc), ∑ u : Mem 𝒢 Bc g, LU * (A u * W pm u) =
      LU * ∑ u : Mem 𝒢 Bc g, A u * ∑ pm : Slot J ℓ → Option (Fin Bc), W pm u := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have hcount : ∀ u : Mem 𝒢 Bc g, ∑ pm : Slot J ℓ → Option (Fin Bc), W pm u ≤
      (1 + (T : ℝ) * v / V) ^ T * (v ^ u.1.val / (u.1.val.factorial : ℝ)) := by
    intro u
    rw [Finset.sum_congr rfl fun pm _ => hW pm u]
    exact edgeAbs_promoShape_sum_le hv hV Cg hT hC u.1.val
  rw [← hLU, Finset.sum_comm]
  calc ∑ pm : Slot J ℓ → Option (Fin Bc), ∑ z : Mem 𝒢 Bc g,
        (if EdgeAbsPromoValid Cg Δ z pm τ then
          (V ^ edgeAbsPromoNum pm)⁻¹ *
            (Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z * v ^ z.1.val *
              ρ ^ memZeroCount z *
              (∏ sl, if Unshared Cg sl ∧ pm sl = none then μ (τ sl) else 1) *
              G (edgeAbsSurv z pm))
        else 0)
      ≤ ∑ pm : Slot J ℓ → Option (Fin Bc), ∑ u : Mem 𝒢 Bc g, LU * (A u * W pm u) :=
        Finset.sum_le_sum fun pm _ => hpm pm
    _ = LU * ∑ u : Mem 𝒢 Bc g, A u * ∑ pm : Slot J ℓ → Option (Fin Bc), W pm u := hswap
    _ ≤ LU * ∑ u : Mem 𝒢 Bc g,
          A u * ((1 + (T : ℝ) * v / V) ^ T * (v ^ u.1.val / (u.1.val.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hcount u) (hA0 u)) hLU0
    _ = (1 + (T : ℝ) * v / V) ^ T * LU *
          ∑ u : Mem 𝒢 Bc g,
            Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
              ρ ^ memZeroCount u * G (List.ofFn u.2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hA, l38_pointMass_eq]
        ring

end OneGroup

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
