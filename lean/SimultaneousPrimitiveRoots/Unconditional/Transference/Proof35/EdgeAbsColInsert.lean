module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsColRemove
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The column bound of the absolute edge: inserting the stored particles

Source: `verification/stage7-sources/S-02.tex`, lines 704–756 and 788–794
(`[S-02:0704–0756, 0788–0794]`), (eq:edge-joint-memory), (eq:edge-joint-measure),
(eq:edge-factorial-reversal).

"Suppose `a` target slots are promotions and `b` source slots are stores …
`Y = T_Δ u ⊔ ((s_h, Δ mod s_h))_{h ≤ b}` … The second [equality of (eq:edge-factorial-reversal)]
selects `b` indices of the output memory into the original source slots on reversal"
[S-02:0706–0734]. "For the column, use (eq:edge-joint-memory), (eq:edge-factorial-reversal) in
reverse. Original stores are now ordered retrievals. Their count is controlled by the original
input `ρ` factors after reversed translation, in exactly the form in (eq:promotion-count)"
[S-02:0788–0792]. In the notation below, `Z''` is the number of pending particles of the target
which are at the residue `Δ mod p` of a stored particle, and the count is `(Z'')_b ≤ (Z'')^b`
against the source damping `ρ^{Z'' - b}`.

For one big group, after the promoted particles have been removed (`EdgeAbsColRemove.lean`), the
source consists of a memory `u` of survivors and of the source labels; the stored labels
`s_h` are integrated against `μ̃_g`, and the new memory is `T_Δ u ⊔ ((s_h, Δ))_h`.

* `l38_anchor`, `l38_anchCount`, `l38_anchInd` — the anchor `Δ mod p` of a stored particle after
  the translation, the number of particles of a list at their anchor (`Z''`), and the indicator of
  the tuples at their anchors.
* `l38_anchor_sum_le` — "each required residue … selects exactly one point of counting measure":
  the integral over the stored labels is an integral over anchored particles.
* `edgeAbs_insert_fixed` — **the reversal for fixed sizes** `k`, `b`: by
  `Graph.ordered_retrieval_joint_sum` ("the factorial accounting is `(j')_b / j'! = 1/(j'-b)!`")
  the integral over `(u, s)` is the integral over the new memory `Y` of the number of ordered
  retrievals of `b` anchored particles, which is at most `(Z'')^b`; the source damping
  `ρ^{#zeros(u)} = ρ^{Z'' - b}` bounds it uniformly (`l38_count_scalar`).
* `edgeAbs_insert_tuple` — the same summed over the sizes of the memories, with the truncation.
* `edgeAbsSrcW`, `edgeAbs_insert_le` — **the insertion step**: the integral over all source
  labels (shared labels are those of the target; unshared labels which are not stored integrate
  to `μ̃_g(𝒫_g)`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Scalars and finite sums -/

/-- `ρ^c = ρ^{c+b} ρ^{-b}`. -/
theorem l38_rho_split {ρ : ℝ} (h0 : 0 < ρ) (c b : ℕ) : ρ ^ c = ρ ^ (c + b) * ρ⁻¹ ^ b := by
  rw [pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ h0.ne', one_pow, mul_one]

theorem l38_countSup_nonneg (T : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 ≤ Schur.countSup T ρ :=
  (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hρ0.le _)).trans
    (Schur.le_countSup T hρ0 hρ1 0)

/-- **`(Z'')^b ρ^{Z''}` is uniformly bounded**, "in exactly the form in (eq:promotion-count)"
[S-02:0790–0792]: `ρ^c c^b ≤ sup_z (z+T)^T ρ^z` for `b ≤ T`. -/
theorem l38_count_scalar {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {T b : ℕ} (hT : 0 < T)
    (hb : b ≤ T) (c : ℕ) : ρ ^ c * (c : ℝ) ^ b ≤ Schur.countSup T ρ := by
  have h1n : 1 ≤ c + T := by omega
  have h1 : (1 : ℝ) ≤ ((c + T : ℕ) : ℝ) := by exact_mod_cast h1n
  have h2 : (c : ℝ) ≤ ((c + T : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right c T
  have h3 : (c : ℝ) ^ b ≤ ((c + T : ℕ) : ℝ) ^ T :=
    (pow_le_pow_left₀ (Nat.cast_nonneg c) h2 b).trans (pow_le_pow_right₀ h1 hb)
  calc ρ ^ c * (c : ℝ) ^ b ≤ ρ ^ c * ((c + T : ℕ) : ℝ) ^ T :=
        mul_le_mul_of_nonneg_left h3 (pow_nonneg hρ0.le c)
    _ = ((c + T : ℕ) : ℝ) ^ T * ρ ^ c := mul_comm _ _
    _ ≤ Schur.countSup T ρ := Schur.le_countSup T hρ0 hρ1 c

/-- A sum over the sizes `n` with `n + b ≤ N` of terms attached to the size `n + b`. -/
theorem l38_sum_shift_le (R : ℕ → ℝ) (h0 : ∀ j, 0 ≤ R j) (N b : ℕ) :
    ∑ n : Fin (N + 1), (if n.val + b ≤ N then R (n.val + b) else 0) ≤
      ∑ j : Fin (N + 1), R j.val := by
  have e1 : ∑ n : Fin (N + 1), (if n.val + b ≤ N then R (n.val + b) else 0) =
      ∑ n ∈ Finset.range (N + 1), (if n + b ≤ N then R (n + b) else 0) :=
    Fin.sum_univ_eq_sum_range (fun n => if n + b ≤ N then R (n + b) else 0) (N + 1)
  have e2 : ∑ j : Fin (N + 1), R j.val = ∑ j ∈ Finset.range (N + 1), R j :=
    Fin.sum_univ_eq_sum_range R (N + 1)
  have e3 : ∑ n ∈ Finset.range (N + 1), (if n + b ≤ N then R (n + b) else 0) =
      ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n + b ≤ N), R (n + b) :=
    (Finset.sum_filter (fun n => n + b ≤ N) (fun n => R (n + b))).symm
  have hinj : Set.InjOn (fun n : ℕ => n + b)
      ↑((Finset.range (N + 1)).filter fun n => n + b ≤ N) :=
    fun n _ n' _ h => Nat.add_right_cancel h
  have e4 := Finset.sum_image (f := R) hinj
  rw [e1, e2, e3]
  refine (le_of_eq e4.symm).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => h0 j
  obtain ⟨n, hn, hnj⟩ := Finset.mem_image.mp hj
  have hnj' : n + b = j := hnj
  rw [← hnj']
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hn).2)

/-- A mapped list is the list of the values at its positions. -/
theorem l38_map_eq_ofFn {α β : Type*} (f : α → β) (l : List α) :
    l.map f = List.ofFn (fun h : Fin l.length => f (l.get h)) := by
  have h := List.map_ofFn (f := l.get) (g := f)
  rw [List.ofFn_get] at h
  exact h

/-- A product over the complement of a set of indices is at most the full product, for factors
which are at least one (the Fintype instance of the complement is arbitrary). -/
theorem l38_prod_compl_le {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    {hF : Fintype {x : ι // ¬p x}} (f g : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i)
    (hg1 : ∀ i, 1 ≤ g i) : ∏ i : {x : ι // ¬p x}, f i ≤ ∏ i, g i := by
  have h2 : ∏ i : {x : ι // ¬p x}, g i = ∏ i ∈ Finset.univ.filter (fun x => ¬p x), g i :=
    (Finset.prod_subtype (Finset.univ.filter fun x => ¬p x)
      (fun x => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ x)) g).symm
  have h1 : (1 : ℝ) ≤ ∏ i ∈ Finset.univ.filter p, g i := by
    have h : ∏ _i ∈ Finset.univ.filter p, (1 : ℝ) ≤ ∏ i ∈ Finset.univ.filter p, g i :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hg1 i)
    rw [Finset.prod_const_one] at h
    exact h
  have h0 : 0 ≤ ∏ i ∈ Finset.univ.filter (fun x => ¬p x), g i :=
    Finset.prod_nonneg fun i _ => zero_le_one.trans (hg1 i)
  calc ∏ i : {x : ι // ¬p x}, f i ≤ ∏ i : {x : ι // ¬p x}, g i :=
        Finset.prod_le_prod (fun i _ => hf0 i.1) (fun i _ => hfg i.1)
    _ = ∏ i ∈ Finset.univ.filter (fun x => ¬p x), g i := h2
    _ = 1 * ∏ i ∈ Finset.univ.filter (fun x => ¬p x), g i := (one_mul _).symm
    _ ≤ (∏ i ∈ Finset.univ.filter p, g i) * ∏ i ∈ Finset.univ.filter (fun x => ¬p x), g i :=
        mul_le_mul_of_nonneg_right h1 h0
    _ = ∏ i, g i := Finset.prod_filter_mul_prod_filter_not Finset.univ p g

section OneGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {g : B}

/-! ### Anchors -/

/-- **The anchor `Δ mod p`**: the residue of a stored particle with label `p` after the
translation by `Δ` (eq:edge-joint-memory). -/
def l38_anchor (𝒢 : GroupFamily S B) (g : B) (Δ : ℤ) (p : {p : ℕ // p ∈ 𝒢.big g}) : Res p.1 :=
  ((Δ : ℤ) : Res p.1)

/-- **`Z''`**: the number of particles of a list which are at their anchor (the pending
particles of the target at the residue `Δ mod p` of a stored particle, (eq:edge-joint-memory)). -/
def l38_anchCount (Δ : ℤ) (l : List (Particle 𝒢 g)) : ℕ :=
  l.countP fun pr => decide (pr.2 = l38_anchor 𝒢 g Δ pr.1)

open _root_.Classical in
/-- The indicator of the tuples all of whose particles are at their anchors. -/
def l38_anchInd (Δ : ℤ) {b : ℕ} (p : Fin b → Particle 𝒢 g) : ℝ :=
  if ∀ h, (p h).2 = l38_anchor 𝒢 g Δ (p h).1 then 1 else 0

theorem l38_anchInd_nonneg (Δ : ℤ) {b : ℕ} (p : Fin b → Particle 𝒢 g) :
    0 ≤ l38_anchInd Δ p := by
  unfold l38_anchInd
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem l38_anchInd_anchored (Δ : ℤ) {b : ℕ} (q : Fin b → {p : ℕ // p ∈ 𝒢.big g}) :
    l38_anchInd Δ (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q) = 1 := by
  unfold l38_anchInd
  exact if_pos fun _ => rfl

theorem l38_anchCount_perm (Δ : ℤ) {l₁ l₂ : List (Particle 𝒢 g)} (h : l₁.Perm l₂) :
    l38_anchCount Δ l₁ = l38_anchCount Δ l₂ :=
  h.countP_eq _

theorem l38_anchCount_append (Δ : ℤ) (l₁ l₂ : List (Particle 𝒢 g)) :
    l38_anchCount Δ (l₁ ++ l₂) = l38_anchCount Δ l₁ + l38_anchCount Δ l₂ :=
  List.countP_append

/-- The translated particles at their anchor are the particles with residue zero. -/
theorem l38_anchCount_map_shift (Δ : ℤ) (l : List (Particle 𝒢 g)) :
    l38_anchCount Δ (l.map (shiftParticle Δ)) = l.countP (fun pr => decide (pr.2 = 0)) := by
  have hfun : ((fun pr : Particle 𝒢 g => decide (pr.2 = l38_anchor 𝒢 g Δ pr.1)) ∘
      shiftParticle Δ) = fun pr : Particle 𝒢 g => decide (pr.2 = 0) :=
    funext fun pr => decide_eq_decide.mpr (by
      show ((Δ : ℤ) : Res pr.1.1) + pr.2 = ((Δ : ℤ) : Res pr.1.1) ↔ pr.2 = 0
      exact add_eq_left)
  unfold l38_anchCount
  rw [List.countP_map, hfun]

/-- A stored particle `(p, 0)` is translated to its anchor. -/
theorem l38_shift_zero (Δ : ℤ) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    shiftParticle Δ (⟨p, 0⟩ : Particle 𝒢 g) = ⟨p, l38_anchor 𝒢 g Δ p⟩ := by
  show (⟨p, ((Δ : ℤ) : Res p.1) + 0⟩ : Particle 𝒢 g) = ⟨p, ((Δ : ℤ) : Res p.1)⟩
  rw [add_zero]

theorem l38_anchCount_anchored (Δ : ℤ) {b : ℕ} (q : Fin b → {p : ℕ // p ∈ 𝒢.big g}) :
    l38_anchCount Δ (List.ofFn (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)) = b := by
  have h : ∀ a ∈ List.ofFn (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q),
      (fun pr : Particle 𝒢 g => decide (pr.2 = l38_anchor 𝒢 g Δ pr.1)) a = true :=
    List.forall_mem_ofFn_iff.mpr fun j => decide_eq_true rfl
  exact (List.countP_eq_length.mpr h).trans List.length_ofFn

/-- **`Z''` of the new memory** `u ⊔ ((s_h, Δ))_h` is `Z''(u) + b`. -/
theorem l38_anchCount_join (Δ : ℤ) {k b : ℕ} (u : Fin k → Particle 𝒢 g)
    (q : Fin b → {p : ℕ // p ∈ 𝒢.big g}) :
    l38_anchCount Δ
        (List.ofFn (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q))) =
      l38_anchCount Δ (List.ofFn u) + b := by
  rw [ofFn_memoryJoin, l38_anchCount_append, l38_anchCount_anchored]

open _root_.Classical in
/-- **"Each required residue … selects exactly one point of counting measure"**
[S-02:0735–0737]: the integral over the labels `q` of anchored particles is at most the integral
over all tuples of particles of the indicator of the anchored tuples (the anchored tuples are in
bijection with their labels). -/
theorem l38_anchor_sum_le (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (hμ : ∀ p, 0 ≤ μ p) (Δ : ℤ)
    {b : ℕ} (G : (Fin b → Particle 𝒢 g) → ℝ) (hG : ∀ p, 0 ≤ G p) :
    ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g},
        (∏ h, μ (q h)) * G (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q) ≤
      ∑ p : Fin b → Particle 𝒢 g, (∏ h, μ (p h).1) * G p * l38_anchInd Δ p := by
  have hinj : Set.InjOn
      (fun q : Fin b → {p : ℕ // p ∈ 𝒢.big g} => Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)
      ↑(Finset.univ : Finset (Fin b → {p : ℕ // p ∈ 𝒢.big g})) := by
    intro q _ q' _ h
    funext i
    exact congrArg (fun p : Fin b → Particle 𝒢 g => (p i).1) h
  have e := Finset.sum_image
    (f := fun p : Fin b → Particle 𝒢 g => (∏ h, μ (p h).1) * G p * l38_anchInd Δ p) hinj
  have e2 : ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g},
        (∏ h, μ (q h)) * G (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q) =
      ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g},
        (fun p : Fin b → Particle 𝒢 g => (∏ h, μ (p h).1) * G p * l38_anchInd Δ p)
          (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    exact ((congrArg (fun t => (∏ h, μ (q h)) *
      G (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q) * t) (l38_anchInd_anchored Δ q)).trans
        (mul_one _)).symm
  refine (le_of_eq (e2.trans e.symm)).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => ?_
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun h _ => hμ _) (hG p))
    (l38_anchInd_nonneg Δ p)

/-- **The number of ordered retrievals of anchored particles** is at most `(Z'')^b`
[S-02:0789–0791]. -/
theorem l38_sum_anchInd_le (Δ : ℤ) {b n : ℕ} (x : Fin n → Particle 𝒢 g) :
    ∑ e : Fin b ↪ Fin n, l38_anchInd Δ (fun h => x (e h)) ≤
      ((l38_anchCount Δ (List.ofFn x) : ℕ) : ℝ) ^ b := by
  refine (le_of_eq (Finset.sum_congr rfl fun e _ => ?_)).trans
    ((l38_sum_embedding_le (b := b) (fun i : Fin n => (x i).2 = l38_anchor 𝒢 g Δ (x i).1)).trans
      (le_of_eq (congrArg (fun m : ℕ => (m : ℝ) ^ b)
        (l38_card_filter_eq_countP x
          (fun pr : Particle 𝒢 g => pr.2 = l38_anchor 𝒢 g Δ pr.1)))))
  unfold l38_anchInd
  exact ite_congr_of_iff Iff.rfl rfl rfl

theorem l38_pointMass_nonneg {μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ} (hμ : ∀ p, 0 ≤ μ p)
    (u : Mem 𝒢 Bc g) :
    0 ≤ Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u := by
  rw [l38_pointMass_eq]
  exact div_nonneg (l38_lw_nonneg hμ _) (Nat.cast_nonneg _)

/-! ### The reversal for fixed sizes -/

/-- **The reversal of the stores for fixed sizes** (eq:edge-joint-measure),
(eq:edge-factorial-reversal), second equality, and [S-02:0788–0792]: for memories `u` of `k`
survivors and `b` stored labels `q`, with the measure `λ^{⊗k}/k! ⊗ μ̃^{⊗b}` and the source
damping `ρ^{#zeros(u)}`, the integral of a symmetric nonnegative function `Ψ'` of the new memory
`T_Δ u ⊔ ((q_h, Δ))_h` is at most `ρ^{-b} sup_z (z+T)^T ρ^z` times the integral of `Ψ'` against
`λ^{⊗(k+b)}/(k+b)!`. -/
theorem edgeAbs_insert_fixed (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (hμ : ∀ p, 0 ≤ μ p) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (Δ : ℤ) {T : ℕ} (hT : 0 < T) (k b : ℕ) (hb : b ≤ T)
    (Ψ' : (Fin (k + b) → Particle 𝒢 g) → ℝ) (hΨ0 : ∀ x, 0 ≤ Ψ' x)
    (hΨ : ∀ (σ : Equiv.Perm (Fin (k + b))) (x : Fin (k + b) → Particle 𝒢 g),
      Ψ' (x ∘ σ) = Ψ' x) :
    ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Fin k → Particle 𝒢 g, (∏ i, μ (u i).1) / (k.factorial : ℝ) *
          ρ ^ (List.ofFn u).countP (fun pr => decide (pr.2 = 0)) *
          Ψ' (Graph.memoryJoin (fun i => shiftParticle Δ (u i))
            (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)) ≤
      ρ⁻¹ ^ b * Schur.countSup T ρ *
        ∑ x : Fin (k + b) → Particle 𝒢 g,
          (∏ i, μ (x i).1) / ((k + b).factorial : ℝ) * Ψ' x := by
  obtain ⟨F, hFdef⟩ : ∃ F : (Fin (k + b) → Particle 𝒢 g) → ℝ,
      ∀ x, F x = ρ ^ l38_anchCount Δ (List.ofFn x) * Ψ' x := ⟨_, fun _ => rfl⟩
  have hF0 : ∀ x, 0 ≤ F x := by
    intro x
    rw [hFdef]
    exact mul_nonneg (pow_nonneg hρ0.le _) (hΨ0 x)
  have hFsym : ∀ (σ : Equiv.Perm (Fin (k + b))) (x : Fin (k + b) → Particle 𝒢 g),
      F (x ∘ σ) = F x := by
    intro σ x
    rw [hFdef, hFdef, hΨ σ x, l38_anchCount_perm Δ (Equiv.Perm.ofFn_comp_perm σ x)]
  have hK : (0 : ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
  have hKb : (0 : ℝ) ≤ ((k + b).factorial : ℝ) := Nat.cast_nonneg _
  have hr0 : 0 ≤ ρ⁻¹ ^ b := pow_nonneg (inv_nonneg.mpr hρ0.le) b
  -- the translation of the survivors, and the damping
  have h1 : ∀ q : Fin b → {p : ℕ // p ∈ 𝒢.big g},
      ∑ u : Fin k → Particle 𝒢 g, (∏ i, μ (u i).1) / (k.factorial : ℝ) *
          ρ ^ (List.ofFn u).countP (fun pr => decide (pr.2 = 0)) *
          Ψ' (Graph.memoryJoin (fun i => shiftParticle Δ (u i))
            (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)) =
        ρ⁻¹ ^ b * ((∑ u : Fin k → Particle 𝒢 g, (∏ i, μ (u i).1) *
          F (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q))) /
            (k.factorial : ℝ)) := by
    intro q
    have ha : ∑ u : Fin k → Particle 𝒢 g, (∏ i, μ (u i).1) / (k.factorial : ℝ) *
          ρ ^ (List.ofFn u).countP (fun pr => decide (pr.2 = 0)) *
          Ψ' (Graph.memoryJoin (fun i => shiftParticle Δ (u i))
            (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)) =
        ∑ u : Fin k → Particle 𝒢 g, (∏ i, μ (u i).1) / (k.factorial : ℝ) *
          ρ ^ l38_anchCount Δ (List.ofFn u) *
          Ψ' (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)) := by
      refine (Finset.sum_congr rfl fun u _ => ?_).trans
        (Equiv.sum_comp
          (Equiv.piCongrRight fun _ : Fin k => Graph.residueTranslation (l38_anchor 𝒢 g Δ))
          (fun u : Fin k → Particle 𝒢 g => (∏ i, μ (u i).1) / (k.factorial : ℝ) *
            ρ ^ l38_anchCount Δ (List.ofFn u) *
            Ψ' (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q))))
      have hc : l38_anchCount Δ (List.ofFn fun i => shiftParticle Δ (u i)) =
          (List.ofFn u).countP (fun pr => decide (pr.2 = 0)) := by
        have e : (List.ofFn fun i => shiftParticle Δ (u i)) =
            (List.ofFn u).map (shiftParticle Δ) :=
          (List.map_ofFn (f := u) (g := shiftParticle Δ)).symm
        rw [e, l38_anchCount_map_shift]
      exact congrArg (fun n : ℕ => (∏ i, μ (u i).1) / (k.factorial : ℝ) * ρ ^ n *
        Ψ' (Graph.memoryJoin (fun i => shiftParticle Δ (u i))
          (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q))) hc.symm
    have hb' : ∀ u : Fin k → Particle 𝒢 g,
        (∏ i, μ (u i).1) / (k.factorial : ℝ) * ρ ^ l38_anchCount Δ (List.ofFn u) *
            Ψ' (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)) =
          ρ⁻¹ ^ b * ((∏ i, μ (u i).1) *
            F (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)) /
              (k.factorial : ℝ)) := by
      intro u
      rw [hFdef, l38_anchCount_join, l38_rho_split hρ0 (l38_anchCount Δ (List.ofFn u)) b]
      ring
    rw [ha, Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => hb' u
  -- the stored labels are anchored particles
  have h2 : ∀ u : Fin k → Particle 𝒢 g,
      ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) * ((∏ i, μ (u i).1) *
          F (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q))) ≤
        ∑ p : Fin b → Particle 𝒢 g,
          (∏ i, μ (u i).1) * (∏ h, μ (p h).1) * F (Graph.memoryJoin u p) *
            l38_anchInd Δ p := by
    intro u
    refine (l38_anchor_sum_le μ hμ Δ
      (fun p => (∏ i, μ (u i).1) * F (Graph.memoryJoin u p))
      (fun p => mul_nonneg (Finset.prod_nonneg fun i _ => hμ _) (hF0 _))).trans
      (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
    show (∏ h, μ (p h).1) * ((∏ i, μ (u i).1) * F (Graph.memoryJoin u p)) *
      l38_anchInd Δ p = _
    ring
  -- the factorial reversal
  have h3 : (∑ u : Fin k → Particle 𝒢 g, ∑ p : Fin b → Particle 𝒢 g,
        (∏ i, μ (u i).1) * (∏ h, μ (p h).1) * F (Graph.memoryJoin u p) *
          l38_anchInd Δ p) / (k.factorial : ℝ) =
      (∑ e : Fin b ↪ Fin (k + b), ∑ x : Fin (k + b) → Particle 𝒢 g,
        (∏ i, μ (x i).1) * F x * l38_anchInd Δ (fun h => x (e h))) /
          ((k + b).factorial : ℝ) :=
    (Graph.ordered_retrieval_joint_sum (fun z : Particle 𝒢 g => μ z.1) F hFsym
      (l38_anchInd Δ)).symm
  -- the number of retrievals and the damping
  have h4 : ∀ x : Fin (k + b) → Particle 𝒢 g,
      ∑ e : Fin b ↪ Fin (k + b), (∏ i, μ (x i).1) * F x * l38_anchInd Δ (fun h => x (e h)) ≤
        (∏ i, μ (x i).1) * (Schur.countSup T ρ * Ψ' x) := by
    intro x
    have hP : 0 ≤ ∏ i, μ (x i).1 := Finset.prod_nonneg fun i _ => hμ _
    have he : ∑ e : Fin b ↪ Fin (k + b), l38_anchInd Δ (fun h => x (e h)) ≤
        ((l38_anchCount Δ (List.ofFn x) : ℕ) : ℝ) ^ b := l38_sum_anchInd_le Δ x
    have hc : ρ ^ l38_anchCount Δ (List.ofFn x) *
        ((l38_anchCount Δ (List.ofFn x) : ℕ) : ℝ) ^ b ≤ Schur.countSup T ρ :=
      l38_count_scalar hρ0 hρ1 hT hb _
    calc ∑ e : Fin b ↪ Fin (k + b), (∏ i, μ (x i).1) * F x * l38_anchInd Δ (fun h => x (e h))
        = (∏ i, μ (x i).1) * F x *
            ∑ e : Fin b ↪ Fin (k + b), l38_anchInd Δ (fun h => x (e h)) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (∏ i, μ (x i).1) * F x * ((l38_anchCount Δ (List.ofFn x) : ℕ) : ℝ) ^ b :=
          mul_le_mul_of_nonneg_left he (mul_nonneg hP (hF0 x))
      _ = (∏ i, μ (x i).1) * ((ρ ^ l38_anchCount Δ (List.ofFn x) *
            ((l38_anchCount Δ (List.ofFn x) : ℕ) : ℝ) ^ b) * Ψ' x) := by
          rw [hFdef]
          ring
      _ ≤ (∏ i, μ (x i).1) * (Schur.countSup T ρ * Ψ' x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (hΨ0 x)) hP
  have e1 : ∑ u : Fin k → Particle 𝒢 g, ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g},
        (∏ h, μ (q h)) * ((∏ i, μ (u i).1) *
          F (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q))) =
      ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Fin k → Particle 𝒢 g, (∏ i, μ (u i).1) *
          F (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => (Finset.mul_sum _ _ _).symm
  calc ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Fin k → Particle 𝒢 g, (∏ i, μ (u i).1) / (k.factorial : ℝ) *
          ρ ^ (List.ofFn u).countP (fun pr => decide (pr.2 = 0)) *
          Ψ' (Graph.memoryJoin (fun i => shiftParticle Δ (u i))
            (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q))
      = ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
          (ρ⁻¹ ^ b * ((∑ u : Fin k → Particle 𝒢 g, (∏ i, μ (u i).1) *
            F (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q))) /
              (k.factorial : ℝ))) :=
        Finset.sum_congr rfl fun q _ => congrArg (fun t => (∏ h, μ (q h)) * t) (h1 q)
    _ = ρ⁻¹ ^ b * ((∑ u : Fin k → Particle 𝒢 g, ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g},
          (∏ h, μ (q h)) * ((∏ i, μ (u i).1) *
            F (Graph.memoryJoin u (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)))) /
              (k.factorial : ℝ)) := by
        rw [e1, Finset.sum_div, Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ ρ⁻¹ ^ b * ((∑ u : Fin k → Particle 𝒢 g, ∑ p : Fin b → Particle 𝒢 g,
          (∏ i, μ (u i).1) * (∏ h, μ (p h).1) * F (Graph.memoryJoin u p) *
            l38_anchInd Δ p) / (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (Finset.sum_le_sum fun u _ => h2 u) hK) hr0
    _ = ρ⁻¹ ^ b * ((∑ e : Fin b ↪ Fin (k + b), ∑ x : Fin (k + b) → Particle 𝒢 g,
          (∏ i, μ (x i).1) * F x * l38_anchInd Δ (fun h => x (e h))) /
            ((k + b).factorial : ℝ)) := by rw [h3]
    _ ≤ ρ⁻¹ ^ b * ((∑ x : Fin (k + b) → Particle 𝒢 g,
          (∏ i, μ (x i).1) * (Schur.countSup T ρ * Ψ' x)) / ((k + b).factorial : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hKb) hr0
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun x _ => h4 x
    _ = ρ⁻¹ ^ b * Schur.countSup T ρ *
          ∑ x : Fin (k + b) → Particle 𝒢 g,
            (∏ i, μ (x i).1) / ((k + b).factorial : ℝ) * Ψ' x := by
        rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring

/-! ### All sizes, with the truncation -/

/-- The reversal of the stores for memories of survivors of one size `n` with `n + b ≤ Bc`. -/
theorem edgeAbs_insert_size (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (hμ : ∀ p, 0 ≤ μ p) {v ρ : ℝ}
    (hv : 1 ≤ v) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (Δ : ℤ) {T : ℕ} (hT : 0 < T) (b : ℕ) (hb : b ≤ T)
    (Ψ : Mem 𝒢 Bc g → ℝ) (hΨ0 : ∀ u, 0 ≤ Ψ u)
    (hΨ : ∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      Ψ ⟨m, y ∘ σ⟩ = Ψ ⟨m, y⟩) (n : Fin (Bc + 1)) (hn : n.val + b ≤ Bc) :
    ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Fin n.val → Particle 𝒢 g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1)
              (⟨n, u⟩ : Mem 𝒢 Bc g) * v ^ n.val *
            ρ ^ memZeroCount (⟨n, u⟩ : Mem 𝒢 Bc g) *
            Ψ (memOfList ((List.ofFn u).map (shiftParticle Δ) ++
              List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g))) ≤
      ρ⁻¹ ^ b * Schur.countSup T ρ *
        ∑ x : Fin (n.val + b) → Particle 𝒢 g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1)
              (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ : Mem 𝒢 Bc g) * v ^ (n.val + b) *
            Ψ ⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hc0 : 0 ≤ ρ⁻¹ ^ b * Schur.countSup T ρ :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hρ0.le) b) (l38_countSup_nonneg T hρ0 hρ1)
  have hvn : v ^ n.val ≤ v ^ (n.val + b) := pow_le_pow_right₀ hv (Nat.le_add_right _ _)
  have hD := edgeAbs_insert_fixed μ hμ hρ0 hρ1 Δ hT n.val b hb
    (fun x : Fin (n.val + b) → Particle 𝒢 g =>
      Ψ (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ : Mem 𝒢 Bc g))
    (fun x => hΨ0 _) (fun σ x => hΨ ⟨n.val + b, Nat.lt_succ_of_le hn⟩ σ x)
  have hL : ∀ (q : Fin b → {p : ℕ // p ∈ 𝒢.big g}) (u : Fin n.val → Particle 𝒢 g),
      List.ofFn (Graph.memoryJoin (fun i => shiftParticle Δ (u i))
          (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)) =
        (List.ofFn u).map (shiftParticle Δ) ++
          List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g) := by
    intro q u
    have ha : (fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g)) =
        Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q := funext fun h => l38_shift_zero Δ (q h)
    rw [ofFn_memoryJoin, ha]
    exact congrArg (fun l => l ++ List.ofFn (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q))
      (List.map_ofFn (f := u) (g := shiftParticle Δ)).symm
  have hterm : ∀ (q : Fin b → {p : ℕ // p ∈ 𝒢.big g}) (u : Fin n.val → Particle 𝒢 g),
      Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) (⟨n, u⟩ : Mem 𝒢 Bc g) *
          v ^ n.val * ρ ^ memZeroCount (⟨n, u⟩ : Mem 𝒢 Bc g) *
          Ψ (memOfList ((List.ofFn u).map (shiftParticle Δ) ++
            List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g))) =
        v ^ n.val * ((∏ i, μ (u i).1) / (n.val.factorial : ℝ) *
          ρ ^ (List.ofFn u).countP (fun pr => decide (pr.2 = 0)) *
          Ψ (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩,
            Graph.memoryJoin (fun i => shiftParticle Δ (u i))
              (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)⟩ : Mem 𝒢 Bc g)) := by
    intro q u
    have hpm : Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1)
        (⟨n, u⟩ : Mem 𝒢 Bc g) = (∏ i, μ (u i).1) / (n.val.factorial : ℝ) := rfl
    have hz : memZeroCount (⟨n, u⟩ : Mem 𝒢 Bc g) =
        (List.ofFn u).countP (fun pr => decide (pr.2 = 0)) := l38_memZeroCount_eq _
    have hΨm : Ψ (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩,
          Graph.memoryJoin (fun i => shiftParticle Δ (u i))
            (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)⟩ : Mem 𝒢 Bc g) =
        Ψ (memOfList ((List.ofFn u).map (shiftParticle Δ) ++
          List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g))) := by
      rw [← hL q u]
      exact H_mk_eq Ψ _ _
    rw [hpm, hz, hΨm]
    ring
  calc ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Fin n.val → Particle 𝒢 g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1)
              (⟨n, u⟩ : Mem 𝒢 Bc g) * v ^ n.val *
            ρ ^ memZeroCount (⟨n, u⟩ : Mem 𝒢 Bc g) *
            Ψ (memOfList ((List.ofFn u).map (shiftParticle Δ) ++
              List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g)))
      = v ^ n.val * ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
          ∑ u : Fin n.val → Particle 𝒢 g, (∏ i, μ (u i).1) / (n.val.factorial : ℝ) *
            ρ ^ (List.ofFn u).countP (fun pr => decide (pr.2 = 0)) *
            Ψ (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩,
              Graph.memoryJoin (fun i => shiftParticle Δ (u i))
                (Graph.anchoredMemory (l38_anchor 𝒢 g Δ) q)⟩ : Mem 𝒢 Bc g) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_congr rfl fun u _ => hterm q u, ← Finset.mul_sum]
        ring
    _ ≤ v ^ n.val * (ρ⁻¹ ^ b * Schur.countSup T ρ *
          ∑ x : Fin (n.val + b) → Particle 𝒢 g,
            (∏ i, μ (x i).1) / ((n.val + b).factorial : ℝ) *
              Ψ (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ : Mem 𝒢 Bc g)) :=
        mul_le_mul_of_nonneg_left hD (pow_nonneg hv0 _)
    _ = ρ⁻¹ ^ b * Schur.countSup T ρ *
          ∑ x : Fin (n.val + b) → Particle 𝒢 g,
            v ^ n.val * ((∏ i, μ (x i).1) / ((n.val + b).factorial : ℝ) *
              Ψ (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ : Mem 𝒢 Bc g)) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ ρ⁻¹ ^ b * Schur.countSup T ρ *
          ∑ x : Fin (n.val + b) → Particle 𝒢 g,
            Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1)
                (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ : Mem 𝒢 Bc g) * v ^ (n.val + b) *
              Ψ ⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) hc0
        have hA0 : 0 ≤ (∏ i, μ (x i).1) / ((n.val + b).factorial : ℝ) :=
          div_nonneg (Finset.prod_nonneg fun i _ => hμ _) (Nat.cast_nonneg _)
        have hpm : Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1)
            (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ : Mem 𝒢 Bc g) =
              (∏ i, μ (x i).1) / ((n.val + b).factorial : ℝ) := rfl
        rw [hpm]
        calc v ^ n.val * ((∏ i, μ (x i).1) / ((n.val + b).factorial : ℝ) *
              Ψ (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ : Mem 𝒢 Bc g))
            = (∏ i, μ (x i).1) / ((n.val + b).factorial : ℝ) *
                Ψ (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ : Mem 𝒢 Bc g) * v ^ n.val := by
              ring
          _ ≤ (∏ i, μ (x i).1) / ((n.val + b).factorial : ℝ) *
                Ψ (⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ : Mem 𝒢 Bc g) * v ^ (n.val + b) :=
              mul_le_mul_of_nonneg_left hvn (mul_nonneg hA0 (hΨ0 _))
          _ = (∏ i, μ (x i).1) / ((n.val + b).factorial : ℝ) * v ^ (n.val + b) *
                Ψ ⟨⟨n.val + b, Nat.lt_succ_of_le hn⟩, x⟩ := by ring

/-- **The reversal of the stores for `b` stored labels**, summed over the sizes of the memories
of survivors, with the truncation of the new memory: the integral over the stored labels `q` and
the memories `u` of survivors of a symmetric nonnegative function of the new memory
`T_Δ u ⊔ ((q_h, Δ))_h` is at most `ρ^{-b} sup_z (z+T)^T ρ^z` times its integral against
`λ^{⊗j}/j! · v^j`. -/
theorem edgeAbs_insert_tuple (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (hμ : ∀ p, 0 ≤ μ p) {v ρ : ℝ}
    (hv : 1 ≤ v) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (Δ : ℤ) {T : ℕ} (hT : 0 < T) (b : ℕ) (hb : b ≤ T)
    (Ψ : Mem 𝒢 Bc g → ℝ) (hΨ0 : ∀ u, 0 ≤ Ψ u)
    (hΨ : ∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      Ψ ⟨m, y ∘ σ⟩ = Ψ ⟨m, y⟩) :
    ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            ρ ^ memZeroCount u *
            (if u.1.val + b ≤ Bc then
              Ψ (memOfList ((List.ofFn u.2).map (shiftParticle Δ) ++
                List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g)))
            else 0) ≤
      ρ⁻¹ ^ b * Schur.countSup T ρ *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            Ψ u := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hc0 : 0 ≤ ρ⁻¹ ^ b * Schur.countSup T ρ :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hρ0.le) b) (l38_countSup_nonneg T hρ0 hρ1)
  -- the integrals over the memories of one size
  obtain ⟨R, hR, hR0⟩ : ∃ R : ℕ → ℝ,
      (∀ (j : ℕ) (h : j ≤ Bc), R j = ∑ x : Fin j → Particle 𝒢 g,
        Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1)
            (⟨⟨j, Nat.lt_succ_of_le h⟩, x⟩ : Mem 𝒢 Bc g) * v ^ j *
          Ψ ⟨⟨j, Nat.lt_succ_of_le h⟩, x⟩) ∧ ∀ j, 0 ≤ R j := by
    refine ⟨fun j => if h : j ≤ Bc then ∑ x : Fin j → Particle 𝒢 g,
        Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1)
            (⟨⟨j, Nat.lt_succ_of_le h⟩, x⟩ : Mem 𝒢 Bc g) * v ^ j *
          Ψ ⟨⟨j, Nat.lt_succ_of_le h⟩, x⟩ else 0, fun j h => dif_pos h, fun j => ?_⟩
    by_cases h : j ≤ Bc
    · refine le_of_le_of_eq ?_ (dif_pos h).symm
      exact Finset.sum_nonneg fun x _ =>
        mul_nonneg (mul_nonneg (l38_pointMass_nonneg hμ _) (pow_nonneg hv0 _)) (hΨ0 _)
    · show (0 : ℝ) ≤ dite (j ≤ Bc) _ _
      rw [dif_neg h]
  obtain ⟨tm, htm⟩ : ∃ tm : (Fin b → {p : ℕ // p ∈ 𝒢.big g}) → Mem 𝒢 Bc g → ℝ, ∀ q u,
      tm q u = Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
        ρ ^ memZeroCount u *
        (if u.1.val + b ≤ Bc then
          Ψ (memOfList ((List.ofFn u.2).map (shiftParticle Δ) ++
            List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g)))
        else 0) := ⟨_, fun _ _ => rfl⟩
  -- one size
  have hsize : ∀ n : Fin (Bc + 1),
      ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
          ∑ u : Fin n.val → Particle 𝒢 g, tm q ⟨n, u⟩ ≤
        ρ⁻¹ ^ b * Schur.countSup T ρ * (if n.val + b ≤ Bc then R (n.val + b) else 0) := by
    intro n
    by_cases hn : n.val + b ≤ Bc
    · rw [if_pos hn, hR (n.val + b) hn]
      refine (le_of_eq (Finset.sum_congr rfl fun q _ =>
        congrArg (fun t => (∏ h, μ (q h)) * t) (Finset.sum_congr rfl fun u _ => ?_))).trans
        (edgeAbs_insert_size μ hμ hv hρ0 hρ1 Δ hT b hb Ψ hΨ0 hΨ n hn)
      rw [htm]
      exact congrArg (fun t =>
        Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) (⟨n, u⟩ : Mem 𝒢 Bc g) *
          v ^ n.val * ρ ^ memZeroCount (⟨n, u⟩ : Mem 𝒢 Bc g) * t) (if_pos hn)
    · rw [if_neg hn, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero fun q _ => ?_)
      have hz : ∑ u : Fin n.val → Particle 𝒢 g, tm q ⟨n, u⟩ = 0 :=
        Finset.sum_eq_zero fun u _ => by
          rw [htm]
          exact mul_eq_zero_of_right _ (if_neg hn)
      rw [hz, mul_zero]
  have hLHS : ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            ρ ^ memZeroCount u *
            (if u.1.val + b ≤ Bc then
              Ψ (memOfList ((List.ofFn u.2).map (shiftParticle Δ) ++
                List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g)))
            else 0) =
      ∑ n : Fin (Bc + 1), ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Fin n.val → Particle 𝒢 g, tm q ⟨n, u⟩ := by
    have h1 : ∀ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            ρ ^ memZeroCount u *
            (if u.1.val + b ≤ Bc then
              Ψ (memOfList ((List.ofFn u.2).map (shiftParticle Δ) ++
                List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g)))
            else 0) =
        ∑ n : Fin (Bc + 1), (∏ h, μ (q h)) *
          ∑ u : Fin n.val → Particle 𝒢 g, tm q ⟨n, u⟩ := by
      intro q
      have h2 : ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            ρ ^ memZeroCount u *
            (if u.1.val + b ≤ Bc then
              Ψ (memOfList ((List.ofFn u.2).map (shiftParticle Δ) ++
                List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g)))
            else 0) =
          ∑ n : Fin (Bc + 1), ∑ u : Fin n.val → Particle 𝒢 g, tm q ⟨n, u⟩ :=
        (Finset.sum_congr rfl fun u _ => (htm q u).symm).trans
          (Fintype.sum_sigma fun u : Mem 𝒢 Bc g => tm q u)
      rw [h2, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun q _ => h1 q]
    exact Finset.sum_comm
  have hRHS : ∑ u : Mem 𝒢 Bc g,
        Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val * Ψ u =
      ∑ j : Fin (Bc + 1), R j.val :=
    (Fintype.sum_sigma fun u : Mem 𝒢 Bc g =>
      Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
        Ψ u).trans
      (Finset.sum_congr rfl fun j _ => (hR j.val (Nat.le_of_lt_succ j.isLt)).symm)
  rw [hLHS, hRHS]
  calc ∑ n : Fin (Bc + 1), ∑ q : Fin b → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) *
        ∑ u : Fin n.val → Particle 𝒢 g, tm q ⟨n, u⟩
      ≤ ∑ n : Fin (Bc + 1),
          ρ⁻¹ ^ b * Schur.countSup T ρ * (if n.val + b ≤ Bc then R (n.val + b) else 0) :=
        Finset.sum_le_sum fun n _ => hsize n
    _ = ρ⁻¹ ^ b * Schur.countSup T ρ *
          ∑ n : Fin (Bc + 1), (if n.val + b ≤ Bc then R (n.val + b) else 0) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ρ⁻¹ ^ b * Schur.countSup T ρ * ∑ j : Fin (Bc + 1), R j.val :=
        mul_le_mul_of_nonneg_left (l38_sum_shift_le R hR0 Bc b) hc0

/-! ### The integral over the source labels -/

open _root_.Classical in
/-- **The weight of a source label of a big group, given the target labels `τ`**: `μ̃_g` in an
unshared slot (eq:memory-hilbert-space), and in a shared slot the label is the label of the
target ("shared particles remain active", [S-02:0491]). -/
def edgeAbsSrcW (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (Cg : Finset (Fin J))
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (sl : Slot J ℓ) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  if Unshared Cg sl then μ p else (if p = τ sl then 1 else 0)

theorem edgeAbsSrcW_of_unshared (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) {Cg : Finset (Fin J)}
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) {sl : Slot J ℓ} (h : Unshared Cg sl)
    (p : {p : ℕ // p ∈ 𝒢.big g}) : edgeAbsSrcW μ Cg τ sl p = μ p := by
  unfold edgeAbsSrcW
  exact if_pos h

theorem edgeAbsSrcW_of_shared (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) {Cg : Finset (Fin J)}
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) {sl : Slot J ℓ} (h : ¬Unshared Cg sl)
    (p : {p : ℕ // p ∈ 𝒢.big g}) {hd : Decidable (p = τ sl)} :
    edgeAbsSrcW μ Cg τ sl p = @ite ℝ (p = τ sl) hd 1 0 := by
  unfold edgeAbsSrcW
  exact (if_neg h).trans (ite_congr_of_iff Iff.rfl rfl rfl)

theorem edgeAbsSrcW_nonneg {μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ} (hμ : ∀ p, 0 ≤ μ p)
    (Cg : Finset (Fin J)) (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (sl : Slot J ℓ)
    (p : {p : ℕ // p ∈ 𝒢.big g}) : 0 ≤ edgeAbsSrcW μ Cg τ sl p := by
  unfold edgeAbsSrcW
  split_ifs
  · exact hμ p
  · exact zero_le_one
  · exact le_rfl

/-- In a shared slot the source labels have total weight one. -/
theorem sum_edgeAbsSrcW_shared (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) {Cg : Finset (Fin J)}
    (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) {sl : Slot J ℓ} (h : ¬Unshared Cg sl) :
    ∑ p, edgeAbsSrcW μ Cg τ sl p = 1 := by
  classical
  have e : ∀ p : {p : ℕ // p ∈ 𝒢.big g},
      edgeAbsSrcW μ Cg τ sl p = if p = τ sl then (1 : ℝ) else 0 :=
    fun p => edgeAbsSrcW_of_shared μ τ h p
  rw [Finset.sum_congr rfl fun p _ => e p]
  exact (Finset.sum_eq_single_of_mem
    (f := fun p : {p : ℕ // p ∈ 𝒢.big g} => if p = τ sl then (1 : ℝ) else 0) (τ sl)
    (Finset.mem_univ _) (fun p _ hp => if_neg hp)).trans (if_pos rfl)

/-- **The insertion step** [S-02:0704–0748, 0788–0792]: for a set `st` of stored unshared slots,
the integral over the source labels `ξ` (weights `edgeAbsSrcW`) and over the memories `u` of
survivors, with the source damping `ρ^{#zeros(u)}`, of a symmetric nonnegative function `Ψ` of the
new memory `T_Δ u ⊔ ((ξ_{sl}, Δ))_{sl ∈ st}` (truncated at `Bc`), is at most
`max(1, μ̃_g(𝒫_g))^T ρ^{-T} sup_z (z+T)^T ρ^z` times the integral of `Ψ` against
`λ^{⊗j}/j! · v^j`. -/
theorem edgeAbs_insert_le (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    {v ρ Mmax : ℝ} (hv : 1 ≤ v) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hM : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, μ p ≤ Mmax) (Cg : Finset (Fin J)) {T : ℕ}
    (hT : 0 < T) (hC : ℓ + Cg.card ≤ T) (Δ : ℤ) (τ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (st : Finset (Slot J ℓ)) (hst : ∀ sl ∈ st, Unshared Cg sl) (Ψ : Mem 𝒢 Bc g → ℝ)
    (hΨ0 : ∀ u, 0 ≤ Ψ u)
    (hΨ : ∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      Ψ ⟨m, y ∘ σ⟩ = Ψ ⟨m, y⟩) :
    ∑ ξ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}, (∏ sl, edgeAbsSrcW μ Cg τ sl (ξ sl)) *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            ρ ^ memZeroCount u *
            (if u.1.val + st.card ≤ Bc then
              Ψ (memOfList ((List.ofFn u.2).map (shiftParticle Δ) ++ edgeAbsStored Δ ξ st))
            else 0) ≤
      (max 1 Mmax) ^ T * (ρ⁻¹ ^ T * Schur.countSup T ρ) *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            Ψ u := by
  classical
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hcs : 0 ≤ Schur.countSup T ρ := l38_countSup_nonneg T hρ0 hρ1
  have hri : (1 : ℝ) ≤ ρ⁻¹ := (one_le_inv₀ hρ0).mpr hρ1.le
  have hM1 : (1 : ℝ) ≤ max 1 Mmax := le_max_left _ _
  have hR0 : 0 ≤ ∑ u : Mem 𝒢 Bc g,
      Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val * Ψ u :=
    Finset.sum_nonneg fun u _ =>
      mul_nonneg (mul_nonneg (l38_pointMass_nonneg hμ u) (pow_nonneg hv0 _)) (hΨ0 u)
  -- the stored slots in their canonical order
  obtain ⟨ls, hls⟩ : ∃ ls : List (Slot J ℓ),
      ls = (slotList J ℓ).filter fun sl => decide (sl ∈ st) := ⟨_, rfl⟩
  have hnd : ls.Nodup := by
    rw [hls]
    exact (l38_slotList_nodup J ℓ).filter _
  have hlen : ls.length = st.card := by
    rw [hls]
    exact l38_length_filter_slotList st
  have hmem : ∀ sl ∈ ls, sl ∈ st := by
    intro sl hsl
    rw [hls] at hsl
    exact of_decide_eq_true (List.mem_filter.mp hsl).2
  have hbT : ls.length ≤ T := by
    rw [hlen]
    have hsub : st ⊆ Finset.univ.filter fun sl : Slot J ℓ => Unshared Cg sl := fun sl hsl =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ sl, hst sl hsl⟩
    exact (Finset.card_le_card hsub).trans ((l38_card_unshared Cg).le.trans hC)
  have hstored : ∀ ξ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}, edgeAbsStored Δ ξ st =
      List.ofFn (fun h : Fin ls.length =>
        shiftParticle Δ (⟨ξ (ls.get h), 0⟩ : Particle 𝒢 g)) := by
    intro ξ
    have e : edgeAbsStored Δ ξ st =
        ls.map (fun sl => shiftParticle Δ (⟨ξ sl, 0⟩ : Particle 𝒢 g)) := by
      subst hls
      rfl
    rw [e]
    exact l38_map_eq_ofFn _ ls
  -- the function of the stored labels
  obtain ⟨H, hH⟩ : ∃ H : (Fin ls.length → {p : ℕ // p ∈ 𝒢.big g}) → ℝ, ∀ q, H q =
      ∑ u : Mem 𝒢 Bc g,
        Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
          ρ ^ memZeroCount u *
          (if u.1.val + ls.length ≤ Bc then
            Ψ (memOfList ((List.ofFn u.2).map (shiftParticle Δ) ++
              List.ofFn fun h => shiftParticle Δ (⟨q h, 0⟩ : Particle 𝒢 g)))
          else 0) := ⟨_, fun _ => rfl⟩
  have hH0 : ∀ q, 0 ≤ H q := by
    intro q
    rw [hH]
    refine Finset.sum_nonneg fun u _ => mul_nonneg (mul_nonneg (mul_nonneg
      (l38_pointMass_nonneg hμ u) (pow_nonneg hv0 _)) (pow_nonneg hρ0.le _)) ?_
    split_ifs
    · exact hΨ0 _
    · exact le_rfl
  have hL : ∀ ξ : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g},
      (∏ sl, edgeAbsSrcW μ Cg τ sl (ξ sl)) *
          ∑ u : Mem 𝒢 Bc g,
            Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
              ρ ^ memZeroCount u *
              (if u.1.val + st.card ≤ Bc then
                Ψ (memOfList ((List.ofFn u.2).map (shiftParticle Δ) ++
                  edgeAbsStored Δ ξ st))
              else 0) =
        (∏ sl, edgeAbsSrcW μ Cg τ sl (ξ sl)) * H (fun h => ξ (ls.get h)) := by
    intro ξ
    rw [hH, hstored ξ, ← hlen]
  have hmarg := l38_marginal ls hnd
    (fun (sl : Slot J ℓ) (p : {p : ℕ // p ∈ 𝒢.big g}) => edgeAbsSrcW μ Cg τ sl p) H
  -- the labels which are not stored
  obtain ⟨gM, hgM⟩ : ∃ gM : Slot J ℓ → ℝ,
      ∀ sl, gM sl = if Unshared Cg sl then max 1 Mmax else 1 := ⟨_, fun _ => rfl⟩
  have hg1 : ∀ sl, 1 ≤ gM sl := by
    intro sl
    rw [hgM]
    split_ifs
    · exact hM1
    · exact le_rfl
  have hωg : ∀ sl, ∑ p, edgeAbsSrcW μ Cg τ sl p ≤ gM sl := by
    intro sl
    rw [hgM]
    by_cases hU : Unshared Cg sl
    · rw [if_pos hU, Finset.sum_congr rfl fun p _ => edgeAbsSrcW_of_unshared μ τ hU p]
      exact hM.trans (le_max_right _ _)
    · rw [if_neg hU, sum_edgeAbsSrcW_shared μ τ hU]
  have hprodg : ∏ sl, gM sl ≤ (max 1 Mmax) ^ T := by
    have e : ∏ sl, gM sl =
        (max 1 Mmax) ^ (Finset.univ.filter fun sl : Slot J ℓ => Unshared Cg sl).card :=
      (Finset.prod_congr rfl fun sl _ => hgM sl).trans
        (l38_prod_ite_const (fun sl : Slot J ℓ => Unshared Cg sl) (max 1 Mmax))
    rw [e, l38_card_unshared Cg]
    exact pow_le_pow_right₀ hM1 hC
  have hq0 : 0 ≤ ∑ q : Fin ls.length → {p : ℕ // p ∈ 𝒢.big g},
      (∏ h, edgeAbsSrcW μ Cg τ (ls.get h) (q h)) * H q :=
    Finset.sum_nonneg fun q _ =>
      mul_nonneg (Finset.prod_nonneg fun h _ => edgeAbsSrcW_nonneg hμ Cg τ _ _) (hH0 q)
  have hqμ : ∑ q : Fin ls.length → {p : ℕ // p ∈ 𝒢.big g},
        (∏ h, edgeAbsSrcW μ Cg τ (ls.get h) (q h)) * H q =
      ∑ q : Fin ls.length → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) * H q := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.prod_congr rfl fun h _ =>
      edgeAbsSrcW_of_unshared μ τ (hst _ (hmem _ (List.get_mem ls h))) (q h)]
  have hE : ∑ q : Fin ls.length → {p : ℕ // p ∈ 𝒢.big g}, (∏ h, μ (q h)) * H q ≤
      ρ⁻¹ ^ ls.length * Schur.countSup T ρ *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            Ψ u :=
    (le_of_eq (Finset.sum_congr rfl fun q _ => by rw [hH])).trans
      (edgeAbs_insert_tuple μ hμ hv hρ0 hρ1 Δ hT ls.length hbT Ψ hΨ0 hΨ)
  refine (le_of_eq ((Finset.sum_congr rfl fun ξ _ => hL ξ).trans hmarg)).trans ?_
  refine (mul_le_mul_of_nonneg_right
    (l38_prod_compl_le (fun i : Slot J ℓ => i ∈ ls)
      (fun i => ∑ a, edgeAbsSrcW μ Cg τ i a) gM
      (fun i => Finset.sum_nonneg fun a _ => edgeAbsSrcW_nonneg hμ Cg τ i a) hωg hg1)
    hq0).trans ?_
  refine (mul_le_mul hprodg ((le_of_eq hqμ).trans hE) hq0
    (pow_nonneg (zero_le_one.trans hM1) T)).trans ?_
  have hpow : ρ⁻¹ ^ ls.length ≤ ρ⁻¹ ^ T := pow_le_pow_right₀ hri hbT
  calc (max 1 Mmax) ^ T * (ρ⁻¹ ^ ls.length * Schur.countSup T ρ *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            Ψ u)
      ≤ (max 1 Mmax) ^ T * (ρ⁻¹ ^ T * Schur.countSup T ρ *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            Ψ u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hcs) hR0)
          (pow_nonneg (zero_le_one.trans hM1) T)
    _ = (max 1 Mmax) ^ T * (ρ⁻¹ ^ T * Schur.countSup T ρ) *
        ∑ u : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) u * v ^ u.1.val *
            Ψ u := by ring

end OneGroup

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
