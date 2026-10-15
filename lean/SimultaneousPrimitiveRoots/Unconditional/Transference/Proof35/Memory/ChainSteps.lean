module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.Statements
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The values of one prime after one edge and one visit operation

Source: `verification/stage7-sources/S-02.tex`, lines 456–514 (`[S-02:0456–0514]`).

Tools for the proof of (M4) `ChainLifespan` (`Memory/ChainLifespanProof.lean`): the values
`Skel.edgeStepVals` and `ghostStepVals` of one big prime `p` of the group `g`, in each of the
cases which the definitions distinguish, without any `if`:

* `chnPow ρ c` — the factor `ρ^{1_c}` (an `if` with a classical instance), `chn_pow_ite`;
* `ghostStepVals_act`, `ghostStepVals_pend_zero`, `ghostStepVals_pend_ne`, `ghostStepVals_dead`,
  `ghostStepVals_unborn` — the visit operation (eq:ghost-row);
* `Skel.edgeStepVals_act_shared`, `…_act_shared_ne`, `…_act_unshared`, `…_act_unshared_ne` — an
  active prime: shared, stored or dropped;
* `Skel.edgeStepVals_pend_zero`, `…_pend_promo`, `…_pend_none` — a pending particle: it stays
  pending, it is promoted, or there is no admissible transition;
* `Skel.edgeStepVals_dead_zero`, `…_dead_ne`, `Skel.edgeStepVals_unborn_zero`, `…_unborn_one`,
  `…_unborn_big` — a dead and an unborn prime.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### The factor `ρ^{1_c}` -/

open _root_.Classical in
/-- `ρ` if `c` holds and `1` otherwise: the factor `ρ^{1_c}` of a pending zero. -/
def chnPow (ρ : ℝ) (c : Prop) : ℝ := if c then ρ else 1

theorem chnPow_pos {ρ : ℝ} {c : Prop} (hc : c) : chnPow ρ c = ρ := if_pos hc

theorem chnPow_neg {ρ : ℝ} {c : Prop} (hc : ¬c) : chnPow ρ c = 1 := if_neg hc

/-- `ρ ^ (if c then 1 else 0) = chnPow ρ c`, for every decidability instance. -/
theorem chn_pow_ite (ρ : ℝ) {c : Prop} {inst : Decidable c} :
    ρ ^ (@ite ℕ c inst 1 0) = chnPow ρ c := by
  by_cases hc : c
  · rw [if_pos hc, pow_one, chnPow_pos hc]
  · rw [if_neg hc, pow_zero, chnPow_neg hc]

theorem chnPow_ne_zero {ρ : ℝ} (hρ : ρ ≠ 0) (c : Prop) : chnPow ρ c ≠ 0 := by
  by_cases hc : c
  · rw [chnPow_pos hc]
    exact hρ
  · rw [chnPow_neg hc]
    exact one_ne_zero

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {D : MemData 𝒢 J ℓ N}

/-! ### Translation of a particle -/

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem shiftParticle_mk (Δ : ℤ) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (r : Res p.1) :
    shiftParticle Δ (⟨p, r⟩ : Particle 𝒢 g) = ⟨p, (Δ : Res p.1) + r⟩ := rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem shiftParticle_snd (Δ : ℤ) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) (r : Res p.1) :
    (shiftParticle Δ (⟨p, r⟩ : Particle 𝒢 g)).2 = (Δ : Res p.1) + r := rfl

/-! ### The final values -/

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem finalVals_act (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) : (finalVals 𝒢).act g p = 1 := rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem finalVals_pend (g : B) (z : Particle 𝒢 g) : (finalVals 𝒢).pend g z = 0 := rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem finalVals_dead (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) : (finalVals 𝒢).dead g p = 1 := rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem finalVals_unborn (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    (finalVals 𝒢).unborn g p = 1 := rfl

/-! ### The visit operation -/

section Ghost

variable (D) (i : ℕ) (v : PrimeVals 𝒢) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g})

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem ghostStepVals_act : (ghostStepVals D i v).act g p = v.act g p := rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem ghostStepVals_dead : (ghostStepVals D i v).dead g p = v.dead g p := rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem ghostStepVals_unborn :
    (ghostStepVals D i v).unborn g p =
      v.unborn g p +
        Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ D.q D.n i) D.ρ *
          tiltLaw (𝒢.big g) D.q D.n p * v.pend g ⟨p, 0⟩ := rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A pending zero terminates or continues. -/
theorem ghostStepVals_pend_of_eq (r : Res p.1) (hr : r = 0) :
    (ghostStepVals D i v).pend g ⟨p, r⟩ =
      Graph.sourceGhostD (visitQ D.q D.n i) D.ρ * v.dead g p +
        Graph.sourceGhostA (visitQ D.q D.n i) D.ρ * v.pend g ⟨p, r⟩ :=
  if_pos hr

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A pending zero terminates or continues. -/
theorem ghostStepVals_pend_zero :
    (ghostStepVals D i v).pend g ⟨p, 0⟩ =
      Graph.sourceGhostD (visitQ D.q D.n i) D.ρ * v.dead g p +
        Graph.sourceGhostA (visitQ D.q D.n i) D.ρ * v.pend g ⟨p, 0⟩ :=
  ghostStepVals_pend_of_eq D i v g p 0 rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A pending particle with nonzero residue is not touched. -/
theorem ghostStepVals_pend_ne (r : Res p.1) (hr : r ≠ 0) :
    (ghostStepVals D i v).pend g ⟨p, r⟩ = v.pend g ⟨p, r⟩ :=
  if_neg hr

end Ghost

/-! ### The edge operation -/

section Edge

variable (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g})

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- An active prime in a shared source slot stays active. -/
theorem Skel.edgeStepVals_act_shared
    (hS : ∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p)
    (he : sk.entryCount i g p = 0) :
    (sk.edgeStepVals i v).act g p = v.act g p :=
  (if_pos hS).trans (if_pos he)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A shared prime which also occurs in an unshared target slot: no transition. -/
theorem Skel.edgeStepVals_act_shared_ne
    (hS : ∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p)
    (he : sk.entryCount i g p ≠ 0) :
    (sk.edgeStepVals i v).act g p = 0 :=
  (if_pos hS).trans (if_neg he)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- An unshared active prime which occurs in an unshared target slot: no transition. -/
theorem Skel.edgeStepVals_act_unshared_ne
    (hS : ¬∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p)
    (he : sk.entryCount i g p ≠ 0) :
    (sk.edgeStepVals i v).act g p = 0 :=
  (if_neg hS).trans (if_neg he)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- An unshared active prime with `p ∤ D` and a nonzero step modulo `p` is stored or dropped. -/
theorem Skel.edgeStepVals_act_unshared
    (hS : ¬∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p)
    (he : sk.entryCount i g p = 0) (hdv : ¬((p : ℕ) ∣ sk.dilAt i))
    (hδ : ((sk.step i : ℤ) : Res p.1) ≠ 0) :
    (sk.edgeStepVals i v).act g p =
      v.pend g ⟨p, ((sk.step i : ℤ) : Res p.1)⟩ + v.dead g p := by
  have hδ' : ¬(shiftParticle (sk.step i) (⟨p, 0⟩ : Particle 𝒢 g)).2 = 0 := by
    intro h
    rw [shiftParticle_snd, add_zero] at h
    exact hδ h
  have hz : shiftParticle (sk.step i) (⟨p, 0⟩ : Particle 𝒢 g) =
      ⟨p, ((sk.step i : ℤ) : Res p.1)⟩ := by
    rw [shiftParticle_mk, add_zero]
  refine (if_neg hS).trans ((if_pos he).trans ?_)
  rw [if_neg hdv, if_neg hδ', pow_zero, one_mul, hz]

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A pending particle of a prime without entry stays pending, with the translated residue. -/
theorem Skel.edgeStepVals_pend_zero (r : Res p.1) (he : sk.entryCount i g p = 0) :
    (sk.edgeStepVals i v).pend g ⟨p, r⟩ =
      chnPow D.ρ (r = 0) * (chnPow D.ρ (((sk.step i : ℤ) : Res p.1) + r = 0) *
        v.pend g ⟨p, ((sk.step i : ℤ) : Res p.1) + r⟩) := by
  have h0 : (sk.edgeStepVals i v).pend g ⟨p, r⟩ = D.ρ ^ _ * (_ + _) := rfl
  have hc : ¬(sk.entryCount i g p = 1 ∧
      (shiftParticle (sk.step i) (⟨p, r⟩ : Particle 𝒢 g)).2 = 0 ∧
        ¬((p : ℕ) ∣ sk.dilAt i)) := fun h => one_ne_zero (h.1.symm.trans he)
  rw [h0]
  dsimp only
  rw [if_neg hc, if_pos he, zero_add]
  simp only [chn_pow_ite]
  rfl

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A pending particle whose translated residue is zero is promoted into the unique unshared
target slot with its label, if `p ∤ D`. -/
theorem Skel.edgeStepVals_pend_promo (r : Res p.1) (he : sk.entryCount i g p = 1)
    (hr : ((sk.step i : ℤ) : Res p.1) + r = 0) (hdv : ¬((p : ℕ) ∣ sk.dilAt i)) :
    (sk.edgeStepVals i v).pend g ⟨p, r⟩ =
      chnPow D.ρ (r = 0) * ((Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹ * v.act g p) := by
  have h0 : (sk.edgeStepVals i v).pend g ⟨p, r⟩ = D.ρ ^ _ * (_ + _) := rfl
  have hc : sk.entryCount i g p = 1 ∧
      (shiftParticle (sk.step i) (⟨p, r⟩ : Particle 𝒢 g)).2 = 0 ∧
        ¬((p : ℕ) ∣ sk.dilAt i) := ⟨he, hr, hdv⟩
  have hne : sk.entryCount i g p ≠ 0 := by
    rw [he]
    exact one_ne_zero
  rw [h0]
  dsimp only
  rw [if_pos hc, if_neg hne, add_zero, chn_pow_ite]

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A pending particle of a prime with an entry, which cannot be promoted: no transition. -/
theorem Skel.edgeStepVals_pend_none (r : Res p.1) (he : sk.entryCount i g p ≠ 0)
    (h : ¬(sk.entryCount i g p = 1 ∧ ((sk.step i : ℤ) : Res p.1) + r = 0 ∧
      ¬((p : ℕ) ∣ sk.dilAt i))) :
    (sk.edgeStepVals i v).pend g ⟨p, r⟩ = 0 := by
  have h0 : (sk.edgeStepVals i v).pend g ⟨p, r⟩ = D.ρ ^ _ * (_ + _) := rfl
  have hc : ¬(sk.entryCount i g p = 1 ∧
      (shiftParticle (sk.step i) (⟨p, r⟩ : Particle 𝒢 g)).2 = 0 ∧
        ¬((p : ℕ) ∣ sk.dilAt i)) := h
  rw [h0]
  dsimp only
  rw [if_neg hc, if_neg he, add_zero, mul_zero]

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.edgeStepVals_dead_zero (he : sk.entryCount i g p = 0) :
    (sk.edgeStepVals i v).dead g p = v.dead g p :=
  if_pos he

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.edgeStepVals_dead_ne (he : sk.entryCount i g p ≠ 0) :
    (sk.edgeStepVals i v).dead g p = 0 :=
  if_neg he

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.edgeStepVals_unborn_zero (he : sk.entryCount i g p = 0) :
    (sk.edgeStepVals i v).unborn g p = v.unborn g p :=
  if_pos he

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- An unborn prime with exactly one entry is born in that slot. -/
theorem Skel.edgeStepVals_unborn_one (he : sk.entryCount i g p = 1) :
    (sk.edgeStepVals i v).unborn g p = tiltLaw (𝒢.big g) D.q D.n p * v.act g p := by
  have hne : sk.entryCount i g p ≠ 0 := by
    rw [he]
    exact one_ne_zero
  exact (if_neg hne).trans (if_pos he)

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.edgeStepVals_unborn_big (he0 : sk.entryCount i g p ≠ 0)
    (he1 : sk.entryCount i g p ≠ 1) :
    (sk.edgeStepVals i v).unborn g p = 0 :=
  (if_neg he0).trans (if_neg he1)

end Edge

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
