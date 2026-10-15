module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.PathExpansion
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueSumWalks
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The summation over paths, part 2: the position enters an edge through two weights

Source: `verification/stage7-sources/S-02.tex`, lines 212–234 (`[S-02:0212–0234]`): "The label
normalization is initially `∏_g V_g^{-M}` and at each edge `∏_g V_g^{-t_g}`, in addition to the
free-label probabilities. All remaining factors are independent of `n`."

Everything is for an arbitrary position model `𝔭`.

* `posWeight 𝔭 𝒢 q n x` — `damping(n)` if the lists `x` are physical at the position `n`, and `0`
  otherwise. It is invariant under slot permutations (`posWeight_permuteLists`).
* `kappaCore`, `physCoef_eq_weights` — the coefficient `physCoef` of a row transition is
  `posWeight(source) · posWeight(target) · κ`, where `κ` (the conditions on the shared labels and
  on the auxiliary labels, the probability of the auxiliary labels, the target normalization and
  the multiplier `K_ν D^{iζ}`) does not depend on the position.
* `kappaF`, `kappaB`, `physFwdCoef_eq_weights`, `physBwdCoef_eq_weights` — the same for the
  coefficients of a forward and of a backward edge of the path expansion.
* `EState`, `edgeCoef`, `edgeTgt`, `edgeW`, `edgeK`, `edgeCoef_eq` — the edges as transitions of
  states with a direction flag (`ResidueSumWalks.lean`).
* `liftSt`, `edgeTgt_liftSt`, `edgeK_liftSt` — for a model with additive translations, the walk
  from the position `pos` is the image of the walk of integer offsets (the same walk in `intPos`,
  started at the offset `0`) under `(offset a, lists) ↦ (pos + a, lists)`: the offsets
  `h_0 = 0, h_1, …, h_N` and the lists are "fixed by these choices" [S-02:0214–0217].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum

open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

section Weight

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ}

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- Slot permutations preserve physical states. -/
theorem isPhys_permute_iff {𝒢 : GroupFamily S B} (π : SlotPerms S J ℓ × SlotPerms B J ℓ)
    (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) : IsPhys 𝔭 n (permuteLists π x) ↔ IsPhys 𝔭 n x := by
  have key : ∀ (π : SlotPerms S J ℓ × SlotPerms B J ℓ) (x : Lists 𝒢 J ℓ),
      IsPhys 𝔭 n x → IsPhys 𝔭 n (permuteLists π x) := fun π x h =>
    ⟨fun g => (h.1 g).comp (π.1 g).injective, fun g => (h.2.1 g).comp (π.2 g).injective,
      fun g i => h.2.2.1 g (π.1 g i), fun g i => h.2.2.2 g (π.2 g i)⟩
  refine ⟨fun h => ?_, key π x⟩
  have h1 := key (π.1⁻¹, π.2⁻¹) _ h
  have e : permuteLists (π.1⁻¹, π.2⁻¹) (permuteLists π x) = x :=
    Prod.ext (permuteSlots_inv_cancel π.1 x.1) (permuteSlots_inv_cancel π.2 x.2)
  rwa [e] at h1

open _root_.Classical in
/-- **The weight through which the position enters a coefficient at one end of an edge**: the
damping `q^{(ω(n) - Ms)/2}` if the lists are physical at the position, and `0` otherwise. -/
def posWeight (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) : ℝ :=
  if IsPhys 𝔭 n x then damping 𝔭 𝒢 J ℓ q n else 0

omit [DecidableEq S] [DecidableEq B] in
theorem posWeight_permuteLists (π : SlotPerms S J ℓ × SlotPerms B J ℓ) (n : 𝔭.Pos)
    (x : Lists 𝒢 J ℓ) : posWeight 𝔭 𝒢 q n (permuteLists π x) = posWeight 𝔭 𝒢 q n x := by
  unfold posWeight
  by_cases h : IsPhys 𝔭 n x
  · rw [if_pos h, if_pos ((isPhys_permute_iff 𝔭 π n x).mpr h)]
  · rw [if_neg h, if_neg fun h' => h ((isPhys_permute_iff 𝔭 π n x).mp h')]

open _root_.Classical in
/-- **The part of the coefficient of a row transition which does not depend on the position**:
the conditions on the shared labels and on the auxiliary labels, the probability of the auxiliary
labels, the target normalization `∏_g V_g^{-t_g}` and the multiplier `K_ν D^{iζ}`. -/
def kappaCore (ν : Pattern 𝒢.big J ℓ) (ζ : ℝ) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C)
    (x' : Lists 𝒢 J ℓ) : ℂ :=
  if SharedSmall x.1 x'.1 ∧ SharedBig ν.C x.2 x'.2 ∧ AuxAvoids ν.C r x ∧ AuxAvoids ν.C r x' then
    ((auxWeight 𝒢.big ν.C r * targetNorm 𝒢 ℓ ν.C : ℝ) : ℂ) *
      (ν.K x.2 x'.2 r * ((dil ν.C x r : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I))
  else 0

omit [DecidableEq S] [DecidableEq B] in
/-- Where `κ` does not vanish, the dilation computed from the target list equals the dilation
computed from the source list [S-02:0122–0123]. -/
theorem dil_eq_of_kappaCore_ne_zero {ν : Pattern 𝒢.big J ℓ} {ζ : ℝ} {x x' : Lists 𝒢 J ℓ}
    {r : AuxList 𝒢.big ν.C} (h : kappaCore 𝒢 ν ζ x r x' ≠ 0) : dil ν.C x' r = dil ν.C x r := by
  unfold kappaCore at h
  split_ifs at h with hc
  · unfold dil
    rw [smallDil_eq_of_shared hc.1, bigDil_eq_of_shared hc.2.1]
  · exact absurd rfl h

omit [DecidableEq S] [DecidableEq B] in
/-- **The coefficient of a row transition is `posWeight(source) · posWeight(target) · κ`.** -/
theorem physCoef_eq_weights (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (n : 𝔭.Pos)
    (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C) (x' : Lists 𝒢 J ℓ) :
    physCoef 𝔭 𝒢 q ν k ζ n x r x' =
      (posWeight 𝔭 𝒢 q n x : ℂ) *
        (posWeight 𝔭 𝒢 q (𝔭.shift (k * dil ν.C x r) n) x' : ℂ) * kappaCore 𝒢 ν ζ x r x' := by
  unfold physCoef posWeight kappaCore
  by_cases h1 : IsPhys 𝔭 n x
  · by_cases h2 : IsPhys 𝔭 (𝔭.shift (k * dil ν.C x r) n) x'
    · by_cases h3 : SharedSmall x.1 x'.1 ∧ SharedBig ν.C x.2 x'.2 ∧ AuxAvoids ν.C r x ∧
          AuxAvoids ν.C r x'
      · rw [if_pos (And.intro h1 (And.intro h2 h3)), if_pos h1, if_pos h2,
          if_pos h3]
        push_cast
        ring
      · rw [if_neg (fun h => h3 h.2.2), if_neg h3, mul_zero]
    · rw [if_neg (fun h => h2 h.2.1), if_neg h2, Complex.ofReal_zero, mul_zero,
        zero_mul]
  · rw [if_neg (fun h => h1 h.1), if_neg h1, Complex.ofReal_zero, zero_mul,
      zero_mul]

end Weight

section Edges

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type} [Fintype N]

/-- The position-independent part of the coefficient of a forward edge. -/
def kappaF (𝔉 : N → Pattern 𝒢.big J ℓ) (ζ : ℝ) (x : Lists 𝒢 J ℓ) (ξ : PhysChoice 𝒢 𝔉) : ℂ :=
  (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹ *
    kappaCore 𝒢 (𝔉 ξ.2.1.1) ζ (permuteLists ξ.1 x) ξ.2.1.2.1 ξ.2.1.2.2 *
    (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹

/-- The position-independent part of the coefficient of a backward edge. -/
def kappaB (𝔉 : N → Pattern 𝒢.big J ℓ) (ζ : ℝ) (x : Lists 𝒢 J ℓ) (ξ : PhysChoice 𝒢 𝔉) : ℂ :=
  (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹ *
    conj (kappaCore 𝒢 (𝔉 ξ.2.1.1) ζ ξ.2.1.2.2 ξ.2.1.2.1 (permuteLists ξ.1 x)) *
    (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹

omit [Fintype N] in
/-- **A forward edge**: its coefficient is `posWeight(source) · posWeight(target) · κ_F`. -/
theorem physFwdCoef_eq_weights (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s : PState 𝔭 𝒢 J ℓ) (ξ : PhysChoice 𝒢 𝔉) :
    physFwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ =
      (posWeight 𝔭 𝒢 q s.1 s.2 : ℂ) *
        (posWeight 𝔭 𝒢 q (physFwdTgt 𝔭 𝒢 𝔉 k s ξ).1 (physFwdTgt 𝔭 𝒢 𝔉 k s ξ).2 : ℂ) *
        kappaF 𝒢 𝔉 ζ s.2 ξ := by
  have e1 : posWeight 𝔭 𝒢 q s.1 (permuteLists ξ.1 s.2) = posWeight 𝔭 𝒢 q s.1 s.2 :=
    posWeight_permuteLists 𝔭 𝒢 q ξ.1 s.1 s.2
  have e2 : posWeight 𝔭 𝒢 q (physFwdTgt 𝔭 𝒢 𝔉 k s ξ).1 (physFwdTgt 𝔭 𝒢 𝔉 k s ξ).2 =
      posWeight 𝔭 𝒢 q
        (𝔭.shift (k * dil (𝔉 ξ.2.1.1).C (permuteLists ξ.1 s.2) ξ.2.1.2.1) s.1) ξ.2.1.2.2 :=
    posWeight_permuteLists 𝔭 𝒢 q ξ.2.2 _ ξ.2.1.2.2
  unfold physFwdCoef kappaF
  rw [physCoef_eq_weights, e1, e2]
  ring

omit [Fintype N] in
/-- **A backward edge**: its coefficient is `posWeight(source) · posWeight(target) · κ_B`. -/
theorem physBwdCoef_eq_weights (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s : PState 𝔭 𝒢 J ℓ) (ξ : PhysChoice 𝒢 𝔉) :
    physBwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ =
      (posWeight 𝔭 𝒢 q s.1 s.2 : ℂ) *
        (posWeight 𝔭 𝒢 q (physBwdTgt 𝔭 𝒢 𝔉 k s ξ).1 (physBwdTgt 𝔭 𝒢 𝔉 k s ξ).2 : ℂ) *
        kappaB 𝒢 𝔉 ζ s.2 ξ := by
  have e1 : posWeight 𝔭 𝒢 q s.1 (permuteLists ξ.1 s.2) = posWeight 𝔭 𝒢 q s.1 s.2 :=
    posWeight_permuteLists 𝔭 𝒢 q ξ.1 s.1 s.2
  have e2 : posWeight 𝔭 𝒢 q (physBwdTgt 𝔭 𝒢 𝔉 k s ξ).1 (physBwdTgt 𝔭 𝒢 𝔉 k s ξ).2 =
      posWeight 𝔭 𝒢 q
        (𝔭.shift (-(k * dil (𝔉 ξ.2.1.1).C (permuteLists ξ.1 s.2) ξ.2.1.2.1)) s.1)
        ξ.2.1.2.2 :=
    posWeight_permuteLists 𝔭 𝒢 q ξ.2.2 _ ξ.2.1.2.2
  unfold physBwdCoef kappaB
  rw [physCoef_eq_weights]
  by_cases hκ : kappaCore 𝒢 (𝔉 ξ.2.1.1) ζ ξ.2.1.2.2 ξ.2.1.2.1 (permuteLists ξ.1 s.2) = 0
  · rw [hκ]
    simp
  · have hD := dil_eq_of_kappaCore_ne_zero 𝒢 hκ
    rw [← hD, 𝔭.shift_shift_neg, e1, e2, map_mul, map_mul, Complex.conj_ofReal,
      Complex.conj_ofReal]
    ring

/-! ### Edges with a direction flag -/

/-- The states of the walk of edges: a direction flag (`false`: the next edge is a forward edge)
and a pair (position, lists). -/
abbrev EState (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) : Type := Bool × PState 𝔭 𝒢 J ℓ

/-- The coefficient of the next edge. -/
def edgeCoef (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    EState 𝔭 𝒢 J ℓ → PhysChoice 𝒢 𝔉 → ℂ :=
  altCoef (physFwdCoef 𝔭 𝒢 q 𝔉 k ζ) (physBwdCoef 𝔭 𝒢 q 𝔉 k ζ)

/-- The state after the next edge. -/
def edgeTgt (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) :
    EState 𝔭 𝒢 J ℓ → PhysChoice 𝒢 𝔉 → EState 𝔭 𝒢 J ℓ :=
  altTgt (physFwdTgt 𝔭 𝒢 𝔉 k) (physBwdTgt 𝔭 𝒢 𝔉 k)

/-- The weight of a state. -/
def edgeW (s : EState 𝔭 𝒢 J ℓ) : ℝ := posWeight 𝔭 𝒢 q s.2.1 s.2.2

/-- The position-independent part of the coefficient of the next edge. -/
def edgeK (𝔉 : N → Pattern 𝒢.big J ℓ) (ζ : ℝ) (s : EState 𝔭 𝒢 J ℓ) (ξ : PhysChoice 𝒢 𝔉) : ℂ :=
  if s.1 then kappaB 𝒢 𝔉 ζ s.2.2 ξ else kappaF 𝒢 𝔉 ζ s.2.2 ξ

omit [Fintype N] in
/-- Every edge: its coefficient is `weight(source) · weight(target) · κ`. -/
theorem edgeCoef_eq (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (s : EState 𝔭 𝒢 J ℓ)
    (ξ : PhysChoice 𝒢 𝔉) :
    edgeCoef 𝔭 𝒢 q 𝔉 k ζ s ξ =
      (edgeW 𝔭 𝒢 q s : ℂ) * (edgeW 𝔭 𝒢 q (edgeTgt 𝔭 𝒢 𝔉 k s ξ) : ℂ) * edgeK 𝔭 𝒢 𝔉 ζ s ξ := by
  obtain ⟨b, s⟩ := s
  cases b
  · exact physFwdCoef_eq_weights 𝔭 𝒢 q 𝔉 k ζ s ξ
  · exact physBwdCoef_eq_weights 𝔭 𝒢 q 𝔉 k ζ s ξ

/-- The state of the model `𝔭` which corresponds to a state of integer offsets, for the start
position `pos`: the offset `a` becomes the position `pos + a`. -/
def liftSt (pos : 𝔭.Pos) (s : EState intPos 𝒢 J ℓ) : EState 𝔭 𝒢 J ℓ :=
  (s.1, (𝔭.shift (show ℤ from s.2.1) pos, s.2.2))

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- For a model with additive translations, the edges commute with `liftSt`. -/
theorem edgeTgt_liftSt
    (hadd : ∀ (a b : ℤ) (n : 𝔭.Pos), 𝔭.shift a (𝔭.shift b n) = 𝔭.shift (b + a) n)
    (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (pos : 𝔭.Pos) (s : EState intPos 𝒢 J ℓ)
    (ξ : PhysChoice 𝒢 𝔉) :
    edgeTgt 𝔭 𝒢 𝔉 k (liftSt 𝔭 𝒢 pos s) ξ = liftSt 𝔭 𝒢 pos (edgeTgt intPos 𝒢 𝔉 k s ξ) := by
  obtain ⟨b, a, x⟩ := s
  cases b
  · show ((true, (𝔭.shift (k * dil (𝔉 ξ.2.1.1).C (permuteLists ξ.1 x) ξ.2.1.2.1)
          (𝔭.shift (show ℤ from a) pos), permuteLists ξ.2.2 ξ.2.1.2.2)) : EState 𝔭 𝒢 J ℓ) =
      (true, (𝔭.shift ((show ℤ from a) +
          k * dil (𝔉 ξ.2.1.1).C (permuteLists ξ.1 x) ξ.2.1.2.1) pos,
        permuteLists ξ.2.2 ξ.2.1.2.2))
    rw [hadd]
  · show ((false, (𝔭.shift (-(k * dil (𝔉 ξ.2.1.1).C (permuteLists ξ.1 x) ξ.2.1.2.1))
          (𝔭.shift (show ℤ from a) pos), permuteLists ξ.2.2 ξ.2.1.2.2)) : EState 𝔭 𝒢 J ℓ) =
      (false, (𝔭.shift ((show ℤ from a) +
          -(k * dil (𝔉 ξ.2.1.1).C (permuteLists ξ.1 x) ξ.2.1.2.1)) pos,
        permuteLists ξ.2.2 ξ.2.1.2.2))
    rw [hadd]

omit [Fintype N] in
/-- The position-independent part of a coefficient is unchanged by `liftSt`. -/
theorem edgeK_liftSt (𝔉 : N → Pattern 𝒢.big J ℓ) (ζ : ℝ) (pos : 𝔭.Pos)
    (s : EState intPos 𝒢 J ℓ) (ξ : PhysChoice 𝒢 𝔉) :
    edgeK 𝔭 𝒢 𝔉 ζ (liftSt 𝔭 𝒢 pos s) ξ = edgeK intPos 𝒢 𝔉 ζ s ξ := rfl

end Edges

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum
