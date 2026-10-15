module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HighRank.Pins
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostAbsoluteProof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Large rank: the weighted row bound of an absolute visit operation with prescribed ghost births

Source: `verification/stage7-sources/S-02.tex`, lines 1130–1135 (`[S-02:1130–1135]`).

"For a ghost operation keep its ordered batch integral and factorial divisor; constraining
indicated fresh coordinates replaces their mass factors by the same single-point bound. The birth
coefficient `V_g` and the memory weight only give fixed constants per constrained coordinate."

* `hrIndB pin β`, `hrIndG pv c` — the indicators that the batch of one group, respectively the
  batches of all big groups, realize the prescribed values: every index with a prescribed value is
  below the size of the batch and carries that value.
* `hr_ghostAbsG_factor` — for a fixed terminated set and a fixed batch size, the absolute
  coefficient `ghostAbsG` times the weight of the new memory is a constant times `∏_j μ̃_g(β_j)`.
* `hr_ghost_group_pinned` — one big group: the row sum with the indicator is at most the product
  of the point masses of the prescribed values times the row sum without it
  (`hr_sum_batch_le`), hence at most that product times `e^{c_max v M_max} v^j`
  (`ghostAbs_row_eq_kernel`, `ghostAbsKernel_row_le`).
* `hr_ghost_row_pinned` — all big groups: the constant of `ghost_rowBound` times the product of the
  point masses. No constant per constrained coordinate is lost, because `μ̃_g(𝒫_g) ≥ 1` and the
  factorial divisor of the batch is kept.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section HrGhostGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {Bc : ℕ} {g : B}

open _root_.Classical in
/-- **The batch of one big group realizes the prescribed values**: every index with a prescribed
value is performed and carries that value (an indicator, as a real number). -/
def hrIndB (pin : Fin Bc → Option ℕ) (β : Batch 𝒢 Bc g) : ℝ :=
  if ∀ j z, pin j = some z → hrBatchBirth β j = some z then 1 else 0

theorem hrIndB_nonneg (pin : Fin Bc → Option ℕ) (β : Batch 𝒢 Bc g) : 0 ≤ hrIndB pin β := by
  unfold hrIndB
  split_ifs
  · exact zero_le_one
  · exact le_rfl

/-- For a fixed terminated set `A'` and a fixed batch size `b`, the absolute coefficient with
doubled births times the weight `v^{j'}` of the new memory is a nonnegative constant times
`∏_j μ̃_g(β_j)`: "the birth coefficient `V_g` and the memory weight only give fixed constants"
[S-02:1133–1135]. -/
theorem hr_ghostAbsG_factor (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B) {v : ℝ}
    (hv : 0 ≤ v) (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (z : Mem 𝒢 Bc g)
    (A' : Finset (Fin Bc)) (b : Fin (Bc + 1)) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
      ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
          v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val =
        Kc * ∏ j, tiltLaw (𝒢.big g) q n (β j) := by
  by_cases hsize : (ghostSurvivors z A').length + b.val ≤ Bc
  · by_cases hval : GhostValid z A'
    · refine ⟨(2 : ℝ) ^ b.val *
          |Graph.sourceGhostD (visitQ q n i) ρ ^ A'.card *
            Graph.sourceGhostA (visitQ q n i) ρ ^ (memZeroCount z - A'.card) *
            (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ ^
              b.val / (b.val.factorial : ℝ))| *
          v ^ ((ghostSurvivors z A').length + b.val),
        mul_nonneg (mul_nonneg (pow_nonneg zero_le_two _) (abs_nonneg _)) (pow_nonneg hv _),
        fun β => ?_⟩
      have hs : ghostNewSize z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) ≤ Bc := hsize
      have h1 : ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) =
          (2 : ℝ) ^ b.val * |ghostCoefG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))| := by
        unfold ghostAbsG
        exact if_pos hs
      have h2 : ghostCoefG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) =
          Graph.sourceGhostD (visitQ q n i) ρ ^ A'.card *
            Graph.sourceGhostA (visitQ q n i) ρ ^ (memZeroCount z - A'.card) *
            (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ ^
              b.val / (b.val.factorial : ℝ)) *
            ∏ j, tiltLaw (𝒢.big g) q n (β j) := by
        unfold ghostCoefG
        exact if_pos hval
      have h3 : (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val =
          (ghostSurvivors z A').length + b.val := ghostNewMem_size z _ hs
      have hP : 0 ≤ ∏ j, tiltLaw (𝒢.big g) q n (β j) :=
        Finset.prod_nonneg fun j _ => hν _ (β j).2
      rw [h1, h2, h3, abs_mul, abs_of_nonneg hP]
      ring
    · refine ⟨0, le_rfl, fun β => ?_⟩
      have h2 : ghostCoefG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) = 0 := by
        unfold ghostCoefG
        exact if_neg hval
      have h1 : ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) = 0 := by
        unfold ghostAbsG
        rw [h2, abs_zero, mul_zero]
        exact ite_self 0
      rw [h1, zero_mul, zero_mul]
  · refine ⟨0, le_rfl, fun β => ?_⟩
    have hs : ¬ghostNewSize z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) ≤ Bc := hsize
    have h1 : ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) = 0 := by
      unfold ghostAbsG
      exact if_neg hs
    rw [h1, zero_mul, zero_mul]

/-- **The weighted row of one big group with prescribed ghost births** [S-02:1130–1135]: the row
sum of the absolute coefficients (with doubled births) over the choices whose batch realizes the
prescribed values is at most the product of the point masses of these values times
`e^{c_max v M_max} v^j`, the bound of the row without constraint. -/
theorem hr_ghost_group_pinned (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B)
    {v cmax Mmax : ℝ} (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (h1 : 1 ≤ ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ q n i) ρ) (hv : 0 < v)
    (hbase : Graph.sourceGhostA (visitQ q n i) ρ +
      |Graph.sourceGhostD (visitQ q n i) ρ| / v ≤ 1)
    (hC : |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ| ≤
      cmax)
    (hM : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) q n p ≤ Mmax)
    (pin : Fin Bc → Option ℕ) (z : Mem 𝒢 Bc g) :
    ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g,
        ghostAbsG 𝒢 q ρ n i g z c * hrIndB pin c.2 * v ^ (ghostNewMem z c).1.val ≤
      (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) * (Real.exp (cmax * v * Mmax) * v ^ z.1.val) := by
  have hW0 : 0 ≤ ∏ j, hrW (hrPtMass 𝒢 q n g) (pin j) :=
    Finset.prod_nonneg fun j _ => hrW_nonneg (hrPtMass_nonneg hν) _
  -- the row without constraint
  have hone : ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g,
      ghostAbsG 𝒢 q ρ n i g z c * v ^ (ghostNewMem z c).1.val ≤
        Real.exp (cmax * v * Mmax) * v ^ z.1.val :=
    (ghostAbs_row_eq_kernel 𝒢 q ρ n i g hA hν (fun y : Mem 𝒢 Bc g => v ^ y.1.val)
      (fun _ _ _ => rfl) z).le.trans
      (ghostAbsKernel_row_le 𝒢 q ρ n i g hν hA hv hbase hC hM z)
  -- a fixed terminated set and a fixed batch size
  have hfix : ∀ (A' : Finset (Fin Bc)) (b : Fin (Bc + 1)),
      ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
          ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
            hrIndB pin (⟨b, β⟩ : Batch 𝒢 Bc g) *
            v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val ≤
        (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) *
          ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
            ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
              v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val := by
    intro A' b
    obtain ⟨Kc, hKc0, hKc⟩ := hr_ghostAbsG_factor 𝒢 q ρ n i g hv.le hν z A' b
    have e1 : ∀ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
        ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
            hrIndB pin (⟨b, β⟩ : Batch 𝒢 Bc g) *
            v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val =
          Kc * (if ∀ j z', pin j = some z' →
              hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) j = some z' then
            ∏ j, tiltLaw (𝒢.big g) q n (β j) else 0) := by
      intro β
      have e2 : ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
            hrIndB pin (⟨b, β⟩ : Batch 𝒢 Bc g) *
            v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val =
          (ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
            v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val) *
            hrIndB pin (⟨b, β⟩ : Batch 𝒢 Bc g) := by ring
      rw [e2, hKc β]
      unfold hrIndB
      by_cases hc : ∀ j z', pin j = some z' →
          hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) j = some z'
      · rw [if_pos hc, if_pos hc, mul_one]
      · rw [if_neg hc, if_neg hc, mul_zero, mul_zero]
    calc ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
          ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
            hrIndB pin (⟨b, β⟩ : Batch 𝒢 Bc g) *
            v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val
        = ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
            Kc * (if ∀ j z', pin j = some z' →
                hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) j = some z' then
              ∏ j, tiltLaw (𝒢.big g) q n (β j) else 0) :=
          Finset.sum_congr rfl fun β _ => e1 β
      _ = Kc * ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
            (if ∀ j z', pin j = some z' →
                hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) j = some z' then
              ∏ j, tiltLaw (𝒢.big g) q n (β j) else 0) := (Finset.mul_sum _ _ _).symm
      _ ≤ Kc * ((∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) *
            ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g}, ∏ j, tiltLaw (𝒢.big g) q n (β j)) :=
          mul_le_mul_of_nonneg_left (hr_sum_batch_le hν h1 b pin) hKc0
      _ = (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) *
            ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
              Kc * ∏ j, tiltLaw (𝒢.big g) q n (β j) := by
          rw [← Finset.mul_sum]
          ring
      _ = (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) *
            ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
              ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
                v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val :=
          congrArg (fun t => (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) * t)
            (Finset.sum_congr rfl fun β _ => (hKc β).symm)
  -- a sum over the choices is a sum over the terminated sets, the batch sizes and the batches
  have hsplit : ∀ F : Finset (Fin Bc) × Batch 𝒢 Bc g → ℝ,
      ∑ c, F c = ∑ A' : Finset (Fin Bc), ∑ b : Fin (Bc + 1),
        ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g}, F (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) := by
    intro F
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun A' _ => ?_
    exact Fintype.sum_sigma fun β : Batch 𝒢 Bc g => F (A', β)
  calc ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g,
        ghostAbsG 𝒢 q ρ n i g z c * hrIndB pin c.2 * v ^ (ghostNewMem z c).1.val
      = ∑ A' : Finset (Fin Bc), ∑ b : Fin (Bc + 1),
          ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
            ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
              hrIndB pin (⟨b, β⟩ : Batch 𝒢 Bc g) *
              v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val :=
        hsplit fun c => ghostAbsG 𝒢 q ρ n i g z c * hrIndB pin c.2 * v ^ (ghostNewMem z c).1.val
    _ ≤ ∑ A' : Finset (Fin Bc), ∑ b : Fin (Bc + 1),
          (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) *
            ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
              ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
                v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val :=
        Finset.sum_le_sum fun A' _ => Finset.sum_le_sum fun b _ => hfix A' b
    _ = (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) *
          ∑ A' : Finset (Fin Bc), ∑ b : Fin (Bc + 1),
            ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
              ghostAbsG 𝒢 q ρ n i g z (A', (⟨b, β⟩ : Batch 𝒢 Bc g)) *
                v ^ (ghostNewMem z (A', (⟨b, β⟩ : Batch 𝒢 Bc g))).1.val := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun A' _ => ?_
        rw [Finset.mul_sum]
    _ = (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) *
          ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g,
            ghostAbsG 𝒢 q ρ n i g z c * v ^ (ghostNewMem z c).1.val :=
        congrArg (fun t => (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) * t)
          (hsplit fun c => ghostAbsG 𝒢 q ρ n i g z c * v ^ (ghostNewMem z c).1.val).symm
    _ ≤ (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) * (Real.exp (cmax * v * Mmax) * v ^ z.1.val) :=
        mul_le_mul_of_nonneg_left hone hW0

end HrGhostGroup

section HrGhostInd

variable {S B : Type} [Fintype B] {𝒢 : GroupFamily S B} {Bc : ℕ}

open _root_.Classical in
/-- **The ghost births of a visit operation realize the prescribed values**: in every big group,
every index with a prescribed value is performed and carries that value (an indicator, as a real
number). -/
def hrIndG (pv : (g : B) → Fin Bc → Option ℕ) (c : GhostChoice 𝒢 Bc) : ℝ :=
  if ∀ g j z, pv g j = some z → hrBatchBirth (c g).2 j = some z then 1 else 0

theorem hrIndG_nonneg (pv : (g : B) → Fin Bc → Option ℕ) (c : GhostChoice 𝒢 Bc) :
    0 ≤ hrIndG pv c := by
  unfold hrIndG
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem hrIndG_of {pv : (g : B) → Fin Bc → Option ℕ} {c : GhostChoice 𝒢 Bc}
    (h : ∀ g j z, pv g j = some z → hrBatchBirth (c g).2 j = some z) : hrIndG pv c = 1 := by
  unfold hrIndG
  exact if_pos h

theorem hrIndG_of_not {pv : (g : B) → Fin Bc → Option ℕ} {c : GhostChoice 𝒢 Bc}
    (h : ¬∀ g j z, pv g j = some z → hrBatchBirth (c g).2 j = some z) : hrIndG pv c = 0 := by
  unfold hrIndG
  exact if_neg h

end HrGhostInd

section HrGhostMulti

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

omit [DecidableEq S] in
/-- **The weighted row bound of the absolute visit operation with prescribed ghost births**
[S-02:1130–1135]: the row sum over the local transition choices whose batches realize the
prescribed values is at most

`(∏_{g ∈ ℬ} e^{c_max v M_max}) · ∏ μ̃_g(z) · v^{j_tot}`,

the last product being over the prescribed values: the constant of `ghost_rowBound` times the
point masses. -/
theorem hr_ghost_row_pinned (D : MemData 𝒢 J ℓ N) (Bc i : ℕ) {v cmax Mmax : ℝ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (h1 : ∀ g, 1 ≤ ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ D.q D.n i) D.ρ) (hv : 0 < v)
    (hbase : Graph.sourceGhostA (visitQ D.q D.n i) D.ρ +
      |Graph.sourceGhostD (visitQ D.q D.n i) D.ρ| / v ≤ 1)
    (hC : ∀ g, |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g))
      (visitQ D.q D.n i) D.ρ| ≤ cmax)
    (hM : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (pv : (g : B) → Fin Bc → Option ℕ) (s : MState 𝒢 J ℓ Bc) :
    ∑ c : GhostChoice 𝒢 Bc,
        hrIndG pv c * |ghostCoef D i s c| * schurWeight v (ghostTgt s c) ≤
      (∏ _g : B, Real.exp (cmax * v * Mmax)) *
        (∏ g, ∏ j, hrW (hrPtMass 𝒢 D.q D.n g) (pv g j)) * schurWeight v s := by
  have hterm : ∀ c : GhostChoice 𝒢 Bc,
      hrIndG pv c * |ghostCoef D i s c| * schurWeight v (ghostTgt s c) ≤
        ∏ g, (ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) * hrIndB (pv g) (c g).2 *
          v ^ (ghostNewMem (s.mem g) (c g)).1.val) := by
    intro c
    have h2 : schurWeight v (ghostTgt s c) = ∏ g, v ^ (ghostNewMem (s.mem g) (c g)).1.val :=
      (Finset.prod_pow_eq_pow_sum Finset.univ
        (fun g => (ghostNewMem (s.mem g) (c g)).1.val) v).symm
    have h3 : |ghostCoef D i s c| ≤ ∏ g, ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) :=
      le_trans (le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ one_le_two))
        (ghostCoef_abs_le D i s c)
    have h4 : hrIndG pv c ≤ ∏ g, hrIndB (pv g) (c g).2 := by
      by_cases hc : ∀ g j z, pv g j = some z → hrBatchBirth (c g).2 j = some z
      · rw [hrIndG_of hc]
        refine le_of_eq (Finset.prod_eq_one fun g _ => ?_).symm
        unfold hrIndB
        exact if_pos (hc g)
      · rw [hrIndG_of_not hc]
        exact Finset.prod_nonneg fun g _ => hrIndB_nonneg _ _
    have h5 : hrIndG pv c * |ghostCoef D i s c| ≤
        (∏ g, ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g)) * ∏ g, hrIndB (pv g) (c g).2 := by
      rw [mul_comm (hrIndG pv c)]
      exact mul_le_mul h3 h4 (hrIndG_nonneg _ _)
        (Finset.prod_nonneg fun g _ => ghostAbsG_nonneg 𝒢 D.q D.ρ D.n i g (s.mem g) (c g))
    rw [h2, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    exact mul_le_mul_of_nonneg_right h5 (Finset.prod_nonneg fun g _ => (pow_pos hv _).le)
  have hsw : (∏ g, v ^ (s.mem g).1.val) = schurWeight v s :=
    Finset.prod_pow_eq_pow_sum Finset.univ (fun g => (s.mem g).1.val) v
  calc ∑ c : GhostChoice 𝒢 Bc,
        hrIndG pv c * |ghostCoef D i s c| * schurWeight v (ghostTgt s c)
      ≤ ∑ c : GhostChoice 𝒢 Bc,
          ∏ g, (ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) * hrIndB (pv g) (c g).2 *
            v ^ (ghostNewMem (s.mem g) (c g)).1.val) := Finset.sum_le_sum fun c _ => hterm c
    _ = ∏ g, ∑ cg : Finset (Fin Bc) × Batch 𝒢 Bc g,
          (ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) cg * hrIndB (pv g) cg.2 *
            v ^ (ghostNewMem (s.mem g) cg).1.val) :=
        (Fintype.prod_sum fun g (cg : Finset (Fin Bc) × Batch 𝒢 Bc g) =>
          ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) cg * hrIndB (pv g) cg.2 *
            v ^ (ghostNewMem (s.mem g) cg).1.val).symm
    _ ≤ ∏ g, ((∏ j, hrW (hrPtMass 𝒢 D.q D.n g) (pv g j)) *
          (Real.exp (cmax * v * Mmax) * v ^ (s.mem g).1.val)) :=
        Finset.prod_le_prod
          (fun g _ => Finset.sum_nonneg fun cg _ =>
            mul_nonneg (mul_nonneg (ghostAbsG_nonneg 𝒢 D.q D.ρ D.n i g (s.mem g) cg)
              (hrIndB_nonneg _ _)) (pow_pos hv _).le)
          (fun g _ => hr_ghost_group_pinned 𝒢 D.q D.ρ D.n i g (hν g) (h1 g) hA hv hbase (hC g)
            (hM g) (pv g) (s.mem g))
    _ = (∏ _g : B, Real.exp (cmax * v * Mmax)) *
          (∏ g, ∏ j, hrW (hrPtMass 𝒢 D.q D.n g) (pv g j)) * schurWeight v s := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hsw]
        ring

end HrGhostMulti

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
