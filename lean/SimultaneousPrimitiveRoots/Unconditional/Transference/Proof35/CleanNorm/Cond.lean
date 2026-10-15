module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.ShRow
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsRowSums
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lemma 3.10: conditioning on the small groups

Source: `verification/stage7-sources/S-02.tex`, lines 919–963 (`[S-02:0919–0963]`).

"Fix an ordered tuple `𝐝` of `J` shared labels in each small group and let `d'` denote their
joint product. Define a map to unrestricted small residue functions by (eq:small-conditioning-map)
`(P_𝐝 w)(y) = (∏_{g ∈ 𝒮} V_g^{-J/2-ℓ}) q^{½ ∑_g (ω_g(y) - M)} ∑_{𝐑} w(y, (𝐝, 𝐑))`. … By Cauchy's
inequality in `𝐑`, followed by summation over `𝐝`, one has (eq:small-map-norm)
`∑_𝐝 ‖P_𝐝 w‖² ≤ L^{C_s} ‖w‖²`. … The clean bilinear form is now exactly
`∑_𝐝 ⟨P_𝐝 w₁, 𝒯'_𝐝 P_𝐝 w₂⟩`."

* `CleanShared`, `cleanCls`, `cleanD` — the tuples `𝐝`, the tuple of a small list, and `d'`.
* `CleanW` — the remaining coordinates `(y, memories; big list)`; `cleanMk`, `cleanBase`.
* `cleanU`, `cleanQ` — the source factor (memory projection, input `ρ` factor, small endpoint
  factor at the source) and the conditioning map `P_𝐝` with the output `ρ` factor and the
  normalization `∏ V_g^{-ℓ}` (the split of the factors `V_g` between the two sides differs from
  the text by constants).
* `cleanCondOp 𝒯` — the operator `F ↦ u · 𝒯_{d'}(P_𝐝 F)` for a family `𝒯_d` of operators on the
  functions of the remaining coordinates.
* `cleanCondOp_bound` — **(eq:small-map-norm) and Cauchy's inequality**: if every `𝒯_d` has norm
  at most `C_T`, then `cleanCondOp 𝒯` has norm at most `K_𝒮 C_T` on `L²` of the measure of `ℋ`,
  where `K_𝒮` bounds the total weight of the small states with given shared labels
  (`clean_sum_smallW_le`: `K_𝒮 = ∏_{g ∈ 𝒮} groupConst v₋ q ℓ`, independent of `J`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

section Cond

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ}

/-- **The tuples `𝐝`**: `J` shared labels in each small group. -/
abbrev CleanShared (𝒢 : GroupFamily S B) (J : ℕ) : Type :=
  (g : S) → Fin J → {p : ℕ // p ∈ 𝒢.small g}

/-- The shared labels of a small list: its first `J` slots. -/
def cleanCls (xs : LabelList 𝒢.small J ℓ) : CleanShared 𝒢 J := fun g i => xs g (Sum.inl i)

/-- `d'`, the product of the shared small labels. -/
def cleanD (a : CleanShared 𝒢 J) : ℕ := ∏ g, ∏ i, (a g i : ℕ)

/-- The small residues and the memories. -/
abbrev CleanY (𝒢 : GroupFamily S B) (Bc : ℕ) : Type :=
  ResVec (smallPrimes 𝒢) × ((g : B) → Mem 𝒢 Bc g)

/-- The coordinates of a memory state other than the small list. -/
abbrev CleanW (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) : Type :=
  CleanY 𝒢 Bc × LabelList 𝒢.big J ℓ

/-- The memory state with the given small list and the given remaining coordinates. -/
def cleanMk (w : CleanW 𝒢 J ℓ Bc) (xs : LabelList 𝒢.small J ℓ) : MState 𝒢 J ℓ Bc :=
  ⟨w.1.1, xs, w.2, w.1.2⟩

/-- The coordinates of a memory state other than the small list. -/
def cleanBase (s : MState 𝒢 J ℓ Bc) : CleanW 𝒢 J ℓ Bc := ((s.y, s.mem), s.xb)

/-- A memory state is its small list and its remaining coordinates. -/
def cleanStateEquiv : MState 𝒢 J ℓ Bc ≃ CleanW 𝒢 J ℓ Bc × LabelList 𝒢.small J ℓ where
  toFun s := (cleanBase s, s.xs)
  invFun p := cleanMk p.1 p.2
  left_inv s := by
    cases s
    rfl
  right_inv p := by
    rcases p with ⟨⟨⟨y, mem⟩, xb⟩, xs⟩
    rfl

/-- A sum over the memory states. -/
theorem clean_sum_state {M : Type*} [AddCommMonoid M] (f : MState 𝒢 J ℓ Bc → M) :
    ∑ s, f s = ∑ w : CleanW 𝒢 J ℓ Bc, ∑ xs : LabelList 𝒢.small J ℓ, f (cleanMk w xs) := by
  rw [← Equiv.sum_comp (cleanStateEquiv (𝒢 := 𝒢) (J := J) (ℓ := ℓ) (Bc := Bc)).symm f]
  exact Fintype.sum_prod_type _

/-- The measure of the small residues and of the memories, with the normalization
`∏_{g ∈ 𝒮} V_g^{-J}` of the shared small labels. -/
def cleanYW (𝒢 : GroupFamily S B) (J : ℕ) (q : ℝ) (n : ℕ) (yy : CleanY 𝒢 Bc) : ℝ :=
  (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹) * haarMass (smallPrimes 𝒢) *
    memMass 𝒢 q n yy.2

/-- The number of pending zeros of a family of memories. -/
def cleanMemZeros (mem : (g : B) → Mem 𝒢 Bc g) : ℕ := ∑ g, memZeroCount (mem g)

open _root_.Classical in
/-- **The source factor of a clean edge**: the memory projection, the input factor `ρ^{#zeros}`
and the small endpoint factor at the source [S-02:0914–0917]. -/
def cleanU (q ρ : ℝ) (s : MState 𝒢 J ℓ Bc) : ℝ :=
  if memTotal s ≤ Bc ∧ IsSmallState 𝒢 s.y s.xs then
    ρ ^ memZeros s * smallDamping 𝒢 J ℓ q s.y
  else 0

open _root_.Classical in
/-- The weight of a small list in the conditioning map: the normalization `∏ V_g^{-ℓ}` and the
small endpoint factor, for the small states at `y` with the shared labels `a`. -/
def cleanSmallW (q : ℝ) (a : CleanShared 𝒢 J) (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) : ℝ :=
  if IsSmallState 𝒢 y xs ∧ cleanCls xs = a then
    (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) * smallDamping 𝒢 J ℓ q y
  else 0

/-- **The conditioning map `P_𝐝`** (eq:small-conditioning-map) [S-02:0922–0929], with the output
factor `ρ^{#zeros}`: the sum over the small states with the shared labels `a`. -/
def cleanQ (q ρ : ℝ) (a : CleanShared 𝒢 J) (G : MState 𝒢 J ℓ Bc → ℂ) :
    CleanW 𝒢 J ℓ Bc → ℂ :=
  fun w => ∑ xs : LabelList 𝒢.small J ℓ,
    ((cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2 : ℝ) : ℂ) * G (cleanMk w xs)

/-- **The conditioned form of a clean edge** (eq:clean-conditioned-form) [S-02:0954–0958]:
`F ↦ u · 𝒯_{d'}(P_𝐝 F)`, where `𝐝` is the tuple of the shared small labels of the state. -/
def cleanCondOp (q ρ : ℝ)
    (𝒯 : ℕ → (CleanW 𝒢 J ℓ Bc → ℂ) → (CleanW 𝒢 J ℓ Bc → ℂ)) (G : MState 𝒢 J ℓ Bc → ℂ) :
    MState 𝒢 J ℓ Bc → ℂ :=
  fun s => ((cleanU q ρ s : ℝ) : ℂ) *
    𝒯 (cleanD (cleanCls s.xs)) (cleanQ q ρ (cleanCls s.xs) G) (cleanBase s)

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem cleanSmallW_nonneg {q : ℝ} (hq : 0 < q) (a : CleanShared 𝒢 J)
    (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ) : 0 ≤ cleanSmallW q a y xs := by
  unfold cleanSmallW
  split_ifs
  · exact mul_nonneg
      (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _))
      (l38_smallDamping_pos hq y).le
  · exact le_rfl

omit [DecidableEq S] [DecidableEq B] in
theorem cleanU_nonneg {q ρ : ℝ} (hq : 0 < q) (hρ : 0 < ρ) (s : MState 𝒢 J ℓ Bc) :
    0 ≤ cleanU q ρ s := by
  unfold cleanU
  split_ifs
  · exact mul_nonneg (pow_nonneg hρ.le _) (l38_smallDamping_pos hq _).le
  · exact le_rfl

omit [DecidableEq S] [DecidableEq B] in
theorem cleanU_le {q ρ : ℝ} (hq : 0 < q) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (s : MState 𝒢 J ℓ Bc) :
    cleanU q ρ s ≤ smallDamping 𝒢 J ℓ q s.y := by
  unfold cleanU
  split_ifs
  · exact mul_le_of_le_one_left (l38_smallDamping_pos hq _).le (pow_le_one₀ hρ0.le hρ1)
  · exact (l38_smallDamping_pos hq _).le

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem clean_smallListMass_eq : smallListMass 𝒢 J ℓ =
    (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹) *
      ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹ := by
  unfold smallListMass
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun g _ => by rw [pow_add, mul_inv]

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
theorem clean_bigListMass_nonneg {q : ℝ} {n : ℕ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (xb : LabelList 𝒢.big J ℓ) :
    0 ≤ bigListMass 𝒢 q n xb :=
  Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g _ (xb g i).2

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
theorem clean_memMass_nonneg {q : ℝ} {n : ℕ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (mem : (g : B) → Mem 𝒢 Bc g) :
    0 ≤ memMass 𝒢 q n mem := by
  refine Finset.prod_nonneg fun g _ => ?_
  unfold Graph.finiteMemoryPointMass Graph.factorialMemoryPointMass
  exact div_nonneg (Finset.prod_nonneg fun i _ => hν g _ ((mem g).2 i).1.2) (Nat.cast_nonneg _)

omit [Fintype B] [DecidableEq B] in
/-- **The total weight of the small states with given shared labels** (eq:small-map-norm)
[S-02:0943–0951]: "the multiplier relative to the original small state measure in group `g` is
bounded by `sup_{z ≥ M} q^{z-M} (z-M+ℓ)_ℓ / V_g^ℓ`, a constant depending only on `q, ℓ, v₋`".
Here the bound is `∏_{g ∈ 𝒮} groupConst v₋ q T` for every `T ≥ ℓ` (Lemma 3.4 for the small
groups). -/
theorem clean_sum_smallW_le {q vMinus : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hv : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g)) {T : ℕ} (hT : 0 < T)
    (hℓT : ℓ ≤ T) (a : CleanShared 𝒢 J) (y : ResVec (smallPrimes 𝒢)) :
    ∑ xs : LabelList 𝒢.small J ℓ, cleanSmallW q a y xs ≤
      ∏ _g : S, Schur.groupConst vMinus q T := by
  by_cases hex : ∃ xs₀ : LabelList 𝒢.small J ℓ, cleanCls xs₀ = a
  · obtain ⟨xs₀, hxs₀⟩ := hex
    have e : ∀ xs : LabelList 𝒢.small J ℓ,
        cleanSmallW q a y xs = edgeAbsSmallW 𝒢 q y xs₀ xs := by
      intro xs
      unfold cleanSmallW edgeAbsSmallW
      refine ite_congr_of_iff ⟨?_, ?_⟩ rfl rfl
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun g i => congrFun (congrFun (h2.trans hxs₀.symm) g) i⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (funext fun g => funext fun i => h2 g i).trans hxs₀⟩
    rw [Finset.sum_congr rfl fun xs _ => e xs]
    exact sum_edgeAbsSmallW_le 𝒢 hq0 hq1 hv hVS hT hℓT y xs₀
  · have e : ∀ xs : LabelList 𝒢.small J ℓ, cleanSmallW q a y xs = 0 := fun xs =>
      if_neg fun h => hex ⟨xs, h.2⟩
    rw [Finset.sum_congr rfl fun xs _ => e xs, Finset.sum_const_zero]
    exact Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _)

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- The measure of `ℋ` times the square of the source factor is dominated by the measure of the
remaining coordinates times the weight of the small list. -/
theorem clean_weight_source_le {q ρ : ℝ} {n : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (w : CleanW 𝒢 J ℓ Bc) (xs : LabelList 𝒢.small J ℓ) (a : CleanShared 𝒢 J) :
    (if cleanCls xs = a then
        memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 else 0) ≤
      cleanYW 𝒢 J q n w.1 * bigListMass 𝒢 q n w.2 * cleanSmallW q a w.1.1 xs := by
  have hh : 0 ≤ haarMass (smallPrimes 𝒢) := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcV : 0 ≤ ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹ :=
    Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
  have hcℓ : 0 ≤ ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹ :=
    Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
  have hb : 0 ≤ bigListMass 𝒢 q n w.2 := clean_bigListMass_nonneg hν _
  have hc : 0 ≤ memMass 𝒢 q n w.1.2 := clean_memMass_nonneg hν _
  have hR0 : 0 ≤ cleanYW 𝒢 J q n w.1 * bigListMass 𝒢 q n w.2 * cleanSmallW q a w.1.1 xs :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcV hh) hc) hb) (cleanSmallW_nonneg hq0 _ _ _)
  by_cases ha : cleanCls xs = a
  · rw [if_pos ha]
    by_cases hss : IsSmallState 𝒢 w.1.1 xs
    · have ew : memWeight 𝒢 q n (cleanMk w xs) =
          haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * bigListMass 𝒢 q n w.2 *
            memMass 𝒢 q n w.1.2 := if_pos hss
      have es : cleanSmallW q a w.1.1 xs =
          (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
            smallDamping 𝒢 J ℓ q w.1.1 := if_pos ⟨hss, ha⟩
      have hd1 : smallDamping 𝒢 J ℓ q w.1.1 ≤ 1 := l38_smallDamping_le_one hq0 hq1.le hss
      have hd0 : 0 ≤ smallDamping 𝒢 J ℓ q w.1.1 := (l38_smallDamping_pos hq0 w.1.1).le
      have hu1 : cleanU q ρ (cleanMk w xs) ≤ smallDamping 𝒢 J ℓ q w.1.1 :=
        cleanU_le hq0 hρ0 hρ1 (cleanMk w xs)
      have hu : cleanU q ρ (cleanMk w xs) ^ 2 ≤ smallDamping 𝒢 J ℓ q w.1.1 := by
        rw [sq]
        exact (mul_le_mul hu1 (hu1.trans hd1) (cleanU_nonneg hq0 hρ0 _) hd0).trans
          (le_of_eq (mul_one _))
      rw [ew, es, clean_smallListMass_eq]
      unfold cleanYW
      calc haarMass (smallPrimes 𝒢) *
            ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹) *
              ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
            bigListMass 𝒢 q n w.2 * memMass 𝒢 q n w.1.2 * cleanU q ρ (cleanMk w xs) ^ 2
          ≤ haarMass (smallPrimes 𝒢) *
            ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹) *
              ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
            bigListMass 𝒢 q n w.2 * memMass 𝒢 q n w.1.2 * smallDamping 𝒢 J ℓ q w.1.1 :=
            mul_le_mul_of_nonneg_left hu
              (mul_nonneg (mul_nonneg (mul_nonneg hh (mul_nonneg hcV hcℓ)) hb) hc)
        _ = (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹) *
              haarMass (smallPrimes 𝒢) * memMass 𝒢 q n w.1.2 * bigListMass 𝒢 q n w.2 *
              ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
                smallDamping 𝒢 J ℓ q w.1.1) := by ring
    · have ew : memWeight 𝒢 q n (cleanMk w xs) = 0 := if_neg hss
      rw [ew, zero_mul]
      exact hR0
  · rw [if_neg ha]
    exact hR0

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- The measure of the remaining coordinates times the weight of the small list in the
conditioning map is dominated by the measure of `ℋ`. -/
theorem clean_weight_target_le {q ρ : ℝ} {n : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (w : CleanW 𝒢 J ℓ Bc) (xs : LabelList 𝒢.small J ℓ) (a : CleanShared 𝒢 J) :
    cleanYW 𝒢 J q n w.1 * bigListMass 𝒢 q n w.2 *
        (cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2) ≤
      (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) := by
  have hh : 0 ≤ haarMass (smallPrimes 𝒢) := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcV : 0 ≤ ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹ :=
    Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
  have hcℓ : 0 ≤ ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹ :=
    Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
  have hb : 0 ≤ bigListMass 𝒢 q n w.2 := clean_bigListMass_nonneg hν _
  have hc : 0 ≤ memMass 𝒢 q n w.1.2 := clean_memMass_nonneg hν _
  by_cases hcnd : IsSmallState 𝒢 w.1.1 xs ∧ cleanCls xs = a
  · obtain ⟨hss, ha⟩ := hcnd
    have ew : memWeight 𝒢 q n (cleanMk w xs) =
        haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * bigListMass 𝒢 q n w.2 *
          memMass 𝒢 q n w.1.2 := if_pos hss
    have es : cleanSmallW q a w.1.1 xs =
        (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          smallDamping 𝒢 J ℓ q w.1.1 := if_pos ⟨hss, ha⟩
    have hd1 : smallDamping 𝒢 J ℓ q w.1.1 ≤ 1 := l38_smallDamping_le_one hq0 hq1.le hss
    have hr0 : 0 ≤ ρ ^ cleanMemZeros w.1.2 := pow_nonneg hρ0.le _
    have hr1 : ρ ^ cleanMemZeros w.1.2 ≤ 1 := pow_le_one₀ hρ0.le hρ1
    have hdr : smallDamping 𝒢 J ℓ q w.1.1 * ρ ^ cleanMemZeros w.1.2 ≤ 1 :=
      (mul_le_mul hd1 hr1 hr0 zero_le_one).trans (le_of_eq (one_mul 1))
    rw [if_pos ha, ew, es, clean_smallListMass_eq]
    unfold cleanYW
    calc (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹) *
            haarMass (smallPrimes 𝒢) * memMass 𝒢 q n w.1.2 * bigListMass 𝒢 q n w.2 *
            ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
              smallDamping 𝒢 J ℓ q w.1.1 * ρ ^ cleanMemZeros w.1.2)
        = haarMass (smallPrimes 𝒢) *
            ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹) *
              ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
            bigListMass 𝒢 q n w.2 * memMass 𝒢 q n w.1.2 *
            (smallDamping 𝒢 J ℓ q w.1.1 * ρ ^ cleanMemZeros w.1.2) := by ring
      _ ≤ haarMass (smallPrimes 𝒢) *
            ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹) *
              ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
            bigListMass 𝒢 q n w.2 * memMass 𝒢 q n w.1.2 * 1 :=
          mul_le_mul_of_nonneg_left hdr
            (mul_nonneg (mul_nonneg (mul_nonneg hh (mul_nonneg hcV hcℓ)) hb) hc)
      _ = haarMass (smallPrimes 𝒢) *
            ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ J)⁻¹) *
              ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
            bigListMass 𝒢 q n w.2 * memMass 𝒢 q n w.1.2 := mul_one _
  · have es : cleanSmallW q a w.1.1 xs = 0 := if_neg hcnd
    rw [es, zero_mul, mul_zero]
    split_ifs
    · exact memWeight_nonneg 𝒢 q n hν _
    · exact le_rfl

open _root_.Classical in
/-- **(eq:small-map-norm) and Cauchy's inequality for (eq:clean-conditioned-form)**
[S-02:0937–0963, 1013–1017]: if every operator `𝒯_d` between the conditioning maps has norm at
most `C_T`, and the small states with given shared labels have total weight at most `K_𝒮`, then
the conditioned operator has norm at most `K_𝒮 C_T` on `L²` of the measure of `ℋ`. -/
theorem cleanCondOp_bound {q ρ : ℝ} {n : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) {KS CT : ℝ}
    (hKS0 : 0 ≤ KS)
    (hKS : ∀ (a : CleanShared 𝒢 J) (y : ResVec (smallPrimes 𝒢)),
      ∑ xs : LabelList 𝒢.small J ℓ, cleanSmallW q a y xs ≤ KS)
    (hCT : 0 ≤ CT) (𝒯 : ℕ → (CleanW 𝒢 J ℓ Bc → ℂ) → (CleanW 𝒢 J ℓ Bc → ℂ))
    (h𝒯 : ∀ (d : ℕ) (H : CleanW 𝒢 J ℓ Bc → ℂ),
      wNorm (fun w : CleanW 𝒢 J ℓ Bc => cleanYW 𝒢 J q n w.1 * bigListMass 𝒢 q n w.2) (𝒯 d H) ≤
        CT * wNorm (fun w : CleanW 𝒢 J ℓ Bc => cleanYW 𝒢 J q n w.1 * bigListMass 𝒢 q n w.2) H)
    (G : MState 𝒢 J ℓ Bc → ℂ) :
    wNorm (memWeight 𝒢 q n) (cleanCondOp q ρ 𝒯 G) ≤ KS * CT * wNorm (memWeight 𝒢 q n) G := by
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀ : CleanW 𝒢 J ℓ Bc → ℝ,
      m₀ = fun w => cleanYW 𝒢 J q n w.1 * bigListMass 𝒢 q n w.2 := ⟨_, rfl⟩
  rw [← hm₀def] at h𝒯
  have hm₀v : ∀ w : CleanW 𝒢 J ℓ Bc,
      m₀ w = cleanYW 𝒢 J q n w.1 * bigListMass 𝒢 q n w.2 := fun w => by rw [hm₀def]
  have hm₀ : ∀ w : CleanW 𝒢 J ℓ Bc, 0 ≤ m₀ w := by
    intro w
    rw [hm₀v]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg fun g _ =>
        inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _))
      (inv_nonneg.mpr (Nat.cast_nonneg _))) (clean_memMass_nonneg hν _))
      (clean_bigListMass_nonneg hν _)
  have hmw : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 q n s := memWeight_nonneg 𝒢 q n hν
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : CleanShared 𝒢 J → CleanW 𝒢 J ℓ Bc → ℂ,
      Φ = fun a => 𝒯 (cleanD a) (cleanQ q ρ a G) := ⟨_, rfl⟩
  have hΦb : ∀ a : CleanShared 𝒢 J,
      wNormSq m₀ (Φ a) ≤ CT ^ 2 * wNormSq m₀ (cleanQ q ρ a G) := by
    intro a
    have h := h𝒯 (cleanD a) (cleanQ q ρ a G)
    have e : Φ a = 𝒯 (cleanD a) (cleanQ q ρ a G) := by rw [hΦ]
    rw [e, ← wNorm_sq hm₀, ← wNorm_sq hm₀, ← mul_pow]
    exact pow_le_pow_left₀ (wNorm_nonneg _ _) h 2
  have hF : ∀ (w : CleanW 𝒢 J ℓ Bc) (xs : LabelList 𝒢.small J ℓ),
      cleanCondOp q ρ 𝒯 G (cleanMk w xs) =
        ((cleanU q ρ (cleanMk w xs) : ℝ) : ℂ) * Φ (cleanCls xs) w := by
    intro w xs
    rw [hΦ]
    rfl
  -- the source side
  have hsrc : ∀ (w : CleanW 𝒢 J ℓ Bc) (a : CleanShared 𝒢 J),
      ∑ xs : LabelList 𝒢.small J ℓ, (if cleanCls xs = a then
        memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 else 0) ≤
        KS * m₀ w := by
    intro w a
    calc ∑ xs : LabelList 𝒢.small J ℓ, (if cleanCls xs = a then
          memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 else 0)
        ≤ ∑ xs : LabelList 𝒢.small J ℓ, m₀ w * cleanSmallW q a w.1.1 xs :=
          Finset.sum_le_sum fun xs _ => by
            rw [hm₀v]
            exact clean_weight_source_le hq0 hq1 hρ0 hρ1 hν w xs a
      _ = m₀ w * ∑ xs : LabelList 𝒢.small J ℓ, cleanSmallW q a w.1.1 xs :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ m₀ w * KS := mul_le_mul_of_nonneg_left (hKS a w.1.1) (hm₀ w)
      _ = KS * m₀ w := mul_comm _ _
  have hB : wNormSq (memWeight 𝒢 q n) (cleanCondOp q ρ 𝒯 G) ≤
      KS * ∑ a : CleanShared 𝒢 J, wNormSq m₀ (Φ a) := by
    have h1 : wNormSq (memWeight 𝒢 q n) (cleanCondOp q ρ 𝒯 G) =
        ∑ w : CleanW 𝒢 J ℓ Bc, ∑ xs : LabelList 𝒢.small J ℓ, ∑ a : CleanShared 𝒢 J,
          (if cleanCls xs = a then
            memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 else 0) *
            ‖Φ a w‖ ^ 2 := by
      unfold wNormSq
      rw [clean_sum_state]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun xs _ => ?_
      have h2 : ∑ a : CleanShared 𝒢 J, (if cleanCls xs = a then
            memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 else 0) *
            ‖Φ a w‖ ^ 2 =
          memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 *
            ‖Φ (cleanCls xs) w‖ ^ 2 :=
        (Finset.sum_eq_single_of_mem
          (f := fun a : CleanShared 𝒢 J => (if cleanCls xs = a then
            memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 else 0) *
            ‖Φ a w‖ ^ 2)
          (cleanCls xs) (Finset.mem_univ _)
          (fun a _ hne => by
            show (if cleanCls xs = a then
              memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 else 0) *
              ‖Φ a w‖ ^ 2 = 0
            rw [if_neg (Ne.symm hne), zero_mul])).trans
          (congrArg (fun z => z * ‖Φ (cleanCls xs) w‖ ^ 2) (if_pos rfl))
      rw [h2, hF w xs, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [h1]
    calc ∑ w : CleanW 𝒢 J ℓ Bc, ∑ xs : LabelList 𝒢.small J ℓ, ∑ a : CleanShared 𝒢 J,
          (if cleanCls xs = a then
            memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 else 0) *
            ‖Φ a w‖ ^ 2
        = ∑ w : CleanW 𝒢 J ℓ Bc, ∑ a : CleanShared 𝒢 J,
            (∑ xs : LabelList 𝒢.small J ℓ, (if cleanCls xs = a then
              memWeight 𝒢 q n (cleanMk w xs) * cleanU q ρ (cleanMk w xs) ^ 2 else 0)) *
              ‖Φ a w‖ ^ 2 := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ w : CleanW 𝒢 J ℓ Bc, ∑ a : CleanShared 𝒢 J, KS * m₀ w * ‖Φ a w‖ ^ 2 :=
          Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_right (hsrc w a) (sq_nonneg _)
      _ = KS * ∑ a : CleanShared 𝒢 J, wNormSq m₀ (Φ a) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [show wNormSq m₀ (Φ a) = ∑ w : CleanW 𝒢 J ℓ Bc, m₀ w * ‖Φ a w‖ ^ 2 from rfl,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => mul_assoc _ _ _
  -- the target side
  have hcs : ∀ (a : CleanShared 𝒢 J) (w : CleanW 𝒢 J ℓ Bc),
      m₀ w * ‖cleanQ q ρ a G w‖ ^ 2 ≤
        KS * ∑ xs : LabelList 𝒢.small J ℓ,
          (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) *
            ‖G (cleanMk w xs)‖ ^ 2 := by
    intro a w
    have hc0 : ∀ xs : LabelList 𝒢.small J ℓ,
        0 ≤ cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2 := fun xs =>
      mul_nonneg (cleanSmallW_nonneg hq0 a _ xs) (pow_nonneg hρ0.le _)
    have h1 : ‖cleanQ q ρ a G w‖ ≤ ∑ xs : LabelList 𝒢.small J ℓ,
        (cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2) * ‖G (cleanMk w xs)‖ := by
      unfold cleanQ
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun xs _ => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 xs)]
    have h2 := Graph.weighted_kernel_row_sq
      (fun xs : LabelList 𝒢.small J ℓ => cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2)
      (fun _ => (1 : ℝ)) (fun xs => ‖G (cleanMk w xs)‖) hc0 (fun _ => one_pos)
    have h3 : ∑ xs : LabelList 𝒢.small J ℓ,
        (cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2) * 1 ≤ KS :=
      (Finset.sum_le_sum fun xs _ => by
        rw [mul_one]
        exact mul_le_of_le_one_right (cleanSmallW_nonneg hq0 a _ xs)
          (pow_le_one₀ hρ0.le hρ1)).trans (hKS a w.1.1)
    have h5 : 0 ≤ ∑ xs : LabelList 𝒢.small J ℓ,
        (cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2) * ‖G (cleanMk w xs)‖ ^ 2 / 1 :=
      Finset.sum_nonneg fun xs _ =>
        div_nonneg (mul_nonneg (hc0 xs) (sq_nonneg _)) zero_le_one
    have h4 : ‖cleanQ q ρ a G w‖ ^ 2 ≤ KS * ∑ xs : LabelList 𝒢.small J ℓ,
        (cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2) * ‖G (cleanMk w xs)‖ ^ 2 / 1 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
        (h2.trans (mul_le_mul_of_nonneg_right h3 h5))
    calc m₀ w * ‖cleanQ q ρ a G w‖ ^ 2
        ≤ m₀ w * (KS * ∑ xs : LabelList 𝒢.small J ℓ,
            (cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2) *
              ‖G (cleanMk w xs)‖ ^ 2 / 1) := mul_le_mul_of_nonneg_left h4 (hm₀ w)
      _ = KS * ∑ xs : LabelList 𝒢.small J ℓ,
            (m₀ w * (cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2)) *
              ‖G (cleanMk w xs)‖ ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun xs _ => ?_
          rw [div_one]
          ring
      _ ≤ KS * ∑ xs : LabelList 𝒢.small J ℓ,
            (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) *
              ‖G (cleanMk w xs)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun xs _ =>
            mul_le_mul_of_nonneg_right (by
              rw [hm₀v]
              exact clean_weight_target_le hq0 hq1 hρ0 hρ1 hν w xs a) (sq_nonneg _)) hKS0
  have hC : ∑ a : CleanShared 𝒢 J, wNormSq m₀ (cleanQ q ρ a G) ≤
      KS * wNormSq (memWeight 𝒢 q n) G := by
    have e1 : wNormSq (memWeight 𝒢 q n) G =
        ∑ w : CleanW 𝒢 J ℓ Bc, ∑ xs : LabelList 𝒢.small J ℓ,
          memWeight 𝒢 q n (cleanMk w xs) * ‖G (cleanMk w xs)‖ ^ 2 := by
      unfold wNormSq
      exact clean_sum_state _
    have e2 : ∀ (w : CleanW 𝒢 J ℓ Bc) (xs : LabelList 𝒢.small J ℓ),
        ∑ a : CleanShared 𝒢 J,
            (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) *
              ‖G (cleanMk w xs)‖ ^ 2 =
          memWeight 𝒢 q n (cleanMk w xs) * ‖G (cleanMk w xs)‖ ^ 2 := by
      intro w xs
      exact (Finset.sum_eq_single_of_mem
        (f := fun a : CleanShared 𝒢 J =>
          (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) *
            ‖G (cleanMk w xs)‖ ^ 2)
        (cleanCls xs) (Finset.mem_univ _)
        (fun a _ hne => by
          show (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) *
            ‖G (cleanMk w xs)‖ ^ 2 = 0
          rw [if_neg (Ne.symm hne), zero_mul])).trans
        (congrArg (fun z => z * ‖G (cleanMk w xs)‖ ^ 2) (if_pos rfl))
    have e3 : ∑ a : CleanShared 𝒢 J, ∑ w : CleanW 𝒢 J ℓ Bc,
          KS * ∑ xs : LabelList 𝒢.small J ℓ,
            (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) *
              ‖G (cleanMk w xs)‖ ^ 2 =
        KS * ∑ a : CleanShared 𝒢 J, ∑ w : CleanW 𝒢 J ℓ Bc,
          ∑ xs : LabelList 𝒢.small J ℓ,
            (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) *
              ‖G (cleanMk w xs)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    calc ∑ a : CleanShared 𝒢 J, wNormSq m₀ (cleanQ q ρ a G)
        = ∑ a : CleanShared 𝒢 J, ∑ w : CleanW 𝒢 J ℓ Bc, m₀ w * ‖cleanQ q ρ a G w‖ ^ 2 := rfl
      _ ≤ ∑ a : CleanShared 𝒢 J, ∑ w : CleanW 𝒢 J ℓ Bc,
            KS * ∑ xs : LabelList 𝒢.small J ℓ,
              (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) *
                ‖G (cleanMk w xs)‖ ^ 2 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun w _ => hcs a w
      _ = KS * wNormSq (memWeight 𝒢 q n) G := by
          rw [e3, e1, clean_sum_comm3 (fun (a : CleanShared 𝒢 J) (w : CleanW 𝒢 J ℓ Bc)
            (xs : LabelList 𝒢.small J ℓ) =>
              (if cleanCls xs = a then memWeight 𝒢 q n (cleanMk w xs) else 0) *
                ‖G (cleanMk w xs)‖ ^ 2), Finset.sum_comm]
          exact congrArg (fun z => KS * z)
            (Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun xs _ => e2 w xs)
  refine wNorm_le_of_wNormSq_le (mul_nonneg hKS0 hCT) ?_
  calc wNormSq (memWeight 𝒢 q n) (cleanCondOp q ρ 𝒯 G)
      ≤ KS * ∑ a : CleanShared 𝒢 J, wNormSq m₀ (Φ a) := hB
    _ ≤ KS * ∑ a : CleanShared 𝒢 J, CT ^ 2 * wNormSq m₀ (cleanQ q ρ a G) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hΦb a) hKS0
    _ = KS * CT ^ 2 * ∑ a : CleanShared 𝒢 J, wNormSq m₀ (cleanQ q ρ a G) := by
        rw [← Finset.mul_sum, mul_assoc]
    _ ≤ KS * CT ^ 2 * (KS * wNormSq (memWeight 𝒢 q n) G) :=
        mul_le_mul_of_nonneg_left hC (mul_nonneg hKS0 (sq_nonneg _))
    _ = (KS * CT) ^ 2 * wNormSq (memWeight 𝒢 q n) G := by ring

end Cond

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
