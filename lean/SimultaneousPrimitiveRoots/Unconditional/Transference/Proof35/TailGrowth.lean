module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.TailAbsSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Memory truncation: the histories which violate the restriction have many ghost births

Source: `verification/stage7-sources/S-02.tex`, lines 796–811 (`[S-02:0796–0811]`).

"We now restrict the total memory size to `B = ⌈L²⌉` before and after every operation … At most
`(ℓ + m)|ℬ|N` particles can be supplied by stores. Thus a path violating this restriction has at
least `B - O((ℓ + m)sN)` ghost births. Multiply every ghost birth by two in the absolute path sum
and use the preceding bounds. The total omitted mass, even with the distinct-birth indicator, is
at most `2^{-B + O((ℓ + m)sN)} L^{O(N)}`."

* `History.condG`, `History.condE`, `History.FitsUpTo`, `History.Fits` — the total memory of a
  history is at most a bound `b` before and after every operation: these are the conditions of
  the coefficients of the visit and edge operations at the cutoff `b`
  (`History.fits_of_weight_ne_zero`: a history with nonzero weight fits its own cutoff).
* `History.memTotal_visitState_le` — the memory at the visit `i` plus the ghost births from the
  visit `i` on is at most the number of all ghost births plus `i (J + ℓ)|ℬ|`: the memory grows
  only by ghost births and by stores, and an edge stores at most `M = J + ℓ` particles in each
  big group. (The paper's bound `ℓ + m` per group holds for the choices with nonvanishing
  coefficient; the cruder bound `M` holds for all choices and serves as well, `J` being fixed.)
* `History.fits_of_births_le` — a history with `#ghost births + N M |ℬ| ≤ b` fits the bound `b`.
* `tail_sum_notFits_le` — **the total omitted mass**: the sum of the moduli of the weights of the
  histories which do not fit `b` is at most `2^{N M |ℬ|} / 2^{b+1} · ‖𝟏_∅‖² R_g^{N+1} R_e^N`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- A sum over the visits from the visit `i` on: the visit `i` and the later visits. -/
theorem tail_fut_split {n : ℕ} (b : Fin (n + 1) → ℕ) (i : ℕ) (hi : i < n + 1) :
    (∑ i' : Fin (n + 1), if i ≤ i'.val then b i' else 0) =
      b ⟨i, hi⟩ + ∑ i' : Fin (n + 1), if i + 1 ≤ i'.val then b i' else 0 := by
  have hpt : ∀ i' : Fin (n + 1), (if i ≤ i'.val then b i' else 0) =
      (if i' = ⟨i, hi⟩ then b i' else 0) + (if i + 1 ≤ i'.val then b i' else 0) := by
    intro i'
    by_cases h1 : i'.val = i
    · have e : i' = ⟨i, hi⟩ := Fin.ext h1
      have h4 : ¬i + 1 ≤ i'.val := by omega
      rw [if_pos (le_of_eq h1.symm), if_pos e, if_neg h4, Nat.add_zero]
    · have e : ¬i' = ⟨i, hi⟩ := fun h => h1 (congrArg Fin.val h)
      by_cases h3 : i ≤ i'.val
      · have h4 : i + 1 ≤ i'.val := by omega
        rw [if_pos h3, if_neg e, if_pos h4, Nat.zero_add]
      · have h4 : ¬i + 1 ≤ i'.val := by omega
        rw [if_neg h3, if_neg e, if_neg h4, Nat.add_zero]
  have hsingle : (∑ i' : Fin (n + 1), if i' = ⟨i, hi⟩ then b i' else 0) = b ⟨i, hi⟩ :=
    (Finset.sum_eq_single_of_mem (f := fun i' : Fin (n + 1) => if i' = ⟨i, hi⟩ then b i' else 0)
      ⟨i, hi⟩ (Finset.mem_univ _) (fun j _ hj => if_neg hj)).trans (if_pos rfl)
  rw [Finset.sum_congr rfl fun i' _ => hpt i', Finset.sum_add_distrib, hsingle]

section Growth

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The memory of a list has at most as many particles as the list. -/
theorem tail_memOfList_size_le {g : B} (l : List (Particle 𝒢 g)) :
    (memOfList (Bc := Bc) l).1.val ≤ l.length := by
  by_cases h : l.length ≤ Bc
  · exact (memOfList_size h).le
  · rw [memOfList_of_not_le h]
    exact Nat.zero_le _

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The surviving particles of a visit operation are at most as many as the old particles. -/
theorem tail_ghostSurvivors_length_le {g : B} (z : Mem 𝒢 Bc g) (A : Finset (Fin Bc)) :
    (ghostSurvivors z A).length ≤ z.1.val := by
  unfold ghostSurvivors
  rw [List.length_filterMap_eq_countP]
  refine (List.countP_mono_left fun j _ hj => ?_).trans (l38_countP_isSome_memAt z).le
  have hj' : (if j ∈ A then none else memAt z j).isSome = true := hj
  show (memAt z j).isSome = true
  by_cases hc : j ∈ A
  · rw [if_pos hc] at hj'
    exact absurd hj' Bool.false_ne_true
  · rw [if_neg hc] at hj'
    exact hj'

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The new memory of a visit operation has at most `ghostNewSize` particles. -/
theorem tail_ghostNewMem_size_le {g : B} (z : Mem 𝒢 Bc g)
    (c : Finset (Fin Bc) × Batch 𝒢 Bc g) : (ghostNewMem z c).1.val ≤ ghostNewSize z c := by
  have hlen : (ghostSurvivors z c.1 ++ batchParticles c.2).length = ghostNewSize z c := by
    unfold ghostNewSize batchParticles
    rw [List.length_append, List.length_ofFn]
  unfold ghostNewMem
  rw [← hlen]
  exact tail_memOfList_size_le _

omit [DecidableEq S] [DecidableEq B] in
/-- A visit operation adds at most its ghost births to the total memory. -/
theorem tail_sum_ghostNewSize_le (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) :
    (∑ g, ghostNewSize (s.mem g) (c g)) ≤ memTotal s + ghostBirthCount c := by
  unfold memTotal ghostBirthCount
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun g _ => Nat.add_le_add_right (tail_ghostSurvivors_length_le _ _) _

omit [DecidableEq S] [DecidableEq B] in
theorem tail_memTotal_ghostTgt_le (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) :
    memTotal (ghostTgt s c) ≤ ∑ g, ghostNewSize (s.mem g) (c g) := by
  unfold memTotal
  exact Finset.sum_le_sum fun g _ => tail_ghostNewMem_size_le _ _

omit [DecidableEq S] [DecidableEq B] in
/-- **"At most `(ℓ + m)|ℬ|N` particles can be supplied by stores"** [S-02:0801–0802], one edge,
with the bound `M = J + ℓ` for the number of stored slots of a group: an edge adds at most
`M|ℬ|` particles to the total memory. -/
theorem tail_sum_edgeNewList_le (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) :
    (∑ g, (edgeNewList D i s c g).length) ≤ memTotal s + (J + ℓ) * Fintype.card B := by
  have h1 : ∀ g, (edgeNewList D i s c g).length ≤ (s.mem g).1.val + (J + ℓ) := by
    intro g
    rw [edgeNewList_eq_abs]
    refine (edgeAbsNewList_length_le _ _ _ _ _).trans (Nat.add_le_add_left ?_ _)
    exact (Finset.card_le_univ _).trans (card_slot J ℓ).le
  calc (∑ g, (edgeNewList D i s c g).length)
      ≤ ∑ g : B, ((s.mem g).1.val + (J + ℓ)) := Finset.sum_le_sum fun g _ => h1 g
    _ = memTotal s + (J + ℓ) * Fintype.card B := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Nat.mul_comm (Fintype.card B) (J + ℓ)]
        rfl

omit [DecidableEq S] [DecidableEq B] in
theorem tail_memTotal_edgeFullTgt_le (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (ξ : EdgeFullChoice D Bc) :
    memTotal (edgeFullTgt D i s ξ) ≤
      ∑ g, (edgeNewList D i (s.permLists ξ.1) ξ.2.1 g).length := by
  show ∑ g, (memOfList (Bc := Bc) (edgeNewList D i (s.permLists ξ.1) ξ.2.1 g)).1.val ≤ _
  exact Finset.sum_le_sum fun g _ => tail_memOfList_size_le _

/-! ### Histories within a bound -/

variable {D : MemData 𝒢 J ℓ N}

/-- **The condition of the visit operation `G_i` along a history, for the bound `b`**: the total
memory is at most `b` before and after the operation (eq:memory-truncation). -/
def History.condG (h : History D Bc) (b : ℕ) (i : Fin (D.n + 1)) : Prop :=
  memTotal (h.visitState i.val) ≤ b ∧
    (∑ g, ghostNewSize ((h.visitState i.val).mem g) (h.ghost i g)) ≤ b

/-- **The condition of the edge operation `ℰ_i` along a history, for the bound `b`**: the total
memory is at most `b` before and after the operation. -/
def History.condE (h : History D Bc) (b : ℕ) (i : Fin D.n) : Prop :=
  memTotal (h.afterGhost i.castSucc) ≤ b ∧
    (∑ g, (edgeNewList D i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1)
      (h.edge i).2.1 g).length) ≤ b

/-- The conditions of all operations before the visit `i`. -/
def History.FitsUpTo (h : History D Bc) (b : ℕ) : ℕ → Prop
  | 0 => True
  | i + 1 => History.FitsUpTo h b i ∧
      ∀ hi : i < D.n, h.condG b (Fin.castSucc ⟨i, hi⟩) ∧ h.condE b ⟨i, hi⟩

/-- **A history fits the bound `b`** (eq:memory-truncation) [S-02:0797–0801]: "the total memory
size [is at most `b`] before and after every operation". -/
def History.Fits (h : History D Bc) (b : ℕ) : Prop :=
  h.FitsUpTo b D.n ∧ h.condG b (Fin.last D.n)

omit [DecidableEq S] [DecidableEq B] in
theorem History.fits_of_forall (h : History D Bc) (b : ℕ)
    (hG : ∀ i : Fin (D.n + 1), h.condG b i) (hE : ∀ i : Fin D.n, h.condE b i) : h.Fits b := by
  have hup : ∀ i : ℕ, h.FitsUpTo b i := by
    intro i
    induction i with
    | zero => exact trivial
    | succ i ih => exact ⟨ih, fun hi => ⟨hG _, hE _⟩⟩
  exact ⟨hup D.n, hG _⟩

/-- **A history with nonvanishing weight fits its own cutoff**: the coefficients of the
operations contain the projections onto total memory size at most the cutoff. -/
theorem History.fits_of_weight_ne_zero (h : History D Bc) (θ : ℝ) (hw : h.weight θ ≠ 0) :
    h.Fits Bc := by
  unfold History.weight at hw
  have h1 := left_ne_zero_of_mul hw
  have h2 := right_ne_zero_of_mul hw
  have h3 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h1)
  have hGc : ∀ (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc),
      ((ghostCoef D i s c : ℝ) : ℂ) ≠ 0 →
        memTotal s ≤ Bc ∧ (∑ g, ghostNewSize (s.mem g) (c g)) ≤ Bc := by
    intro i s c hne
    by_contra hcon
    refine hne ?_
    have hz : ghostCoef D i s c = 0 := by
      unfold ghostCoef
      exact if_neg hcon
    rw [hz, Complex.ofReal_zero]
  refine h.fits_of_forall Bc (fun i => ?_) (fun i => ?_)
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hGc D.n _ _ (left_ne_zero_of_mul h2)
    · exact hGc j.val _ _ (left_ne_zero_of_mul (h3 j (Finset.mem_univ j)))
  · have he := right_ne_zero_of_mul (h3 i (Finset.mem_univ i))
    have hcond : EdgeAbsCond D i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1)
        (h.edge i).2.1 := by
      by_contra hcon
      refine he ?_
      unfold edgeFullCoef
      rw [edgeCoef_of_not_cond D θ i.val _ _ hcon, mul_zero, mul_zero, zero_mul]
    obtain ⟨hc1, hc2, _⟩ := hcond
    exact ⟨hc1, hc2⟩

/-- The ghost births of a history from the visit `i` on. -/
def History.futBirths (h : History D Bc) (i : ℕ) : ℕ :=
  ∑ i' : Fin (D.n + 1), if i ≤ i'.val then ghostBirthCount (h.ghost i') else 0

omit [DecidableEq S] [DecidableEq B] in
/-- **The memory grows only by ghost births and by stores** [S-02:0801–0803]: the total memory at
the visit `i` plus the ghost births from the visit `i` on is at most the number of all ghost
births plus `i κ`, where `κ ≥ M|ℬ|` bounds the number of particles which an edge can store. -/
theorem History.memTotal_visitState_le (h : History D Bc) {κ : ℕ}
    (hκ : (J + ℓ) * Fintype.card B ≤ κ) :
    ∀ i : ℕ, i ≤ D.n → memTotal (h.visitState i) + h.futBirths i ≤ h.ghostBirthTotal + i * κ := by
  intro i
  induction i with
  | zero =>
    intro _
    have e1 : memTotal (h.visitState 0) = 0 := Finset.sum_eq_zero fun g _ => rfl
    have e2 : h.futBirths 0 = h.ghostBirthTotal :=
      Finset.sum_congr rfl fun i' _ => if_pos (Nat.zero_le _)
    rw [e1, e2]
    omega
  | succ i ih =>
    intro hi
    have hi' : i < D.n := hi
    have hprev := ih (Nat.le_of_succ_le hi)
    have hvs : h.visitState (i + 1) =
        edgeFullTgt D i (h.afterGhost (Fin.castSucc ⟨i, hi'⟩)) (h.edge ⟨i, hi'⟩) :=
      History.visitState_succ h ⟨i, hi'⟩
    have a1 : memTotal (h.visitState (i + 1)) ≤
        ∑ g, (edgeNewList D i ((h.afterGhost (Fin.castSucc ⟨i, hi'⟩)).permLists
          (h.edge ⟨i, hi'⟩).1) (h.edge ⟨i, hi'⟩).2.1 g).length := by
      rw [hvs]
      exact tail_memTotal_edgeFullTgt_le D i _ _
    have a2 : (∑ g, (edgeNewList D i ((h.afterGhost (Fin.castSucc ⟨i, hi'⟩)).permLists
          (h.edge ⟨i, hi'⟩).1) (h.edge ⟨i, hi'⟩).2.1 g).length) ≤
        memTotal (h.afterGhost (Fin.castSucc ⟨i, hi'⟩)) + (J + ℓ) * Fintype.card B :=
      tail_sum_edgeNewList_le D i _ _
    have a3 : memTotal (h.afterGhost (Fin.castSucc ⟨i, hi'⟩)) ≤
        ∑ g, ghostNewSize ((h.visitState i).mem g) (h.ghost (Fin.castSucc ⟨i, hi'⟩) g) :=
      tail_memTotal_ghostTgt_le _ _
    have a4 : (∑ g, ghostNewSize ((h.visitState i).mem g)
          (h.ghost (Fin.castSucc ⟨i, hi'⟩) g)) ≤
        memTotal (h.visitState i) + ghostBirthCount (h.ghost (Fin.castSucc ⟨i, hi'⟩)) :=
      tail_sum_ghostNewSize_le _ _
    have a5 : h.futBirths i =
        ghostBirthCount (h.ghost (Fin.castSucc ⟨i, hi'⟩)) + h.futBirths (i + 1) :=
      tail_fut_split (fun i' => ghostBirthCount (h.ghost i')) i (Nat.lt_succ_of_lt hi')
    rw [add_one_mul]
    omega

omit [DecidableEq S] [DecidableEq B] in
/-- **"A path violating this restriction has at least `B - O((ℓ + m)sN)` ghost births"**
[S-02:0802–0803], in contrapositive form: a history whose number of ghost births plus `N M|ℬ|` is
at most `b` fits the bound `b`. -/
theorem History.fits_of_births_le (h : History D Bc) (b : ℕ)
    (hb : h.ghostBirthTotal + D.n * ((J + ℓ) * Fintype.card B) ≤ b) : h.Fits b := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, κ = (J + ℓ) * Fintype.card B := ⟨_, rfl⟩
  rw [← hκ] at hb
  have hgrow := h.memTotal_visitState_le (κ := κ) hκ.ge
  have hbirth : ∀ i : Fin (D.n + 1), ghostBirthCount (h.ghost i) ≤ h.futBirths i.val := by
    intro i
    have e := tail_fut_split (fun i' => ghostBirthCount (h.ghost i')) i.val i.isLt
    have e' : h.futBirths i.val = ghostBirthCount (h.ghost i) +
        ∑ i' : Fin (D.n + 1), if i.val + 1 ≤ i'.val then ghostBirthCount (h.ghost i') else 0 := e
    omega
  have hG : ∀ i : Fin (D.n + 1), memTotal (h.visitState i.val) ≤ b ∧
      (∑ g, ghostNewSize ((h.visitState i.val).mem g) (h.ghost i g)) ≤ b := by
    intro i
    have h1 := hgrow i.val (Nat.le_of_lt_succ i.isLt)
    have h2 := hbirth i
    have h3 : i.val * κ ≤ D.n * κ := Nat.mul_le_mul_right κ (Nat.le_of_lt_succ i.isLt)
    have h4 := tail_sum_ghostNewSize_le (h.visitState i.val) (h.ghost i)
    constructor <;> omega
  refine h.fits_of_forall b hG (fun i => ?_)
  have h1 := hgrow i.val i.isLt.le
  have h2 := hbirth i.castSucc
  have h3 : (i.val + 1) * κ ≤ D.n * κ := Nat.mul_le_mul_right κ i.isLt
  rw [add_one_mul] at h3
  have a3 : memTotal (h.afterGhost i.castSucc) ≤
      ∑ g, ghostNewSize ((h.visitState i.val).mem g) (h.ghost i.castSucc g) :=
    tail_memTotal_ghostTgt_le _ _
  have a4 := tail_sum_ghostNewSize_le (h.visitState i.val) (h.ghost i.castSucc)
  have a2 : (∑ g, (edgeNewList D i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1)
        (h.edge i).2.1 g).length) ≤
      memTotal (h.afterGhost i.castSucc) + (J + ℓ) * Fintype.card B :=
    tail_sum_edgeNewList_le D i.val _ _
  have h2' : ghostBirthCount (h.ghost i.castSucc) ≤ h.futBirths i.val := h2
  rw [← hκ] at a2
  refine ⟨?_, ?_⟩
  · omega
  · show (∑ g, (edgeNewList D i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1)
        (h.edge i).2.1 g).length) ≤ b
    omega

end Growth

/-! ### The total omitted mass -/

section Mass

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

open _root_.Classical in
/-- **The total omitted mass** (eq:memory-tail) [S-02:0803–0811]: "multiply every ghost birth by
two in the absolute path sum and use the preceding bounds. The total omitted mass … is at most
`2^{-B + O((ℓ + m)sN)} L^{O(N)}`." For every cutoff `Bc` and every bound `b`, the histories which
do not fit `b` have total absolute weight at most
`2^{N M|ℬ|} / 2^{b+1} · ‖𝟏_∅‖² R_g^{N+1} R_e^N`. -/
theorem tail_sum_notFits_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (b : ℕ) {v Rg Re : ℝ}
    (hv : 1 ≤ v) (hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s) (hRg : 0 ≤ Rg)
    (hRe : 0 ≤ Re)
    (hG : ∀ i, i ≤ D.n → RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) =>
        (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c|) ghostTgt Rg)
    (hE : ∀ i, i < D.n → RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖) (edgeFullTgt D i) Re) :
    ∑ h : History D Bc, (if h.Fits b then 0 else ‖h.weight θ‖) ≤
      (2 : ℝ) ^ (D.n * ((J + ℓ) * Fintype.card B)) / 2 ^ (b + 1) *
        (wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) * (Rg ^ (D.n + 1) * Re ^ D.n)) := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, κ = D.n * ((J + ℓ) * Fintype.card B) := ⟨_, rfl⟩
  rw [← hκ]
  have hpos : (0 : ℝ) < 2 ^ (b + 1) := pow_pos two_pos _
  have hc0 : (0 : ℝ) ≤ 2 ^ κ / 2 ^ (b + 1) := div_nonneg (pow_nonneg zero_le_two _) hpos.le
  have hterm : ∀ h : History D Bc, (if h.Fits b then 0 else ‖h.weight θ‖) ≤
      (2 : ℝ) ^ κ / 2 ^ (b + 1) * ((2 : ℝ) ^ h.ghostBirthTotal * ‖h.weight θ‖) := by
    intro h
    by_cases hf : h.Fits b
    · rw [if_pos hf]
      exact mul_nonneg hc0 (mul_nonneg (pow_nonneg zero_le_two _) (norm_nonneg _))
    · rw [if_neg hf]
      have hlt : b + 1 ≤ κ + h.ghostBirthTotal := by
        by_contra hcon
        refine hf (h.fits_of_births_le b ?_)
        rw [← hκ]
        omega
      have h2 : (2 : ℝ) ^ (b + 1) ≤ (2 : ℝ) ^ κ * 2 ^ h.ghostBirthTotal := by
        rw [← pow_add]
        exact pow_le_pow_right₀ one_le_two hlt
      calc ‖h.weight θ‖ = ‖h.weight θ‖ * 2 ^ (b + 1) / 2 ^ (b + 1) :=
            (mul_div_cancel_right₀ _ hpos.ne').symm
        _ ≤ ‖h.weight θ‖ * ((2 : ℝ) ^ κ * 2 ^ h.ghostBirthTotal) / 2 ^ (b + 1) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) hpos.le
        _ = (2 : ℝ) ^ κ / 2 ^ (b + 1) * ((2 : ℝ) ^ h.ghostBirthTotal * ‖h.weight θ‖) := by
            ring
  calc ∑ h : History D Bc, (if h.Fits b then 0 else ‖h.weight θ‖)
      ≤ ∑ h : History D Bc,
          (2 : ℝ) ^ κ / 2 ^ (b + 1) * ((2 : ℝ) ^ h.ghostBirthTotal * ‖h.weight θ‖) :=
        Finset.sum_le_sum fun h _ => hterm h
    _ = (2 : ℝ) ^ κ / 2 ^ (b + 1) *
          ∑ h : History D Bc, (2 : ℝ) ^ h.ghostBirthTotal * ‖h.weight θ‖ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℝ) ^ κ / 2 ^ (b + 1) *
          (wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) *
            (Rg ^ (D.n + 1) * Re ^ D.n)) :=
        mul_le_mul_of_nonneg_left (tail_absSum_le D Bc θ hv hm hRg hRe hG hE) hc0

end Mass

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
