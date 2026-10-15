module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.TailSync
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Memory truncation: the histories at the cutoff `B` among the histories at a larger cutoff

Source: `verification/stage7-sources/S-02.tex`, lines 796–802 (`[S-02:0796–0802]`).

"We now restrict the total memory size to `B` before and after every operation, writing the
projections implicitly."

`tail_sum_fits_eq`: for `b ≤ Bc`, the path integral with the distinct-birth rule at the cutoff `b`
is the sum, over the histories at the cutoff `Bc` whose total memory is at most `b` before and
after every operation (`History.Fits`), of the same terms:

`∑_{h' at Bc, h' fits b} 1[distinct births] weight(h') = distinctSum b`.

* `restrictSet`, `restrictBatch`, `restrictIdx`, `restrictGhost`, `restrictEdge`, `restrictFull`,
  `restrictHist` — the restriction of the choices at the cutoff `Bc` to the cutoff `b`; it is a
  left inverse of `liftHist` (`restrictHist_lift`).
* `liftHist_restrict_of_fits` — a history at the cutoff `Bc` which fits `b` and has nonvanishing
  weight is the lift of its restriction: its terminated and promoted indices are indices of
  pending particles (`GhostValid`, `PromoValid`) and its batches enter the memory, so all of them
  are below `b`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section Restrict

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} {b Bc : ℕ} {D : MemData 𝒢 J ℓ N}

/-! ### Restriction of the choices -/

/-- The indices below `b` of a set of indices below `Bc`. -/
def restrictSet (hb : b ≤ Bc) (A : Finset (Fin Bc)) : Finset (Fin b) :=
  Finset.univ.filter fun j => Fin.castLE hb j ∈ A

theorem restrictSet_map (hb : b ≤ Bc) (A : Finset (Fin b)) :
    restrictSet hb (A.map (Fin.castLEEmb hb)) = A :=
  Finset.ext fun j => (Finset.mem_filter.trans (and_iff_right (Finset.mem_univ j))).trans
    (Finset.mem_map' (Fin.castLEEmb hb))

theorem map_restrictSet (hb : b ≤ Bc) (A : Finset (Fin Bc)) (hA : ∀ j ∈ A, j.val < b) :
    (restrictSet hb A).map (Fin.castLEEmb hb) = A := by
  refine Finset.ext fun j' => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp h
    exact (Finset.mem_filter.mp hj).2
  · exact Finset.mem_map.mpr ⟨⟨j'.val, hA j' h⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- A batch at the cutoff `Bc` as a batch at the cutoff `b` (the empty batch if it is too
large). -/
def restrictBatch (b : ℕ) {g : B} (β : Batch 𝒢 Bc g) : Batch 𝒢 b g :=
  if h : β.1.val ≤ b then ⟨⟨β.1.val, Nat.lt_succ_of_le h⟩, β.2⟩
  else ⟨⟨0, Nat.succ_pos b⟩, Fin.elim0⟩

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem restrictBatch_lift (hb : b ≤ Bc) {g : B} (β : Batch 𝒢 b g) :
    restrictBatch b (liftBatch hb β) = β := by
  have hle : (liftBatch hb β).1.val ≤ b := Nat.le_of_lt_succ β.1.isLt
  have e : restrictBatch b (liftBatch hb β) =
      ⟨⟨(liftBatch hb β).1.val, Nat.lt_succ_of_le hle⟩, (liftBatch hb β).2⟩ := dif_pos hle
  exact e.trans rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem liftBatch_restrict (hb : b ≤ Bc) {g : B} (β : Batch 𝒢 Bc g) (hβ : β.1.val ≤ b) :
    liftBatch hb (restrictBatch b β) = β := by
  have e : restrictBatch b β = ⟨⟨β.1.val, Nat.lt_succ_of_le hβ⟩, β.2⟩ := dif_pos hβ
  exact (congrArg (liftBatch hb) e).trans rfl

/-- An index below `Bc` as an index below `b`, if it is one. -/
def restrictIdx (b : ℕ) {Bc : ℕ} (j : Fin Bc) : Option (Fin b) :=
  if h : j.val < b then some ⟨j.val, h⟩ else none

theorem restrictIdx_castLE (hb : b ≤ Bc) (j : Fin b) :
    restrictIdx b (Fin.castLE hb j) = some j :=
  (dif_pos j.isLt :
    restrictIdx b (Fin.castLE hb j) = some ⟨(Fin.castLE hb j).val, j.isLt⟩)

theorem bind_restrictIdx_map (hb : b ≤ Bc) (o : Option (Fin b)) :
    (o.map (Fin.castLE hb)).bind (restrictIdx b) = o := by
  cases o with
  | none => rfl
  | some j => exact restrictIdx_castLE hb j

theorem map_bind_restrictIdx (hb : b ≤ Bc) (o : Option (Fin Bc))
    (ho : ∀ j, o = some j → j.val < b) :
    (o.bind (restrictIdx b)).map (Fin.castLE hb) = o := by
  cases o with
  | none => rfl
  | some j =>
    have hj := ho j rfl
    have e : restrictIdx b j = some ⟨j.val, hj⟩ := dif_pos hj
    exact (congrArg (Option.map (Fin.castLE hb)) e).trans rfl

/-- A choice of the visit operation at the cutoff `Bc`, restricted to the cutoff `b`. -/
def restrictGhost (hb : b ≤ Bc) (c : GhostChoice 𝒢 Bc) : GhostChoice 𝒢 b :=
  fun g => (restrictSet hb (c g).1, restrictBatch b (c g).2)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem restrictGhost_lift (hb : b ≤ Bc) (c : GhostChoice 𝒢 b) :
    restrictGhost hb (liftGhost hb c) = c :=
  funext fun g => Prod.ext (restrictSet_map hb (c g).1) (restrictBatch_lift hb (c g).2)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem liftGhost_restrict (hb : b ≤ Bc) (c : GhostChoice 𝒢 Bc)
    (hc : ∀ g, (∀ j ∈ (c g).1, j.val < b) ∧ (c g).2.1.val ≤ b) :
    liftGhost hb (restrictGhost hb c) = c :=
  funext fun g => Prod.ext (map_restrictSet hb (c g).1 (hc g).1)
    (liftBatch_restrict hb (c g).2 (hc g).2)

/-- A choice of the row transition of an edge at the cutoff `Bc`, restricted to the cutoff
`b`. -/
def restrictEdge (b : ℕ) {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) :
    EdgeChoice 𝒢 𝔉 b :=
  ⟨c.ν, c.r, c.store, fun g sl => (c.promo g sl).bind (restrictIdx b), c.xsT, c.xbT⟩

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem restrictEdge_lift (hb : b ≤ Bc) {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 b) :
    restrictEdge b (liftEdge hb c) = c := by
  obtain ⟨ν, r, store, promo, xsT, xbT⟩ := c
  exact congrArg (fun p => (⟨ν, r, store, p, xsT, xbT⟩ : EdgeChoice 𝒢 𝔉 b))
    (funext fun g => funext fun sl => bind_restrictIdx_map hb (promo g sl))

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem liftEdge_restrict (hb : b ≤ Bc) {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc)
    (hc : ∀ g sl j, c.promo g sl = some j → j.val < b) :
    liftEdge hb (restrictEdge b c) = c := by
  obtain ⟨ν, r, store, promo, xsT, xbT⟩ := c
  exact congrArg (fun p => (⟨ν, r, store, p, xsT, xbT⟩ : EdgeChoice 𝒢 𝔉 Bc))
    (funext fun g => funext fun sl => map_bind_restrictIdx hb (promo g sl) (hc g sl))

/-- A choice of the edge operation at the cutoff `Bc`, restricted to the cutoff `b`. -/
def restrictFull (b : ℕ) {D : MemData 𝒢 J ℓ N} (ξ : EdgeFullChoice D Bc) : EdgeFullChoice D b :=
  (ξ.1, restrictEdge b ξ.2.1, ξ.2.2)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem restrictFull_lift (hb : b ≤ Bc) (ξ : EdgeFullChoice D b) :
    restrictFull b (liftFull hb ξ) = ξ :=
  Prod.ext rfl (Prod.ext (restrictEdge_lift hb ξ.2.1) rfl)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem liftFull_restrict (hb : b ≤ Bc) (ξ : EdgeFullChoice D Bc)
    (hc : ∀ g sl j, ξ.2.1.promo g sl = some j → j.val < b) :
    liftFull hb (restrictFull b ξ) = ξ :=
  Prod.ext rfl (Prod.ext (liftEdge_restrict hb ξ.2.1 hc) rfl)

/-- **A history at the cutoff `Bc`, restricted to the cutoff `b`.** -/
def restrictHist (hb : b ≤ Bc) (h' : History D Bc) : History D b :=
  ⟨h'.y₀, h'.xs₀, h'.xb₀, fun i => restrictGhost hb (h'.ghost i),
    fun i => restrictFull b (h'.edge i)⟩

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The restriction is a left inverse of the embedding of the histories. -/
theorem restrictHist_lift (hb : b ≤ Bc) (h : History D b) :
    restrictHist hb (liftHist hb h) = h := by
  obtain ⟨y₀, xs₀, xb₀, ghost, edge⟩ := h
  exact congrArg₂ (fun gh ed => (⟨y₀, xs₀, xb₀, gh, ed⟩ : History D b))
    (funext fun i => restrictGhost_lift hb (ghost i))
    (funext fun i => restrictFull_lift hb (edge i))

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem liftHist_restrict (hb : b ≤ Bc) (h' : History D Bc)
    (hG : ∀ i g, (∀ j ∈ (h'.ghost i g).1, j.val < b) ∧ (h'.ghost i g).2.1.val ≤ b)
    (hE : ∀ i g sl j, (h'.edge i).2.1.promo g sl = some j → j.val < b) :
    liftHist hb (restrictHist hb h') = h' := by
  obtain ⟨y₀, xs₀, xb₀, ghost, edge⟩ := h'
  exact congrArg₂ (fun gh ed => (⟨y₀, xs₀, xb₀, gh, ed⟩ : History D Bc))
    (funext fun i => liftGhost_restrict hb (ghost i) (hG i))
    (funext fun i => liftFull_restrict hb (edge i) (hE i))

/-! ### Histories with nonvanishing weight -/

/-- The coefficients of all operations of a history with nonvanishing weight are nonzero. -/
theorem History.coef_ne_zero_of_weight_ne_zero (h : History D Bc) (θ : ℝ)
    (hw : h.weight θ ≠ 0) :
    (∀ i : Fin (D.n + 1), ghostCoef D i.val (h.visitState i.val) (h.ghost i) ≠ 0) ∧
      ∀ i : Fin D.n,
        edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i) ≠ 0 := by
  unfold History.weight at hw
  have h1 := left_ne_zero_of_mul hw
  have h2 := right_ne_zero_of_mul hw
  have h3 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h1)
  refine ⟨fun i => ?_, fun i => right_ne_zero_of_mul (h3 i (Finset.mem_univ i))⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact Complex.ofReal_ne_zero.mp (left_ne_zero_of_mul h2)
  · exact Complex.ofReal_ne_zero.mp (left_ne_zero_of_mul (h3 j (Finset.mem_univ j)))

omit [DecidableEq S] [DecidableEq B] in
/-- A nonvanishing coefficient of a visit operation terminates pending zeros only. -/
theorem ghostValid_of_ghostCoef_ne_zero (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : GhostChoice 𝒢 Bc) (hne : ghostCoef D i s c ≠ 0) (g : B) :
    GhostValid (s.mem g) (c g).1 := by
  by_contra hcon
  refine hne ?_
  have hz : ghostCoefG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) = 0 := by
    unfold ghostCoefG
    exact if_neg hcon
  unfold ghostCoef
  split_ifs
  · exact Finset.prod_eq_zero (Finset.mem_univ g) hz
  · rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem tail_lt_of_memAt {g : B} {z : Mem 𝒢 Bc g} {j : Fin Bc} {pr : Particle 𝒢 g}
    (h : memAt z j = some pr) : j.val < z.1.val := by
  by_contra hcon
  have e : memAt z j = none := dif_neg hcon
  rw [e] at h
  exact absurd h.symm (Option.some_ne_none pr)

/-- **A history at the cutoff `Bc` which fits `b` and has nonvanishing weight is a history at the
cutoff `b`.** -/
theorem liftHist_restrict_of_fits (hb : b ≤ Bc) (h' : History D Bc) (θ : ℝ) (hf : h'.Fits b)
    (hw : h'.weight θ ≠ 0) : liftHist hb (restrictHist hb h') = h' := by
  obtain ⟨hG, hE⟩ := h'.cond_of_fits b hf
  obtain ⟨hgne, hene⟩ := h'.coef_ne_zero_of_weight_ne_zero θ hw
  refine liftHist_restrict hb h' (fun i g => ?_) (fun i g sl j hj => ?_)
  · obtain ⟨hc1, hc2⟩ := hG i
    have hval := ghostValid_of_ghostCoef_ne_zero D i.val (h'.visitState i.val) (h'.ghost i)
      (hgne i) g
    have hsize : ((h'.visitState i.val).mem g).1.val ≤ b :=
      (Finset.single_le_sum (f := fun g => ((h'.visitState i.val).mem g).1.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans hc1
    refine ⟨fun j hj => ?_, ?_⟩
    · obtain ⟨pr, hpr, _⟩ := hval j hj
      exact lt_of_lt_of_le (tail_lt_of_memAt hpr) hsize
    · have h1 : (h'.ghost i g).2.1.val ≤
          ghostNewSize ((h'.visitState i.val).mem g) (h'.ghost i g) := Nat.le_add_left _ _
      have h2 : ghostNewSize ((h'.visitState i.val).mem g) (h'.ghost i g) ≤
          ∑ g, ghostNewSize ((h'.visitState i.val).mem g) (h'.ghost i g) :=
        Finset.single_le_sum
          (f := fun g => ghostNewSize ((h'.visitState i.val).mem g) (h'.ghost i g))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
      exact h1.trans (h2.trans hc2)
  · obtain ⟨hc1, _⟩ := hE i
    have hcond : EdgeAbsCond D i.val ((h'.afterGhost i.castSucc).permLists (h'.edge i).1)
        (h'.edge i).2.1 := by
      by_contra hcon
      refine hene i ?_
      unfold edgeFullCoef
      rw [edgeCoef_of_not_cond D θ i.val _ _ hcon, mul_zero, mul_zero, zero_mul]
    obtain ⟨_, _, _, _, _, _, _, _, _, h10⟩ := hcond
    obtain ⟨_, _, pr, hpr, _⟩ := h10 g sl j hj
    have hlt : j.val < ((h'.afterGhost i.castSucc).mem g).1.val := tail_lt_of_memAt hpr
    have hsize : ((h'.afterGhost i.castSucc).mem g).1.val ≤ b :=
      (Finset.single_le_sum (f := fun g => ((h'.afterGhost i.castSucc).mem g).1.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans hc1
    exact lt_of_lt_of_le hlt hsize

/-! ### The path integral at the cutoff `b` inside the path integral at the cutoff `Bc` -/

variable [Fintype N]

open _root_.Classical in
/-- **The histories at the cutoff `b` are the histories at the cutoff `Bc ≥ b` in which the total
memory never exceeds `b`, with the same weights and births** [S-02:0797–0801]: the path integral
with the distinct-birth rule at the cutoff `b` is the sum of the same terms over the histories at
the cutoff `Bc` which fit `b`. -/
theorem tail_sum_fits_eq (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (θ : ℝ) :
    ∑ h' : History D Bc, (if h'.Fits b then
        (if Graph.PerformedBirthsDistinct h'.birth then h'.weight θ else 0) else 0) =
      distinctSum D b θ := by
  have hL : ∑ h' : History D Bc, (if h'.Fits b then
        (if Graph.PerformedBirthsDistinct h'.birth then h'.weight θ else 0) else 0) =
      ∑ h' ∈ Finset.univ.filter (fun h' : History D Bc => h'.Fits b ∧ h'.weight θ ≠ 0),
        (if h'.Fits b then
          (if Graph.PerformedBirthsDistinct h'.birth then h'.weight θ else 0) else 0) := by
    refine (Finset.sum_filter_of_ne fun h' _ hne => ?_).symm
    by_cases hf : h'.Fits b
    · refine ⟨hf, fun hw0 => hne ?_⟩
      rw [if_pos hf, hw0, ite_self]
    · exact absurd (if_neg hf) hne
  have hR : distinctSum D b θ =
      ∑ h ∈ Finset.univ.filter (fun h : History D b => h.weight θ ≠ 0),
        (if Graph.PerformedBirthsDistinct h.birth then h.weight θ else 0) := by
    unfold distinctSum
    refine (Finset.sum_filter_of_ne fun h _ hne => ?_).symm
    intro hw0
    refine hne ?_
    rw [hw0, ite_self]
  rw [hL, hR]
  refine (Finset.sum_nbij' (liftHist hb) (restrictHist hb) ?_ ?_ ?_ ?_ ?_).symm
  · intro h hh
    have hw : h.weight θ ≠ 0 := (Finset.mem_filter.mp hh).2
    have hf : h.Fits b := h.fits_of_weight_ne_zero θ hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (sync_fits hb h).mpr hf, ?_⟩
    rw [sync_weight hb h θ hf]
    exact hw
  · intro h' hh'
    obtain ⟨hf, hw⟩ := (Finset.mem_filter.mp hh').2
    have hlr := liftHist_restrict_of_fits hb h' θ hf hw
    have hf' : (restrictHist hb h').Fits b := by
      refine (sync_fits hb (restrictHist hb h')).mp ?_
      rw [hlr]
      exact hf
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hwe := sync_weight hb (restrictHist hb h') θ hf'
    rw [hlr] at hwe
    rw [← hwe]
    exact hw
  · intro h _
    exact restrictHist_lift hb h
  · intro h' hh'
    obtain ⟨hf, hw⟩ := (Finset.mem_filter.mp hh').2
    exact liftHist_restrict_of_fits hb h' θ hf hw
  · intro h hh
    have hw : h.weight θ ≠ 0 := (Finset.mem_filter.mp hh).2
    have hf : h.Fits b := h.fits_of_weight_ne_zero θ hw
    rw [if_pos ((sync_fits hb h).mpr hf), sync_weight hb h θ hf]
    exact ite_congr_of_iff (sync_birthsDistinct hb h).symm rfl rfl

end Restrict

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
