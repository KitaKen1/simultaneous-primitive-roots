module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.History
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemPerm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The path integral is the matrix element of the operator product

Source: `verification/stage7-sources/S-02.tex`, lines 523–534 and 1183–1191
(`[S-02:0523–0534, 1183–1191]`).

`historyExpansion : HistoryExpansion` is proved here: for every family `Φ` of multipliers on the
births,

`∑_h Φ(h) · weight(h) = ∫ Φ_init · 𝟏_∅ · (G_0^Φ ℰ_0^Φ G_1^Φ ⋯ ℰ_{N-1}^Φ G_N^Φ 𝟏_∅) dm`,

the sum being over the histories (the terms of "the expanded path integral", [S-02:0532–0534]) and
the integral over the memory states with the measure `memWeight`.

## The proof

* **Generic part.** For row operators `T¹_j = rowOp (c₁ j) t₁` and `T²_j = rowOp (c₂ j) (t₂ j)`,
  the alternating product `T¹_j T²_j T¹_{j+1} ⋯ T²_{j+m-1} T¹_{j+m} e` (`altTail`) is the sum over
  the words `w` of `m` double steps and over a last choice `c` of the product of the coefficients
  along the walk times `e` at the end (`altTail_eq_sum`). The walk carries the time index, which
  the coefficients depend on (`altCoef`, `altTgt` on `ℕ × X`).
  `walk_ofFn` computes the end and the coefficient of the walk along a word from a sequence of
  states which satisfies the recursion of the walk.
* **Operators.** `memTailWith m` is `altTail m (N - m)` for the visit and edge operations with the
  multipliers `Φ` (`memTailWith_eq_altTail`).
* **Histories.** A history is its initial data, the word of its `N` double steps (the choice of
  `G_i` and of `ℰ_i`, `i < N`) and its last choice (of `G_N`) (`histWalkEquiv`);
  `History.visitState` satisfies the recursion of the walk, so the product of the multipliers and
  of the weight of a history is the term of its word (`History.mult_mul_weight`).
* **States.** `𝟏_∅` vanishes unless all memories are empty, so the integral over the states is a
  sum over the initial data (`sum_mstate`, `emptyVec_of_ne`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Walks -/

section Walks

variable {X Ξ : Type*}

theorem walkEnd_append (tgt : X → Ξ → X) (s : X) (l : List Ξ) (ξ : Ξ) :
    walkEnd tgt s (l ++ [ξ]) = tgt (walkEnd tgt s l) ξ := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => exact ih (tgt s a)

theorem walkCoef_append (coef : X → Ξ → ℂ) (tgt : X → Ξ → X) (s : X) (l : List Ξ) (ξ : Ξ) :
    walkCoef coef tgt s (l ++ [ξ]) = walkCoef coef tgt s l * coef (walkEnd tgt s l) ξ := by
  induction l generalizing s with
  | nil =>
    show coef s ξ * 1 = 1 * coef s ξ
    ring
  | cons a l ih =>
    show coef s a * walkCoef coef tgt (tgt s a) (l ++ [ξ]) =
      coef s a * walkCoef coef tgt (tgt s a) l * coef (walkEnd tgt (tgt s a) l) ξ
    rw [ih (tgt s a)]
    ring

/-- **The walk along a word, from a sequence of states**: if `σ (i + 1)` is the target of `σ i`
under the choice `w i`, the walk from `σ 0` along `w` ends at `σ k`, and its coefficient is the
product of the coefficients at the states `σ i`. -/
theorem walk_ofFn (coef : X → Ξ → ℂ) (tgt : X → Ξ → X) (σ : ℕ → X) :
    ∀ (k : ℕ) (w : Fin k → Ξ), (∀ i : Fin k, σ (i.val + 1) = tgt (σ i.val) (w i)) →
      walkEnd tgt (σ 0) (List.ofFn w) = σ k ∧
        walkCoef coef tgt (σ 0) (List.ofFn w) = ∏ i : Fin k, coef (σ i.val) (w i) := by
  intro k
  induction k with
  | zero =>
    intro w _
    rw [List.ofFn_zero]
    exact ⟨rfl, (Fin.prod_univ_zero _).symm⟩
  | succ k ih =>
    intro w hw
    obtain ⟨h1, h2⟩ := ih (fun i => w i.castSucc) (fun i => hw i.castSucc)
    have hl : List.ofFn w = List.ofFn (fun i : Fin k => w i.castSucc) ++ [w (Fin.last k)] := by
      rw [List.ofFn_succ', List.concat_eq_append]
    have h1' : walkEnd tgt (σ 0) (List.ofFn fun i : Fin k => w i.castSucc) = σ k := h1
    have h2' : walkCoef coef tgt (σ 0) (List.ofFn fun i : Fin k => w i.castSucc) =
        ∏ i : Fin k, coef (σ i.val) (w i.castSucc) := h2
    rw [hl, walkEnd_append, walkCoef_append, h1', h2', Fin.prod_univ_castSucc]
    exact ⟨(hw (Fin.last k)).symm, rfl⟩

end Walks

/-! ### Alternating products of row operators -/

section Generic

variable {X Ξ₁ Ξ₂ : Type*} [Fintype Ξ₁] [Fintype Ξ₂]
  (c₁ : ℕ → X → Ξ₁ → ℂ) (t₁ : X → Ξ₁ → X) (c₂ : ℕ → X → Ξ₂ → ℂ) (t₂ : ℕ → X → Ξ₂ → X)
  (e : X → ℂ)

/-- The alternating product `T¹_j T²_j T¹_{j+1} ⋯ T²_{j+m-1} T¹_{j+m} e` of the row operators
`T¹_i = rowOp (c₁ i) t₁` and `T²_i = rowOp (c₂ i) (t₂ i)`, with `m` double steps. -/
def altTail : ℕ → ℕ → X → ℂ
  | 0, j => rowOp (c₁ j) t₁ e
  | m + 1, j => rowOp (c₁ j) t₁ (rowOp (c₂ j) (t₂ j) (altTail m (j + 1)))

/-- The coefficient of a double step `T¹_i T²_i`, on states with their time index. -/
def altCoef (x : ℕ × X) (ξ : Ξ₁ × Ξ₂) : ℂ := c₁ x.1 x.2 ξ.1 * c₂ x.1 (t₁ x.2 ξ.1) ξ.2

/-- The target of a double step `T¹_i T²_i`, on states with their time index. -/
def altTgt (x : ℕ × X) (ξ : Ξ₁ × Ξ₂) : ℕ × X := (x.1 + 1, t₂ x.1 (t₁ x.2 ξ.1) ξ.2)

/-- The last factor `T¹_i e` for the choice `c`. -/
def altLast (c : Ξ₁) (x : ℕ × X) : ℂ := c₁ x.1 x.2 c * e (t₁ x.2 c)

/-- The contribution of a word of double steps: the sum over the last choice. -/
def altWalk (x : ℕ × X) {k : ℕ} (w : Fin k → Ξ₁ × Ξ₂) : ℂ :=
  ∑ c : Ξ₁, walkCoef (altCoef c₁ t₁ c₂) (altTgt t₁ t₂) x (List.ofFn w) *
    altLast c₁ t₁ e c (walkEnd (altTgt t₁ t₂) x (List.ofFn w))

omit [Fintype Ξ₂] in
theorem altWalk_cons (j : ℕ) (s : X) {m : ℕ} (ξ : Ξ₁ × Ξ₂) (w : Fin m → Ξ₁ × Ξ₂) :
    altWalk c₁ t₁ c₂ t₂ e (j, s) (wordConsEquiv m (Ξ₁ × Ξ₂) (ξ, w)) =
      altCoef c₁ t₁ c₂ (j, s) ξ * altWalk c₁ t₁ c₂ t₂ e (altTgt t₁ t₂ (j, s) ξ) w := by
  have h0 : wordConsEquiv m (Ξ₁ × Ξ₂) (ξ, w) 0 = ξ := by simp [wordConsEquiv]
  have hs : (fun i : Fin m => wordConsEquiv m (Ξ₁ × Ξ₂) (ξ, w) i.succ) = w := by
    funext i
    simp [wordConsEquiv]
  have hl : List.ofFn (wordConsEquiv m (Ξ₁ × Ξ₂) (ξ, w)) = ξ :: List.ofFn w := by
    rw [List.ofFn_succ, h0, hs]
  unfold altWalk
  rw [hl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [walkCoef, walkEnd, mul_assoc]

/-- **The alternating product is the sum over the words of double steps.** -/
theorem altTail_eq_sum : ∀ (m j : ℕ) (s : X),
    altTail c₁ t₁ c₂ t₂ e m j s = ∑ w : Fin m → Ξ₁ × Ξ₂, altWalk c₁ t₁ c₂ t₂ e (j, s) w := by
  intro m
  induction m with
  | zero =>
    intro j s
    rw [Fintype.sum_unique]
    unfold altWalk
    rw [List.ofFn_zero]
    show ∑ c, c₁ j s c * e (t₁ s c) = ∑ c, 1 * (c₁ j s c * e (t₁ s c))
    exact Finset.sum_congr rfl fun c _ => (one_mul _).symm
  | succ m ih =>
    intro j s
    have hL : altTail c₁ t₁ c₂ t₂ e (m + 1) j s =
        ∑ ξ : Ξ₁ × Ξ₂, altCoef c₁ t₁ c₂ (j, s) ξ *
          altTail c₁ t₁ c₂ t₂ e m (j + 1) (t₂ j (t₁ s ξ.1) ξ.2) :=
      rowOp_comp_apply (c₁ j) t₁ (c₂ j) (t₂ j) (altTail c₁ t₁ c₂ t₂ e m (j + 1)) s
    have hR : ∑ w : Fin (m + 1) → Ξ₁ × Ξ₂, altWalk c₁ t₁ c₂ t₂ e (j, s) w =
        ∑ ξ : Ξ₁ × Ξ₂, ∑ w : Fin m → Ξ₁ × Ξ₂,
          altWalk c₁ t₁ c₂ t₂ e (j, s) (wordConsEquiv m (Ξ₁ × Ξ₂) (ξ, w)) :=
      (Equiv.sum_comp (wordConsEquiv m (Ξ₁ × Ξ₂))
        (fun w => altWalk c₁ t₁ c₂ t₂ e (j, s) w)).symm.trans (Fintype.sum_prod_type _)
    rw [hL, hR]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [ih, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => (altWalk_cons c₁ t₁ c₂ t₂ e j s ξ w).symm

end Generic

section Sums

/-- A sum over a type which is in bijection with a triple product. -/
theorem sum_equiv_triple {H A W C : Type*} [Fintype H] [Fintype A] [Fintype W] [Fintype C]
    (ε : H ≃ A × W × C) (F : A → W → C → ℂ) :
    ∑ h, F (ε h).1 (ε h).2.1 (ε h).2.2 = ∑ a, ∑ w, ∑ c, F a w c := by
  have h1 : ∑ h, F (ε h).1 (ε h).2.1 (ε h).2.2 = ∑ t : A × W × C, F t.1 t.2.1 t.2.2 :=
    Equiv.sum_comp ε (fun t : A × W × C => F t.1 t.2.1 t.2.2)
  rw [h1]
  simp only [Fintype.sum_prod_type]

theorem mul_sum_sum {W C : Type*} [Fintype W] [Fintype C] (a b : ℂ) (f : W → C → ℂ) :
    a * (b * ∑ w, ∑ c, f w c) = ∑ w, ∑ c, b * a * f w c := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end Sums

/-! ### The memory operators -/

section Concrete

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

/-- The coefficient of the visit operation `G_j` with the multiplier of `Φ`. -/
def ghostStepCoef (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc) (j : ℕ)
    (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) : ℂ :=
  Φ.ghost j (ghostBirths c) * ((ghostCoef D j s c : ℝ) : ℂ)

/-- The coefficient of the edge operation `ℰ_j` with the multiplier of `Φ`. -/
def edgeStepCoef (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc) (θ : ℝ) (j : ℕ)
    (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) : ℂ :=
  edgeFullCoef D (Φ.edge j) θ j s ξ

/-- The choices of a double step `G_j ℰ_j` form a finite type. (A named instance, built from the
instances of the two factors: the instance found by unfolding the nested products and function
types is large.) -/
instance stepChoiceFintype (D : MemData 𝒢 J ℓ N) (Bc : ℕ) :
    Fintype (GhostChoice 𝒢 Bc × EdgeFullChoice D Bc) :=
  instFintypeProd _ _

/-- The coefficient of the double step `G_j ℰ_j` with the multipliers of `Φ`. -/
def stepCoef (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc) (θ : ℝ) :
    ℕ × MState 𝒢 J ℓ Bc → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc → ℂ :=
  altCoef (ghostStepCoef D Bc Φ) ghostTgt (edgeStepCoef D Bc Φ θ)

/-- The target of the double step `G_j ℰ_j`. -/
def stepTgt (D : MemData 𝒢 J ℓ N) (Bc : ℕ) :
    ℕ × MState 𝒢 J ℓ Bc → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc → ℕ × MState 𝒢 J ℓ Bc :=
  altTgt ghostTgt (edgeFullTgt D)

/-- The last factor `G_j^Φ 𝟏_∅` for the choice `c`. -/
def lastTerm (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc) :
    GhostChoice 𝒢 Bc → ℕ × MState 𝒢 J ℓ Bc → ℂ :=
  altLast (ghostStepCoef D Bc Φ) ghostTgt (emptyVec 𝒢 J ℓ Bc)

/-- `memTailWith m` is the alternating product of the visit and edge operations with the
multipliers `Φ`, starting at the visit `N - m`. -/
theorem memTailWith_eq_altTail (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc)
    (θ : ℝ) : ∀ m : ℕ, m ≤ D.n →
      memTailWith D Bc Φ θ m =
        altTail (ghostStepCoef D Bc Φ) ghostTgt (edgeStepCoef D Bc Φ θ) (edgeFullTgt D)
          (emptyVec 𝒢 J ℓ Bc) m (D.n - m) := by
  intro m
  induction m with
  | zero =>
    intro _
    rfl
  | succ m ih =>
    intro hm
    have hidx : D.n - (m + 1) + 1 = D.n - m := by omega
    show ghostOpWith D Bc (Φ.ghost (D.n - (m + 1))) (D.n - (m + 1))
        (edgeOpWith D Bc (Φ.edge (D.n - (m + 1))) θ (D.n - (m + 1))
          (memTailWith D Bc Φ θ m)) =
      rowOp (ghostStepCoef D Bc Φ (D.n - (m + 1))) ghostTgt
        (rowOp (edgeStepCoef D Bc Φ θ (D.n - (m + 1))) (edgeFullTgt D (D.n - (m + 1)))
          (altTail (ghostStepCoef D Bc Φ) ghostTgt (edgeStepCoef D Bc Φ θ) (edgeFullTgt D)
            (emptyVec 𝒢 J ℓ Bc) m (D.n - (m + 1) + 1)))
    rw [hidx, ← ih (Nat.le_of_succ_le hm)]
    rfl

/-! ### Initial data, words and histories -/

/-- The initial state with the initial data `a = (y, small list, big list)`: all memories are
empty. -/
def initState (a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ)
    (Bc : ℕ) : MState 𝒢 J ℓ Bc :=
  ⟨a.1, a.2.1, a.2.2, fun g => emptyMem 𝒢 Bc g⟩

/-- The term of the initial data `a`, the word `w` of double steps and the last choice `c`: the
product of the coefficients (with the multipliers of `Φ`) along the walk, times `𝟏_∅` at its
end. -/
def histTerm (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc) (θ : ℝ)
    (a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ)
    (w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc) (c : GhostChoice 𝒢 Bc) : ℂ :=
  walkCoef (stepCoef D Bc Φ θ) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
    lastTerm D Bc Φ c (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w))

/-- **The operator product at an initial state is the sum over the words and the last choices.** -/
theorem memTailWith_eq_sum_walks (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc)
    (θ : ℝ) (a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ) :
    memTailWith D Bc Φ θ D.n (initState a Bc) =
      ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
        histTerm D Bc Φ θ a w c := by
  rw [memTailWith_eq_altTail D Bc Φ θ D.n le_rfl, Nat.sub_self]
  exact altTail_eq_sum (ghostStepCoef D Bc Φ) ghostTgt (edgeStepCoef D Bc Φ θ) (edgeFullTgt D)
    (emptyVec 𝒢 J ℓ Bc) D.n 0 (initState a Bc)

/-- **A history is its initial data, the word of its `N` double steps and its last choice.** -/
def histWalkEquiv (D : MemData 𝒢 J ℓ N) (Bc : ℕ) :
    History D Bc ≃
      (ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ) ×
        (Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc) × GhostChoice 𝒢 Bc where
  toFun h :=
    ((h.y₀, h.xs₀, h.xb₀), (fun i => (h.ghost i.castSucc, h.edge i)), h.ghost (Fin.last D.n))
  invFun t :=
    ⟨t.1.1, t.1.2.1, t.1.2.2,
      Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i : Fin D.n => (t.2.1 i).1) t.2.2,
      fun i => (t.2.1 i).2⟩
  left_inv h := by
    obtain ⟨y₀, xs₀, xb₀, ghost, edge⟩ := h
    have e : Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i : Fin D.n => ghost i.castSucc)
        (ghost (Fin.last D.n)) = ghost := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Fin.snoc_last _ _
      · exact Fin.snoc_castSucc _ _ j
    exact congrArg (fun g => (⟨y₀, xs₀, xb₀, g, edge⟩ : History D Bc)) e
  right_inv t := by
    obtain ⟨⟨y, xs, xb⟩, w, c⟩ := t
    have e1 : (fun i : Fin D.n =>
        ((Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i => (w i).1) c :
          Fin (D.n + 1) → GhostChoice 𝒢 Bc) i.castSucc, (w i).2)) = w := by
      funext i
      refine Prod.ext ?_ rfl
      show Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i : Fin D.n => (w i).1) c
        i.castSucc = (w i).1
      exact Fin.snoc_castSucc (α := fun _ => GhostChoice 𝒢 Bc) c (fun i : Fin D.n => (w i).1) i
    have e2 : (Fin.snoc (α := fun _ => GhostChoice 𝒢 Bc) (fun i => (w i).1) c :
        Fin (D.n + 1) → GhostChoice 𝒢 Bc) (Fin.last D.n) = c := Fin.snoc_last _ _
    exact Prod.ext rfl (Prod.ext e1 e2)

omit [Fintype N] in
/-- **The multipliers and the weight of a history are the term of its word.** -/
theorem History.mult_mul_weight (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc)
    (θ : ℝ) (h : History D Bc) :
    h.mult Φ * h.weight θ =
      Φ.init h.xb₀ * ((memWeight 𝒢 D.q D.n h.init : ℝ) : ℂ) *
        histTerm D Bc Φ θ (h.y₀, h.xs₀, h.xb₀) (fun i => (h.ghost i.castSucc, h.edge i))
          (h.ghost (Fin.last D.n)) := by
  -- the walk of the history
  obtain ⟨hend, hcoef⟩ := walk_ofFn (stepCoef D Bc Φ θ) (stepTgt D Bc)
    (fun i => ((i : ℕ), h.visitState i)) D.n (fun i => (h.ghost i.castSucc, h.edge i))
    (fun i => congrArg (fun t => (i.val + 1, t)) (History.visitState_succ h i))
  have hend' : walkEnd (stepTgt D Bc) ((0 : ℕ), h.init)
      (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) =
      (D.n, h.visitState D.n) := hend
  have hcoef' : walkCoef (stepCoef D Bc Φ θ) (stepTgt D Bc) ((0 : ℕ), h.init)
      (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) =
      ∏ i : Fin D.n, stepCoef D Bc Φ θ (i.val, h.visitState i.val)
        (h.ghost i.castSucc, h.edge i) := hcoef
  have hT : histTerm D Bc Φ θ (h.y₀, h.xs₀, h.xb₀) (fun i => (h.ghost i.castSucc, h.edge i))
      (h.ghost (Fin.last D.n)) =
      (∏ i : Fin D.n, stepCoef D Bc Φ θ (i.val, h.visitState i.val)
        (h.ghost i.castSucc, h.edge i)) *
        lastTerm D Bc Φ (h.ghost (Fin.last D.n)) (D.n, h.visitState D.n) := by
    show walkCoef (stepCoef D Bc Φ θ) (stepTgt D Bc) ((0 : ℕ), h.init)
          (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) *
        lastTerm D Bc Φ (h.ghost (Fin.last D.n))
          (walkEnd (stepTgt D Bc) ((0 : ℕ), h.init)
            (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i))) = _
    rw [hend', hcoef']
  -- one double step
  have hstep : ∀ i : Fin D.n,
      stepCoef D Bc Φ θ (i.val, h.visitState i.val) (h.ghost i.castSucc, h.edge i) =
        (Φ.ghost i.val (ghostBirths (h.ghost i.castSucc)) *
            Φ.edge i.val (edgeBirths (h.edge i).2.1)) *
          (((ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) : ℝ) : ℂ) *
            edgeFullCoef D (fun _ => 1) θ i.val
              (ghostTgt (h.visitState i.val) (h.ghost i.castSucc)) (h.edge i)) := by
    intro i
    show Φ.ghost i.val (ghostBirths (h.ghost i.castSucc)) *
          ((ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) : ℝ) : ℂ) *
        edgeFullCoef D (Φ.edge i.val) θ i.val
          (ghostTgt (h.visitState i.val) (h.ghost i.castSucc)) (h.edge i) = _
    simp only [edgeFullCoef]
    ring
  have hP : ∏ i : Fin D.n, stepCoef D Bc Φ θ (i.val, h.visitState i.val)
        (h.ghost i.castSucc, h.edge i) =
      (∏ i : Fin D.n, Φ.ghost i.val (ghostBirths (h.ghost i.castSucc))) *
          (∏ i : Fin D.n, Φ.edge i.val (edgeBirths (h.edge i).2.1)) *
        ∏ i : Fin D.n,
          (((ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) : ℝ) : ℂ) *
            edgeFullCoef D (fun _ => 1) θ i.val
              (ghostTgt (h.visitState i.val) (h.ghost i.castSucc)) (h.edge i)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hstep i
  have hG : ∏ i : Fin (D.n + 1), Φ.ghost i.val (ghostBirths (h.ghost i)) =
      (∏ i : Fin D.n, Φ.ghost i.val (ghostBirths (h.ghost i.castSucc))) *
        Φ.ghost D.n (ghostBirths (h.ghost (Fin.last D.n))) :=
    Fin.prod_univ_castSucc (fun i : Fin (D.n + 1) => Φ.ghost i.val (ghostBirths (h.ghost i)))
  have key : ∀ (I0 G1 PB M PC CL EV P PA gl : ℂ), G1 = PA * gl → P = PA * PB * PC →
      I0 * G1 * PB * (M * PC * (CL * EV)) = I0 * M * (P * (gl * CL * EV)) := by
    intro I0 G1 PB M PC CL EV P PA gl h1 h2
    rw [h1, h2]
    ring
  rw [hT]
  exact key _ _ _ _ _ _ _ _ _ _ hG hP

/-! ### The integral over the memory states -/

/-- A memory state is its initial data and its memories. -/
def mstateEquiv (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) :
    MState 𝒢 J ℓ Bc ≃
      (ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ) ×
        ((g : B) → Mem 𝒢 Bc g) where
  toFun s := ((s.y, s.xs, s.xb), s.mem)
  invFun t := ⟨t.1.1, t.1.2.1, t.1.2.2, t.2⟩
  left_inv s := by
    cases s
    rfl
  right_inv t := by
    obtain ⟨⟨y, xs, xb⟩, mem⟩ := t
    rfl

theorem sum_mstate {Bc : ℕ} (H : MState 𝒢 J ℓ Bc → ℂ) :
    ∑ s, H s =
      ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        ∑ mem : (g : B) → Mem 𝒢 Bc g, H ⟨a.1, a.2.1, a.2.2, mem⟩ :=
  (Equiv.sum_comp (mstateEquiv 𝒢 J ℓ Bc).symm H).symm.trans
    (Fintype.sum_prod_type fun t : (ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ ×
      LabelList 𝒢.big J ℓ) × ((g : B) → Mem 𝒢 Bc g) => H ((mstateEquiv 𝒢 J ℓ Bc).symm t))

omit [DecidableEq S] [DecidableEq B] in
/-- `𝟏_∅` is one at the initial states. -/
theorem emptyVec_initState {Bc : ℕ}
    (a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ) :
    emptyVec 𝒢 J ℓ Bc (initState a Bc) = 1 := by
  have h : memTotal (initState a Bc) = 0 := Finset.sum_eq_zero fun g _ => rfl
  unfold emptyVec
  exact if_pos h

omit [DecidableEq S] [DecidableEq B] in
/-- `𝟏_∅` vanishes at the states with a nonempty memory. -/
theorem emptyVec_of_ne {Bc : ℕ}
    (a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ)
    (mem : (g : B) → Mem 𝒢 Bc g) (hmem : mem ≠ fun g => emptyMem 𝒢 Bc g) :
    emptyVec 𝒢 J ℓ Bc (⟨a.1, a.2.1, a.2.2, mem⟩ : MState 𝒢 J ℓ Bc) = 0 := by
  unfold emptyVec
  refine if_neg fun htot => hmem (funext fun g => ?_)
  have htot' : ∑ g' : B, (mem g').1.val = 0 := htot
  have hle : (mem g).1.val ≤ ∑ g' : B, (mem g').1.val :=
    Finset.single_le_sum (f := fun g' : B => (mem g').1.val) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ g)
  have hsize : (mem g).1.val = 0 := by omega
  have h1 : List.ofFn (mem g).2 = [] := List.ofFn_eq_nil_iff.mpr hsize
  have h2 : List.ofFn (emptyMem 𝒢 Bc g).2 = [] := List.ofFn_eq_nil_iff.mpr rfl
  exact mem_ext_ofFn _ _ (h1.trans h2.symm)

/-- `HistoryExpansion` for one family of groups. -/
theorem historyExpansion_aux (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc)
    (θ : ℝ) :
    (∑ h : History D Bc, h.mult Φ * h.weight θ) =
      ∑ s : MState 𝒢 J ℓ Bc, ((memWeight 𝒢 D.q D.n s : ℝ) : ℂ) *
        (Φ.init s.xb * emptyVec 𝒢 J ℓ Bc s * memTailWith D Bc Φ θ D.n s) := by
  -- the left side: the histories are the initial data, the words and the last choices
  have hL : (∑ h : History D Bc, h.mult Φ * h.weight θ) =
      ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
          Φ.init a.2.2 * ((memWeight 𝒢 D.q D.n (initState a Bc) : ℝ) : ℂ) *
            histTerm D Bc Φ θ a w c :=
    (Finset.sum_congr rfl fun h _ => History.mult_mul_weight D Bc Φ θ h).trans
      (sum_equiv_triple (histWalkEquiv D Bc) (fun a w c =>
        Φ.init a.2.2 * ((memWeight 𝒢 D.q D.n (initState a Bc) : ℝ) : ℂ) *
          histTerm D Bc Φ θ a w c))
  -- the right side: only the states with empty memories contribute
  rw [hL, sum_mstate]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Eq.trans ?_ (Fintype.sum_eq_single (fun g => emptyMem 𝒢 Bc g) ?_).symm
  · show (∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
          Φ.init a.2.2 * ((memWeight 𝒢 D.q D.n (initState a Bc) : ℝ) : ℂ) *
            histTerm D Bc Φ θ a w c) =
      ((memWeight 𝒢 D.q D.n (initState a Bc) : ℝ) : ℂ) *
        (Φ.init a.2.2 * emptyVec 𝒢 J ℓ Bc (initState a Bc) *
          memTailWith D Bc Φ θ D.n (initState a Bc))
    rw [emptyVec_initState, memTailWith_eq_sum_walks, mul_one]
    exact (mul_sum_sum _ _ _).symm
  · intro mem hmem
    show ((memWeight 𝒢 D.q D.n (⟨a.1, a.2.1, a.2.2, mem⟩ : MState 𝒢 J ℓ Bc) : ℝ) : ℂ) *
        (Φ.init a.2.2 * emptyVec 𝒢 J ℓ Bc (⟨a.1, a.2.1, a.2.2, mem⟩ : MState 𝒢 J ℓ Bc) *
          memTailWith D Bc Φ θ D.n (⟨a.1, a.2.1, a.2.2, mem⟩ : MState 𝒢 J ℓ Bc)) = 0
    rw [emptyVec_of_ne a mem hmem]
    ring

end Concrete

/-- **The path integral is the matrix element of the operator product** [S-02:0523–0534,
1183–1191]: for every family `Φ` of multipliers on the births, the sum over the histories of
(multipliers) × (weight) is the integral of `Φ_init · 𝟏_∅ · (G_0^Φ ℰ_0^Φ G_1^Φ ⋯ ℰ_{N-1}^Φ G_N^Φ
𝟏_∅)` over the memory states. -/
theorem historyExpansion : HistoryExpansion :=
  fun _ _ _ _ _ _ _ _ _ _ _ D Bc Φ θ => historyExpansion_aux D Bc Φ θ

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
