module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealOperator
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# The comparison kernels and the residual pattern family ([S] §4)

Source: `verification/stage7-sources/S-03.tex` (`[S-03:…]`).

The objects needed to state Theorem 4.1 [S-03:0011–0052] and Lemma 4.3 [S-03:0270–0292]:

* `tupleProd`, `logCell`, `cellMass`, `primitiveCharSum`, `cellKernel` — the products of label
  tuples, the log cells `I_j = [jh, (j+1)h)`, the cell probabilities `ν_{Λ j}`, the set `𝒞_Q` of
  primitive characters of conductor at most `Q`, and the kernel `𝒦_Λ` of (eq:ideal-cell-kernel)
  [S-03:0176–0194].
* `comparisonDefect`, `tupleNorm` — the left side of (eq:ideal-comparison) [S-03:0280–0288] and
  the `L²` norm of a tuple test.
* `probeSlots`, `BalancedSplit`, `IsComparison`, `comparisonPattern`, `comparisonFamily` — the
  probes, the two blocks of big groups and the family "consisting of the raw pattern and signed
  comparison patterns" with coefficients (eq:ideal-comparison-coefficient) [S-03:0038–0052,
  0441–0454].

A slot set `Λ` "using `k_g ≤ m` slots from group `g`" [S-03:0079] is a family
`Λ : B → Finset (Fin J)`; its label tuples are `AuxList big Λ` and their product law is
`auxWeight big Λ` (the same objects as the auxiliary free labels of a pattern with `C = Λ`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators ComplexConjugate

noncomputable section

section Kernel

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

/-- The product `P_Λ` of the labels of a tuple on the slot set `Λ` [S-03:0079–0080]. -/
def tupleProd {big : B → Finset ℕ} (Λ : B → Finset (Fin J)) (t : AuxList big Λ) : ℕ :=
  ∏ g, ∏ i : {i : Fin J // i ∈ Λ g}, (t g i : ℕ)

/-- The index `j` of the log cell `I_j = [jh, (j+1)h)` containing `log D` [S-03:0181–0183]. -/
def logCell (h : ℝ) (D : ℕ) : ℤ := ⌊Real.log D / h⌋

/-- The cell probability `ν_{Λ j} = ℙ(log D ∈ I_j)` for a tuple of type `Λ` with independent
labels of laws `μ_g` [S-03:0183]. -/
def cellMass (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (h : ℝ) (j : ℤ) : ℝ :=
  ∑ t : AuxList big Λ, if logCell h (tupleProd Λ t) = j then auxWeight big Λ t else 0

/-- The number `N_Λ` of log cells met by the tuples of type `Λ` [S-03:0196–0199] (for positive
laws: the cells of positive mass). -/
def cellCount (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (h : ℝ) : ℕ :=
  (Finset.univ.image fun t : AuxList big Λ => logCell h (tupleProd Λ t)).card

open Classical in
/-- `∑_{χ ∈ 𝒞_Q} conj(χ(D)) χ(X)`, where `𝒞_Q` is the set of primitive Dirichlet characters of
conductor at most `Q` [S-03:0184–0186]; "the conductor-1 character is included". A primitive
character of conductor `r` is a primitive `DirichletCharacter ℂ r`. -/
def primitiveCharSum (Q : ℝ) (D X : ℕ) : ℂ :=
  ∑ r ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ r,
    if χ.IsPrimitive then conj (χ (D : ZMod r)) * χ (X : ZMod r) else 0

open Classical in
/-- The number of elements of `𝒞_Q` ("at most `Q²` characters", [S-03:0196]). -/
def primitiveCharCount (Q : ℝ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 ⌊Q⌋₊, (Finset.univ.filter fun χ : DirichletCharacter ℂ r => χ.IsPrimitive).card

open Classical in
/-- **The kernel `𝒦_Λ(D, X)` of (eq:ideal-cell-kernel)** [S-03:0187–0192]:
`∑_{j : ν_{Λ j} ≥ ξ} 1_{log D ∈ I_j} 1_{log X ∈ I_j} / ν_{Λ j} · ∑_{χ ∈ 𝒞_Q} conj(χ(D)) χ(X)`.
At most one `j` contributes: the common cell of `log D` and `log X`. -/
def cellKernel (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ) (D X : ℕ) : ℂ :=
  if logCell h D = logCell h X ∧ ξ ≤ cellMass big Λ h (logCell h D) then
    ((cellMass big Λ h (logCell h D) : ℝ) : ℂ)⁻¹ * primitiveCharSum Q D X
  else 0

/-- The kernel vanishes off the diagonal of log cells: it "has support only where
`|log D - log X| < h`" [S-03:0205–0206]. -/
theorem cellKernel_eq_zero_of_logCell_ne {big : B → Finset ℕ} {Λ : B → Finset (Fin J)}
    {Q h ξ : ℝ} {D X : ℕ} (hne : logCell h D ≠ logCell h X) :
    cellKernel big Λ Q h ξ D X = 0 := by
  unfold cellKernel
  exact if_neg fun hc => hne hc.1

/-- The kernel vanishes on discarded cells ("the kernel is zero for discarded `X`",
[S-03:0205]). -/
theorem cellKernel_eq_zero_of_mass_lt {big : B → Finset ℕ} {Λ : B → Finset (Fin J)}
    {Q h ξ : ℝ} {D X : ℕ} (hlt : cellMass big Λ h (logCell h D) < ξ) :
    cellKernel big Λ Q h ξ D X = 0 := by
  unfold cellKernel
  exact if_neg fun hc => not_le.mpr hlt hc.2

/-- The `L²` norm `‖f‖₂` of a test on the label tuples of type `Λ` [S-03:0276–0278]. -/
def tupleNorm (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (f : AuxList big Λ → ℂ) : ℝ :=
  wNorm (auxWeight big Λ) f

/-- **The left side of (eq:ideal-comparison)** [S-03:0280–0288], before taking absolute values:
the expectation over four independent label tuples `X_A, X_B, D_A, D_B` (of types `A, B, A, B`) of
`conj(f(X_B)) g(X_A) [(X_A X_B)^{iζ} e(α X_A X_B) - 𝒦_A(D_A, X_A) 𝒦_B(D_B, X_B) (D_A D_B)^{iζ}
e(α D_A D_B)]`. The tests `f`, `g` are functions of the whole tuples, "not an assumption of
dependence only on the product". -/
def comparisonDefect (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ)
    (f : AuxList big Bs → ℂ) (g : AuxList big A → ℂ) (α ζ : ℝ) : ℂ :=
  ∑ xA : AuxList big A, ∑ xB : AuxList big Bs, ∑ dA : AuxList big A, ∑ dB : AuxList big Bs,
    ((auxWeight big A xA * auxWeight big Bs xB * auxWeight big A dA * auxWeight big Bs dB : ℝ) : ℂ) *
      (conj (f xB) * g xA) *
      (dilPhase ζ α (tupleProd A xA * tupleProd Bs xB) -
        cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
          cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
          dilPhase ζ α (tupleProd A dA * tupleProd Bs dB))

end Kernel

/-! ### Probes, blocks and the comparison patterns -/

section Family

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

/-- The probes of a big group: "the first `m` of the first `J` slots" [S-03:0444–0446]. -/
def probeSlots (J m : ℕ) : Finset (Fin J) := Finset.univ.filter fun i => i.val < m

theorem card_probeSlots_le (J m : ℕ) : (probeSlots J m).card ≤ m := by
  have h : (probeSlots J m).card ≤ (Finset.range m).card := by
    refine Finset.card_le_card_of_injOn (fun i : Fin J => i.val) ?_ ?_
    · intro i hi
      rw [Finset.mem_coe] at hi ⊢
      rw [probeSlots, Finset.mem_filter] at hi
      exact Finset.mem_range.mpr hi.2
    · intro i _ j _ hij
      exact Fin.ext hij
  rwa [Finset.card_range] at h

/-- A split of the big groups into two blocks `ℬ₁ = {blk = true}`, `ℬ₂ = {blk = false}` whose
sizes differ by at most one [S-03:0442–0443]. -/
def BalancedSplit (blk : B → Bool) : Prop :=
  (Finset.univ.filter fun g => blk g = true).card ≤
      (Finset.univ.filter fun g => blk g = false).card + 1 ∧
    (Finset.univ.filter fun g => blk g = false).card ≤
      (Finset.univ.filter fun g => blk g = true).card + 1

/-- The part of a family of slot sets lying in the block `b`. -/
def restrictBlock (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J)) : B → Finset (Fin J) :=
  fun g => if blk g = b then C g else ∅

/-- `C = A ∪ B` is the set of freed probes of a comparison: every `C_g` consists of probes, and
the parts `A` (in the first block) and `B` (in the second block) are nonempty
[S-03:0448–0450]. -/
def IsComparison (blk : B → Bool) (m : ℕ) (C : B → Finset (Fin J)) : Prop :=
  (∀ g, C g ⊆ probeSlots J m) ∧ (∃ g, blk g = true ∧ (C g).Nonempty) ∧
    ∃ g, blk g = false ∧ (C g).Nonempty

variable {big : B → Finset ℕ} {ℓ : ℕ}

/-- The product of the auxiliary free labels in the block `b`: `D_A` for `b = true`, `D_B` for
`b = false` [S-03:0046]. -/
def blockAuxProd (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J)) (r : AuxList big C) : ℕ :=
  ∏ g, if blk g = b then ∏ i : {i : Fin J // i ∈ C g}, (r g i : ℕ) else 1

/-- The product of the labels of the list `p` in the freed slots of the block `b`: with the target
list and `b = true` this is `X_A`, with the source list and `b = false` it is `X_B`
[S-03:0047–0048]. -/
def blockListProd (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J))
    (p : LabelList big J ℓ) : ℕ :=
  ∏ g, if blk g = b then ∏ i ∈ C g, (p g (Sum.inl i) : ℕ) else 1

/-- **The comparison pattern freeing the probes `C = A ∪ B`** [S-03:0038–0049]: its coefficient
is (eq:ideal-comparison-coefficient),
`-(-1)^{|A|+|B|} 𝒦_A(D_A, X_A) 𝒦_B(D_B, X_B)`, where `D_A, D_B` are the products of the free
labels, `X_A` is the product of the *target* labels in `A` and `X_B` the product of the *source*
(input) labels in `B`. It uses no shared label and none of the last `ℓ` labels. -/
def comparisonPattern (big : B → Finset ℕ) (J ℓ : ℕ) (blk : B → Bool) (Q h ξ : ℝ)
    (C : B → Finset (Fin J)) : Pattern big J ℓ where
  C := C
  K := fun p p' r =>
    -((-1 : ℂ) ^ (∑ g, (C g).card)) *
      (cellKernel big (restrictBlock blk true C) Q h ξ
          (blockAuxProd blk true C r) (blockListProd blk true C p') *
        cellKernel big (restrictBlock blk false C) Q h ξ
          (blockAuxProd blk false C r) (blockListProd blk false C p))

/-- The index set of the residual family: `none` is the raw pattern, `some C` the comparison
freeing `C`. -/
abbrev ComparisonIndex (B : Type) [Fintype B] [DecidableEq B] (blk : B → Bool) (J m : ℕ) : Type :=
  Option {C : B → Finset (Fin J) // IsComparison blk m C}

instance comparisonIndexFintype (blk : B → Bool) (m : ℕ) :
    Fintype {C : B → Finset (Fin J) // IsComparison blk m C} := Fintype.ofFinite _

/-- **The residual pattern family of Theorem 4.1** [S-03:0016–0026, 0038–0049, 0441–0454]: the raw
pattern (`C_g = ∅`, `K_0 = 1`) and, for every pair of nonempty sets of probes `A ⊆ ℐ₁`,
`B ⊆ ℐ₂`, the comparison pattern freeing exactly `A ∪ B`. -/
def comparisonFamily (big : B → Finset ℕ) (J ℓ m : ℕ) (blk : B → Bool) (Q h ξ : ℝ) :
    ComparisonIndex B blk J m → Pattern big J ℓ
  | none => Pattern.raw big J ℓ
  | some C => comparisonPattern big J ℓ blk Q h ξ C.1

/-- Every pattern of the residual family frees at most `m` slots in each big group:
`|C_g| ≤ m` [S-03:0023–0025]. So the family satisfies the pattern hypothesis of Theorem 3.5 with
the same `m`. -/
theorem comparisonFamily_card_le (big : B → Finset ℕ) (J ℓ m : ℕ) (blk : B → Bool) (Q h ξ : ℝ)
    (ν : ComparisonIndex B blk J m) (g : B) :
    ((comparisonFamily big J ℓ m blk Q h ξ ν).C g).card ≤ m := by
  cases ν with
  | none => simp [comparisonFamily, Pattern.raw]
  | some C => exact (Finset.card_le_card (C.2.1 g)).trans (card_probeSlots_le J m)

end Family

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
