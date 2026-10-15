module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Hilbert
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealOperator
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Averaging the labels of a set of coordinates of `ℋ_id`

Source: `verification/stage7-sources/S-03.tex`, lines 456–489 (`[S-03:0456–0489]`).

The coordinates of the ideal space `ℋ_id = L²(∏_g 𝒫_g^M, ⊗ μ_g^{⊗M})` are the pairs
`(g, s) : B × Slot J ℓ`. For a finite set `U` of coordinates:

* `mix U p q` is the list with the labels of `q` in the coordinates of `U` and those of `p`
  elsewhere;
* `avg big J ℓ U` is the operator "averaging the labels" of the coordinates of `U`
  [S-03:0474]: `(avg U F) p = ∑_q μ(q) F (mix U p q)`, where `q` runs over all label lists with
  the product measure of `ℋ_id` (the labels of `q` outside `U` are not used and integrate
  to one).

The basic tool is `sum_swap`: the map `(p, q) ↦ (mix U p q, mix U q p)` is a measure-preserving
involution of `ℋ_id × ℋ_id`. It gives `avg U * avg V = avg (U ∪ V)` (`avg_mul`), that `avg U` is
self-adjoint (`avg_sa`) and preserves integrals (`sum_avg`). So the averages form an
`AvgSystem` (`labelAvg`), and `avg` intertwines slot permutations (`avg_permute`, `permOp_D`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Mixing two label lists -/

section Mix

variable {B : Type} [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- The list with the labels of `q` in the coordinates of `U` and the labels of `p` elsewhere. -/
def mix (U : Finset (B × Slot J ℓ)) (p q : LabelList big J ℓ) : LabelList big J ℓ :=
  fun g s => if (g, s) ∈ U then q g s else p g s

theorem mix_of_mem {U : Finset (B × Slot J ℓ)} (p q : LabelList big J ℓ) {g : B}
    {s : Slot J ℓ} (h : (g, s) ∈ U) : mix U p q g s = q g s := by
  simp [mix, h]

theorem mix_of_notMem {U : Finset (B × Slot J ℓ)} (p q : LabelList big J ℓ) {g : B}
    {s : Slot J ℓ} (h : (g, s) ∉ U) : mix U p q g s = p g s := by
  simp [mix, h]

theorem mix_empty (p q : LabelList big J ℓ) : mix (∅ : Finset (B × Slot J ℓ)) p q = p := by
  funext g s
  exact mix_of_notMem p q (Finset.notMem_empty _)

/-- The swap `(p, q) ↦ (mix U p q, mix U q p)` is an involution. -/
theorem mix_mix_swap (U : Finset (B × Slot J ℓ)) (p q : LabelList big J ℓ) :
    mix U (mix U p q) (mix U q p) = p := by
  funext g s
  by_cases h : (g, s) ∈ U <;> simp [mix, h]

theorem mix_mix_same (U : Finset (B × Slot J ℓ)) (p q q' : LabelList big J ℓ) :
    mix U (mix U p q) q' = mix U p q' := by
  funext g s
  by_cases h : (g, s) ∈ U <;> simp [mix, h]

theorem mix_mix_union (U V : Finset (B × Slot J ℓ)) (p q q' : LabelList big J ℓ) :
    mix V (mix U p q) q' = mix (U ∪ V) p (mix V q q') := by
  funext g s
  by_cases hV : (g, s) ∈ V
  · simp [mix, hV]
  · by_cases hU : (g, s) ∈ U <;> simp [mix, hV, hU]

/-- Mixing in disjoint sets of coordinates commutes. -/
theorem mix_mix_comm {U V : Finset (B × Slot J ℓ)} (h : Disjoint U V)
    (p q q' : LabelList big J ℓ) : mix U (mix V p q) q' = mix V (mix U p q') q := by
  funext g s
  by_cases hU : (g, s) ∈ U
  · have hV : (g, s) ∉ V := Finset.disjoint_left.mp h hU
    simp [mix, hU, hV]
  · by_cases hV : (g, s) ∈ V <;> simp [mix, hU, hV]

/-- `F` does not depend on the labels in the coordinates of `U`. -/
def Indep (U : Finset (B × Slot J ℓ)) (F : LabelList big J ℓ → ℂ) : Prop :=
  ∀ p q : LabelList big J ℓ, F (mix U p q) = F p

theorem Indep.mono {U V : Finset (B × Slot J ℓ)} {F : LabelList big J ℓ → ℂ}
    (h : Indep U F) (hVU : V ⊆ U) : Indep V F := by
  intro p q
  have e : mix V p q = mix U p (mix V p q) := by
    funext g s
    by_cases hV : (g, s) ∈ V
    · have hU : (g, s) ∈ U := hVU hV
      simp [mix, hV, hU]
    · by_cases hU : (g, s) ∈ U <;> simp [mix, hV, hU]
  rw [e, h]

theorem Indep.union {U V : Finset (B × Slot J ℓ)} {F : LabelList big J ℓ → ℂ}
    (hU : Indep U F) (hV : Indep V F) : Indep (U ∪ V) F := by
  intro p q
  have e : mix (U ∪ V) p q = mix V (mix U p q) q := by
    funext g s
    by_cases h2 : (g, s) ∈ V
    · simp [mix, h2]
    · by_cases h1 : (g, s) ∈ U <;> simp [mix, h1, h2]
  rw [e, hV, hU]

theorem Indep.mul {U : Finset (B × Slot J ℓ)} {k F : LabelList big J ℓ → ℂ}
    (hk : Indep U k) (hF : Indep U F) : Indep U (fun p => k p * F p) := by
  intro p q
  show k (mix U p q) * F (mix U p q) = k p * F p
  rw [hk p q, hF p q]

/-- The action of a family of slot permutations on the coordinates. -/
def coordPerm (σ : SlotPerms B J ℓ) (k : B × Slot J ℓ) : B × Slot J ℓ := (k.1, σ k.1 k.2)

omit [DecidableEq B] in
theorem coordPerm_injective (σ : SlotPerms B J ℓ) : Function.Injective (coordPerm σ) := by
  intro k k' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have h1' : k.1 = k'.1 := h1
  have h2' : σ k.1 k.2 = σ k'.1 k'.2 := h2
  rw [← h1'] at h2'
  exact Prod.ext h1' ((σ k.1).injective h2')

theorem mix_permute (σ : SlotPerms B J ℓ) (U : Finset (B × Slot J ℓ))
    (p q : LabelList big J ℓ) :
    mix U (permuteSlots σ p) (permuteSlots σ q) =
      permuteSlots σ (mix (U.image (coordPerm σ)) p q) := by
  funext g s
  have hiff : (g, σ g s) ∈ U.image (coordPerm σ) ↔ (g, s) ∈ U := by
    constructor
    · intro h
      obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.mp h
      have hk' : k = (g, s) := coordPerm_injective σ hkeq
      rw [← hk']
      exact hk
    · intro h
      exact Finset.mem_image.mpr ⟨(g, s), h, rfl⟩
  by_cases h : (g, s) ∈ U
  · have h' := hiff.mpr h
    rw [mix_of_mem _ _ h]
    show permuteSlots σ q g s = mix (U.image (coordPerm σ)) p q g (σ g s)
    rw [mix_of_mem _ _ h']
    rfl
  · have h' : (g, σ g s) ∉ U.image (coordPerm σ) := fun hh => h (hiff.mp hh)
    rw [mix_of_notMem _ _ h]
    show permuteSlots σ p g s = mix (U.image (coordPerm σ)) p q g (σ g s)
    rw [mix_of_notMem _ _ h']
    rfl

end Mix

/-! ### Averages -/

section Avg

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

theorem idealWeight_mix_mul (U : Finset (B × Slot J ℓ)) (p q : LabelList big J ℓ) :
    idealWeight big J ℓ (mix U p q) * idealWeight big J ℓ (mix U q p) =
      idealWeight big J ℓ p * idealWeight big J ℓ q := by
  unfold idealWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases h : (g, s) ∈ U
  · rw [mix_of_mem p q h, mix_of_mem q p h, mul_comm]
  · rw [mix_of_notMem p q h, mix_of_notMem q p h]

/-- The swap of the labels in the coordinates of `U`, as a bijection of pairs of lists. -/
def swapEquiv (U : Finset (B × Slot J ℓ)) :
    (LabelList big J ℓ × LabelList big J ℓ) ≃ (LabelList big J ℓ × LabelList big J ℓ) where
  toFun x := (mix U x.1 x.2, mix U x.2 x.1)
  invFun x := (mix U x.1 x.2, mix U x.2 x.1)
  left_inv x := Prod.ext (mix_mix_swap U x.1 x.2) (mix_mix_swap U x.2 x.1)
  right_inv x := Prod.ext (mix_mix_swap U x.1 x.2) (mix_mix_swap U x.2 x.1)

/-- **The swap is measure preserving**: a sum over two independent lists is unchanged when the
labels in the coordinates of `U` are exchanged. -/
theorem sum_swap (U : Finset (B × Slot J ℓ))
    (Φ : LabelList big J ℓ → LabelList big J ℓ → ℂ) :
    ∑ p, ∑ q, (idealWeight big J ℓ p : ℂ) * ((idealWeight big J ℓ q : ℂ) *
        Φ (mix U p q) (mix U q p)) =
      ∑ p, ∑ q, (idealWeight big J ℓ p : ℂ) * ((idealWeight big J ℓ q : ℂ) * Φ p q) := by
  have key : ∀ x : LabelList big J ℓ × LabelList big J ℓ,
      (idealWeight big J ℓ x.1 : ℂ) * ((idealWeight big J ℓ x.2 : ℂ) *
        Φ (mix U x.1 x.2) (mix U x.2 x.1)) =
      (idealWeight big J ℓ (mix U x.1 x.2) : ℂ) *
        ((idealWeight big J ℓ (mix U x.2 x.1) : ℂ) * Φ (mix U x.1 x.2) (mix U x.2 x.1)) := by
    intro x
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      idealWeight_mix_mul U x.1 x.2]
  calc ∑ p, ∑ q, (idealWeight big J ℓ p : ℂ) * ((idealWeight big J ℓ q : ℂ) *
        Φ (mix U p q) (mix U q p))
      = ∑ x : LabelList big J ℓ × LabelList big J ℓ,
          (idealWeight big J ℓ x.1 : ℂ) * ((idealWeight big J ℓ x.2 : ℂ) *
            Φ (mix U x.1 x.2) (mix U x.2 x.1)) :=
        (Fintype.sum_prod_type (fun x : LabelList big J ℓ × LabelList big J ℓ =>
          (idealWeight big J ℓ x.1 : ℂ) * ((idealWeight big J ℓ x.2 : ℂ) *
            Φ (mix U x.1 x.2) (mix U x.2 x.1)))).symm
    _ = ∑ x : LabelList big J ℓ × LabelList big J ℓ,
          (idealWeight big J ℓ x.1 : ℂ) * ((idealWeight big J ℓ x.2 : ℂ) * Φ x.1 x.2) :=
        Fintype.sum_equiv (swapEquiv U)
          (fun x : LabelList big J ℓ × LabelList big J ℓ =>
            (idealWeight big J ℓ x.1 : ℂ) * ((idealWeight big J ℓ x.2 : ℂ) *
              Φ (mix U x.1 x.2) (mix U x.2 x.1)))
          (fun x : LabelList big J ℓ × LabelList big J ℓ =>
            (idealWeight big J ℓ x.1 : ℂ) * ((idealWeight big J ℓ x.2 : ℂ) * Φ x.1 x.2))
          (fun x => key x)
    _ = ∑ p, ∑ q, (idealWeight big J ℓ p : ℂ) * ((idealWeight big J ℓ q : ℂ) * Φ p q) :=
        Fintype.sum_prod_type (fun x : LabelList big J ℓ × LabelList big J ℓ =>
          (idealWeight big J ℓ x.1 : ℂ) * ((idealWeight big J ℓ x.2 : ℂ) * Φ x.1 x.2))

theorem sum_idealWeight_cast (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1) :
    ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) = 1 := by
  rw [← Complex.ofReal_sum, sum_idealWeight hlaw, Complex.ofReal_one]

/-- **Averaging the labels of the coordinates of `U`** [S-03:0474]. -/
def avg (big : B → Finset ℕ) (J ℓ : ℕ) (U : Finset (B × Slot J ℓ)) :
    Module.End ℂ (LabelList big J ℓ → ℂ) :=
  rowOp (Ξ := LabelList big J ℓ) (fun _ q => (idealWeight big J ℓ q : ℂ))
    (fun p q => mix U p q)

theorem avg_apply (U : Finset (B × Slot J ℓ)) (F : LabelList big J ℓ → ℂ)
    (p : LabelList big J ℓ) :
    avg big J ℓ U F p = ∑ q, (idealWeight big J ℓ q : ℂ) * F (mix U p q) := rfl

theorem avg_empty (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1) :
    avg big J ℓ (∅ : Finset (B × Slot J ℓ)) = 1 := by
  refine LinearMap.ext fun F => funext fun p => ?_
  rw [avg_apply]
  simp only [mix_empty]
  rw [← Finset.sum_mul, sum_idealWeight_cast hlaw, one_mul]
  rfl

theorem avg_mul (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (U V : Finset (B × Slot J ℓ)) :
    avg big J ℓ U * avg big J ℓ V = avg big J ℓ (U ∪ V) := by
  refine LinearMap.ext fun F => funext fun p => ?_
  have h1 : avg big J ℓ U (avg big J ℓ V F) p =
      ∑ q, ∑ q', (idealWeight big J ℓ q : ℂ) * ((idealWeight big J ℓ q' : ℂ) *
        F (mix (U ∪ V) p (mix V q q'))) := by
    rw [avg_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [avg_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    rw [mix_mix_union]
  show avg big J ℓ U (avg big J ℓ V F) p = avg big J ℓ (U ∪ V) F p
  rw [h1, sum_swap V (fun a _ => F (mix (U ∪ V) p a)), avg_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.mul_sum, ← Finset.sum_mul, sum_idealWeight_cast hlaw, one_mul]

theorem avg_sa (U : Finset (B × Slot J ℓ)) :
    IsSA (idealWeight big J ℓ) (avg big J ℓ U) := by
  intro G H
  have hL : wInner (idealWeight big J ℓ) G (avg big J ℓ U H) =
      ∑ p, ∑ q, (idealWeight big J ℓ p : ℂ) * ((idealWeight big J ℓ q : ℂ) *
        (conj (G p) * H (mix U p q))) := by
    unfold wInner
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [avg_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hR : wInner (idealWeight big J ℓ) (avg big J ℓ U G) H =
      ∑ p, ∑ q, (idealWeight big J ℓ p : ℂ) * ((idealWeight big J ℓ q : ℂ) *
        (conj (G (mix U p q)) * H p)) := by
    unfold wInner
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [avg_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  have h := sum_swap U (fun a b => conj (G a) * H (mix U a b))
  simp only [mix_mix_swap] at h
  rw [hL, hR]
  exact h.symm

/-- Averaging preserves integrals. -/
theorem sum_avg (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (U : Finset (B × Slot J ℓ)) (F : LabelList big J ℓ → ℂ) :
    ∑ p, (idealWeight big J ℓ p : ℂ) * avg big J ℓ U F p =
      ∑ p, (idealWeight big J ℓ p : ℂ) * F p := by
  have h := sum_swap U (fun a (_ : LabelList big J ℓ) => F a)
  calc ∑ p, (idealWeight big J ℓ p : ℂ) * avg big J ℓ U F p
      = ∑ p, ∑ q, (idealWeight big J ℓ p : ℂ) * ((idealWeight big J ℓ q : ℂ) *
          F (mix U p q)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [avg_apply, Finset.mul_sum]
    _ = ∑ p, ∑ q, (idealWeight big J ℓ p : ℂ) * ((idealWeight big J ℓ q : ℂ) * F p) := h
    _ = ∑ p, (idealWeight big J ℓ p : ℂ) * F p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul, sum_idealWeight_cast hlaw, one_mul]

/-- The conditional second moments integrate to the squared norm. -/
theorem sum_cond_sq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (U : Finset (B × Slot J ℓ)) (G : LabelList big J ℓ → ℂ) :
    ∑ p, idealWeight big J ℓ p * ∑ q, idealWeight big J ℓ q * ‖G (mix U p q)‖ ^ 2 =
      wNormSq (idealWeight big J ℓ) G := by
  have h := sum_avg hlaw U (fun p => ((‖G p‖ ^ 2 : ℝ) : ℂ))
  simp only [avg_apply] at h
  unfold wNormSq
  exact_mod_cast h

/-- **The averaging system of `ℋ_id`**: `E U = avg U`. -/
def labelAvg (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1) :
    AvgSystem (B × Slot J ℓ) (idealWeight big J ℓ) where
  E := avg big J ℓ
  E_empty := avg_empty hlaw
  E_mul := avg_mul hlaw
  E_sa := avg_sa

theorem labelAvg_E (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (U : Finset (B × Slot J ℓ)) :
    (labelAvg (J := J) (ℓ := ℓ) hlaw).E U = avg big J ℓ U := rfl

/-! ### Independence of a set of coordinates -/

theorem indep_avg (U : Finset (B × Slot J ℓ)) (F : LabelList big J ℓ → ℂ) :
    Indep U (avg big J ℓ U F) := by
  intro p q
  rw [avg_apply, avg_apply]
  simp only [mix_mix_same]

theorem avg_of_indep (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {U : Finset (B × Slot J ℓ)} {F : LabelList big J ℓ → ℂ} (h : Indep U F) :
    avg big J ℓ U F = F := by
  funext p
  rw [avg_apply]
  simp only [h p]
  rw [← Finset.sum_mul, sum_idealWeight_cast hlaw, one_mul]

/-- Averaging a set of coordinates preserves independence of another set. -/
theorem indep_avg_of_indep {U V : Finset (B × Slot J ℓ)} {F : LabelList big J ℓ → ℂ}
    (h : Indep V F) : Indep V (avg big J ℓ U F) := by
  intro p q
  rw [avg_apply, avg_apply]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have e : mix U (mix V p q) q' = mix V (mix U p q') (mix U q q') := by
    funext g s
    by_cases h1 : (g, s) ∈ U
    · by_cases h2 : (g, s) ∈ V <;> simp [mix, h1, h2]
    · by_cases h2 : (g, s) ∈ V <;> simp [mix, h1, h2]
  rw [e, h]

/-- A multiplier which does not depend on the coordinates of `V` commutes with `avg V`. -/
theorem avg_mul_left_of_indep {V : Finset (B × Slot J ℓ)} {k : LabelList big J ℓ → ℂ}
    (hk : Indep V k) (F : LabelList big J ℓ → ℂ) :
    avg big J ℓ V (fun p => k p * F p) = fun p => k p * avg big J ℓ V F p := by
  funext p
  show avg big J ℓ V (fun p => k p * F p) p = k p * avg big J ℓ V F p
  rw [avg_apply, avg_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  show (idealWeight big J ℓ q : ℂ) * (k (mix V p q) * F (mix V p q)) =
    k p * ((idealWeight big J ℓ q : ℂ) * F (mix V p q))
  rw [hk p q]
  ring

/-- Pairing with a function which does not depend on the coordinates of `U`: the other entry
may be averaged. -/
theorem wInner_avg_left_of_indep (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {U : Finset (B × Slot J ℓ)} (G : LabelList big J ℓ → ℂ) {Ψ : LabelList big J ℓ → ℂ}
    (h : Indep U Ψ) :
    wInner (idealWeight big J ℓ) G Ψ = wInner (idealWeight big J ℓ) (avg big J ℓ U G) Ψ := by
  have h1 := avg_sa (big := big) U G Ψ
  rw [avg_of_indep hlaw h] at h1
  exact h1

/-! ### Slot permutations -/

/-- Composition with a family of slot permutations. -/
def permOp (σ : SlotPerms B J ℓ) : Module.End ℂ (LabelList big J ℓ → ℂ) where
  toFun F := fun p => F (permuteSlots σ p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype B] [DecidableEq B] in
theorem permOp_apply (σ : SlotPerms B J ℓ) (F : LabelList big J ℓ → ℂ)
    (p : LabelList big J ℓ) : permOp σ F p = F (permuteSlots σ p) := rfl

theorem wNormSq_permOp (σ : SlotPerms B J ℓ) (F : LabelList big J ℓ → ℂ) :
    wNormSq (idealWeight big J ℓ) (permOp σ F) = wNormSq (idealWeight big J ℓ) F := by
  unfold wNormSq
  refine Fintype.sum_equiv (permuteEquiv σ)
    (fun p => idealWeight big J ℓ p * ‖permOp σ F p‖ ^ 2)
    (fun p => idealWeight big J ℓ p * ‖F p‖ ^ 2) fun p => ?_
  show idealWeight big J ℓ p * ‖permOp σ F p‖ ^ 2 =
    idealWeight big J ℓ (permuteSlots σ p) * ‖F (permuteSlots σ p)‖ ^ 2
  rw [idealWeight_permute]
  rfl

theorem avg_permute (σ : SlotPerms B J ℓ) (U : Finset (B × Slot J ℓ))
    (F : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    avg big J ℓ U F (permuteSlots σ p) =
      avg big J ℓ (U.image (coordPerm σ)) (permOp σ F) p := by
  rw [avg_apply, avg_apply]
  refine (Fintype.sum_equiv (permuteEquiv σ)
    (fun q => (idealWeight big J ℓ q : ℂ) * permOp σ F (mix (U.image (coordPerm σ)) p q))
    (fun q => (idealWeight big J ℓ q : ℂ) * F (mix U (permuteSlots σ p) q)) fun q => ?_).symm
  show (idealWeight big J ℓ q : ℂ) * permOp σ F (mix (U.image (coordPerm σ)) p q) =
    (idealWeight big J ℓ (permuteSlots σ q) : ℂ) *
      F (mix U (permuteSlots σ p) (permuteSlots σ q))
  rw [idealWeight_permute, mix_permute]
  rfl

/-- Slot permutations intertwine the projections `D`. -/
theorem permOp_D (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (σ : SlotPerms B J ℓ) (V : Finset (B × Slot J ℓ)) (G : LabelList big J ℓ → ℂ) :
    permOp σ ((labelAvg hlaw).D V G) =
      (labelAvg hlaw).D (V.image (coordPerm σ)) (permOp σ G) :=
  (labelAvg hlaw).D_equivariant (coordPerm σ) (coordPerm_injective σ) (permOp σ)
    (fun V G => funext fun p => avg_permute σ V G p) V G

/-- The values of `bigSym F` are invariant under slot permutations. -/
theorem bigSym_permute (F : LabelList big J ℓ → ℂ) (σ : SlotPerms B J ℓ)
    (p : LabelList big J ℓ) :
    bigSym big J ℓ F (permuteSlots σ p) = bigSym big J ℓ F p := by
  have hsum : ∑ τ : SlotPerms B J ℓ, F (permuteSlots τ (permuteSlots σ p)) =
      ∑ ρ : SlotPerms B J ℓ, F (permuteSlots ρ p) :=
    Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun τ => by
      simp only [Equiv.coe_mulLeft, permuteSlots_mul]
  rw [bigSym_apply, bigSym_apply, hsum]

end Avg

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction
