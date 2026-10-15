module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Scales
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# One label varying, all other labels fixed

Source: `verification/stage7-sources/S-03.tex`, lines 7–9 and 216–218: "This additional
assumption allows us to use Theorem `thm:sw` with one label varying and all other labels fixed",
"hold all but one label fixed".

For a product measure, resampling one coordinate does not change an expectation:

* `Resample.sum_resample` — for independent coordinates `t_i` of laws `ν_i`,
  `E F(t) = E_t E_a F(t with the coordinate i₀ replaced by a)`, `a` of law `ν_{i₀}`.
* `Resample.sum_resample_tuple` — for a label tuple of type `Λ` and a slot `(g₀, i₀)` of `Λ`:
  `E F(t) = E_t E_u E_p F(t with the labels of the group g₀ replaced by u, and then the label of
  the slot i₀ replaced by p)`.
* `Resample.tupleProd_update` — the product of the resampled tuple is `p · R`, where `R` is the
  product of the other labels.
* `Resample.norm_sum_le_of_slices` — hence a bound for all the one-label sums
  `E_p F(…, p, …)` is a bound for `E F`: "averaging the other labels" [S-03:0239].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Resample

/-! ### The abstract statement -/

section Abstract

variable {ι : Type} [DecidableEq ι] {α : ι → Type}

/-- Exchange the coordinate `i₀` of a point with an extra value. -/
def swapAt (i₀ : ι) (q : (∀ i, α i) × α i₀) : (∀ i, α i) × α i₀ :=
  (Function.update q.1 i₀ q.2, q.1 i₀)

theorem swapAt_involutive (i₀ : ι) : Function.Involutive (swapAt (α := α) i₀) := by
  intro q
  unfold swapAt
  dsimp only
  rw [Function.update_idem, Function.update_eq_self, Function.update_self]

variable [Fintype ι] [∀ i, Fintype (α i)]

/-- The integrand of the resampled expectation on the pairs (point, new value). -/
def pairTerm (ν : ∀ i, α i → ℝ) (i₀ : ι) (F : (∀ i, α i) → ℂ) (q : (∀ i, α i) × α i₀) : ℂ :=
  ((∏ i, ν i (q.1 i) : ℝ) : ℂ) * (((ν i₀ q.2 : ℝ) : ℂ) * F (Function.update q.1 i₀ q.2))

omit [∀ i, Fintype (α i)] in
theorem pairTerm_swapAt (ν : ∀ i, α i → ℝ) (i₀ : ι) (F : (∀ i, α i) → ℂ) (t : ∀ i, α i)
    (a : α i₀) :
    pairTerm ν i₀ F (swapAt i₀ (t, a)) =
      ((ν i₀ a : ℝ) : ℂ) * (((∏ i, ν i (t i) : ℝ) : ℂ) * F t) := by
  have hW : ∀ s : ∀ i, α i,
      ∏ i, ν i (s i) = ν i₀ (s i₀) * ∏ i ∈ Finset.univ.erase i₀, ν i (s i) := fun s =>
    (Finset.mul_prod_erase Finset.univ (fun i => ν i (s i)) (Finset.mem_univ i₀)).symm
  have hW' : ∏ i ∈ Finset.univ.erase i₀, ν i (Function.update t i₀ a i) =
      ∏ i ∈ Finset.univ.erase i₀, ν i (t i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  unfold pairTerm swapAt
  dsimp only
  rw [Function.update_idem, Function.update_eq_self, hW (Function.update t i₀ a),
    Function.update_self, hW', hW t]
  push_cast
  ring

/-- **Resampling one coordinate of a product measure.** -/
theorem sum_resample (ν : ∀ i, α i → ℝ) (i₀ : ι) (hν : ∑ a, ν i₀ a = 1)
    (F : (∀ i, α i) → ℂ) :
    ∑ t : ∀ i, α i, ((∏ i, ν i (t i) : ℝ) : ℂ) * F t =
      ∑ t : ∀ i, α i, ((∏ i, ν i (t i) : ℝ) : ℂ) *
        ∑ a : α i₀, ((ν i₀ a : ℝ) : ℂ) * F (Function.update t i₀ a) := by
  have h1 : ∑ t : ∀ i, α i, ((∏ i, ν i (t i) : ℝ) : ℂ) * F t =
      ∑ t : ∀ i, α i, ∑ a : α i₀, pairTerm ν i₀ F (swapAt i₀ (t, a)) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl fun a _ => pairTerm_swapAt ν i₀ F t a, ← Finset.sum_mul,
      ← Complex.ofReal_sum, hν, Complex.ofReal_one, one_mul]
  have h2 : ∑ t : ∀ i, α i, ∑ a : α i₀, pairTerm ν i₀ F (swapAt i₀ (t, a)) =
      ∑ q : (∀ i, α i) × α i₀, pairTerm ν i₀ F (swapAt i₀ q) :=
    (Fintype.sum_prod_type fun q : (∀ i, α i) × α i₀ => pairTerm ν i₀ F (swapAt i₀ q)).symm
  have h3 : ∑ q : (∀ i, α i) × α i₀, pairTerm ν i₀ F (swapAt i₀ q) =
      ∑ q : (∀ i, α i) × α i₀, pairTerm ν i₀ F q :=
    Fintype.sum_bijective (swapAt i₀) (swapAt_involutive i₀).bijective _ _ fun _ => rfl
  have h4 : ∑ q : (∀ i, α i) × α i₀, pairTerm ν i₀ F q =
      ∑ t : ∀ i, α i, ∑ a : α i₀, pairTerm ν i₀ F (t, a) :=
    Fintype.sum_prod_type fun q : (∀ i, α i) × α i₀ => pairTerm ν i₀ F q
  rw [h1, h2, h3, h4]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  rfl

end Abstract

/-! ### Label tuples -/

section Tuples

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] {J : ℕ}

/-- The product of a tuple in which the labels of the group `g₀` are replaced by `u`, and then the
label of the slot `i₀` by `p`: `p` times the product of the other labels. -/
theorem tupleProd_update {big : B → Finset ℕ} (Λ : B → Finset (Fin J)) (t : AuxList big Λ)
    (g₀ : B) (u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ big g₀}) (i₀ : {i : Fin J // i ∈ Λ g₀})
    (p : {p : ℕ // p ∈ big g₀}) :
    tupleProd Λ (Function.update t g₀ (Function.update u i₀ p)) =
      (p : ℕ) * ((∏ i ∈ Finset.univ.erase i₀, (u i : ℕ)) *
        ∏ g ∈ Finset.univ.erase g₀, ∏ i : {i : Fin J // i ∈ Λ g}, (t g i : ℕ)) := by
  have hA : ∏ i ∈ Finset.univ.erase i₀, ((Function.update u i₀ p i : {p : ℕ // p ∈ big g₀}) : ℕ) =
      ∏ i ∈ Finset.univ.erase i₀, (u i : ℕ) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hB : ∏ g ∈ Finset.univ.erase g₀, ∏ i : {i : Fin J // i ∈ Λ g},
        ((Function.update t g₀ (Function.update u i₀ p) g i : {p : ℕ // p ∈ big g}) : ℕ) =
      ∏ g ∈ Finset.univ.erase g₀, ∏ i : {i : Fin J // i ∈ Λ g}, (t g i : ℕ) :=
    Finset.prod_congr rfl fun g hg => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hg)]
  unfold tupleProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ g₀), Function.update_self,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), Function.update_self, hA, hB,
    mul_assoc]

omit [DecidableEq B] in
/-- The labels of one big group have total probability one. -/
theorem sum_groupLaw (𝔊 : PrimeGroups P x S B) (g : B) :
    ∑ p : {p : ℕ // p ∈ 𝔊.big g}, Graph.primeGroupLaw (𝔊.big g) p = 1 := by
  rw [Finset.sum_coe_sort (𝔊.big g) (fun q => Graph.primeGroupLaw (𝔊.big g) q)]
  exact 𝔊.big_law_sum g

omit [DecidableEq B] in
/-- The label tuples of one big group have total probability one. -/
theorem sum_groupTupleLaw (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) (g : B) :
    ∑ u : {i : Fin J // i ∈ Λ g} → {p : ℕ // p ∈ 𝔊.big g},
      ∏ i, Graph.primeGroupLaw (𝔊.big g) (u i) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : {i : Fin J // i ∈ Λ g}) (q : {q : ℕ // q ∈ 𝔊.big g}) =>
    Graph.primeGroupLaw (𝔊.big g) q)]
  exact Finset.prod_eq_one fun i _ => sum_groupLaw 𝔊 g

omit [DecidableEq B] in
theorem groupTupleLaw_nonneg (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) (g : B)
    (u : {i : Fin J // i ∈ Λ g} → {p : ℕ // p ∈ 𝔊.big g}) :
    0 ≤ ∏ i, Graph.primeGroupLaw (𝔊.big g) (u i) :=
  Finset.prod_nonneg fun i _ => (𝔊.big_law_pos g (u i) (u i).2).le

/-- **Resampling one label of a tuple**: first the labels of the group `g₀`, then the label of
the slot `i₀`. -/
theorem sum_resample_tuple (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) (g₀ : B)
    (i₀ : {i : Fin J // i ∈ Λ g₀}) (F : AuxList 𝔊.big Λ → ℂ) :
    ∑ t : AuxList 𝔊.big Λ, ((auxWeight 𝔊.big Λ t : ℝ) : ℂ) * F t =
      ∑ t : AuxList 𝔊.big Λ, ((auxWeight 𝔊.big Λ t : ℝ) : ℂ) *
        ∑ u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀},
          ((∏ i, Graph.primeGroupLaw (𝔊.big g₀) (u i) : ℝ) : ℂ) *
            ∑ p : {p : ℕ // p ∈ 𝔊.big g₀}, ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
              F (Function.update t g₀ (Function.update u i₀ p)) := by
  have h1 := sum_resample
    (α := fun g : B => {i : Fin J // i ∈ Λ g} → {p : ℕ // p ∈ 𝔊.big g})
    (fun g u => ∏ i, Graph.primeGroupLaw (𝔊.big g) (u i)) g₀ (sum_groupTupleLaw 𝔊 Λ g₀) F
  have h2 : ∀ t : AuxList 𝔊.big Λ,
      ∑ u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀},
          ((∏ i, Graph.primeGroupLaw (𝔊.big g₀) (u i) : ℝ) : ℂ) * F (Function.update t g₀ u) =
        ∑ u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀},
          ((∏ i, Graph.primeGroupLaw (𝔊.big g₀) (u i) : ℝ) : ℂ) *
            ∑ p : {p : ℕ // p ∈ 𝔊.big g₀}, ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
              F (Function.update t g₀ (Function.update u i₀ p)) := fun t =>
    sum_resample (α := fun _ : {i : Fin J // i ∈ Λ g₀} => {p : ℕ // p ∈ 𝔊.big g₀})
      (fun _ p => Graph.primeGroupLaw (𝔊.big g₀) p) i₀ (sum_groupLaw 𝔊 g₀)
      (fun u => F (Function.update t g₀ u))
  calc ∑ t : AuxList 𝔊.big Λ, ((auxWeight 𝔊.big Λ t : ℝ) : ℂ) * F t
      = ∑ t : AuxList 𝔊.big Λ, ((auxWeight 𝔊.big Λ t : ℝ) : ℂ) *
          ∑ u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀},
            ((∏ i, Graph.primeGroupLaw (𝔊.big g₀) (u i) : ℝ) : ℂ) *
              F (Function.update t g₀ u) := h1
    _ = _ := Finset.sum_congr rfl fun t _ => by rw [h2 t]

/-- **Averaging the other labels** [S-03:0239]: a bound for every one-label sum is a bound for
the expectation. -/
theorem norm_sum_le_of_slices (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) (g₀ : B)
    (i₀ : {i : Fin J // i ∈ Λ g₀}) (F : AuxList 𝔊.big Λ → ℂ) (δ : ℝ)
    (h : ∀ (t : AuxList 𝔊.big Λ) (u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀}),
      ‖∑ p : {p : ℕ // p ∈ 𝔊.big g₀}, ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
        F (Function.update t g₀ (Function.update u i₀ p))‖ ≤ δ) :
    ‖∑ t : AuxList 𝔊.big Λ, ((auxWeight 𝔊.big Λ t : ℝ) : ℂ) * F t‖ ≤ δ := by
  have hinner : ∀ t : AuxList 𝔊.big Λ,
      ‖∑ u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀},
          ((∏ i, Graph.primeGroupLaw (𝔊.big g₀) (u i) : ℝ) : ℂ) *
            ∑ p : {p : ℕ // p ∈ 𝔊.big g₀}, ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
              F (Function.update t g₀ (Function.update u i₀ p))‖ ≤ δ := by
    intro t
    refine (norm_sum_le _ _).trans ?_
    calc ∑ u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀},
          ‖((∏ i, Graph.primeGroupLaw (𝔊.big g₀) (u i) : ℝ) : ℂ) *
            ∑ p : {p : ℕ // p ∈ 𝔊.big g₀}, ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
              F (Function.update t g₀ (Function.update u i₀ p))‖
        ≤ ∑ u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀},
            (∏ i, Graph.primeGroupLaw (𝔊.big g₀) (u i)) * δ := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [norm_mul, Complex.norm_of_nonneg (groupTupleLaw_nonneg 𝔊 Λ g₀ u)]
          exact mul_le_mul_of_nonneg_left (h t u) (groupTupleLaw_nonneg 𝔊 Λ g₀ u)
      _ = δ := by rw [← Finset.sum_mul, sum_groupTupleLaw 𝔊 Λ g₀, one_mul]
  rw [sum_resample_tuple 𝔊 Λ g₀ i₀ F]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ t : AuxList 𝔊.big Λ, ‖((auxWeight 𝔊.big Λ t : ℝ) : ℂ) *
        ∑ u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀},
          ((∏ i, Graph.primeGroupLaw (𝔊.big g₀) (u i) : ℝ) : ℂ) *
            ∑ p : {p : ℕ // p ∈ 𝔊.big g₀}, ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
              F (Function.update t g₀ (Function.update u i₀ p))‖
      ≤ ∑ t : AuxList 𝔊.big Λ, auxWeight 𝔊.big Λ t * δ := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [norm_mul, Complex.norm_of_nonneg (tupleWeight_nonneg 𝔊 Λ t)]
        exact mul_le_mul_of_nonneg_left (hinner t) (tupleWeight_nonneg 𝔊 Λ t)
    _ = δ := by rw [← Finset.sum_mul, sum_tupleWeight 𝔊 Λ, one_mul]

end Tuples

end Resample

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
