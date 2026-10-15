module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Objects

/-!
# Sanity of the weights with marks removed

* `partialLists_empty`, `partialWeight_empty`: with no mark removed, `partialWeight` is
  `ActiveGroups.activeWeight`, so `hMarks … ∅` is the manuscript's `H_marks = 𝒲 W_𝐭^𝐛`
  (`[P-06:0567]`).
* `EndpointConfig.endpoint_eq_hMarks`: the first endpoint in the form (cor:U-form)
  (`[P-06:0635–0640]`), `𝒰(w) = ψ_1(w/Y) w^{iσ} (∑_𝔩 1_{l ∣ w} - C_x) H_marks(w)`.
* `partialLists_singleton_apply`: in a list with the mark of `g` removed, the entry of `g` is the
  dummy list.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-- With no mark removed, the lists are the represented lists. -/
theorem partialLists_empty (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ) (n : ℕ) :
    partialLists 𝔊 t ∅ n = 𝔊.representedLists t n := by
  unfold partialLists ActiveGroups.representedLists
  simp only [Finset.notMem_empty, ↓reduceIte]

/-- With no mark removed, the weight is the active marked weight `W_𝐭^𝐛`. -/
theorem partialWeight_empty (𝔊 : ActiveGroups) (q₀ : ℝ) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    partialWeight 𝔊 q₀ t test ∅ n = 𝔊.activeWeight q₀ t test n := by
  unfold partialWeight ActiveGroups.activeWeight
  rw [partialLists_empty]
  simp only [Finset.notMem_empty, ↓reduceIte]

/-- `H_marks = 𝒲 W_𝐭^𝐛` (`[P-06:0567]`). -/
theorem hMarks_empty (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups)
    (t : 𝔊.Index → ℕ) (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    hMarks q q₀ 𝔞 x 𝔊 t test ∅ n =
      ((markedWeight q 𝔞 x n : ℝ) : ℂ) * 𝔊.activeWeight q₀ t test n := by
  unfold hMarks
  rw [partialWeight_empty]

/-- In a list with the mark of the group `g` removed, the entry of `g` is the dummy list. -/
theorem partialLists_singleton_apply {𝔊 : ActiveGroups} {t : 𝔊.Index → ℕ} {g : 𝔊.Index} {n : ℕ}
    {𝔭 : (g : 𝔊.Index) → Fin (t g) → ℕ} (h : 𝔭 ∈ partialLists 𝔊 t {g} n) :
    𝔭 g = fun _ => 0 := by
  unfold partialLists at h
  have h1 : 𝔭 g ∈ (if g ∈ ({g} : Finset 𝔊.Index) then ({fun _ => 0} : Finset (Fin (t g) → ℕ))
      else (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun p => p ∣ n).filter
        fun 𝔮 => Function.Injective 𝔮) := Fintype.mem_piFinset.mp h g
  rw [if_pos (Finset.mem_singleton_self g)] at h1
  exact Finset.mem_singleton.mp h1

namespace EndpointConfig

variable {d : ℕ}

/-- (cor:U-form) (`[P-06:0635–0640]`):
`𝒰(w) = ψ_1(w/Y) w^{iσ} (∑_𝔩 1_{l ∣ w} - C_x) H_marks(w)`. -/
theorem endpoint_eq_hMarks (c : EndpointConfig d) (D : EndpointData) (x : ℝ) (w : ℕ) :
    c.endpoint D x w = c.ψ₁ ((w : ℝ) / c.Y) * (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) *
      ((((slotCount c.S w : ℝ) - slotMass c.S : ℝ) : ℂ) *
        hMarks D.q D.q₀ D.𝔞 x c.𝔊 c.t c.test ∅ w) := by
  rw [hMarks_empty]
  unfold endpoint comparisonEndpoint centeredCore
  rw [Complex.ofReal_mul]
  ring

end EndpointConfig

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
