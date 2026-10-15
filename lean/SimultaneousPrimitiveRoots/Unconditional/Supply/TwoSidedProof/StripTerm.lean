module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.StripStates
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.Pointwise

/-!
# Removal of the shared labels: one term

`[P-06:0318–0346]`. For a pattern `ν` with freed slots `C_g`, at `n = D_R w`, `n' = D_R (w + D_C)`:

* `corePart`: the factor `Ψ(w/(x D_C))/w · 𝓑(w, w + D_C) F(w) G(w + D_C)` of a stripped term;
  `edgeSummand_mk`: the summand of the edge sum is `corePart` times the list factors
  (`1/n = 1/(D_R w)`, the invariance of the cores and of the joint factor).
* `edgeList σ r w`: the list factors of the edge sum summed over the unshared labels of the two
  endpoints; `mainList r w`: the list factors of the stripped expression (cor:stripped).
* `edgeList_of_good`: away from collisions (`Good`) and when no free label divides `w`,
  `edgeList σ r w = (law of σ) · mainList r w`: "The factor `D_R⁻¹` changes each shared sum into
  its probability law `μ_g`, and the remaining list factors and damping are exactly
  `W_𝐭(w) W_𝐭(w')`."
* `norm_edgeList_le` (for all shared labels, by the count (eq:physical-count-bound) of [S]) and
  `norm_mainList_le` (by (cor:marked-bound)); `norm_edgeList_sub_le` combines the three.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

namespace Strip

section Term

variable {𝔊 : ActiveGroups} {J : ℕ} {P : ActiveGroupConstants} {x₀ : ℝ}

/-! ### Definitions -/

/-- The factor of a term of the stripped sums that involves neither the lists nor the active
marks: `Ψ(w/(x D_C))/w · 𝓑(w, w + D_C) · F(w) · G(w + D_C)`. -/
def corePart (x : ℝ) (Ψ : ℝ → ℂ) {H : ℕ} (𝔅 : JointResidueWeight H) (F : ℕ → ℝ) (G : ℕ → ℂ)
    (C : Fin 𝔊.numBig → Finset (Fin J)) (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) : ℂ :=
  Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
    ((𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H) : ℝ) : ℂ) *
    ((F w : ℝ) : ℂ) * G (w + tupleProd C r)

/-- **The list factors of the edge sum** at the shared labels `σ`, the free labels `r` and the
position `n = D_R w`, summed over the unshared labels of the two endpoints. -/
def edgeList (q₀ : ℝ) (ν : Pattern (groupFamily 𝔊).big J 1) (σ : ShT 𝔊 ν.C)
    (r : AuxList (groupFamily 𝔊).big ν.C) (w : ℕ) : ℂ :=
  ∑ u : UnT 𝔊 ν.C, ∑ u' : UnT 𝔊 ν.C,
    ((((shProd σ : ℕ) : ℝ)⁻¹ * stateMass (groupFamily 𝔊) J 1 *
        (damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) *
          damping intPos (groupFamily 𝔊) J 1 q₀
            ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)) : ℝ) : ℂ) *
      physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 ((shProd σ * w : ℕ) : ℤ)
        ((listSplit 𝔊 ν.C).symm (σ, u)) r ((listSplit 𝔊 ν.C).symm (σ, u'))

/-- **The list factors of the stripped expression** (cor:stripped) at the free labels `r` and the
position `w`: the law of `r`, the two scalar factors of `W_𝐭` and the double sum of the stripped
coefficient `κ` over the represented lists. -/
def mainList (q₀ : ℝ) (C : Fin 𝔊.numBig → Finset (Fin J))
    (κ : AuxList (groupFamily 𝔊).big C → ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) →
      ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ)
    (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) : ℂ :=
  ((auxWeight (groupFamily 𝔊).big C r * (activeCoeff 𝔊 q₀ (markCount 𝔊 C) w *
      activeCoeff 𝔊 q₀ (markCount 𝔊 C) (w + tupleProd C r)) : ℝ) : ℂ) *
    ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
      ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r), κ r 𝔭 𝔭'

open _root_.Classical in
/-- The indicator that a free label divides `w` (then it divides `w + D_C` as well). -/
def freeInd {C : Fin 𝔊.numBig → Finset (Fin J)} (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) :
    ℝ :=
  if ∃ (g : Fin 𝔊.numBig) (i : {i : Fin J // i ∈ C g}), (r g i : ℕ) ∣ w then 1 else 0

theorem freeInd_nonneg {C : Fin 𝔊.numBig → Finset (Fin J)}
    (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) : 0 ≤ freeInd r w := by
  unfold freeInd
  split_ifs
  · exact zero_le_one
  · exact le_rfl

/-! ### Elementary facts -/

/-- Every free label divides the product of the free labels. -/
theorem aux_dvd_tupleProd {C : Fin 𝔊.numBig → Finset (Fin J)}
    (r : AuxList (groupFamily 𝔊).big C) (g : Fin 𝔊.numBig) (i : {i : Fin J // i ∈ C g}) :
    (r g i : ℕ) ∣ tupleProd C r := by
  unfold tupleProd
  exact (Finset.dvd_prod_of_mem (fun i' : {i : Fin J // i ∈ C g} => (r g i' : ℕ))
      (Finset.mem_univ i)).trans
    (Finset.dvd_prod_of_mem
      (fun g' : Fin 𝔊.numBig => ∏ i' : {i : Fin J // i ∈ C g'}, (r g' i' : ℕ))
      (Finset.mem_univ g))

/-- A position with a represented list has at least `∑_g t_g` active prime divisors. -/
theorem sum_markCount_le_totalHits {C : Fin 𝔊.numBig → Finset (Fin J)} {u : UnT 𝔊 C} {w : ℕ}
    (hu : IsRepr u w) : ∑ g, markCount 𝔊 C g ≤ 𝔊.totalHits w := by
  unfold ActiveGroups.totalHits
  refine Finset.sum_le_sum fun g _ => ?_
  have h : (Finset.univ : Finset (Fin (markCount 𝔊 C g))).card ≤
      ((𝔊.group g).filter fun p => p ∣ w).card :=
    Finset.card_le_card_of_injOn (fun j => (u g j : ℕ))
      (fun j _ => Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨(u g j).2, hu.2 g j⟩))
      (fun j _ j' _ hjj' => hu.1 g (Subtype.ext hjj'))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

/-- The target position `n + D` of the operators is `D_R (w + D_C)`. -/
theorem shift_mk (ν : Pattern (groupFamily 𝔊).big J 1) (σ : ShT 𝔊 ν.C) (u : UnT 𝔊 ν.C)
    (r : AuxList (groupFamily 𝔊).big ν.C) (w : ℕ) :
    intPos.shift (1 * (dil ν.C ((listSplit 𝔊 ν.C).symm (σ, u)) r : ℤ))
        ((shProd σ * w : ℕ) : ℤ) =
      ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ) := by
  rw [intPos_shift_one_mul, dil_mk]
  exact (by push_cast; ring : ((shProd σ * w : ℕ) : ℤ) + ((shProd σ * tupleProd ν.C r : ℕ) : ℤ) =
    ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ))

/-- The algebra of (cor:stripping-normalization). -/
theorem strip_alg {R' sm d1 d2 aux tn shW a1 a2 : ℝ} (e1 : sm * R' = shW * tn)
    (e2 : tn * d1 ^ 2 = a1) (e3 : tn * d2 ^ 2 = a2) :
    (R' * sm * (d1 * d2)) * (aux * tn * (d1 * d2)) = shW * (aux * (a1 * a2)) := by
  linear_combination (aux * tn * d1 ^ 2 * d2 ^ 2) * e1 + (shW * aux * tn * d2 ^ 2) * e2 +
    (shW * aux * a1) * e3

/-! ### The summand of the edge sum at `n = D_R w` -/

/-- **The summand of the edge sum at `n = D_R w`** (`[P-06:0318–0328]`, `[PUB-tex:0482–0485]`):
`1/n = 1/(D_R w)`, the cores and the joint factor are invariant under the shared labels. -/
theorem edgeSummand_mk (h𝔊 : 𝔊.Admissible P x₀) {H : ℕ} (hH0 : 0 < H)
    (hH : ∀ p ∈ 𝔊.allPrimes, H < p) (𝔅 : JointResidueWeight H) {F : ℕ → ℝ}
    (hF : ∀ p ∈ 𝔊.allPrimes, ∀ n : ℕ, F (p * n) = F n) {x₁ Cg : ℝ} {G : ℕ → ℂ}
    (hG : CoreAdmissible 𝔊 x₁ Cg G) (q₀ x : ℝ) (Ψ : ℝ → ℂ)
    (ν : Pattern (groupFamily 𝔊).big J 1) (σ : ShT 𝔊 ν.C) (u u' : UnT 𝔊 ν.C)
    (r : AuxList (groupFamily 𝔊).big ν.C) {w : ℕ} (hw : 0 < w) :
    edgeSummand 𝔊 q₀ ν x Ψ 𝔅 F G ((shProd σ * w : ℕ) : ℤ)
        ((listSplit 𝔊 ν.C).symm (σ, u)) r ((listSplit 𝔊 ν.C).symm (σ, u')) =
      corePart x Ψ 𝔅 F G ν.C r w *
        (((((shProd σ : ℕ) : ℝ)⁻¹ * stateMass (groupFamily 𝔊) J 1 *
            (damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) *
              damping intPos (groupFamily 𝔊) J 1 q₀
                ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)) : ℝ) : ℂ) *
          physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 ((shProd σ * w : ℕ) : ℤ)
            ((listSplit 𝔊 ν.C).symm (σ, u)) r ((listSplit 𝔊 ν.C).symm (σ, u'))) := by
  have hR : 0 < shProd σ := shProd_pos h𝔊 σ
  have hRR : ((shProd σ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have hD : dil ν.C ((listSplit 𝔊 ν.C).symm (σ, u)) r = shProd σ * tupleProd ν.C r :=
    dil_mk σ u r
  have hn' : ((shProd σ * w : ℕ) : ℤ) + ((shProd σ * tupleProd ν.C r : ℕ) : ℤ) =
      ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ) := by
    push_cast
    ring
  have hΨ : ((((shProd σ * w : ℕ) : ℤ) : ℝ)) / (x * ((shProd σ * tupleProd ν.C r : ℕ) : ℝ)) =
      (w : ℝ) / (x * (tupleProd ν.C r : ℝ)) := by
    rw [Int.cast_natCast, Nat.cast_mul, Nat.cast_mul, mul_left_comm x,
      mul_div_mul_left _ _ hRR]
  have hB := weight_shProd_mul h𝔊 hH0 hH 𝔅 σ w (w + tupleProd ν.C r)
  have hFv := first_shProd_mul hF σ w
  have hGv := core_shProd_mul h𝔊 hG σ (v := w + tupleProd ν.C r) (Nat.add_pos_left hw _)
  have hinv : (((shProd σ * w : ℕ) : ℤ) : ℂ) = ((shProd σ : ℕ) : ℂ) * (w : ℂ) := by
    rw [Int.cast_natCast, Nat.cast_mul]
  unfold edgeSummand corePart
  rw [hD, hn', hΨ, hinv]
  simp only [Int.cast_natCast, Int.toNat_natCast]
  rw [hB, hFv, hGv]
  push_cast
  ring

/-- The summands at `n = D_R w`, summed over the unshared labels. -/
theorem sum_edgeSummand_mk (h𝔊 : 𝔊.Admissible P x₀) {H : ℕ} (hH0 : 0 < H)
    (hH : ∀ p ∈ 𝔊.allPrimes, H < p) (𝔅 : JointResidueWeight H) {F : ℕ → ℝ}
    (hF : ∀ p ∈ 𝔊.allPrimes, ∀ n : ℕ, F (p * n) = F n) {x₁ Cg : ℝ} {G : ℕ → ℂ}
    (hG : CoreAdmissible 𝔊 x₁ Cg G) (q₀ x : ℝ) (Ψ : ℝ → ℂ)
    (ν : Pattern (groupFamily 𝔊).big J 1) (σ : ShT 𝔊 ν.C)
    (r : AuxList (groupFamily 𝔊).big ν.C) {w : ℕ} (hw : 0 < w) :
    ∑ u : UnT 𝔊 ν.C, ∑ u' : UnT 𝔊 ν.C,
        edgeSummand 𝔊 q₀ ν x Ψ 𝔅 F G ((shProd σ * w : ℕ) : ℤ)
          ((listSplit 𝔊 ν.C).symm (σ, u)) r ((listSplit 𝔊 ν.C).symm (σ, u')) =
      corePart x Ψ 𝔅 F G ν.C r w * edgeList q₀ ν σ r w := by
  unfold edgeList
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u' _ =>
    edgeSummand_mk h𝔊 hH0 hH 𝔅 hF hG q₀ x Ψ ν σ u u' r hw

/-! ### Away from collisions -/

open _root_.Classical in
/-- **The row coefficient away from collisions**: it is the product of its factors exactly when
the unshared labels of the two endpoints are represented lists at `w` and at `w + D_C`. -/
theorem physCoef_mk_of_good (h𝔊 : 𝔊.Admissible P x₀) (q₀ : ℝ)
    (ν : Pattern (groupFamily 𝔊).big J 1) (σ : ShT 𝔊 ν.C) (u u' : UnT 𝔊 ν.C)
    (r : AuxList (groupFamily 𝔊).big ν.C) {w : ℕ} (hgood : Good σ (forbid r w))
    (hfree : ∀ (g : Fin 𝔊.numBig) (i : {i : Fin J // i ∈ ν.C g}), ¬(r g i : ℕ) ∣ w) :
    physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 ((shProd σ * w : ℕ) : ℤ)
        ((listSplit 𝔊 ν.C).symm (σ, u)) r ((listSplit 𝔊 ν.C).symm (σ, u')) =
      if IsRepr u w ∧ IsRepr u' (w + tupleProd ν.C r) then
        ((auxWeight (groupFamily 𝔊).big ν.C r * targetNorm (groupFamily 𝔊) 1 ν.C *
            (damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) *
              damping intPos (groupFamily 𝔊) J 1 q₀
                ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)) : ℝ) : ℂ) *
          ν.K ((listSplit 𝔊 ν.C).symm (σ, u)).2 ((listSplit 𝔊 ν.C).symm (σ, u')).2 r
      else 0 := by
  unfold physCoef
  rw [shift_mk ν σ u r w, Complex.ofReal_zero, zero_mul, Complex.cpow_zero, mul_one]
  refine if_congr ⟨fun hc => ?_, fun h => ?_⟩ rfl rfl
  · exact ⟨dvd_of_isPhys_mk h𝔊 σ u hc.1, dvd_of_isPhys_mk h𝔊 σ u' hc.2.1⟩
  · have hsh := (shared_iff ((listSplit 𝔊 ν.C).symm (σ, u))
      ((listSplit 𝔊 ν.C).symm (σ, u'))).mpr
        (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
    exact ⟨isPhys_mk_of σ hgood.1 hgood.not_dvd u h.1,
      isPhys_mk_of σ hgood.1 hgood.not_dvd_add u' h.2, hsh.1, hsh.2,
      auxAvoids_mk_of σ u r hgood.ne_aux h.1.2 hfree,
      auxAvoids_mk_of σ u' r hgood.ne_aux h.2.2 fun g i hd =>
        hfree g i (dvd_of_dvd_add hd (aux_dvd_tupleProd r g i))⟩

/-- **Away from collisions the list factors of the edge sum are the law of the shared labels
times the list factors of the stripped expression** (`[P-06:0321–0328]`). -/
theorem edgeList_of_good (h𝔊 : 𝔊.Admissible P x₀) {q₀ : ℝ} (hq : 0 < q₀)
    (ν : Pattern (groupFamily 𝔊).big J 1)
    (κ : AuxList (groupFamily 𝔊).big ν.C → ((g : 𝔊.Index) → Fin (markCount 𝔊 ν.C g) → ℕ) →
      ((g : 𝔊.Index) → Fin (markCount 𝔊 ν.C g) → ℕ) → ℂ)
    (hκ : ∀ (σ : ShT 𝔊 ν.C) (u u' : UnT 𝔊 ν.C) (r : AuxList (groupFamily 𝔊).big ν.C),
      ν.K ((listSplit 𝔊 ν.C).symm (σ, u)).2 ((listSplit 𝔊 ν.C).symm (σ, u')).2 r =
        κ r (unVal u) (unVal u'))
    (σ : ShT 𝔊 ν.C) (r : AuxList (groupFamily 𝔊).big ν.C) {w : ℕ}
    (hgood : Good σ (forbid r w))
    (hfree : ∀ (g : Fin 𝔊.numBig) (i : {i : Fin J // i ∈ ν.C g}), ¬(r g i : ℕ) ∣ w) :
    edgeList q₀ ν σ r w = ((shWeight σ : ℝ) : ℂ) * mainList q₀ ν.C κ r w := by
  classical
  have hterm : ∀ u u' : UnT 𝔊 ν.C,
      ((((shProd σ : ℕ) : ℝ)⁻¹ * stateMass (groupFamily 𝔊) J 1 *
          (damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) *
            damping intPos (groupFamily 𝔊) J 1 q₀
              ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)) : ℝ) : ℂ) *
        physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 ((shProd σ * w : ℕ) : ℤ)
          ((listSplit 𝔊 ν.C).symm (σ, u)) r ((listSplit 𝔊 ν.C).symm (σ, u')) =
      ((shWeight σ * (auxWeight (groupFamily 𝔊).big ν.C r *
          (activeCoeff 𝔊 q₀ (markCount 𝔊 ν.C) w *
            activeCoeff 𝔊 q₀ (markCount 𝔊 ν.C) (w + tupleProd ν.C r))) : ℝ) : ℂ) *
        (if IsRepr u w ∧ IsRepr u' (w + tupleProd ν.C r) then κ r (unVal u) (unVal u')
          else 0) := by
    intro u u'
    rw [physCoef_mk_of_good h𝔊 q₀ ν σ u u' r hgood hfree]
    by_cases h : IsRepr u w ∧ IsRepr u' (w + tupleProd ν.C r)
    · have e1 := stateMass_mul_inv_shProd σ
      have e2 := targetNorm_mul_damping_sq h𝔊 hq σ hgood.1 hgood.not_dvd
        (sum_markCount_le_totalHits h.1)
      have e3 := targetNorm_mul_damping_sq h𝔊 hq σ hgood.1 hgood.not_dvd_add
        (sum_markCount_le_totalHits h.2)
      have hre := strip_alg (aux := auxWeight (groupFamily 𝔊).big ν.C r) e1 e2 e3
      rw [if_pos h, if_pos h, hκ, ← hre]
      push_cast
      ring
    · rw [if_neg h, if_neg h, mul_zero, mul_zero]
  have hinner : ∀ u : UnT 𝔊 ν.C,
      ∑ u' : UnT 𝔊 ν.C, (if IsRepr u w ∧ IsRepr u' (w + tupleProd ν.C r) then
          κ r (unVal u) (unVal u') else 0) =
        if IsRepr u w then
          ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 ν.C) (w + tupleProd ν.C r), κ r (unVal u) 𝔭'
        else 0 := by
    intro u
    by_cases hA : IsRepr u w
    · rw [if_pos hA, sum_representedLists (w + tupleProd ν.C r) (fun 𝔭' => κ r (unVal u) 𝔭')]
      exact Finset.sum_congr rfl fun u' _ => if_congr (and_iff_right hA) rfl rfl
    · rw [if_neg hA]
      exact Finset.sum_eq_zero fun u' _ => if_neg fun h => hA h.1
  unfold edgeList mainList
  calc ∑ u : UnT 𝔊 ν.C, ∑ u' : UnT 𝔊 ν.C,
        ((((shProd σ : ℕ) : ℝ)⁻¹ * stateMass (groupFamily 𝔊) J 1 *
            (damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) *
              damping intPos (groupFamily 𝔊) J 1 q₀
                ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)) : ℝ) : ℂ) *
          physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 ((shProd σ * w : ℕ) : ℤ)
            ((listSplit 𝔊 ν.C).symm (σ, u)) r ((listSplit 𝔊 ν.C).symm (σ, u'))
      = ∑ u : UnT 𝔊 ν.C, ∑ u' : UnT 𝔊 ν.C,
          ((shWeight σ * (auxWeight (groupFamily 𝔊).big ν.C r *
            (activeCoeff 𝔊 q₀ (markCount 𝔊 ν.C) w *
              activeCoeff 𝔊 q₀ (markCount 𝔊 ν.C) (w + tupleProd ν.C r))) : ℝ) : ℂ) *
          (if IsRepr u w ∧ IsRepr u' (w + tupleProd ν.C r) then κ r (unVal u) (unVal u')
            else 0) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => hterm u u'
    _ = ((shWeight σ * (auxWeight (groupFamily 𝔊).big ν.C r *
            (activeCoeff 𝔊 q₀ (markCount 𝔊 ν.C) w *
              activeCoeff 𝔊 q₀ (markCount 𝔊 ν.C) (w + tupleProd ν.C r))) : ℝ) : ℂ) *
          ∑ u : UnT 𝔊 ν.C, ∑ u' : UnT 𝔊 ν.C,
            (if IsRepr u w ∧ IsRepr u' (w + tupleProd ν.C r) then κ r (unVal u) (unVal u')
              else 0) :=
        (Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm).trans
          (Finset.mul_sum _ _ _).symm
    _ = ((shWeight σ * (auxWeight (groupFamily 𝔊).big ν.C r *
            (activeCoeff 𝔊 q₀ (markCount 𝔊 ν.C) w *
              activeCoeff 𝔊 q₀ (markCount 𝔊 ν.C) (w + tupleProd ν.C r))) : ℝ) : ℂ) *
          ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 ν.C) w,
            ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 ν.C) (w + tupleProd ν.C r), κ r 𝔭 𝔭' := by
        rw [Finset.sum_congr rfl fun u _ => hinner u,
          sum_representedLists w (fun 𝔭 =>
            ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 ν.C) (w + tupleProd ν.C r), κ r 𝔭 𝔭')]
    _ = _ := by
        push_cast
        ring

/-! ### Bounds for all shared labels -/

open _root_.Classical in
/-- The modulus of the row coefficient at `n = D_R w`. -/
theorem norm_physCoef_mk_le {q₀ : ℝ} (hq : 0 < q₀) (ν : Pattern (groupFamily 𝔊).big J 1)
    {Kmax : ℝ} (hK0 : 0 ≤ Kmax) (hK : ∀ p p' r, ‖ν.K p p' r‖ ≤ Kmax) (σ : ShT 𝔊 ν.C)
    (u u' : UnT 𝔊 ν.C) (r : AuxList (groupFamily 𝔊).big ν.C) (w : ℕ) :
    ‖physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 ((shProd σ * w : ℕ) : ℤ)
        ((listSplit 𝔊 ν.C).symm (σ, u)) r ((listSplit 𝔊 ν.C).symm (σ, u'))‖ ≤
      (if IsPhys intPos ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 ν.C).symm (σ, u)) ∧
          IsPhys intPos ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)
            ((listSplit 𝔊 ν.C).symm (σ, u')) then
        auxWeight (groupFamily 𝔊).big ν.C r * targetNorm (groupFamily 𝔊) 1 ν.C *
          (damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) *
            damping intPos (groupFamily 𝔊) J 1 q₀
              ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ))
        else 0) * Kmax := by
  have hA : 0 ≤ auxWeight (groupFamily 𝔊).big ν.C r * targetNorm (groupFamily 𝔊) 1 ν.C *
      (damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) *
        damping intPos (groupFamily 𝔊) J 1 q₀
          ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)) :=
    mul_nonneg (mul_nonneg (Schur.auxWeight_nonneg _ _ _) (Schur.targetNorm_nonneg _ _ _))
      (mul_nonneg (Schur.damping_pos intPos (groupFamily 𝔊) J 1 hq _).le
        (Schur.damping_pos intPos (groupFamily 𝔊) J 1 hq _).le)
  unfold physCoef
  rw [shift_mk ν σ u r w]
  split_ifs with hc h2 h2
  · rw [norm_mul, Complex.norm_of_nonneg hA, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ hA
    calc ‖ν.K ((listSplit 𝔊 ν.C).symm (σ, u)).2 ((listSplit 𝔊 ν.C).symm (σ, u')).2 r‖ *
          ‖((dil ν.C ((listSplit 𝔊 ν.C).symm (σ, u)) r : ℕ) : ℂ) ^
            (((0 : ℝ) : ℂ) * Complex.I)‖ ≤ Kmax * 1 :=
          mul_le_mul (hK _ _ _) (Schur.norm_natCast_cpow_mul_I_le_one _ 0) (norm_nonneg _) hK0
      _ = Kmax := mul_one _
  · exact absurd ⟨hc.1, hc.2.1⟩ h2
  · rw [norm_zero]
    exact mul_nonneg hA hK0
  · rw [norm_zero, zero_mul]

open _root_.Classical in
/-- **The count (eq:physical-count-bound) of [S] for the unshared labels**: for every position and
every choice of the shared labels, the unshared lists that complete them to a physical state,
weighted by `∏_g V_g^{-t_g}` and the squared damping, have total weight at most
`∏_g groupConst`. -/
theorem sum_phys_le (h𝔊 : 𝔊.Admissible P x₀) {q₀ : ℝ} (hq0 : 0 < q₀) (hq1 : q₀ < 1)
    (C : Fin 𝔊.numBig → Finset (Fin J)) {T : ℕ} (hT1 : 1 ≤ T)
    (hT : ∀ g, 1 + (C g).card ≤ T) (σ : ShT 𝔊 C) (n : ℤ) :
    ∑ u : UnT 𝔊 C, (if IsPhys intPos n ((listSplit 𝔊 C).symm (σ, u)) then
        targetNorm (groupFamily 𝔊) 1 C * damping intPos (groupFamily 𝔊) J 1 q₀ n ^ 2
      else 0) ≤
      (∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
        ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T := by
  have hg0 : (0 : ℝ) ≤ Schur.groupConst P.vlo q₀ T :=
    zero_le_one.trans (Schur.one_le_groupConst _ _ _)
  have hΓ0 : (0 : ℝ) ≤ (∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
      ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => hg0) (Finset.prod_nonneg fun _ _ => hg0)
  rcases isEmpty_or_nonempty (UnT 𝔊 C) with hE | ⟨⟨u₀⟩⟩
  · rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact hΓ0
  · have hS := Schur.sum_sharedWeight_le intPos (groupFamily 𝔊) hq0 hq1 P.vlo_pos
      (fun g => h𝔊.mass_ge (Sum.inl g)) (fun g => h𝔊.mass_ge (Sum.inr g))
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hT1) hT1 C hT n ((listSplit 𝔊 C).symm (σ, u₀))
    obtain ⟨f, hf⟩ : ∃ f : Lists (groupFamily 𝔊) J 1 → ℝ, ∀ b, f b =
        Schur.sharedWeight intPos (groupFamily 𝔊) q₀ C n ((listSplit 𝔊 C).symm (σ, u₀)) b :=
      ⟨_, fun _ => rfl⟩
    have hf0 : ∀ b, 0 ≤ f b := fun b => by
      rw [hf]
      exact Schur.sharedWeight_nonneg intPos (groupFamily 𝔊) hq0 C n _ _
    have hS' : ∑ b, f b ≤ (∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
        ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T := by
      rw [Finset.sum_congr rfl fun b _ => hf b]
      exact hS
    have hpt : ∀ u : UnT 𝔊 C, (if IsPhys intPos n ((listSplit 𝔊 C).symm (σ, u)) then
          targetNorm (groupFamily 𝔊) 1 C * damping intPos (groupFamily 𝔊) J 1 q₀ n ^ 2
        else 0) ≤ f ((listSplit 𝔊 C).symm (σ, u)) := by
      intro u
      rw [hf]
      by_cases hp : IsPhys intPos n ((listSplit 𝔊 C).symm (σ, u))
      · have hsh := (shared_iff ((listSplit 𝔊 C).symm (σ, u₀))
          ((listSplit 𝔊 C).symm (σ, u))).mpr
            (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
        have hd1 : damping intPos (groupFamily 𝔊) J 1 q₀ n ≤ 1 :=
          Schur.damping_le_one hq0 hq1.le hp
        have hd0 : 0 < damping intPos (groupFamily 𝔊) J 1 q₀ n :=
          Schur.damping_pos intPos (groupFamily 𝔊) J 1 hq0 n
        unfold Schur.sharedWeight
        rw [if_pos hp, if_pos ⟨hp, hsh.1, hsh.2⟩, pow_two]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hd0.le hd1)
          (Schur.targetNorm_nonneg _ _ _)
      · rw [if_neg hp]
        exact Schur.sharedWeight_nonneg intPos (groupFamily 𝔊) hq0 C n _ _
    calc ∑ u : UnT 𝔊 C, (if IsPhys intPos n ((listSplit 𝔊 C).symm (σ, u)) then
            targetNorm (groupFamily 𝔊) 1 C * damping intPos (groupFamily 𝔊) J 1 q₀ n ^ 2
          else 0)
        ≤ ∑ u : UnT 𝔊 C, f ((listSplit 𝔊 C).symm (σ, u)) :=
          Finset.sum_le_sum fun u _ => hpt u
      _ ≤ ∑ σ' : ShT 𝔊 C, ∑ u : UnT 𝔊 C, f ((listSplit 𝔊 C).symm (σ', u)) :=
          Finset.single_le_sum
            (f := fun σ' : ShT 𝔊 C => ∑ u : UnT 𝔊 C, f ((listSplit 𝔊 C).symm (σ', u)))
            (fun σ' _ => Finset.sum_nonneg fun u _ => hf0 _) (Finset.mem_univ σ)
      _ = ∑ p : ShT 𝔊 C × UnT 𝔊 C, f ((listSplit 𝔊 C).symm p) :=
          (Fintype.sum_prod_type
            (fun p : ShT 𝔊 C × UnT 𝔊 C => f ((listSplit 𝔊 C).symm p))).symm
      _ = ∑ b : Lists (groupFamily 𝔊) J 1, f b := Equiv.sum_comp (listSplit 𝔊 C).symm f
      _ ≤ _ := hS'

open _root_.Classical in
/-- **The list factors of the edge sum for arbitrary shared labels** (`[P-06:0344–0346]`:
"Changing the damping loses at most `q_0^{-2M s_P} = L^{O(J)}`"; here by the count of [S]):
`|edgeList| ≤ (law of σ) · (law of r) · sup|K_ν| · (∏_g groupConst)²`. -/
theorem norm_edgeList_le (h𝔊 : 𝔊.Admissible P x₀) {q₀ : ℝ} (hq0 : 0 < q₀) (hq1 : q₀ < 1)
    (ν : Pattern (groupFamily 𝔊).big J 1) {Kmax : ℝ} (hK0 : 0 ≤ Kmax)
    (hK : ∀ p p' r, ‖ν.K p p' r‖ ≤ Kmax) {T : ℕ} (hT1 : 1 ≤ T)
    (hT : ∀ g, 1 + (ν.C g).card ≤ T) (σ : ShT 𝔊 ν.C) (r : AuxList (groupFamily 𝔊).big ν.C)
    (w : ℕ) :
    ‖edgeList q₀ ν σ r w‖ ≤
      shWeight σ * auxWeight (groupFamily 𝔊).big ν.C r * Kmax *
        (((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
            ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) *
          ((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
            ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T)) := by
  have hg0 : (0 : ℝ) ≤ Schur.groupConst P.vlo q₀ T :=
    zero_le_one.trans (Schur.one_le_groupConst _ _ _)
  have hΓ0 : (0 : ℝ) ≤ (∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
      ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => hg0) (Finset.prod_nonneg fun _ _ => hg0)
  have haux : 0 ≤ auxWeight (groupFamily 𝔊).big ν.C r := Schur.auxWeight_nonneg _ _ _
  have htn : 0 ≤ targetNorm (groupFamily 𝔊) 1 ν.C := Schur.targetNorm_nonneg _ _ _
  have hd1 : 0 ≤ damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) :=
    (Schur.damping_pos intPos (groupFamily 𝔊) J 1 hq0 _).le
  have hd2 : 0 ≤ damping intPos (groupFamily 𝔊) J 1 q₀
      ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ) :=
    (Schur.damping_pos intPos (groupFamily 𝔊) J 1 hq0 _).le
  have hc0 : 0 ≤ ((shProd σ : ℕ) : ℝ)⁻¹ * stateMass (groupFamily 𝔊) J 1 *
      (damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) *
        damping intPos (groupFamily 𝔊) J 1 q₀
          ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)) :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Pairing.stateMass_nonneg _ _ _)) (mul_nonneg hd1 hd2)
  have hcst : 0 ≤ shWeight σ * auxWeight (groupFamily 𝔊).big ν.C r * Kmax :=
    mul_nonneg (mul_nonneg (shWeight_nonneg σ) haux) hK0
  have e1 := stateMass_mul_inv_shProd σ
  have hterm : ∀ u u' : UnT 𝔊 ν.C,
      ‖((((shProd σ : ℕ) : ℝ)⁻¹ * stateMass (groupFamily 𝔊) J 1 *
          (damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) *
            damping intPos (groupFamily 𝔊) J 1 q₀
              ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)) : ℝ) : ℂ) *
        physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 ((shProd σ * w : ℕ) : ℤ)
          ((listSplit 𝔊 ν.C).symm (σ, u)) r ((listSplit 𝔊 ν.C).symm (σ, u'))‖ ≤
      shWeight σ * auxWeight (groupFamily 𝔊).big ν.C r * Kmax *
        ((if IsPhys intPos ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 ν.C).symm (σ, u)) then
            targetNorm (groupFamily 𝔊) 1 ν.C *
              damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) ^ 2
          else 0) *
          (if IsPhys intPos ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)
              ((listSplit 𝔊 ν.C).symm (σ, u')) then
            targetNorm (groupFamily 𝔊) 1 ν.C * damping intPos (groupFamily 𝔊) J 1 q₀
              ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ) ^ 2
          else 0)) := by
    intro u u'
    rw [norm_mul, Complex.norm_of_nonneg hc0]
    refine (mul_le_mul_of_nonneg_left
      (norm_physCoef_mk_le hq0 ν hK0 hK σ u u' r w) hc0).trans (le_of_eq ?_)
    by_cases h : IsPhys intPos ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 ν.C).symm (σ, u)) ∧
        IsPhys intPos ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)
          ((listSplit 𝔊 ν.C).symm (σ, u'))
    · rw [if_pos h, if_pos h.1, if_pos h.2]
      linear_combination (auxWeight (groupFamily 𝔊).big ν.C r *
        targetNorm (groupFamily 𝔊) 1 ν.C *
        damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) ^ 2 *
        damping intPos (groupFamily 𝔊) J 1 q₀
          ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ) ^ 2 * Kmax) * e1
    · rw [if_neg h, zero_mul, mul_zero]
      rcases not_and_or.mp h with h1 | h2
      · rw [if_neg h1, zero_mul, mul_zero]
      · rw [if_neg h2, mul_zero, mul_zero]
  have hZ1 := sum_phys_le h𝔊 hq0 hq1 ν.C hT1 hT σ ((shProd σ * w : ℕ) : ℤ)
  have hZ2 := sum_phys_le h𝔊 hq0 hq1 ν.C hT1 hT σ
    ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)
  have hZ2nn : 0 ≤ ∑ u' : UnT 𝔊 ν.C,
      (if IsPhys intPos ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ)
          ((listSplit 𝔊 ν.C).symm (σ, u')) then
        targetNorm (groupFamily 𝔊) 1 ν.C * damping intPos (groupFamily 𝔊) J 1 q₀
          ((shProd σ * (w + tupleProd ν.C r) : ℕ) : ℤ) ^ 2
      else 0) :=
    Finset.sum_nonneg fun u' _ => by
      split_ifs
      · exact mul_nonneg htn (pow_nonneg hd2 2)
      · exact le_rfl
  unfold edgeList
  refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => norm_sum_le _ _)).trans ?_
  refine (Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => hterm u u').trans ?_
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (mul_le_mul hZ1 hZ2 hZ2nn hΓ0) hcst)
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm

/-- **The list factors of the stripped expression** are bounded by (cor:marked-bound):
`|mainList| ≤ (law of r) · sup|κ| · L^{2 C(m')}`. -/
theorem norm_mainList_le (h𝔊 : 𝔊.Admissible P x₀) {q₀ : ℝ} (hq0 : 0 < q₀)
    (C : Fin 𝔊.numBig → Finset (Fin J))
    (κ : AuxList (groupFamily 𝔊).big C → ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) →
      ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ) {Kmax : ℝ} (hK0 : 0 ≤ Kmax)
    (hκ : ∀ r 𝔭 𝔭', ‖κ r 𝔭 𝔭'‖ ≤ Kmax) {Lm : ℝ}
    (hMB : ∀ n : ℕ, ‖𝔊.activeWeight q₀ (markCount 𝔊 C) (fun _ => 1) n‖ ≤ Lm)
    (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) :
    ‖mainList q₀ C κ r w‖ ≤ auxWeight (groupFamily 𝔊).big C r * Kmax * (Lm * Lm) := by
  have hV : ∀ g : 𝔊.Index, 0 ≤ reciprocalMass (𝔊.group g) := fun g =>
    P.vlo_pos.le.trans (h𝔊.mass_ge g)
  have haC : ∀ n : ℕ, 0 ≤ activeCoeff 𝔊 q₀ (markCount 𝔊 C) n := fun n =>
    mul_nonneg (pow_nonneg hq0.le _)
      (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (hV g) _))
  have hLm0 : 0 ≤ Lm := (norm_nonneg _).trans (hMB 0)
  have haux : 0 ≤ auxWeight (groupFamily 𝔊).big C r := Schur.auxWeight_nonneg _ _ _
  have hN : ∀ n : ℕ, activeCoeff 𝔊 q₀ (markCount 𝔊 C) n *
      ((𝔊.representedLists (markCount 𝔊 C) n).card : ℝ) ≤ Lm := fun n => by
    have h := hMB n
    rw [activeWeight_eq_activeCoeff, Finset.sum_const, nsmul_eq_mul, mul_one, norm_mul,
      Complex.norm_of_nonneg (haC n), Complex.norm_natCast] at h
    exact h
  have hsum : ‖∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
        ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r), κ r 𝔭 𝔭'‖ ≤
      ((𝔊.representedLists (markCount 𝔊 C) w).card : ℝ) *
        (((𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r)).card : ℝ) * Kmax) := by
    calc ‖∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
          ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r), κ r 𝔭 𝔭'‖
        ≤ ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
            ‖∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r), κ r 𝔭 𝔭'‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
            (((𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r)).card : ℝ) * Kmax) :=
          Finset.sum_le_sum fun 𝔭 _ => (norm_sum_le _ _).trans
            ((Finset.sum_le_sum fun 𝔭' _ => hκ r 𝔭 𝔭').trans
              (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul])))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  unfold mainList
  rw [norm_mul, Complex.norm_of_nonneg (mul_nonneg haux (mul_nonneg (haC _) (haC _)))]
  calc auxWeight (groupFamily 𝔊).big C r * (activeCoeff 𝔊 q₀ (markCount 𝔊 C) w *
          activeCoeff 𝔊 q₀ (markCount 𝔊 C) (w + tupleProd C r)) *
        ‖∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
          ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r), κ r 𝔭 𝔭'‖
      ≤ auxWeight (groupFamily 𝔊).big C r * (activeCoeff 𝔊 q₀ (markCount 𝔊 C) w *
          activeCoeff 𝔊 q₀ (markCount 𝔊 C) (w + tupleProd C r)) *
        (((𝔊.representedLists (markCount 𝔊 C) w).card : ℝ) *
          (((𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r)).card : ℝ) * Kmax)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg haux (mul_nonneg (haC _) (haC _)))
    _ = auxWeight (groupFamily 𝔊).big C r * Kmax *
          ((activeCoeff 𝔊 q₀ (markCount 𝔊 C) w *
              ((𝔊.representedLists (markCount 𝔊 C) w).card : ℝ)) *
            (activeCoeff 𝔊 q₀ (markCount 𝔊 C) (w + tupleProd C r) *
              ((𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r)).card : ℝ))) := by
        ring
    _ ≤ auxWeight (groupFamily 𝔊).big C r * Kmax * (Lm * Lm) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hN w) (hN _) (mul_nonneg (haC _) (Nat.cast_nonneg _)) hLm0)
          (mul_nonneg haux hK0)

/-! ### The difference at one choice of the shared labels -/

/-- **The edge sum against the stripped expression at one choice of the shared labels**
(`[P-06:0318–0346]`): they agree away from collisions and when no free label divides `w`;
otherwise each is bounded. -/
theorem norm_edgeList_sub_le (h𝔊 : 𝔊.Admissible P x₀) {q₀ : ℝ} (hq0 : 0 < q₀) (hq1 : q₀ < 1)
    (ν : Pattern (groupFamily 𝔊).big J 1)
    (κ : AuxList (groupFamily 𝔊).big ν.C → ((g : 𝔊.Index) → Fin (markCount 𝔊 ν.C g) → ℕ) →
      ((g : 𝔊.Index) → Fin (markCount 𝔊 ν.C g) → ℕ) → ℂ)
    (hκ : ∀ (σ : ShT 𝔊 ν.C) (u u' : UnT 𝔊 ν.C) (r : AuxList (groupFamily 𝔊).big ν.C),
      ν.K ((listSplit 𝔊 ν.C).symm (σ, u)).2 ((listSplit 𝔊 ν.C).symm (σ, u')).2 r =
        κ r (unVal u) (unVal u'))
    {Kmax : ℝ} (hK0 : 0 ≤ Kmax) (hK : ∀ p p' r, ‖ν.K p p' r‖ ≤ Kmax)
    (hκK : ∀ r 𝔭 𝔭', ‖κ r 𝔭 𝔭'‖ ≤ Kmax) {T : ℕ} (hT1 : 1 ≤ T)
    (hT : ∀ g, 1 + (ν.C g).card ≤ T) {Lm : ℝ}
    (hMB : ∀ n : ℕ, ‖𝔊.activeWeight q₀ (markCount 𝔊 ν.C) (fun _ => 1) n‖ ≤ Lm)
    (σ : ShT 𝔊 ν.C) (r : AuxList (groupFamily 𝔊).big ν.C) (w : ℕ) :
    ‖edgeList q₀ ν σ r w - ((shWeight σ : ℝ) : ℂ) * mainList q₀ ν.C κ r w‖ ≤
      shWeight σ * (auxWeight (groupFamily 𝔊).big ν.C r * Kmax *
        (((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
            ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) *
          ((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
            ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) + Lm * Lm)) *
        (freeInd r w + badInd σ (forbid r w)) := by
  have hg0 : (0 : ℝ) ≤ Schur.groupConst P.vlo q₀ T :=
    zero_le_one.trans (Schur.one_le_groupConst _ _ _)
  have hΓ0 : (0 : ℝ) ≤ (∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
      ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => hg0) (Finset.prod_nonneg fun _ _ => hg0)
  have hLm0 : 0 ≤ Lm := (norm_nonneg _).trans (hMB 0)
  have haux : 0 ≤ auxWeight (groupFamily 𝔊).big ν.C r := Schur.auxWeight_nonneg _ _ _
  have hX0 : 0 ≤ shWeight σ * (auxWeight (groupFamily 𝔊).big ν.C r * Kmax *
      (((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
          ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) *
        ((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
          ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) + Lm * Lm)) :=
    mul_nonneg (shWeight_nonneg σ) (mul_nonneg (mul_nonneg haux hK0)
      (add_nonneg (mul_nonneg hΓ0 hΓ0) (mul_nonneg hLm0 hLm0)))
  have hB : ‖edgeList q₀ ν σ r w - ((shWeight σ : ℝ) : ℂ) * mainList q₀ ν.C κ r w‖ ≤
      shWeight σ * (auxWeight (groupFamily 𝔊).big ν.C r * Kmax *
        (((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
            ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) *
          ((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
            ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) + Lm * Lm)) := by
    have h1 := norm_edgeList_le h𝔊 hq0 hq1 ν hK0 hK hT1 hT σ r w
    have h2 : ‖((shWeight σ : ℝ) : ℂ) * mainList q₀ ν.C κ r w‖ ≤
        shWeight σ * (auxWeight (groupFamily 𝔊).big ν.C r * Kmax * (Lm * Lm)) := by
      rw [norm_mul, Complex.norm_of_nonneg (shWeight_nonneg σ)]
      exact mul_le_mul_of_nonneg_left (norm_mainList_le h𝔊 hq0 ν.C κ hK0 hκK hMB r w)
        (shWeight_nonneg σ)
    refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    ring
  have hind0 : 0 ≤ freeInd r w + badInd σ (forbid r w) :=
    add_nonneg (freeInd_nonneg r w) (badInd_nonneg σ _)
  by_cases hgood : Good σ (forbid r w)
  · by_cases hfree : ∃ (g : Fin 𝔊.numBig) (i : {i : Fin J // i ∈ ν.C g}), (r g i : ℕ) ∣ w
    · have h1 : (1 : ℝ) ≤ freeInd r w + badInd σ (forbid r w) := by
        have hf : freeInd r w = 1 := by
          unfold freeInd
          exact if_pos hfree
        rw [hf]
        linarith [badInd_nonneg σ (forbid r w)]
      exact hB.trans (le_mul_of_one_le_right hX0 h1)
    · rw [edgeList_of_good h𝔊 hq0 ν κ hκ σ r hgood fun g i hd => hfree ⟨g, i, hd⟩, sub_self,
        norm_zero]
      exact mul_nonneg hX0 hind0
  · have h1 : (1 : ℝ) ≤ freeInd r w + badInd σ (forbid r w) := by
      rw [badInd_of_not hgood]
      linarith [freeInd_nonneg r w]
    exact hB.trans (le_mul_of_one_le_right hX0 h1)

end Term

end Strip

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
