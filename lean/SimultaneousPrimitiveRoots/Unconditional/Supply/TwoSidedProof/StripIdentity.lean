module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.StripTerm

/-!
# Removal of the shared labels: the edge sum as a sum over `w`

`[P-06:0318–0346]`: "For a single pattern put `n = D_R w`, `n' = D_R w'`. The shift becomes
`w' = w + D_C`."

* `sum_reindex`: a sum over positions `n`, source lists, free labels and target lists whose terms
  vanish unless the two lists have the same shared labels `σ` and `n = D_R(σ) w` is a sum over
  `w`, the free labels, the shared labels and the unshared labels of the two endpoints.
* `edgeTerm_eq_strip`: the edge sum of a pattern is
  `∑_w ∑_r ∑_σ corePart(r, w) · edgeList(σ, r, w)`.
* `genStrip`: the stripped expression (cor:stripped) of a pattern with a stripped coefficient `κ`;
  `genStrip_eq_sum`: it is `∑_w ∑_r ∑_σ corePart(r, w) · (law of σ) · mainList(r, w)`.
* `norm_edgeTerm_sub_le`: the difference is at most
  `sup|K| (Γ² + L^{2C}) ∑_w ∑_r |corePart(r, w)| · (law of r) · (1_{a free label divides w} +
  ℙ_σ(collision))`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

namespace Strip

section Identity

variable {𝔊 : ActiveGroups} {J : ℕ} {P : ActiveGroupConstants} {x₀ : ℝ}

/-! ### Reindexing -/

/-- A sum over a set of integers of a function supported on the multiples `R w`, `w ∈ W`. -/
theorem sum_eq_sum_of_support {M : Type*} [AddCommMonoid M] (f : ℤ → M) (T : Finset ℤ)
    (W : Finset ℕ) (R : ℕ) (hR : 0 < R) (hT : ∀ n, n ∉ T → f n = 0)
    (hW : ∀ n, f n ≠ 0 → ∃ w ∈ W, ((R * w : ℕ) : ℤ) = n) :
    ∑ n ∈ T, f n = ∑ w ∈ W, f ((R * w : ℕ) : ℤ) := by
  have h1 : ∑ᶠ n, f n = ∑ n ∈ T, f n :=
    finsum_eq_sum_of_support_subset _ fun n hn => by
      by_contra h
      exact hn (hT n fun hm => h (Finset.mem_coe.mpr hm))
  have h2 : ∑ᶠ n, f n = ∑ n ∈ W.image (fun w : ℕ => ((R * w : ℕ) : ℤ)), f n :=
    finsum_eq_sum_of_support_subset _ fun n hn => by
      obtain ⟨w, hw, rfl⟩ := hW n hn
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  rw [← h1, h2, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hR (Int.ofNat_inj.mp hab)

/-- A sum over source lists, free labels and target lists whose terms vanish unless the two lists
have the same shared labels. -/
theorem sum_lists_strip (C : Fin 𝔊.numBig → Finset (Fin J))
    (g : Lists (groupFamily 𝔊) J 1 → AuxList (groupFamily 𝔊).big C →
      Lists (groupFamily 𝔊) J 1 → ℂ)
    (hg : ∀ s r s', (listSplit 𝔊 C s').1 ≠ (listSplit 𝔊 C s).1 → g s r s' = 0) :
    ∑ s, ∑ r, ∑ s', g s r s' =
      ∑ σ : ShT 𝔊 C, ∑ u : UnT 𝔊 C, ∑ r, ∑ u' : UnT 𝔊 C,
        g ((listSplit 𝔊 C).symm (σ, u)) r ((listSplit 𝔊 C).symm (σ, u')) := by
  have h1 : ∀ s r, ∑ s', g s r s' =
      ∑ u' : UnT 𝔊 C, g s r ((listSplit 𝔊 C).symm ((listSplit 𝔊 C s).1, u')) := fun s r => by
    rw [← Equiv.sum_comp (listSplit 𝔊 C).symm (fun s' => g s r s'),
      Fintype.sum_prod_type (fun p : ShT 𝔊 C × UnT 𝔊 C => g s r ((listSplit 𝔊 C).symm p))]
    refine Finset.sum_eq_single ((listSplit 𝔊 C s).1) (fun σ' _ hσ' => ?_)
      (fun h => absurd (Finset.mem_univ _) h)
    exact Finset.sum_eq_zero fun u' _ => hg s r _ (by
      rw [Equiv.apply_symm_apply]
      exact hσ')
  rw [← Equiv.sum_comp (listSplit 𝔊 C).symm (fun s => ∑ r, ∑ s', g s r s'),
    Fintype.sum_prod_type
      (fun p : ShT 𝔊 C × UnT 𝔊 C => ∑ r, ∑ s', g ((listSplit 𝔊 C).symm p) r s')]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun u _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [h1]
  exact Finset.sum_congr rfl fun u' _ => by rw [Equiv.apply_symm_apply]

/-- **The reindexing `n = D_R w`**: a sum over positions, source lists, free labels and target
lists, whose terms vanish outside `T`, unless the two lists have the same shared labels `σ`, and
unless `n = D_R(σ) w` with `w ∈ W`. -/
theorem sum_reindex (C : Fin 𝔊.numBig → Finset (Fin J))
    (g : ℤ → Lists (groupFamily 𝔊) J 1 → AuxList (groupFamily 𝔊).big C →
      Lists (groupFamily 𝔊) J 1 → ℂ) (T : Finset ℤ) (W : Finset ℕ)
    (hpos : ∀ σ : ShT 𝔊 C, 0 < shProd σ) (hgT : ∀ n, n ∉ T → ∀ s r s', g n s r s' = 0)
    (hgsh : ∀ n s r s', (listSplit 𝔊 C s').1 ≠ (listSplit 𝔊 C s).1 → g n s r s' = 0)
    (hgW : ∀ (σ : ShT 𝔊 C) (n : ℤ) (u : UnT 𝔊 C) (r : AuxList (groupFamily 𝔊).big C)
      (u' : UnT 𝔊 C),
      g n ((listSplit 𝔊 C).symm (σ, u)) r ((listSplit 𝔊 C).symm (σ, u')) ≠ 0 →
        ∃ w ∈ W, ((shProd σ * w : ℕ) : ℤ) = n) :
    ∑ n ∈ T, ∑ s, ∑ r, ∑ s', g n s r s' =
      ∑ w ∈ W, ∑ r, ∑ σ : ShT 𝔊 C, ∑ u : UnT 𝔊 C, ∑ u' : UnT 𝔊 C,
        g ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 C).symm (σ, u)) r
          ((listSplit 𝔊 C).symm (σ, u')) := by
  have hT' : ∀ (σ : ShT 𝔊 C) (n : ℤ), n ∉ T →
      ∑ u : UnT 𝔊 C, ∑ r, ∑ u' : UnT 𝔊 C,
        g n ((listSplit 𝔊 C).symm (σ, u)) r ((listSplit 𝔊 C).symm (σ, u')) = 0 :=
    fun σ n hn => Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun r _ =>
      Finset.sum_eq_zero fun u' _ => hgT n hn _ _ _
  have hW' : ∀ (σ : ShT 𝔊 C) (n : ℤ),
      ∑ u : UnT 𝔊 C, ∑ r, ∑ u' : UnT 𝔊 C,
        g n ((listSplit 𝔊 C).symm (σ, u)) r ((listSplit 𝔊 C).symm (σ, u')) ≠ 0 →
      ∃ w ∈ W, ((shProd σ * w : ℕ) : ℤ) = n := by
    intro σ n hne
    by_contra hcon
    refine hne (Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun r _ =>
      Finset.sum_eq_zero fun u' _ => ?_)
    by_contra hterm
    exact hcon (hgW σ n u r u' hterm)
  calc ∑ n ∈ T, ∑ s, ∑ r, ∑ s', g n s r s'
      = ∑ n ∈ T, ∑ σ : ShT 𝔊 C, ∑ u : UnT 𝔊 C, ∑ r, ∑ u' : UnT 𝔊 C,
          g n ((listSplit 𝔊 C).symm (σ, u)) r ((listSplit 𝔊 C).symm (σ, u')) :=
        Finset.sum_congr rfl fun n _ => sum_lists_strip C (g n) (hgsh n)
    _ = ∑ σ : ShT 𝔊 C, ∑ n ∈ T, ∑ u : UnT 𝔊 C, ∑ r, ∑ u' : UnT 𝔊 C,
          g n ((listSplit 𝔊 C).symm (σ, u)) r ((listSplit 𝔊 C).symm (σ, u')) :=
        Finset.sum_comm
    _ = ∑ σ : ShT 𝔊 C, ∑ w ∈ W, ∑ u : UnT 𝔊 C, ∑ r, ∑ u' : UnT 𝔊 C,
          g ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 C).symm (σ, u)) r
            ((listSplit 𝔊 C).symm (σ, u')) :=
        Finset.sum_congr rfl fun σ _ =>
          sum_eq_sum_of_support
            (fun n : ℤ => ∑ u : UnT 𝔊 C, ∑ r, ∑ u' : UnT 𝔊 C,
              g n ((listSplit 𝔊 C).symm (σ, u)) r ((listSplit 𝔊 C).symm (σ, u')))
            T W (shProd σ) (hpos σ) (hT' σ) (hW' σ)
    _ = ∑ w ∈ W, ∑ σ : ShT 𝔊 C, ∑ u : UnT 𝔊 C, ∑ r, ∑ u' : UnT 𝔊 C,
          g ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 C).symm (σ, u)) r
            ((listSplit 𝔊 C).symm (σ, u')) :=
        Finset.sum_comm
    _ = ∑ w ∈ W, ∑ σ : ShT 𝔊 C, ∑ r, ∑ u : UnT 𝔊 C, ∑ u' : UnT 𝔊 C,
          g ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 C).symm (σ, u)) r
            ((listSplit 𝔊 C).symm (σ, u')) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun σ _ => Finset.sum_comm
    _ = ∑ w ∈ W, ∑ r, ∑ σ : ShT 𝔊 C, ∑ u : UnT 𝔊 C, ∑ u' : UnT 𝔊 C,
          g ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 C).symm (σ, u)) r
            ((listSplit 𝔊 C).symm (σ, u')) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_comm

/-! ### The summands of the edge sum -/

/-- The summand vanishes unless the two lists have the same shared labels. -/
theorem edgeSummand_eq_zero_of_shared {H : ℕ} (𝔅 : JointResidueWeight H) (F : ℕ → ℝ)
    (G : ℕ → ℂ) (q₀ x : ℝ) (Ψ : ℝ → ℂ) (ν : Pattern (groupFamily 𝔊).big J 1) (n : ℤ)
    (s : Lists (groupFamily 𝔊) J 1) (r : AuxList (groupFamily 𝔊).big ν.C)
    (s' : Lists (groupFamily 𝔊) J 1)
    (h : (listSplit 𝔊 ν.C s').1 ≠ (listSplit 𝔊 ν.C s).1) :
    edgeSummand 𝔊 q₀ ν x Ψ 𝔅 F G n s r s' = 0 := by
  have hz : physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 n s r s' = 0 :=
    Schur.physCoef_eq_zero_of_not fun hc => h ((shared_iff s s').mp ⟨hc.2.2.1, hc.2.2.2.1⟩)
  unfold edgeSummand
  rw [hz, mul_zero]

/-- A nonzero summand has `n = D_R w` with `1 ≤ w < N`, when the cutoff `Ψ(w/(x D_C))` vanishes
for `w ≥ N`. -/
theorem exists_of_edgeSummand_ne_zero (h𝔊 : 𝔊.Admissible P x₀) {H : ℕ}
    (𝔅 : JointResidueWeight H) (F : ℕ → ℝ) (G : ℕ → ℂ) (q₀ : ℝ) {x : ℝ} (hx : 0 < x)
    {Ψ : ℝ → ℂ} (hΨ0 : ∀ t : ℝ, t ≤ 0 → Ψ t = 0) (ν : Pattern (groupFamily 𝔊).big J 1) {N : ℕ}
    (hN : ∀ (r : AuxList (groupFamily 𝔊).big ν.C) (w : ℕ), N ≤ w →
      Ψ ((w : ℝ) / (x * (tupleProd ν.C r : ℝ))) = 0)
    (σ : ShT 𝔊 ν.C) (n : ℤ) (u : UnT 𝔊 ν.C) (r : AuxList (groupFamily 𝔊).big ν.C)
    (u' : UnT 𝔊 ν.C)
    (hne : edgeSummand 𝔊 q₀ ν x Ψ 𝔅 F G n ((listSplit 𝔊 ν.C).symm (σ, u)) r
      ((listSplit 𝔊 ν.C).symm (σ, u')) ≠ 0) :
    ∃ w ∈ Finset.Ico 1 N, ((shProd σ * w : ℕ) : ℤ) = n := by
  have hR : 0 < shProd σ := shProd_pos h𝔊 σ
  have hRR : (0 : ℝ) < ((shProd σ : ℕ) : ℝ) := Nat.cast_pos.mpr hR
  have hΨ : Ψ ((n : ℝ) / (x * (dil ν.C ((listSplit 𝔊 ν.C).symm (σ, u)) r : ℝ))) ≠ 0 :=
    fun h => hne (edgeSummand_eq_zero _ h)
  have hpc : physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 n ((listSplit 𝔊 ν.C).symm (σ, u)) r
      ((listSplit 𝔊 ν.C).symm (σ, u')) ≠ 0 := fun h => hne (by
    unfold edgeSummand
    rw [h, mul_zero])
  have hphys : IsPhys intPos n ((listSplit 𝔊 ν.C).symm (σ, u)) :=
    (Pairing.isPhys_of_physCoef_ne_zero hpc).1
  rw [dil_mk] at hΨ
  have hd : ((listProd ((listSplit 𝔊 ν.C).symm (σ, u)) : ℕ) : ℤ) ∣ n :=
    listProd_dvd_of_isPhys hphys (gf_prime_small h𝔊) (gf_prime_big h𝔊) (gf_disj_small h𝔊)
      (gf_disj_big h𝔊) (gf_disj_small_big h𝔊)
  rw [listProd_mk, Nat.cast_mul] at hd
  obtain ⟨m, hm⟩ := (dvd_mul_right ((shProd σ : ℕ) : ℤ) ((unProd u : ℕ) : ℤ)).trans hd
  subst hm
  have hn0 : (0 : ℤ) < ((shProd σ : ℕ) : ℤ) * m := by
    by_contra hcon
    exact hΨ (hΨ0 _ (div_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr (not_lt.mp hcon))
      (mul_nonneg hx.le (Nat.cast_nonneg _))))
  have hm0 : 0 < m := by
    by_contra hcon
    exact absurd hn0 (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _)
      (not_lt.mp hcon)))
  have hwm : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm0.le
  have hcast : ((shProd σ * m.toNat : ℕ) : ℤ) = ((shProd σ : ℕ) : ℤ) * m := by
    rw [Nat.cast_mul, hwm]
  refine ⟨m.toNat, Finset.mem_Ico.mpr ⟨by omega, ?_⟩, hcast⟩
  by_contra hcon
  refine hΨ ?_
  have harg : ((((shProd σ : ℕ) : ℤ) * m : ℤ) : ℝ) /
      (x * ((shProd σ * tupleProd ν.C r : ℕ) : ℝ)) =
      ((m.toNat : ℕ) : ℝ) / (x * (tupleProd ν.C r : ℝ)) := by
    rw [← hcast, Int.cast_natCast, Nat.cast_mul, Nat.cast_mul, mul_left_comm x,
      mul_div_mul_left _ _ hRR.ne']
  rw [harg]
  exact hN r m.toNat (not_lt.mp hcon)

/-- **The edge sum of a pattern as a sum over `w`, the free labels and the shared labels**
(`[P-06:0318–0321]`). -/
theorem edgeTerm_eq_strip (h𝔊 : 𝔊.Admissible P x₀) {H : ℕ} (hH0 : 0 < H)
    (hH : ∀ p ∈ 𝔊.allPrimes, H < p) (𝔅 : JointResidueWeight H) {F : ℕ → ℝ}
    (hF : ∀ p ∈ 𝔊.allPrimes, ∀ n : ℕ, F (p * n) = F n) {x₁ Cg : ℝ} {G : ℕ → ℂ}
    (hG : CoreAdmissible 𝔊 x₁ Cg G) (q₀ : ℝ) {x : ℝ} (hx : 0 < x) {Ψ : ℝ → ℂ}
    (hΨ0 : ∀ t : ℝ, t ≤ 0 → Ψ t = 0) {c₂ : ℝ} (hc₂0 : 0 ≤ c₂)
    (hc₂ : ∀ t : ℝ, c₂ < t → Ψ t = 0) (ν : Pattern (groupFamily 𝔊).big J 1) {N : ℕ}
    (hN : ∀ (r : AuxList (groupFamily 𝔊).big ν.C) (w : ℕ), N ≤ w →
      Ψ ((w : ℝ) / (x * (tupleProd ν.C r : ℝ))) = 0) :
    edgeTerm 𝔊 q₀ ν x Ψ 𝔅 F G =
      ∑ w ∈ Finset.Ico 1 N, ∑ r, ∑ σ : ShT 𝔊 ν.C,
        corePart x Ψ 𝔅 F G ν.C r w * edgeList q₀ ν σ r w := by
  -- a finite set of positions
  have hT : ∀ n : ℤ,
      n ∉ Finset.Icc (1 : ℤ) ⌈c₂ * x * (Pairing.dilBound (groupFamily 𝔊) J : ℝ)⌉ →
      ∀ (s : Lists (groupFamily 𝔊) J 1) (r : AuxList (groupFamily 𝔊).big ν.C),
        Ψ ((n : ℝ) / (x * (dil ν.C s r : ℝ))) = 0 := by
    intro n hn s r
    have hDpos : (0 : ℝ) < (dil ν.C s r : ℝ) :=
      Nat.cast_pos.mpr (dil_pos (fun g p hp => (gf_prime_small h𝔊 g p hp).pos)
        (fun g p hp => (gf_prime_big h𝔊 g p hp).pos) ν.C s r)
    by_cases h1 : n ≤ 0
    · exact hΨ0 _ (div_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr h1)
        (mul_nonneg hx.le hDpos.le))
    · have hM : ⌈c₂ * x * (Pairing.dilBound (groupFamily 𝔊) J : ℝ)⌉ < n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨by omega, not_lt.mp h⟩)
      refine hc₂ _ ?_
      rw [lt_div_iff₀ (mul_pos hx hDpos)]
      have h4 : (dil ν.C s r : ℝ) ≤ (Pairing.dilBound (groupFamily 𝔊) J : ℝ) :=
        Nat.cast_le.mpr (Pairing.dil_le_dilBound ν.C s r)
      calc c₂ * (x * (dil ν.C s r : ℝ))
          ≤ c₂ * (x * (Pairing.dilBound (groupFamily 𝔊) J : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hx.le) hc₂0
        _ = c₂ * x * (Pairing.dilBound (groupFamily 𝔊) J : ℝ) := by ring
        _ ≤ ((⌈c₂ * x * (Pairing.dilBound (groupFamily 𝔊) J : ℝ)⌉ : ℤ) : ℝ) := Int.le_ceil _
        _ < (n : ℝ) := Int.cast_lt.mpr hM
  rw [edgeTerm_eq_sum 𝔊 q₀ ν x Ψ 𝔅 F G _ hT,
    sum_reindex ν.C (fun n s r s' => edgeSummand 𝔊 q₀ ν x Ψ 𝔅 F G n s r s') _
      (Finset.Ico 1 N) (fun σ => shProd_pos h𝔊 σ)
      (fun n hn s r s' => edgeSummand_eq_zero s' (hT n hn s r))
      (fun n s r s' h => edgeSummand_eq_zero_of_shared 𝔅 F G q₀ x Ψ ν n s r s' h)
      (fun σ n u r u' hne =>
        exists_of_edgeSummand_ne_zero h𝔊 𝔅 F G q₀ hx hΨ0 ν hN σ n u r u' hne)]
  refine Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun σ _ => ?_
  exact sum_edgeSummand_mk h𝔊 hH0 hH 𝔅 hF hG q₀ x Ψ ν σ r (Finset.mem_Ico.mp hw).1

/-! ### The stripped expression -/

/-- `corePart` vanishes where the cutoff vanishes. -/
theorem corePart_eq_zero_of {x : ℝ} {Ψ : ℝ → ℂ} {H : ℕ} {𝔅 : JointResidueWeight H} {F : ℕ → ℝ}
    {G : ℕ → ℂ} {C : Fin 𝔊.numBig → Finset (Fin J)} {r : AuxList (groupFamily 𝔊).big C} {w : ℕ}
    (h : Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0) : corePart x Ψ 𝔅 F G C r w = 0 := by
  unfold corePart
  rw [h, zero_div, zero_mul, zero_mul, zero_mul]

/-- `corePart` vanishes at `w = 0`. -/
theorem corePart_zero (x : ℝ) (Ψ : ℝ → ℂ) {H : ℕ} (𝔅 : JointResidueWeight H) (F : ℕ → ℝ)
    (G : ℕ → ℂ) (C : Fin 𝔊.numBig → Finset (Fin J)) (r : AuxList (groupFamily 𝔊).big C) :
    corePart x Ψ 𝔅 F G C r 0 = 0 := by
  unfold corePart
  rw [Nat.cast_zero (R := ℂ), div_zero, zero_mul, zero_mul, zero_mul]

/-- **The stripped expression (cor:stripped) of a pattern** with freed slots `C` and a stripped
coefficient `κ` on the represented lists (`[P-06:0330–0339]`); `strippedSumOf` is the case of the
comparison coefficient, and for the raw pattern it is the two-sided sum (eq:two-sided). -/
def genStrip (q₀ x : ℝ) (Ψ : ℝ → ℂ) {H : ℕ} (𝔅 : JointResidueWeight H) (F : ℕ → ℝ) (G : ℕ → ℂ)
    (C : Fin 𝔊.numBig → Finset (Fin J))
    (κ : AuxList (groupFamily 𝔊).big C → ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) →
      ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ) : ℂ :=
  ∑ r : AuxList (groupFamily 𝔊).big C, ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ) *
    ∑ᶠ w : ℕ, corePart x Ψ 𝔅 F G C r w *
      ((activeCoeff 𝔊 q₀ (markCount 𝔊 C) w *
          activeCoeff 𝔊 q₀ (markCount 𝔊 C) (w + tupleProd C r) : ℝ) : ℂ) *
      ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
        ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r), κ r 𝔭 𝔭'

/-- **The stripped expression as a sum over `w`, the free labels and the shared labels** (the
shared labels enter only through their law, of total mass one). -/
theorem genStrip_eq_sum
    (hlaw : ∀ g : 𝔊.Index, ∑ p ∈ 𝔊.group g, Graph.primeGroupLaw (𝔊.group g) p = 1)
    (q₀ x : ℝ) (Ψ : ℝ → ℂ) {H : ℕ} (𝔅 : JointResidueWeight H) (F : ℕ → ℝ) (G : ℕ → ℂ)
    (C : Fin 𝔊.numBig → Finset (Fin J))
    (κ : AuxList (groupFamily 𝔊).big C → ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) →
      ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ) {N : ℕ}
    (hN : ∀ (r : AuxList (groupFamily 𝔊).big C) (w : ℕ), N ≤ w →
      Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0) :
    genStrip q₀ x Ψ 𝔅 F G C κ =
      ∑ w ∈ Finset.Ico 1 N, ∑ r, ∑ σ : ShT 𝔊 C,
        corePart x Ψ 𝔅 F G C r w * (((shWeight σ : ℝ) : ℂ) * mainList q₀ C κ r w) := by
  have hσ : ∀ (r : AuxList (groupFamily 𝔊).big C) (w : ℕ),
      ∑ σ : ShT 𝔊 C, corePart x Ψ 𝔅 F G C r w *
          (((shWeight σ : ℝ) : ℂ) * mainList q₀ C κ r w) =
        corePart x Ψ 𝔅 F G C r w * mainList q₀ C κ r w := by
    intro r w
    have h1 : ∑ σ : ShT 𝔊 C, ((shWeight σ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_sum, sum_shWeight hlaw, Complex.ofReal_one]
    calc ∑ σ : ShT 𝔊 C, corePart x Ψ 𝔅 F G C r w *
          (((shWeight σ : ℝ) : ℂ) * mainList q₀ C κ r w)
        = ∑ σ : ShT 𝔊 C, ((shWeight σ : ℝ) : ℂ) *
            (corePart x Ψ 𝔅 F G C r w * mainList q₀ C κ r w) :=
          Finset.sum_congr rfl fun σ _ => by ring
      _ = (∑ σ : ShT 𝔊 C, ((shWeight σ : ℝ) : ℂ)) *
            (corePart x Ψ 𝔅 F G C r w * mainList q₀ C κ r w) := (Finset.sum_mul _ _ _).symm
      _ = corePart x Ψ 𝔅 F G C r w * mainList q₀ C κ r w := by rw [h1, one_mul]
  have hsupp : ∀ r : AuxList (groupFamily 𝔊).big C,
      (Function.support fun w : ℕ => corePart x Ψ 𝔅 F G C r w *
        ((activeCoeff 𝔊 q₀ (markCount 𝔊 C) w *
            activeCoeff 𝔊 q₀ (markCount 𝔊 C) (w + tupleProd C r) : ℝ) : ℂ) *
        ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
          ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r), κ r 𝔭 𝔭') ⊆
        ((Finset.Ico 1 N : Finset ℕ) : Set ℕ) := by
    intro r w hw
    by_contra hmem
    refine hw ?_
    show corePart x Ψ 𝔅 F G C r w * _ * _ = 0
    rcases Nat.eq_zero_or_pos w with h0 | hpos
    · rw [h0, corePart_zero, zero_mul, zero_mul]
    · have hNw : N ≤ w := by
        by_contra hlt
        exact hmem (Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨hpos, not_le.mp hlt⟩))
      rw [corePart_eq_zero_of (hN r w hNw), zero_mul, zero_mul]
  have hr : ∀ r : AuxList (groupFamily 𝔊).big C,
      ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ) *
        ∑ᶠ w : ℕ, corePart x Ψ 𝔅 F G C r w *
          ((activeCoeff 𝔊 q₀ (markCount 𝔊 C) w *
              activeCoeff 𝔊 q₀ (markCount 𝔊 C) (w + tupleProd C r) : ℝ) : ℂ) *
          ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
            ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r), κ r 𝔭 𝔭' =
      ∑ w ∈ Finset.Ico 1 N, corePart x Ψ 𝔅 F G C r w * mainList q₀ C κ r w := by
    intro r
    rw [finsum_eq_sum_of_support_subset _ (hsupp r), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold mainList
    push_cast
    ring
  unfold genStrip
  rw [Finset.sum_congr rfl fun r _ => hr r, Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun r _ => (hσ r w).symm

/-! ### The structural inequality -/

/-- **The edge sum of a pattern against its stripped expression** (`[P-06:0318–0346]`): the
difference is controlled by the positions `w` divisible by a free label and by the probability of
a collision of the shared labels. -/
theorem norm_edgeTerm_sub_le (h𝔊 : 𝔊.Admissible P x₀)
    (hlaw : ∀ g : 𝔊.Index, ∑ p ∈ 𝔊.group g, Graph.primeGroupLaw (𝔊.group g) p = 1) {H : ℕ}
    (hH0 : 0 < H) (hH : ∀ p ∈ 𝔊.allPrimes, H < p) (𝔅 : JointResidueWeight H) {F : ℕ → ℝ}
    (hF : ∀ p ∈ 𝔊.allPrimes, ∀ n : ℕ, F (p * n) = F n) {x₁ Cg : ℝ} {G : ℕ → ℂ}
    (hG : CoreAdmissible 𝔊 x₁ Cg G) {q₀ : ℝ} (hq0 : 0 < q₀) (hq1 : q₀ < 1) {x : ℝ} (hx : 0 < x)
    {Ψ : ℝ → ℂ} (hΨ0 : ∀ t : ℝ, t ≤ 0 → Ψ t = 0) {c₂ : ℝ} (hc₂0 : 0 ≤ c₂)
    (hc₂ : ∀ t : ℝ, c₂ < t → Ψ t = 0) (ν : Pattern (groupFamily 𝔊).big J 1)
    (κ : AuxList (groupFamily 𝔊).big ν.C → ((g : 𝔊.Index) → Fin (markCount 𝔊 ν.C g) → ℕ) →
      ((g : 𝔊.Index) → Fin (markCount 𝔊 ν.C g) → ℕ) → ℂ)
    (hκ : ∀ (σ : ShT 𝔊 ν.C) (u u' : UnT 𝔊 ν.C) (r : AuxList (groupFamily 𝔊).big ν.C),
      ν.K ((listSplit 𝔊 ν.C).symm (σ, u)).2 ((listSplit 𝔊 ν.C).symm (σ, u')).2 r =
        κ r (unVal u) (unVal u'))
    {Kmax : ℝ} (hK0 : 0 ≤ Kmax) (hK : ∀ p p' r, ‖ν.K p p' r‖ ≤ Kmax)
    (hκK : ∀ r 𝔭 𝔭', ‖κ r 𝔭 𝔭'‖ ≤ Kmax) {T : ℕ} (hT1 : 1 ≤ T)
    (hT : ∀ g, 1 + (ν.C g).card ≤ T) {Lm : ℝ}
    (hMB : ∀ n : ℕ, ‖𝔊.activeWeight q₀ (markCount 𝔊 ν.C) (fun _ => 1) n‖ ≤ Lm) {N : ℕ}
    (hN : ∀ (r : AuxList (groupFamily 𝔊).big ν.C) (w : ℕ), N ≤ w →
      Ψ ((w : ℝ) / (x * (tupleProd ν.C r : ℝ))) = 0) :
    ‖edgeTerm 𝔊 q₀ ν x Ψ 𝔅 F G - genStrip q₀ x Ψ 𝔅 F G ν.C κ‖ ≤
      Kmax * (((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
            ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) *
          ((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
            ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) + Lm * Lm) *
        ∑ w ∈ Finset.Ico 1 N, ∑ r : AuxList (groupFamily 𝔊).big ν.C,
          ‖corePart x Ψ 𝔅 F G ν.C r w‖ * (auxWeight (groupFamily 𝔊).big ν.C r *
            (freeInd r w + ∑ σ : ShT 𝔊 ν.C, shWeight σ * badInd σ (forbid r w))) := by
  obtain ⟨Γ2, hΓ2⟩ : ∃ Γ2 : ℝ, Γ2 =
      ((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
          ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) *
        ((∏ _g : Fin 𝔊.numSmall, Schur.groupConst P.vlo q₀ T) *
          ∏ _g : Fin 𝔊.numBig, Schur.groupConst P.vlo q₀ T) + Lm * Lm := ⟨_, rfl⟩
  have hdiff : edgeTerm 𝔊 q₀ ν x Ψ 𝔅 F G - genStrip q₀ x Ψ 𝔅 F G ν.C κ =
      ∑ w ∈ Finset.Ico 1 N, ∑ r, ∑ σ : ShT 𝔊 ν.C, corePart x Ψ 𝔅 F G ν.C r w *
        (edgeList q₀ ν σ r w - ((shWeight σ : ℝ) : ℂ) * mainList q₀ ν.C κ r w) := by
    rw [edgeTerm_eq_strip h𝔊 hH0 hH 𝔅 hF hG q₀ hx hΨ0 hc₂0 hc₂ ν hN,
      genStrip_eq_sum hlaw q₀ x Ψ 𝔅 F G ν.C κ hN, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun σ _ => (mul_sub _ _ _).symm
  have hterm : ∀ (w : ℕ) (r : AuxList (groupFamily 𝔊).big ν.C) (σ : ShT 𝔊 ν.C),
      ‖corePart x Ψ 𝔅 F G ν.C r w *
        (edgeList q₀ ν σ r w - ((shWeight σ : ℝ) : ℂ) * mainList q₀ ν.C κ r w)‖ ≤
      ‖corePart x Ψ 𝔅 F G ν.C r w‖ * (shWeight σ *
        (auxWeight (groupFamily 𝔊).big ν.C r * Kmax * Γ2) *
          (freeInd r w + badInd σ (forbid r w))) := by
    intro w r σ
    rw [norm_mul, hΓ2]
    exact mul_le_mul_of_nonneg_left
      (norm_edgeList_sub_le h𝔊 hq0 hq1 ν κ hκ hK0 hK hκK hT1 hT hMB σ r w) (norm_nonneg _)
  have hsumσ : ∀ (w : ℕ) (r : AuxList (groupFamily 𝔊).big ν.C),
      ∑ σ : ShT 𝔊 ν.C, ‖corePart x Ψ 𝔅 F G ν.C r w‖ * (shWeight σ *
        (auxWeight (groupFamily 𝔊).big ν.C r * Kmax * Γ2) *
          (freeInd r w + badInd σ (forbid r w))) =
      Kmax * Γ2 * (‖corePart x Ψ 𝔅 F G ν.C r w‖ * (auxWeight (groupFamily 𝔊).big ν.C r *
        (freeInd r w + ∑ σ : ShT 𝔊 ν.C, shWeight σ * badInd σ (forbid r w)))) := by
    intro w r
    have e : ∀ σ : ShT 𝔊 ν.C, ‖corePart x Ψ 𝔅 F G ν.C r w‖ * (shWeight σ *
          (auxWeight (groupFamily 𝔊).big ν.C r * Kmax * Γ2) *
            (freeInd r w + badInd σ (forbid r w))) =
        (‖corePart x Ψ 𝔅 F G ν.C r w‖ * auxWeight (groupFamily 𝔊).big ν.C r * Kmax * Γ2 *
            freeInd r w) * shWeight σ +
          (‖corePart x Ψ 𝔅 F G ν.C r w‖ * auxWeight (groupFamily 𝔊).big ν.C r * Kmax * Γ2) *
            (shWeight σ * badInd σ (forbid r w)) := fun σ => by ring
    rw [Finset.sum_congr rfl fun σ _ => e σ, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_shWeight hlaw]
    ring
  rw [hdiff, ← hΓ2]
  calc ‖∑ w ∈ Finset.Ico 1 N, ∑ r, ∑ σ : ShT 𝔊 ν.C, corePart x Ψ 𝔅 F G ν.C r w *
        (edgeList q₀ ν σ r w - ((shWeight σ : ℝ) : ℂ) * mainList q₀ ν.C κ r w)‖
      ≤ ∑ w ∈ Finset.Ico 1 N, ∑ r, ∑ σ : ShT 𝔊 ν.C, ‖corePart x Ψ 𝔅 F G ν.C r w *
          (edgeList q₀ ν σ r w - ((shWeight σ : ℝ) : ℂ) * mainList q₀ ν.C κ r w)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => norm_sum_le _ _))
    _ ≤ ∑ w ∈ Finset.Ico 1 N, ∑ r, ∑ σ : ShT 𝔊 ν.C,
          ‖corePart x Ψ 𝔅 F G ν.C r w‖ * (shWeight σ *
            (auxWeight (groupFamily 𝔊).big ν.C r * Kmax * Γ2) *
              (freeInd r w + badInd σ (forbid r w))) :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun r _ =>
          Finset.sum_le_sum fun σ _ => hterm w r σ
    _ = ∑ w ∈ Finset.Ico 1 N, ∑ r : AuxList (groupFamily 𝔊).big ν.C,
          Kmax * Γ2 * (‖corePart x Ψ 𝔅 F G ν.C r w‖ * (auxWeight (groupFamily 𝔊).big ν.C r *
            (freeInd r w + ∑ σ : ShT 𝔊 ν.C, shWeight σ * badInd σ (forbid r w)))) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun r _ => hsumσ w r
    _ = Kmax * Γ2 * ∑ w ∈ Finset.Ico 1 N, ∑ r : AuxList (groupFamily 𝔊).big ν.C,
          ‖corePart x Ψ 𝔅 F G ν.C r w‖ * (auxWeight (groupFamily 𝔊).big ν.C r *
            (freeInd r w + ∑ σ : ShT 𝔊 ν.C, shWeight σ * badInd σ (forbid r w))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => (Finset.mul_sum _ _ _).symm

end Identity

end Strip

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
