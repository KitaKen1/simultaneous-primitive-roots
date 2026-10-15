module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements

/-!
# Ordinary and exceptional times: the cell argument

The threshold split of `[P-06:0763–0832]` ("On the set `|P_s(t)| ≤ L^{-A_s}` … Let `𝒥` be the
integer unit intervals meeting `{|t| ≤ 2T_0 : |P_s(t)| > L^{-A_s}}` … Select a point exceeding
the threshold from each occupied interval, and split their integer indices … to get separated
sets … Choose maximizing points and again split into … separated classes"), as a statement about
integrals over an interval `[a, b]`.

* `integral_le_of_unit_cells`: with the cells `[a + i, a + i + 1] ∩ [a, b]`, a bound
  `F ≤ g + κ_i` on the `i`-th cell gives `∫_a^b F ≤ ∫_a^b g + ∑_i κ_i`.
* `integral_le_of_ordinary_exceptional`: let `Pex` be the exceptional times. If `F ≤ g` at
  ordinary times and `F ≤ g + ρ` at exceptional times, every `1`-separated set of exceptional
  times in `[a, b]` has at most `K_c` elements, and `∑_{t ∈ 𝒯} ρ(t) ≤ Σ₀` for every `1`-separated
  `𝒯 ⊆ [a, b]` with at most `K_c` elements, then `∫_a^b F ≤ ∫_a^b g + 2 Σ₀`. (On a cell
  containing an exceptional time, `F ≤ g + max_{cell} ρ`; the cells of even index, and those of
  odd index, give `1`-separated sets of maximizing points and of exceptional points.)
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-- **Unit cells**: if `F ≤ g + κ_i` on `[a + i, a + i + 1] ∩ [a, b]` for every `i`, then
`∫_a^b F ≤ ∫_a^b g + ∑_{i < ⌈b - a⌉} κ_i`. -/
theorem integral_le_of_unit_cells {F g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) (κ : ℕ → ℝ)
    (hκ : ∀ i, 0 ≤ κ i)
    (h : ∀ i : ℕ, ∀ u ∈ Set.Icc (min (a + (i : ℝ)) b) (min (a + ((i + 1 : ℕ) : ℝ)) b),
      F u ≤ g u + κ i) :
    ∫ u in a..b, F u ≤ (∫ u in a..b, g u) + ∑ i ∈ Finset.range ⌈b - a⌉₊, κ i := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℝ, ∀ i, p i = min (a + (i : ℝ)) b :=
    ⟨fun i => min (a + (i : ℝ)) b, fun _ => rfl⟩
  have hp0 : p 0 = a := by rw [hp, Nat.cast_zero, add_zero, min_eq_left hab]
  have hpn : p ⌈b - a⌉₊ = b := by
    have h1 : b - a ≤ (⌈b - a⌉₊ : ℝ) := Nat.le_ceil _
    rw [hp]
    exact min_eq_right (by linarith)
  have hmono : ∀ i, p i ≤ p (i + 1) := fun i => by
    rw [hp i, hp (i + 1)]
    refine min_le_min ?_ le_rfl
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hpa : ∀ i, a ≤ p i := fun i => by
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    rw [hp]
    exact le_min (by linarith) hab
  have hpb : ∀ i, p i ≤ b := fun i => by
    rw [hp]
    exact min_le_right _ _
  have hlen : ∀ i, p (i + 1) - p i ≤ 1 := fun i => by
    rw [hp i, hp (i + 1), Nat.cast_add, Nat.cast_one]
    rcases le_total (a + (i : ℝ)) b with h1 | h1
    · have h2 := min_le_left (a + ((i : ℝ) + 1)) b
      rw [min_eq_left h1]
      linarith
    · rw [min_eq_right h1, min_eq_right (by linarith)]
      linarith
  have hsub : ∀ i, Set.Icc (p i) (p (i + 1)) ⊆ Set.Icc a b := fun i =>
    Set.Icc_subset_Icc (hpa i) (hpb (i + 1))
  have hintF : ∀ i, IntervalIntegrable F MeasureTheory.volume (p i) (p (i + 1)) := fun i =>
    ContinuousOn.intervalIntegrable_of_Icc (hmono i) (hF.mono (hsub i))
  have hintg : ∀ i, IntervalIntegrable g MeasureTheory.volume (p i) (p (i + 1)) := fun i =>
    ContinuousOn.intervalIntegrable_of_Icc (hmono i) (hg.mono (hsub i))
  have hcell : ∀ i, ∫ u in p i..p (i + 1), F u ≤ (∫ u in p i..p (i + 1), g u) + κ i := by
    intro i
    have hc : IntervalIntegrable (fun _ : ℝ => κ i) MeasureTheory.volume (p i) (p (i + 1)) :=
      continuous_const.intervalIntegrable _ _
    have h1 : ∫ u in p i..p (i + 1), F u ≤ ∫ u in p i..p (i + 1), (g u + κ i) :=
      intervalIntegral.integral_mono_on (hmono i) (hintF i) ((hintg i).add hc) (fun u hu => by
        rw [hp i, hp (i + 1)] at hu
        exact h i u hu)
    have h2 : ∫ u in p i..p (i + 1), (g u + κ i) =
        (∫ u in p i..p (i + 1), g u) + (p (i + 1) - p i) * κ i := by
      rw [intervalIntegral.integral_add (hintg i) hc, intervalIntegral.integral_const,
        smul_eq_mul]
    have h3 : (p (i + 1) - p i) * κ i ≤ κ i := by
      have h4 := mul_le_mul_of_nonneg_right (hlen i) (hκ i)
      rw [one_mul] at h4
      exact h4
    linarith
  have hsumF : ∑ i ∈ Finset.range ⌈b - a⌉₊, ∫ u in p i..p (i + 1), F u = ∫ u in a..b, F u := by
    have h1 := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (f := F) (a := p) (n := ⌈b - a⌉₊) (fun k _ => hintF k)
    rw [hp0, hpn] at h1
    exact h1
  have hsumg : ∑ i ∈ Finset.range ⌈b - a⌉₊, ∫ u in p i..p (i + 1), g u = ∫ u in a..b, g u := by
    have h1 := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (f := g) (a := p) (n := ⌈b - a⌉₊) (fun k _ => hintg k)
    rw [hp0, hpn] at h1
    exact h1
  rw [← hsumF, ← hsumg, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => hcell i

/-- **Ordinary and exceptional times.** If `F ≤ g` at the ordinary times of `[a, b]` and
`F ≤ g + ρ` at the exceptional ones (`Pex`), a `1`-separated set of exceptional times has at most
`K_c` elements, and `∑_{t ∈ 𝒯} ρ(t) ≤ Σ₀` on `1`-separated sets with at most `K_c` elements, then
`∫_a^b F ≤ ∫_a^b g + 2 Σ₀`. -/
theorem integral_le_of_ordinary_exceptional {F g ρ : ℝ → ℝ} {a b Kc Sg : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hρ : ContinuousOn ρ (Set.Icc a b)) (hρ0 : ∀ u ∈ Set.Icc a b, 0 ≤ ρ u) (Pex : ℝ → Prop)
    (hord : ∀ u ∈ Set.Icc a b, ¬ Pex u → F u ≤ g u)
    (hexc : ∀ u ∈ Set.Icc a b, Pex u → F u ≤ g u + ρ u)
    (hcount : ∀ 𝒮 : Finset ℝ, (∀ s ∈ 𝒮, s ∈ Set.Icc a b ∧ Pex s) →
      (∀ s ∈ 𝒮, ∀ s' ∈ 𝒮, s ≠ s' → 1 ≤ |s - s'|) → (𝒮.card : ℝ) ≤ Kc)
    (hsparse : ∀ 𝒯 : Finset ℝ, (∀ t ∈ 𝒯, t ∈ Set.Icc a b) →
      (∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, t ≠ t' → 1 ≤ |t - t'|) → (𝒯.card : ℝ) ≤ Kc →
        ∑ t ∈ 𝒯, ρ t ≤ Sg) :
    ∫ u in a..b, F u ≤ (∫ u in a..b, g u) + 2 * Sg := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℝ, ∀ i, p i = min (a + (i : ℝ)) b :=
    ⟨fun i => min (a + (i : ℝ)) b, fun _ => rfl⟩
  have hmono : ∀ i, p i ≤ p (i + 1) := fun i => by
    rw [hp i, hp (i + 1)]
    refine min_le_min ?_ le_rfl
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hpa : ∀ i, a ≤ p i := fun i => by
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    rw [hp]
    exact le_min (by linarith) hab
  have hpb : ∀ i, p i ≤ b := fun i => by
    rw [hp]
    exact min_le_right _ _
  have hsub : ∀ i, Set.Icc (p i) (p (i + 1)) ⊆ Set.Icc a b := fun i =>
    Set.Icc_subset_Icc (hpa i) (hpb (i + 1))
  -- maximizing points of `ρ` on the cells
  have hmax : ∀ i, ∃ τ ∈ Set.Icc (p i) (p (i + 1)),
      ∀ u ∈ Set.Icc (p i) (p (i + 1)), ρ u ≤ ρ τ := by
    intro i
    obtain ⟨τ, hτ, hτmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (hmono i))
      (hρ.mono (hsub i))
    exact ⟨τ, hτ, fun u hu => isMaxOn_iff.mp hτmax u hu⟩
  choose t ht_mem ht_max using hmax
  -- the exceptional cells and a point exceeding the threshold in each
  obtain ⟨Exc, hExc⟩ : ∃ Exc : ℕ → Prop,
      ∀ i, Exc i ↔ ∃ s ∈ Set.Icc (p i) (p (i + 1)), Pex s :=
    ⟨fun i => ∃ s ∈ Set.Icc (p i) (p (i + 1)), Pex s, fun _ => Iff.rfl⟩
  have hsel : ∀ i, ∃ σ : ℝ, Exc i → σ ∈ Set.Icc (p i) (p (i + 1)) ∧ Pex σ := by
    intro i
    by_cases hi : Exc i
    · obtain ⟨σ, h1, h2⟩ := (hExc i).mp hi
      exact ⟨σ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' hi⟩
  choose s hs using hsel
  -- the bound on each cell
  have hκ0 : ∀ i, 0 ≤ (if Exc i then ρ (t i) else 0) := fun i => by
    by_cases hi : Exc i
    · rw [if_pos hi]
      exact hρ0 (t i) (hsub i (ht_mem i))
    · exact le_of_eq (if_neg hi).symm
  have hcellpt : ∀ i : ℕ,
      ∀ u ∈ Set.Icc (min (a + (i : ℝ)) b) (min (a + ((i + 1 : ℕ) : ℝ)) b),
        F u ≤ g u + (if Exc i then ρ (t i) else 0) := by
    intro i u hu
    rw [← hp i, ← hp (i + 1)] at hu
    have huab := hsub i hu
    by_cases hi : Exc i
    · rw [if_pos hi]
      by_cases hPu : Pex u
      · have h1 := hexc u huab hPu
        have h2 := ht_max i u hu
        linarith
      · have h1 := hord u huab hPu
        have h2 := hρ0 (t i) (hsub i (ht_mem i))
        linarith
    · rw [if_neg hi, add_zero]
      exact hord u huab fun hP => hi ((hExc i).mpr ⟨u, hu, hP⟩)
  have hmain : ∫ u in a..b, F u ≤ (∫ u in a..b, g u) +
      ∑ i ∈ Finset.range ⌈b - a⌉₊, (if Exc i then ρ (t i) else 0) :=
    integral_le_of_unit_cells hab hF hg (fun i => if Exc i then ρ (t i) else 0) hκ0 hcellpt
  -- one class of cells with gaps
  have hclass : ∀ I' : Finset ℕ, (∀ i ∈ I', i < ⌈b - a⌉₊ ∧ Exc i) →
      (∀ i ∈ I', ∀ j ∈ I', i ≠ j → i + 2 ≤ j ∨ j + 2 ≤ i) → ∑ i ∈ I', ρ (t i) ≤ Sg := by
    intro I' hI' hgap
    have key : ∀ i j : ℕ, j < ⌈b - a⌉₊ → i + 2 ≤ j → ∀ u ∈ Set.Icc (p i) (p (i + 1)),
        ∀ v ∈ Set.Icc (p j) (p (j + 1)), 1 ≤ v - u := by
      intro i j hj hij u hu v hv
      have hjlt : (j : ℝ) < b - a := Nat.lt_ceil.mp hj
      have hpj : p j = a + (j : ℝ) := by
        rw [hp]
        exact min_eq_left (by linarith)
      have hpi1 : p (i + 1) ≤ a + ((i : ℝ) + 1) := by
        rw [hp, Nat.cast_add, Nat.cast_one]
        exact min_le_left _ _
      have hij' : (i : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hij
      have h1 := hu.2
      have h2 := hv.1
      rw [hpj] at h2
      linarith
    have hsep : ∀ i ∈ I', ∀ j ∈ I', i ≠ j → ∀ u ∈ Set.Icc (p i) (p (i + 1)),
        ∀ v ∈ Set.Icc (p j) (p (j + 1)), 1 ≤ |u - v| := by
      intro i hi j hj hij u hu v hv
      rcases hgap i hi j hj hij with h1 | h1
      · have h2 := key i j (hI' j hj).1 h1 u hu v hv
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        exact h2
      · have h2 := key j i (hI' i hi).1 h1 v hv u hu
        rw [abs_of_nonneg (by linarith)]
        exact h2
    have hsmem : ∀ i ∈ I', s i ∈ Set.Icc (p i) (p (i + 1)) ∧ Pex (s i) := fun i hi =>
      hs i (hI' i hi).2
    have htinj : Set.InjOn t (I' : Set ℕ) := by
      intro i hi j hj hij
      by_contra hne
      have h1 := hsep i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hne (t i) (ht_mem i)
        (t j) (ht_mem j)
      rw [hij, sub_self, abs_zero] at h1
      linarith
    have hsinj : Set.InjOn s (I' : Set ℕ) := by
      intro i hi j hj hij
      by_contra hne
      have h1 := hsep i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hne (s i)
        (hsmem i (Finset.mem_coe.mp hi)).1 (s j) (hsmem j (Finset.mem_coe.mp hj)).1
      rw [hij, sub_self, abs_zero] at h1
      linarith
    have hcardS : ((I'.image s).card : ℝ) ≤ Kc := by
      refine hcount (I'.image s) ?_ ?_
      · intro σ hσ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hσ
        exact ⟨hsub i (hsmem i hi).1, (hsmem i hi).2⟩
      · intro σ hσ σ' hσ' hne
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hσ
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hσ'
        have hij : i ≠ j := fun h' => hne (by rw [h'])
        exact hsep i hi j hj hij (s i) (hsmem i hi).1 (s j) (hsmem j hj).1
    have hT : ∑ i ∈ I', ρ (t i) = ∑ τ ∈ I'.image t, ρ τ :=
      (Finset.sum_image (f := ρ) htinj).symm
    rw [hT]
    refine hsparse (I'.image t) ?_ ?_ ?_
    · intro τ hτ
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hτ
      exact hsub i (ht_mem i)
    · intro τ hτ τ' hτ' hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hτ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hτ'
      have hij : i ≠ j := fun h' => hne (by rw [h'])
      exact hsep i hi j hj hij (t i) (ht_mem i) (t j) (ht_mem j)
    · rw [Finset.card_image_of_injOn htinj, ← Finset.card_image_of_injOn hsinj]
      exact hcardS
  -- the cells of even and of odd index
  have heven := hclass (((Finset.range ⌈b - a⌉₊).filter Exc).filter (fun i => i % 2 = 0))
    (fun i hi => by
      have h2 := Finset.mem_filter.mp (Finset.mem_filter.mp hi).1
      exact ⟨Finset.mem_range.mp h2.1, h2.2⟩)
    (fun i hi j hj hij => by
      have h1 := (Finset.mem_filter.mp hi).2
      have h2 := (Finset.mem_filter.mp hj).2
      omega)
  have hodd := hclass (((Finset.range ⌈b - a⌉₊).filter Exc).filter (fun i => ¬ i % 2 = 0))
    (fun i hi => by
      have h2 := Finset.mem_filter.mp (Finset.mem_filter.mp hi).1
      exact ⟨Finset.mem_range.mp h2.1, h2.2⟩)
    (fun i hi j hj hij => by
      have h1 := (Finset.mem_filter.mp hi).2
      have h2 := (Finset.mem_filter.mp hj).2
      omega)
  have hsplit : ∑ i ∈ Finset.range ⌈b - a⌉₊, (if Exc i then ρ (t i) else 0) =
      ∑ i ∈ ((Finset.range ⌈b - a⌉₊).filter Exc).filter (fun i => i % 2 = 0), ρ (t i) +
        ∑ i ∈ ((Finset.range ⌈b - a⌉₊).filter Exc).filter (fun i => ¬ i % 2 = 0), ρ (t i) := by
    rw [Finset.sum_filter_add_sum_filter_not, Finset.sum_filter]
  rw [hsplit] at hmain
  linarith

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
