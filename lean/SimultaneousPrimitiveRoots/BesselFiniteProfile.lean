module

public import SimultaneousPrimitiveRoots.BesselKIntegralProfile
public import SimultaneousPrimitiveRoots.ReflectionKernelMellin

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

/-- A nonempty finite list of actual local K integrals, convolved against dt/t. -/
def artinBesselProductProfile (c : ℝ) : List ℝ → ℝ → ℂ
  | [] => artinBesselLocalProfile c
  | d :: ds => artinMultiplicativeConvolution (artinBesselLocalProfile d)
      (artinBesselProductProfile c ds)

def artinBesselProductC (c : ℝ) (ds : List ℝ) : ℝ :=
  (2 / c ^ 2) * (ds.map (fun d => 2 / d ^ 2)).prod

def artinBesselProductA (c : ℝ) (ds : List ℝ) : ℝ :=
  (4 / c ^ 2) * (ds.map (fun d => 4 / d ^ 2)).prod

theorem artinBesselProductC_cons (c d : ℝ) (ds : List ℝ) :
    artinBesselProductC c (d :: ds) = (2 / d ^ 2) * artinBesselProductC c ds := by
  simp only [artinBesselProductC, List.map_cons, List.prod_cons]
  ring

theorem artinBesselProductA_cons (c d : ℝ) (ds : List ℝ) :
    artinBesselProductA c (d :: ds) = (4 / d ^ 2) * artinBesselProductA c ds := by
  simp only [artinBesselProductA, List.map_cons, List.prod_cons]
  ring

theorem artinBesselProduct_constants_pos {c : ℝ} (hc : 0 < c) {ds : List ℝ}
    (hds : ∀ d ∈ ds, 0 < d) :
    0 < artinBesselProductC c ds ∧ 0 < artinBesselProductA c ds := by
  induction ds with
  | nil => simpa [artinBesselProductC, artinBesselProductA] using
      artinBesselLocalProfile_constants_pos hc
  | cons d ds ih =>
    have hd : 0 < d := hds d (by simp)
    have hr := ih (fun x hx => hds x (by simp [hx]))
    rw [artinBesselProductC_cons, artinBesselProductA_cons]
    exact ⟨mul_pos (by positivity) hr.1, mul_pos (by positivity) hr.2⟩

theorem artinBesselProductProfile_mellin_convergent {c : ℝ} (hc : 0 < c)
    {ds : List ℝ} (hds : ∀ d ∈ ds, 0 < d) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinBesselProductProfile c ds) s := by
  induction ds with
  | nil => exact artinBesselLocalProfile_mellin_convergent hc hs
  | cons d ds ih =>
    exact artinMultiplicativeConvolution_mellin_convergent
      (artinBesselLocalProfile_mellin_convergent (hds d (by simp)) hs)
      (ih (fun x hx => hds x (by simp [hx])))

theorem artinBesselProductProfile_mellin {c : ℝ} (hc : 0 < c)
    {ds : List ℝ} (hds : ∀ d ∈ ds, 0 < d) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinBesselProductProfile c ds) s =
      (artinBesselProductC c ds : ℂ) * (artinBesselProductA c ds : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (ds.length + 1) := by
  induction ds with
  | nil => simpa [artinBesselProductProfile, artinBesselProductC, artinBesselProductA]
      using artinBesselLocalProfile_mellin_gammaForm hc hs
  | cons d ds ih =>
    have hd : 0 < d := hds d (by simp)
    have hr : ∀ x ∈ ds, 0 < x := fun x hx => hds x (by simp [hx])
    rw [artinBesselProductProfile, artinMultiplicativeConvolution_mellin
      (artinBesselLocalProfile_mellin_convergent hd hs)
      (artinBesselProductProfile_mellin_convergent hc hr hs),
      artinBesselLocalProfile_mellin_gammaForm hd hs, ih hr,
      artinBesselProductC_cons, artinBesselProductA_cons]
    simp only [Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (by positivity)
        (artinBesselProduct_constants_pos hc hr).2.le, List.length_cons, pow_succ]
    push_cast
    ring

/-- D is an explicit positive mass parameter. Its identification with the
paper's finite-place and angular Haar masses is not assumed proved. -/
def artinBesselFiniteProfile (D c : ℝ) (ds : List ℝ) (u : ℝ) : ℂ :=
  (D : ℂ) * artinBesselProductProfile c ds u

theorem artinBesselFiniteProfile_mellin_convergent (D : ℝ) {c : ℝ} (hc : 0 < c)
    {ds : List ℝ} (hds : ∀ d ∈ ds, 0 < d) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinBesselFiniteProfile D c ds) s :=
  (artinBesselProductProfile_mellin_convergent hc hds hs).const_smul (D : ℂ)

theorem artinBesselFiniteProfile_mellin (D : ℝ) {c : ℝ} (hc : 0 < c)
    {ds : List ℝ} (hds : ∀ d ∈ ds, 0 < d) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinBesselFiniteProfile D c ds) s =
      ((D * artinBesselProductC c ds : ℝ) : ℂ) * (artinBesselProductA c ds : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (ds.length + 1) := by
  change mellin (fun u => (D : ℂ) • artinBesselProductProfile c ds u) s = _
  rw [mellin_const_smul, artinBesselProductProfile_mellin hc hds hs]
  simp only [smul_eq_mul, Complex.ofReal_mul]
  ring

theorem artinBesselFiniteProfile_constants_pos {D c : ℝ} (hD : 0 < D) (hc : 0 < c)
    {ds : List ℝ} (hds : ∀ d ∈ ds, 0 < d) :
    0 < D * artinBesselProductC c ds ∧ 0 < artinBesselProductA c ds := by
  have h := artinBesselProduct_constants_pos hc hds
  exact ⟨mul_pos hD h.1, h.2⟩

end
end SimultaneousPrimitiveRoots
