module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Meromorphic.Order

/-!
# Zero-freeness through a factorization into meromorphic factors

Let `f` be entire and suppose that on `Re s > 1`

`f s = (s - 1) * (E s * ∏ i ∈ X, Λ i s)`,

where `E` is analytic and nonvanishing on `Re s > 0` and every `Λ i` is meromorphic on the
half-plane `Re s > 1 - δ` with meromorphic order `≤ 0` at each of its points (no zeros; poles are
allowed). Then `f` has no zeros in `Re s > 1 - δ` other than possibly `s = 1`
(`ne_zero_of_meromorphic_factorization`).

This is the analytic step of the ascent of [A], Lemma `spl:field-bounds`: with
`f = (s - 1) ζ_L(s)` for an abelian extension `L` of a cyclotomic field `F ⊇ μ₁₂`, `E` the finite
Euler correction and `Λ i` the continued Hecke `L`-functions of the characters of `Gal(L/F)`, it
turns a zero-free region for Hecke `L`-functions stated with meromorphic orders into the
nonvanishing of the entire function `(s - 1) ζ_L(s)`. The statement mentions only Mathlib notions,
so it can be applied to any formalization of the Hecke zero-free region.

The proof is the identity principle for meromorphic functions on the (convex, hence preconnected)
half-plane, and additivity of the meromorphic order.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional

open Filter Topology

/-- An analytic function whose meromorphic order at a point is `≤ 0` does not vanish there. -/
theorem ne_zero_of_meromorphicOrderAt_nonpos {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x)
    (h : meromorphicOrderAt f x ≤ 0) : f x ≠ 0 := by
  intro hx
  have h0 : analyticOrderAt f x ≠ 0 := fun h0 =>
    (analyticOrderAt_eq_zero.mp h0).elim (fun hna => hna hf) (fun hne => hne hx)
  rw [hf.meromorphicOrderAt_eq] at h
  cases hn : analyticOrderAt f x with
  | top => simp [hn] at h
  | coe n =>
    rw [hn, ENat.map_natCast] at h
    have hn0 : n = 0 := by
      have : (n : ℤ) ≤ 0 := by exact_mod_cast h
      omega
    exact h0 (by rw [hn, hn0]; rfl)

/-- **Zero-freeness through a meromorphic factorization.** If the entire function `f` equals
`(s - 1) * (E s * ∏ i ∈ X, Λ i s)` on `Re s > 1`, with `E` analytic and nonvanishing on
`Re s > 0` and each `Λ i` meromorphic of order `≤ 0` on `Re s > 1 - δ`, then `f s ≠ 0` for
`Re s > 1 - δ`, `s ≠ 1`. -/
theorem ne_zero_of_meromorphic_factorization {ι : Type*} (X : Finset ι) {f E : ℂ → ℂ}
    {Λ : ι → ℂ → ℂ} {δ : ℝ} (hδ : δ ≤ 1) (hf : Differentiable ℂ f)
    (hE : ∀ s : ℂ, 0 < s.re → AnalyticAt ℂ E s) (hEne : ∀ s : ℂ, 0 < s.re → E s ≠ 0)
    (hΛ : ∀ i ∈ X, MeromorphicOn (Λ i) {s : ℂ | 1 - δ < s.re})
    (hord : ∀ i ∈ X, ∀ s : ℂ, 1 - δ < s.re → meromorphicOrderAt (Λ i) s ≤ 0)
    (hfac : ∀ s : ℂ, 1 < s.re → f s = (s - 1) * (E s * ∏ i ∈ X, Λ i s)) :
    ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 → f s ≠ 0 := by
  intro s hs hs1
  set H : Set ℂ := {s : ℂ | 1 - δ < s.re} with hH
  have hpre : IsPreconnected H := (convex_halfSpace_re_gt (1 - δ)).isPreconnected
  have hHpos : ∀ z ∈ H, 0 < z.re := fun z hz => by
    have hz' : 1 - δ < z.re := hz
    linarith
  -- a base point in `H ∩ {Re > 1}`
  set z₀ : ℂ := ((2 + |δ| : ℝ) : ℂ) with hz₀def
  have hz₀re : z₀.re = 2 + |δ| := Complex.ofReal_re _
  have hz₀1 : 1 < z₀.re := by
    rw [hz₀re]
    linarith [abs_nonneg δ]
  have hz₀ : z₀ ∈ H := by
    change 1 - δ < z₀.re
    rw [hz₀re]
    linarith [neg_abs_le δ]
  -- the two sides as meromorphic functions on `H`
  have hprod : MeromorphicOn (fun z => ∏ i ∈ X, Λ i z) H :=
    MeromorphicOn.fun_prod fun i hi => hΛ i hi
  have hEan : ∀ z ∈ H, AnalyticAt ℂ E z := fun z hz => hE z (hHpos z hz)
  have hlin : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => w - 1) z := fun z =>
    analyticAt_id.sub analyticAt_const
  let P : ℂ → ℂ := fun z => (z - 1) * E z
  have hPan : ∀ z ∈ H, AnalyticAt ℂ P z := fun z hz => (hlin z).mul (hEan z hz)
  let G : ℂ → ℂ := P * fun z => ∏ i ∈ X, Λ i z
  have hGmer : MeromorphicOn G H := fun z hz => (hPan z hz).meromorphicAt.mul (hprod z hz)
  have hfmer : MeromorphicOn f H := fun z _ => (hf.analyticAt z).meromorphicAt
  have hDmer : MeromorphicOn (fun z => f z - G z) H := fun z hz => (hfmer z hz).sub (hGmer z hz)
  -- they agree near `z₀`, hence everywhere on `H` as meromorphic germs
  have hDtop : meromorphicOrderAt (fun z => f z - G z) z₀ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hnear : (fun z => f z - G z) =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀1] with z hz
      change f z - (z - 1) * E z * ∏ i ∈ X, Λ i z = 0
      rw [hfac z hz]
      ring
    exact hnear.filter_mono nhdsWithin_le_nhds
  have hDs : meromorphicOrderAt (fun z => f z - G z) s = ⊤ := by
    by_contra hne
    exact (hDmer.meromorphicOrderAt_ne_top_of_isPreconnected hpre hs hz₀ hne) hDtop
  have hloc : f =ᶠ[𝓝[≠] s] G := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp hDs] with z hz
    exact sub_eq_zero.mp hz
  -- the order of `G` at `s`
  have hPne : P s ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hs1) (hEne s (hHpos s hs))
  have hGord : meromorphicOrderAt G s = ∑ i ∈ X, meromorphicOrderAt (Λ i) s := by
    change meromorphicOrderAt (P * fun z => ∏ i ∈ X, Λ i z) s = _
    rw [meromorphicOrderAt_mul_of_ne_zero (hPan s hs) hPne,
      meromorphicOrderAt_fun_prod fun i hi => hΛ i hi s hs]
  have hle : meromorphicOrderAt f s ≤ 0 := by
    rw [meromorphicOrderAt_congr hloc, hGord]
    exact Finset.sum_nonpos fun i hi => hord i hi s hs
  exact ne_zero_of_meromorphicOrderAt_nonpos (hf.analyticAt s) hle

end SimultaneousPrimitiveRoots.Unconditional
