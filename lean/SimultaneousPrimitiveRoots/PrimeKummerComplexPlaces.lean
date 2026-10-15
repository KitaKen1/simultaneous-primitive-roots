module

public import SimultaneousPrimitiveRoots.NumberFieldComplexCutoffBessel
public import SimultaneousPrimitiveRoots.PrimeKummerSplitting
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField NumberField.InfinitePlace
noncomputable section

variable (a q : ℕ) [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]

/-- The existing Kummer field has no real places, so the complex product includes all infinity. -/
instance primeKummerField_isTotallyComplex : IsTotallyComplex (PrimeKummerField a q) := by
  letI : NeZero q := ⟨hq.out.ne_zero⟩
  letI : IsTotallyComplex (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := q) (CyclotomicField q ℚ)
      (by have := ha.out; have := haq.out; omega)
  exact NumberField.isTotallyComplex_of_algebra (CyclotomicField q ℚ) (PrimeKummerField a q)

theorem primeKummerField_nrRealPlaces : nrRealPlaces (PrimeKummerField a q) = 0 :=
  IsTotallyComplex.nrRealPlaces_eq_zero _

theorem primeKummerField_all_places_complex (v : InfinitePlace (PrimeKummerField a q)) :
    v.IsComplex := IsTotallyComplex.isComplex v

theorem primeKummerField_complex_places_pos : 0 < nrComplexPlaces (PrimeKummerField a q) :=
  artinNumberFieldComplexPlaces_pos _

theorem primeKummerField_twice_complex_places :
    2 * nrComplexPlaces (PrimeKummerField a q) = q * (q - 1) := by
  rw [← IsTotallyComplex.finrank, primeKummerField_absolute_degree ha.out hq.out haq.out]

theorem primeKummerField_complex_places_count :
    nrComplexPlaces (PrimeKummerField a q) = q * (q - 1) / 2 := by
  rw [← primeKummerField_twice_complex_places a q]
  omega

theorem primeKummerField_actual_norm_kernel_haar_exists :
    ∃ μ : MeasureTheory.Measure (artinNumberFieldFiniteComplexNormKernel (PrimeKummerField a q)),
      μ.IsHaarMeasure := artinNumberFieldFiniteComplexNormKernelHaar_exists _

end
end SimultaneousPrimitiveRoots
