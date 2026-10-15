module

public import SimultaneousPrimitiveRoots.CyclotomicRadicals

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Polynomial
open scoped IntermediateField

/-- The radical polynomial over the q-th cyclotomic field. -/
noncomputable def primeRadicalPolynomial (a q : ℕ) : (CyclotomicField q ℚ)[X] :=
  X ^ q - C (a : CyclotomicField q ℚ)

/-- A canonical model of Q(mu_q, a^(1/q)). -/
abbrev PrimeKummerField (a q : ℕ) := AdjoinRoot (primeRadicalPolynomial a q)

instance primeRadicalPolynomial_irreducible (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    Fact (Irreducible (primeRadicalPolynomial a q)) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  exact ⟨cyclotomic_prime_radical_irreducible ha.out hq.out haq.out⟩

theorem primeKummerField_root_pow (a q : ℕ) :
    (AdjoinRoot.root (primeRadicalPolynomial a q)) ^ q =
      (a : PrimeKummerField a q) := by
  change (AdjoinRoot.root ((X : (CyclotomicField q ℚ)[X]) ^ q - C (a : CyclotomicField q ℚ))) ^ q =
    (a : AdjoinRoot ((X : (CyclotomicField q ℚ)[X]) ^ q - C (a : CyclotomicField q ℚ)))
  rw [root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq]
  exact map_natCast _ _

theorem primeKummerField_root_generates (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    (CyclotomicField q ℚ)⟮AdjoinRoot.root (primeRadicalPolynomial a q)⟯ = ⊤ :=
  IntermediateField.adjoin_root_eq_top _

theorem primeKummerField_relative_degree {a q : ℕ}
    (ha : 2 ≤ a) (hq : q.Prime) (haq : a < q) :
    Module.finrank (CyclotomicField q ℚ) (PrimeKummerField a q) = q := by
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  exact cyclotomic_radical_relative_degree ha hq haq
    (primeKummerField_root_generates a q) (primeKummerField_root_pow a q)

theorem primeKummerField_absolute_degree {a q : ℕ}
    (ha : 2 ≤ a) (hq : q.Prime) (haq : a < q) :
    Module.finrank ℚ (PrimeKummerField a q) = q * (q - 1) := by
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  exact cyclotomic_radical_absolute_degree ha hq haq
    (primeKummerField_root_generates a q) (primeKummerField_root_pow a q)

end SimultaneousPrimitiveRoots
