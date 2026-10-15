/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-! The single-factor monoid homomorphism from the pinned later Mathlib. -/

@[expose] public section

namespace RestrictedProduct

variable {ι : Type*} {S G : ι → Type*} [∀ i, SetLike (S i) (G i)]
  (A : ∀ i, S i) [DecidableEq ι]

/-- Set all entries other than the specified factor to one. -/
def mulSingleMonoidHom [∀ i, Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)]
    (i : ι) : G i →* Πʳ (i : ι), [G i, A i] where
  toFun := mulSingle A i
  map_one' := mulSingle_one A i
  map_mul' := mulSingle_mul A i

@[simp]
theorem mulSingleMonoidHom_apply [∀ i, Monoid (G i)]
    [∀ i, SubmonoidClass (S i) (G i)] (i : ι) (x : G i) :
    mulSingleMonoidHom A i x = mulSingle A i x := rfl

end RestrictedProduct
