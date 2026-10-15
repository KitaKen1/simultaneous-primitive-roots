/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Completion embeddings and idele definitions expressed using the v4.33.1 adele rings. -/

@[expose] public section
noncomputable section

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

@[simps!]
def ofAdicCompletion (v : HeightOneSpectrum R) :
    v.adicCompletion K →* FiniteAdeleRing R K :=
  letI := Classical.decEq (HeightOneSpectrum R)
  { toFun := RestrictedProduct.mulSingle (fun w ↦ w.adicCompletionIntegers K) v
    map_one' := RestrictedProduct.mulSingle_one _ v
    map_mul' := RestrictedProduct.mulSingle_mul _ v }

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField

open IsDedekindDomain

variable {K : Type*} [Field K]

@[simps!]
def InfiniteAdeleRing.ofCompletion (v : InfinitePlace K) : v.Completion →* InfiniteAdeleRing K :=
  letI := Classical.decEq (InfinitePlace K)
  MonoidHom.mulSingle InfinitePlace.Completion v

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

namespace AdeleRing

@[simps!]
def ofCompletion (v : InfinitePlace K) : v.Completion →* AdeleRing R K :=
  .prod (InfiniteAdeleRing.ofCompletion v) 1

@[simps!]
def ofAdicCompletion (v : HeightOneSpectrum R) : v.adicCompletion K →* AdeleRing R K :=
  .prod 1 (FiniteAdeleRing.ofAdicCompletion K v)

end AdeleRing

abbrev IdeleGroup := (AdeleRing R K)ˣ

namespace IdeleGroup

@[simps!]
def unitEmbedding : Kˣ →* IdeleGroup R K :=
  Units.map (algebraMap K (AdeleRing R K)).toMonoidHom

@[simps!]
def ofCompletion (v : InfinitePlace K) : v.Completionˣ →* IdeleGroup R K :=
  Units.map (AdeleRing.ofCompletion R K v)

@[simps!]
def ofAdicCompletion (v : HeightOneSpectrum R) : (v.adicCompletion K)ˣ →* IdeleGroup R K :=
  Units.map (AdeleRing.ofAdicCompletion R K v)

abbrev principalSubgroup : Subgroup (IdeleGroup R K) := (unitEmbedding R K).range

end IdeleGroup

abbrev IdeleClassGroup := IdeleGroup R K ⧸ IdeleGroup.principalSubgroup R K

namespace IdeleClassGroup

@[simps!]
def ofCompletion (v : InfinitePlace K) : v.Completionˣ →* IdeleClassGroup R K :=
  (QuotientGroup.mk' (IdeleGroup.principalSubgroup R K)).comp (IdeleGroup.ofCompletion R K v)

@[simps!]
def ofAdicCompletion (v : HeightOneSpectrum R) : (v.adicCompletion K)ˣ →* IdeleClassGroup R K :=
  (QuotientGroup.mk' (IdeleGroup.principalSubgroup R K)).comp (IdeleGroup.ofAdicCompletion R K v)

end IdeleClassGroup

end NumberField
