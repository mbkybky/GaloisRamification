/-
Copyright (c) 2024 Zixun Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zixun Guo
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
/-!
Some extra lemma to IsFractionRing
-/

namespace IsFractionRing
/--
If K, K' are both fraction rings of R, then K ≃ₐ[R] K'
-/
noncomputable def algEquiv
(R K K': Type*)
[CommRing R] [IsDomain R]
[Field K'] [Field K]
[Algebra R K] [IsFractionRing R K]
[Algebra R K'] [IsFractionRing R K']
: K ≃ₐ[R] K'
:= (FractionRing.algEquiv R K).symm.trans (FractionRing.algEquiv R K')

variable
{R K: Type*} [CommRing R] [IsDomain R]
[Field K] [Algebra R K] [IsFractionRing R K]


theorem lift_unique
{L: Type*} [Field L]
{g: R →+* L} (hg: Function.Injective g)
{f: K →+* L}
(hf1: ∀ x, f (algebraMap R K x) = g x)
: IsFractionRing.lift hg = f := IsLocalization.lift_unique _ hf1

theorem lift_unique'
{L: Type*} [Field L]
{g: R →+* L} (hg: Function.Injective g)
{f1 f2: K →+* L}
(hf1: ∀ x, f1 (algebraMap R K x) = g x)
(hf2: ∀ x, f2 (algebraMap R K x) = g x)
: f1 = f2 := Eq.trans (lift_unique hg hf1).symm (lift_unique hg hf2)

theorem lift_unique_scalar_tower
{L: Type*} [Field L]
[Algebra R L] (hg: Function.Injective (algebraMap R L))
[Algebra K L] [IsScalarTower R K L]
: algebraMap K L = IsFractionRing.lift hg
:= (lift_unique hg (fun x => (IsScalarTower.algebraMap_apply R K L x).symm)).symm


end IsFractionRing
