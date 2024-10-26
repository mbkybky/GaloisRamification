/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.FieldTheory.Galois.Basic

attribute [local instance] FractionRing.liftAlgebra

variable (A K L B : Type*)
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

theorem IsGalois.of_isGalois_fractionRing [IsGalois (FractionRing A) (FractionRing B)] :
    IsGalois K L := sorry

theorem IsGalois.of_isGalois_isFractionRing [IsGalois K L] :
    IsGalois (FractionRing A) (FractionRing B) := sorry
