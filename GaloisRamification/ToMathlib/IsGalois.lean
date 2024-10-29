/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Zixun Guo
-/
import Mathlib.FieldTheory.Galois.Basic
import GaloisRamification.ToMathlib.IsFractionRing
import GaloisRamification.ToMathlib.TransAlgStruct

attribute [local instance] FractionRing.liftAlgebra

/-
  The aim is to prove a commutative diagram:
  ----------------
  |               |
  \/             \/
  L  <--- B ---> L'
  /\      /\     /\
  |       |      |
  |       |      |
  K  <--- A ---> K'
  /\             /\
  |               |
  -----------------
  in which K <-> K' and L <-> L' come from canonical isomorphisms between two fraction rings of A and B, respectively. The only path to prove is :
  K -> L -> L' = K -> K' -> L'
  which induced by the fact that they are both lifting functions of A -> L'
-/
#check Equiv.algEquiv
section
variable (A B K L K' L' : Type*)
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
  [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]
  [Field K'] [Field L']
  [Algebra A K'] [IsFractionRing A K']
  [Algebra B L'] [IsFractionRing B L']
  [Algebra K' L'] [Algebra A L']
  [IsScalarTower A B L'] [IsScalarTower A K' L']

private noncomputable def KK': HasRingEquiv K K' := { ringEquiv := IsFractionRing.algEquiv A K K' }
private noncomputable def LL': HasRingEquiv L L' := { ringEquiv := IsFractionRing.algEquiv B L L' }

private noncomputable def alg_KL' : Algebra K L' := Algebra.algOfAlgOnEquivRing K' L' (e := KK' A K K')

/- following directly from definition, there is a scalar tower K -> K' -> L'
-/
private def scalar_tower_K_K'_L':
  let _ := alg_KL' A K K' L'
  let _ := KK' A K K'
  let _ := Algebra.algOfRingEquiv K K'
  IsScalarTower K K' L' :=
    let _ := alg_KL' A K K' L'
    let _ := KK' A K K'
    let _ := Algebra.algOfRingEquiv K K'
    Algebra.ofAlgOnEquivRing_scalar_tower _ _


private def scalar_tower_K_L_L':
  let _ := alg_KL' A K K' L'
  let _ := LL' B L L'
  let _ := Algebra.algOfRingEquiv L L'
  IsScalarTower K L L' := by
    letI _ := alg_KL' A K K' L'
    letI _ := LL' B L L'
    letI _ := KK' A K K'
    letI _ := Algebra.algOfRingEquiv L L'
    letI _ := Algebra.algOfRingEquiv K K'
    letI _KK'L' := scalar_tower_K_K'_L' A K K' L'
    simp at _KK'L'
    simp only at *
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [<-Function.comp_apply (x := x) (g := algebraMap K L) (f := algebraMap L L')]
    apply congrFun
    rw [<-RingHom.coe_comp, DFunLike.coe_fn_eq]
    apply IsFractionRing.lift_unique' (R := A) (g := algebraMap A L')
    · rw [IsScalarTower.algebraMap_eq A B L', RingHom.coe_comp]
      apply Function.Injective.comp
      · exact NoZeroSMulDivisors.algebraMap_injective B L'
      · exact NoZeroSMulDivisors.algebraMap_injective A B
    · intro x
      rw [@IsScalarTower.algebraMap_eq K K' L' _ _ _ _ _ _ _KK'L']
      simp only [RingHom.coe_comp, Function.comp_apply, Algebra.algOfAlgOnEquivRing_algebraMap_def,
        smul_eq_mul, mul_one]
      rw [show (HasRingEquiv.ringEquiv: K -> K') = IsFractionRing.algEquiv A K K' from rfl]
      rw [AlgEquiv.commutes]
      exact Eq.symm (IsScalarTower.algebraMap_apply A K' L' x)
    · intro x
      rw [IsScalarTower.algebraMap_eq A B L']
      have : algebraMap B L' = (algebraMap L L').comp (algebraMap B L) := by
        rw [Algebra.algOfRingEquiv_algebraMap_def']
        rw [show (HasRingEquiv.ringEquiv: L ≃+* L') = IsFractionRing.algEquiv B L L' from rfl]
        simp only [AlgEquiv.toRingEquiv_toRingHom]
        ext r
        simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes]
      rw [this]
      simp only [Algebra.algOfRingEquiv_algebraMap_def', RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
      rw [<-IsScalarTower.algebraMap_apply A K L]
      rw [<-IsScalarTower.algebraMap_apply A B L]

end


/- Galois extension is transfered between two pairs of fraction rings
-/
theorem IsGalois.of_isGalois_isfractionRing
  (A B K L K' L' : Type*)
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
  [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]
  [Field K'] [Field L']
  [Algebra A K'] [IsFractionRing A K']
  [Algebra B L'] [IsFractionRing B L']
  [Algebra K' L'] [Algebra A L']
  [IsScalarTower A B L'] [IsScalarTower A K' L']
  [IsGalois K L] :
    IsGalois K' L' := by
      letI _ := alg_KL' A K K' L'
      letI _ := LL' B L L'
      letI _ := KK' A K K'
      letI _ := Algebra.algOfRingEquiv L L'
      letI _ := Algebra.algOfRingEquiv K K'
      letI _KK'L' := scalar_tower_K_K'_L' A K K' L'
      letI _KLL' := scalar_tower_K_L_L' A B  K L K' L'
      haveI : IsGalois K L' := by
        apply IsGalois.of_algEquiv (E := L)
        apply AlgEquiv.ofRingEquiv (f := IsFractionRing.algEquiv B L L')
        rw [@IsScalarTower.algebraMap_eq K L L' _ _ _ _ _ _ _KLL']
        simp only [AlgEquiv.coe_ringEquiv, Algebra.algOfRingEquiv_algebraMap_def', RingHom.coe_comp,
          RingHom.coe_coe, Function.comp_apply]
        intro x
        apply congrFun
        rfl
      exact @IsGalois.tower_top_of_isGalois K K' L' _ _ _ _ _ _ _KK'L' _


theorem IsGalois.isFractionRing_of_isGalois_FractionRing
(A B K L : Type*)
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
  [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]
  [IsGalois (FractionRing A) (FractionRing B)]
  : IsGalois K L := IsGalois.of_isGalois_isfractionRing A B (FractionRing A) (FractionRing B) K L


theorem IsGalois.FractionRing_of_isGalois_isFractionRing
(A B K L : Type*)
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
  [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]
  [IsGalois K L]
  : IsGalois (FractionRing A) (FractionRing B) := IsGalois.of_isGalois_isfractionRing A B K L (FractionRing A) (FractionRing B)
