/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

import GaloisRamification.ToMathlib.Finite
import GaloisRamification.ToMathlib.FractionRing
import GaloisRamification.ToMathlib.IsGalois
import GaloisRamification.ToMathlib.Normal
import GaloisRamification.ToMathlib.restrictScalarsHom
import GaloisRamification.ToMathlib.separableClosure

set_option autoImplicit false

open Algebra

open scoped BigOperators

/-! ### Preliminary -/

section Galois

open IntermediateField AlgEquiv QuotientGroup

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L]
 [FiniteDimensional K L]

-- have better defEq comparing with `FixedPoints.toAlgAutMulEquiv`
/-- If `H` is a subgroup of `Gal(L/K)`, then `Gal(L / fixedField H)` is isomorphic to `H`. -/
def IntermediateField.subgroup_equiv_aut (H : Subgroup (L ≃ₐ[K] L)) :
    (L ≃ₐ[fixedField H] L) ≃* H where
  toFun ϕ := ⟨ϕ.restrictScalars K, le_of_eq (fixingSubgroup_fixedField H) ϕ.commutes⟩
  invFun ϕ := { toRingEquiv (ϕ : L ≃ₐ[K] L) with
    commutes' := (ge_of_eq (fixingSubgroup_fixedField H)) ϕ.mem }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

end Galois



namespace Polynomial

variable {R : Type*} (S L : Type*) [CommRing R] [CommRing S] [IsDomain S] [CommRing L] [IsDomain L]
[Algebra R L] [Algebra S L] [Algebra R S] [IsScalarTower R S L] [IsIntegralClosure S R L]


open Multiset

/-- If `L` be an extension of `R`, then for a monic polynomial `p : R[X]`, the roots of `p`in `L`
are equal to the roots of `p` in the integral closure of `R` in `L`. -/
theorem Monic.roots_map_eq_of_isIntegralClosure {p : R[X]} (hp : p.Monic):
    (p.map (algebraMap R S)).roots.map (algebraMap S L) = (p.map (algebraMap R L)).roots := by
  classical
  ext x
  by_cases hx : ∃ y : S, algebraMap S L y = x
  · rcases hx with ⟨y, h⟩
    have hi : Function.Injective (algebraMap S L) := IsIntegralClosure.algebraMap_injective S R L
    rw [← h, count_map_eq_count' _ _ hi _, count_roots, count_roots,
      IsScalarTower.algebraMap_eq R S L, ← map_map, ← eq_rootMultiplicity_map hi]
  · have h : count x ((p.map (algebraMap R S)).roots.map (algebraMap S L)) = 0 := by
      simp only [mem_map, mem_roots', ne_eq, IsRoot.def, Subtype.exists, not_exists,
        not_and, and_imp, count_eq_zero]
      intro y _ _ h
      exact hx ⟨y, h⟩
    rw [h]
    exact Decidable.byContradiction fun h ↦ hx <| IsIntegralClosure.isIntegral_iff.mp
      ⟨p, hp, (eval₂_eq_eval_map (algebraMap R L)).trans <|
        (mem_roots (hp.map (algebraMap R L)).ne_zero).1 (count_ne_zero.mp (Ne.symm h))⟩

/-- If `L` be an extension of `R`, then for a monic polynomial `p : R[X]`, the number of roots
of `p` in `L` is equal to the number of roots of `p` in the integral closure of `R` in `L`. -/
theorem Monic.roots_card_eq_of_isIntegralClosure {p : R[X]} (hp : p.Monic) :
    card (p.map (algebraMap R S)).roots = card (p.map (algebraMap R L)).roots := by
  rw [← roots_map_eq_of_isIntegralClosure S L hp, card_map]

end Polynomial

section AKLB

variable (A B C : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [CommRing C] [IsDomain C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [NoZeroSMulDivisors A C]

include C in
theorem noZeroSMulDivisors_tower_bot : NoZeroSMulDivisors A B := by
  sorry

variable (A B K L : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

include K L in
theorem noZeroSMulDivisors_of_isFractionRing_algebra : NoZeroSMulDivisors A B := by
  have := NoZeroSMulDivisors.trans A K L
  exact NoZeroSMulDivisors.of_field_isFractionRing A B K L

end AKLB
