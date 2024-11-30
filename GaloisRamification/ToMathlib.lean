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

/-- If `H` is a subgroup of `Gal(L/K)`, then `Gal(L / fixedField H)` is isomorphic to `H`. -/
def IntermediateField.subgroup_equiv_aut (H : Subgroup (L ≃ₐ[K] L)) :
    (L ≃ₐ[fixedField H] L) ≃* H where
  toFun ϕ := ⟨ϕ.restrictScalars _, le_of_eq (fixingSubgroup_fixedField H) ϕ.commutes⟩
  invFun ϕ := { toRingEquiv (ϕ : L ≃ₐ[K] L) with
    commutes' := (ge_of_eq (fixingSubgroup_fixedField H)) ϕ.mem }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {E : IntermediateField K L}

/-- If `H` is a normal Subgroup of `Gal(L / K)`, then `fixedField H` is Galois over `K`. -/
instance of_fixedField_normal_subgroup [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [hn : Subgroup.Normal H] : IsGalois K (fixedField H) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply normal_iff_forall_map_le'.mpr
    intro σ x ⟨a, ha, hax⟩ τ
    rw [← hax]
    calc _ = (σ * σ⁻¹ * τ.1 * σ) a := by rw [mul_inv_cancel]; rfl
      _ = _ := by nth_rw 2 [← ha ⟨_ , (Subgroup.Normal.conj_mem hn τ.1 τ.2 σ⁻¹)⟩]; rfl

/-- If `H` is a normal Subgroup of `Gal(L/K)`, then `Gal(fixedField H/K)` is isomorphic to
`Gal(L/K)⧸H`. -/
noncomputable def IsGalois.normal_aut_equiv_quotient [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [Subgroup.Normal H] :
    ((fixedField H) ≃ₐ[K] (fixedField H)) ≃* (L ≃ₐ[K] L) ⧸ H := sorry/- by
  apply MulEquiv.symm <| (quotientMulEquivOfEq ((fixingSubgroup_fixedField H).symm.trans _)).trans
    <| quotientKerEquivOfSurjective (restrictNormalHom (fixedField H)) <|
      restrictNormalHom_surjective L
  ext σ
  apply (((mem_fixingSubgroup_iff (L ≃ₐ[K] L)).trans ⟨fun h ⟨x, hx⟩ ↦ Subtype.val_inj.mp <|
    (restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩).trans (h x hx) , _⟩).trans
      AlgEquiv.ext_iff.symm).trans (MonoidHom.mem_ker (restrictNormalHom (fixedField H))).symm
  intro h x hx
  dsimp
  have hs : ((restrictNormalHom (fixedField H)) σ) ⟨x, hx⟩ = σ x :=
    restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩
  rw [← hs]
  exact Subtype.val_inj.mpr (h ⟨x, hx⟩) -/

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

/-- A variant of the theorem `Polynomial.roots_map_of_injective_of_card_eq_natDegree` that
  replaces the injectivity condition with the condition `Polynomial.map f p ≠ 0`. -/
theorem roots_map_of_map_ne_zero_of_card_eq_natDegree {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0)
    (hroots : card p.roots = p.natDegree) : p.roots.map f  = (p.map f).roots :=
  eq_of_le_of_card_le (map_roots_le h) <|
    by simpa only [card_map, hroots] using (card_roots' (p.map f)).trans (natDegree_map_le f p)

theorem Monic.roots_map_of_card_eq_natDegree {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] {p : A[X]} (hm : p.Monic) {f : A →+* B}
    (hroots : card p.roots = p.natDegree) : p.roots.map f  = (p.map f).roots :=
  roots_map_of_map_ne_zero_of_card_eq_natDegree (map_monic_ne_zero hm) hroots

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
