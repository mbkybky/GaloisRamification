/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

import GaloisRamification.ToMathlib

set_option autoImplicit false

/-!

# Ramification theory in Galois extensions of Dedekind domains

In this file, we discuss the ramification theory in Galois extensions of Dedekind domains, which is
  also called Hilbert's Ramification Theory.

## Main definitions and results

* `isMaximal_conjugates` : The Galois group `Gal(K/L)` acts transitively on the set of all maximal ideals.
* `ramificationIdx_eq_of_isGalois` : In the case of Galois extension,
all the `ramificationIdx` are the same.
* `inertiaDeg_eq_of_isGalois`: In the case of Galois extension, all the `inertiaDeg` are the same.
* `DecompositionGroup` is consisting of all elements of the Galois group `L ≃ₐ[K] L` such
that keep `P` invariant.
* `inertiaDeg_of_DecompositionIdeal_over_bot_eq_oneThe` : The residue class field corresponding to
`DecompositionField p P` is isomorphic toresidue class field corresponding to `p`.
* `InertiaGroup` is the subgorup of `L ≃ₐ[K] L` that consists of all
the `σ : L ≃ₐ[K] L` that are identity modulo `P`.

## References

 * [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

-/


open Algebra Ideal UniqueFactorizationMonoid

open scoped BigOperators

attribute [local instance] FractionRing.liftAlgebra Quotient.field FractionRing.isScalarTower_liftAlgebra

/-! ### lies over -/

section lie_over

namespace Ideal

variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsMaximal] (B : Type*) [CommRing B] [Nontrivial B]
  [Algebra A B] [NoZeroSMulDivisors A B] [Algebra.IsIntegral A B]

theorem exists_ideal_liesOver_maximal_of_isIntegral : ∃ P : Ideal B, P.IsMaximal ∧ P.LiesOver p := by
  rcases exists_ideal_over_maximal_of_isIntegral p <|
    (NoZeroSMulDivisors.ker_algebraMap_eq_bot A B).trans_le bot_le with ⟨P, hm, hP⟩
  exact ⟨P, hm, ⟨hP.symm⟩⟩

/-- For any maximal idela `p` in `A`, there exists a maximal ideal in `B` lying over `p`. -/
noncomputable def over_isMaximal : Ideal B :=
  Classical.choose <| exists_ideal_over_maximal_of_isIntegral p <|
    (NoZeroSMulDivisors.ker_algebraMap_eq_bot A B).trans_le bot_le

instance isMaximal_of_over_isMaximal : (p.over_isMaximal B).IsMaximal :=
  (Classical.choose_spec <| exists_ideal_over_maximal_of_isIntegral p <|
    (NoZeroSMulDivisors.ker_algebraMap_eq_bot A B).trans_le bot_le).1

instance lies_over_of_over_isMaximal : (p.over_isMaximal B).LiesOver p where
  over := (Classical.choose_spec <| exists_ideal_over_maximal_of_isIntegral p <|
    (NoZeroSMulDivisors.ker_algebraMap_eq_bot A B).trans_le bot_le).2.symm

attribute [irreducible] over_isMaximal

variable (A : Type*) [CommRing A] (p : Ideal A) [p.IsMaximal] (B : Type*) [Ring B] [Nontrivial B]
  [Algebra A B] [NoZeroSMulDivisors A B]

@[simp]
theorem under_bot : under A (⊥ : Ideal B) = ⊥ :=
  comap_bot_of_injective (algebraMap A B) (NoZeroSMulDivisors.algebraMap_injective A B)

instance bot_liesOber_bot : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) where
  over := (under_bot A B).symm

theorem ne_bot_of_liesOver_of_ne_bot {A : Type*} [CommRing A] {p : Ideal A} (hp : p ≠ ⊥) {B : Type*}
    [Ring B] [Nontrivial B] [Algebra A B] [NoZeroSMulDivisors A B]
    (P : Ideal B) [P.LiesOver p] : P ≠ ⊥ := by
  contrapose! hp
  apply (over_def P p).trans
  rw [hp]
  exact under_bot A B

end Ideal



variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B] (p : Ideal A) (P : Ideal B) [ho : P.LiesOver p]

open scoped Classical in
/-- The `Finset` consists of all primes lying over `p : Ideal A`. -/
noncomputable abbrev primes_over (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B] :
    Finset (Ideal B) :=
  (UniqueFactorizationMonoid.factors (map (algebraMap A B) p)).toFinset

/- /-- The image of a maximal ideal under the algebraMap between ring of integers is non-zero. -/
theorem Ideal.map_isMaximal_ne_bot (hp0 : p ≠ ⊥) : map (algebraMap A B) p ≠ ⊥ := sorry -/

theorem prime_iff_isMaximal {p : Ideal A} (hp0 : p ≠ ⊥) : Prime p ↔ p.IsMaximal :=
  ⟨fun hp ↦ (isPrime_of_prime hp).isMaximal hp.ne_zero,
    fun hp ↦ prime_of_isPrime hp0 hp.isPrime⟩

end lie_over

section primesOver

variable {A : Type*} [CommSemiring A] (p : Ideal A) (B : Type*) [Semiring B] [Algebra A B]

def primesOver : Set (Ideal B) :=
  { P : Ideal B | P.IsPrime ∧ P.LiesOver p }

instance primesOver.isPrime (Q : primesOver p B) : Q.1.IsPrime :=
  Q.2.1

instance primesOver.liesOver (Q : primesOver p B) : Q.1.LiesOver p :=
  Q.2.2

def primesOver.mk (P : Ideal B) [hPp : P.IsPrime] [hp : P.LiesOver p] : primesOver p B :=
  ⟨P, ⟨hPp, hp⟩⟩

instance primesOver.isMaximal {A : Type*} [CommRing A] {p : Ideal A} [p.IsMaximal] {B : Type*}
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (Q : primesOver p B) : IsMaximal Q.1 :=
  IsMaximal.of_liesOver_isMaximal Q.1 p

end primesOver

section primesOverFinset

open scoped Classical in
noncomputable def primesOverFinset {A : Type*} [CommRing A] (p : Ideal A) (B : Type*) [CommRing B]
    [IsDedekindDomain B] [Algebra A B]: Finset (Ideal B) :=
  (factors (p.map (algebraMap A B))).toFinset

theorem coe_primesOverFinset {A : Type*} [CommRing A] {p : Ideal A} (hpb : p ≠ ⊥) [hpm : p.IsMaximal]
    (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B] [NoZeroSMulDivisors A B]: primesOverFinset p B = primesOver p B := by
  classical
  ext P
  constructor
  · intro hp
    have h : P ≠ ⊥ := Factors.ne_bot p ⟨P, hp⟩
    have hp : P ∈ factors (map (algebraMap A B) p) := Multiset.mem_toFinset.mp hp
    have hPp : P.IsPrime := isPrime_of_prime (prime_of_factor P hp)
    exact ⟨hPp, ⟨hpm.eq_of_le (comap_ne_top _ hPp.ne_top)
      (le_comap_of_map_le (le_of_dvd (dvd_of_mem_factors hp)))⟩⟩
  · intro ⟨hPp, hp⟩
    rw [primesOverFinset, Finset.mem_coe, Multiset.mem_toFinset]
    have hd := dvd_iff_le.mpr (map_le_of_le_comap (le_of_eq hp.over))
    have hir : Irreducible P := irreducible_iff_prime.mpr <|
      prime_of_isPrime (ne_bot_of_liesOver_of_ne_bot hpb P) hPp
    have : map (algebraMap A B) p ≠ ⊥ :=
      (map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective A B)).mp.mt hpb
    rcases exists_mem_factors_of_dvd this hir hd with ⟨_, hq, he⟩
    rw [associated_iff_eq.mp he]
    exact hq

end primesOverFinset

namespace Ideal

open scoped Classical in
/-- In the case of Galois extension, it can be seen from the Theorem `ramificationIdx_eq_of_IsGalois`
  that all `ramificationIdx` are the same, which we define as the `Ideal.ramificationIdxIn`. -/
noncomputable def ramificationIdxIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then
    Ideal.ramificationIdx (algebraMap A B) p h.choose else 0

open scoped Classical in
/-- In the case of Galois extension, it can be seen from the Theorem `inertiaDeg_eq_of_IsGalois`
  that all `inertiaDeg` are the same, which we define as the `Ideal.inertiaDegIn`. -/
noncomputable def inertiaDegIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : ℕ :=
  if h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p then
    Ideal.inertiaDeg (algebraMap A B) p h.choose else 0

section RamificationInertia

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [NoZeroSMulDivisors A B]
  (p : Ideal A) (P Q : Ideal B) [p.IsMaximal] [hPp : P.IsPrime] [hp : P.LiesOver p]
  [hQp : Q.IsPrime] [Q.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

include p in
theorem exists_map_eq_of_isGalois [IsGalois K L] : ∃ σ : B ≃ₐ[A] B, map σ P = Q := by
  haveI := IsGalois.fractionRing_of_isGalois_isFractionRing A B K L
  haveI : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P p
  haveI hQm : Q.IsMaximal := IsMaximal.of_liesOver_isMaximal Q p
  by_contra hs
  push_neg at hs
  rcases Submodule.mem_sup.mp <| (eq_top_iff_one (Q ⊔ ∏ σ : B ≃ₐ[A] B, map σ P)).mp <|
    sup_prod_eq_top fun σ _ ↦ hQm.coprime_of_ne inferInstance (hs σ).symm
      with ⟨x, hx, y, hy, hxy⟩
  let n : B := ∏ σ : B ≃ₐ[A] B, σ x
  have hnx : n = (algebraMap A B) (intNorm A B x) := (algebraMap_intNorm_of_isGalois A B).symm
  have hnk : intNorm A B x ∈ P.under A := by
    rw [← P.over_def p, Q.over_def p, mem_comap, ← hnx]
    refine (span_singleton_le_iff_mem Q).mp ?_
    rw [← prod_span_singleton]
    exact hQm.isPrime.prod_le.mpr ⟨1, Finset.mem_univ 1, (span_singleton_le_iff_mem Q).mpr hx⟩
  rcases IsPrime.prod_mem_iff.mp (Eq.mpr (hnx ▸ Eq.refl (n ∈ P)) hnk : n ∈ P) with ⟨σ, _, hs⟩
  have hxp : x ∈ map σ.symm P := by
    rw [← AlgEquiv.symm_apply_apply σ x]
    exact mem_map_of_mem σ.symm hs
  have h := (map σ.symm P).add_mem hxp <|
    (prod_le_inf.trans (Finset.inf_le (Finset.mem_univ σ.symm))) hy
  rw [hxy] at h
  exact IsMaximal.ne_top inferInstance ((eq_top_iff_one _).mpr h)

/-- In the case of Galois extension, all the `ramificationIdx` over a fixed ideal are the same. -/
theorem ramificationIdx_eq_of_isGalois [IsGalois K L] :
    ramificationIdx (algebraMap A B) p P = ramificationIdx (algebraMap A B) p Q := by
  rcases exists_map_eq_of_isGalois p P Q K L with ⟨σ, hs⟩
  rw [← hs]
  exact (ramificationIdx_map_eq p P σ).symm

/-- In the case of Galois extension, all the `inertiaDeg` are the same. -/
theorem inertiaDeg_eq_of_isGalois [IsGalois K L] :
    inertiaDeg (algebraMap A B) p P = inertiaDeg (algebraMap A B) p Q := by
  rcases exists_map_eq_of_isGalois p P Q K L with ⟨σ, hs⟩
  rw [← hs]
  exact (inertiaDeg_map_eq p P σ).symm

/-- In the case of Galois extension, the `ramificationIdxIn` is equal to any ramification index. -/
theorem ramificationIdxIn_eq_ramificationIdx [IsGalois K L] :
    ramificationIdxIn p B = ramificationIdx (algebraMap A B) p P := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [ramificationIdxIn, dif_pos h]
  exact ramificationIdx_eq_of_isGalois p h.choose P K L

/-- In the case of Galois extension, the `inertiaDegIn` is equal to any inertia degree. -/
theorem inertiaDegIn_eq_inertiaDeg [IsGalois K L] :
    inertiaDegIn p B = inertiaDeg (algebraMap A B) p P := by
  have h : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn, dif_pos h]
  exact inertiaDeg_eq_of_isGalois p h.choose P K L

end RamificationInertia

section fundamental_identity

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [NoZeroSMulDivisors A B]
  {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal] (P : Ideal B) [P.IsPrime] [hp : P.LiesOver p]
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

include hpb in
/-- The form of the **fundamental identity** in the case of Galois extension. -/
theorem ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn [IsGalois K L] :
    (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Module.finrank K L := by
  rw [← smul_eq_mul, ← coe_primesOverFinset hpb B, Set.ncard_coe_Finset, ← Finset.sum_const]
  rw [← sum_ramification_inertia B p K L hpb]
  apply Finset.sum_congr rfl
  intro P hp
  rw [← Finset.mem_coe, coe_primesOverFinset hpb B] at hp
  obtain ⟨_, _⟩ := hp
  rw [ramificationIdxIn_eq_ramificationIdx p P K L, inertiaDegIn_eq_inertiaDeg p P K L]

end fundamental_identity

section MulAction

open MulAction
/-
/-- The `MulAction` of the Galois group `L ≃ₐ[K] L` on the set `primesOver p L`,
given by `σ ↦ (P ↦ σ P)`. -/
instance Gal_MulAction_primes (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    MulAction (L ≃ₐ[K] L) (primesOver p L) where
  smul σ Q := primesOver.mk p (map (mapRingHom σ) Q.1)
  one_smul Q := by
    show primesOver.mk p (map (mapRingHom (1 : L ≃ₐ[K] L)) Q.1) = Q
    simp only [← Subtype.val_inj, mapRingHom_one, map_id]
  mul_smul σ τ Q := by
    show primesOver.mk p (map (mapRingHom (σ * τ)) Q.1) =
        primesOver.mk p (map (mapRingHom σ) (primesOver.mk p (map (mapRingHom τ) Q.1)).1)
    simp only [← Subtype.val_inj, map_map]
    rfl

theorem Gal_MulAction_primes_mk_coe (σ : L ≃ₐ[K] L) :
  (σ • primesOver.mk p P).1 = map (mapRingHom σ) P := rfl

instance [IsDedekindDomain R] [IsGalois K L] (p : Ideal R) :
    MulAction.IsPretransitive (L ≃ₐ[K] L) (primesOver S p) :=
 -/
end MulAction

end Ideal

section

namespace Ideal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- `MonoidHom` version of `Ideal.quotientAlgEquiv`. -/
def quotientAlgEquivHom (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (h : ∀ σ : B ≃ₐ[A] B, P = map σ P) : (B ≃ₐ[A] B) →* ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) where
  toFun σ := Quotient.algEquivOfEqMap p σ (h σ)
  map_one' := by ext ⟨⟩; rfl
  map_mul' _ _ := by ext ⟨⟩; rfl

open Polynomial IntermediateField

section

variable {A B : Type*} [CommRing A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B]
  [Module.Finite A B] (p : Ideal A) (P : Ideal B) [p.IsMaximal] [P.IsMaximal] [P.LiesOver p]
  (h : ∀ σ : B ≃ₐ[A] B, P = map σ P)
  (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [Algebra K L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [hn : Normal K L]

include K L
theorem quotientAlgEquivHom_surjective :
    Function.Surjective (quotientAlgEquivHom p P h) := by
  haveI := (IsFractionRing.injective A K).isDomain
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let F := A ⧸ p
  let E := B ⧸ P
  have e : PowerBasis F (separableClosure F E) := Field.powerBasisOfFiniteOfSeparable F _
  intro σ
  let β := (e.liftEquiv (S' := E)).toFun (σ.toAlgHom.restrictDomain (separableClosure F E))
  rcases Quotient.exists_rep e.gen.1 with ⟨a, ha⟩
  let f : A[X] := minpoly A a
  let fl : B[X] := f.map (algebraMap A B)
  let ϕp : A →+* F := Ideal.Quotient.mk p
  let ϕP : B →+* E := Ideal.Quotient.mk P
  have hq : ⟦a⟧ = ϕP a := rfl
  rw [hq] at ha
  have hai : IsIntegral A a := IsIntegral.isIntegral a
  have hm : f.Monic := minpoly.monic hai
  have h0 : (fl.map ϕP) ≠ 0 := map_monic_ne_zero (Monic.map (algebraMap A B) hm)
  have hbr : β.1 ∈ (fl.map ϕP).roots := by
    apply (mem_roots_iff_aeval_eq_zero h0).mpr
    have hc : fl.map ϕP = (f.map ϕp).map (algebraMap F E) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      rfl
    have hbz : (aeval β.1) (Polynomial.map ϕp f) = 0 := by
      refine aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd F e.gen ?_) β.2
      refine Subtype.val_inj.mp <| (Subalgebra.aeval_coe _ e.gen (f.map ϕp)).symm.trans ?_
      rw [← ha, ← map_aeval_eq_aeval_map, minpoly.aeval, map_zero, ZeroMemClass.coe_zero]
      rfl
    simp only [Equiv.toFun_as_coe, AlgEquiv.toAlgHom_eq_coe, PowerBasis.liftEquiv_apply_coe,
      AlgHom.coe_coe, hc, aeval_map_algebraMap, ← hbz]
  have hfe : (Polynomial.map (algebraMap A K) f) = minpoly K (algebraMap B L a) := by
    refine minpoly.eq_of_irreducible_of_monic
      ((Monic.irreducible_iff_irreducible_map_fraction_map (minpoly.monic hai)).mp
        (minpoly.irreducible hai)) ?_ (Monic.map (algebraMap A K) (minpoly.monic hai))
    simp only [aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, minpoly.aeval, f]
  have h : fl.roots.map ϕP = (fl.map ϕP).roots := by
    have h := (natDegree_eq_card_roots' (hn.splits (algebraMap B L a))).symm
    rw [← hfe, natDegree_map, Monic.natDegree_map (minpoly.monic hai), Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq A K L,
      ← isIntegralClosure_root_card_eq_ofMonic B L (minpoly.monic hai),
      ← Monic.natDegree_map (minpoly.monic hai) (algebraMap A B)] at h
    exact roots_map_of_card_eq_natDegree h0 h
  rw [← h] at hbr
  rcases Multiset.mem_map.mp hbr with ⟨b, ⟨hbr, hb⟩⟩
  have h : aeval (algebraMap B L b) (minpoly K (AdjoinSimple.gen K (algebraMap B L a))) = 0 := by
    have he : minpoly K (AdjoinSimple.gen K (algebraMap B L a)) = minpoly K (algebraMap B L a) :=
      minpoly_eq (AdjoinSimple.gen K ((algebraMap B L) a))
    rw [he, ← hfe, aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, aeval_def, ← eval_map,
      ← coe_aeval_eq_eval, (mem_roots_iff_aeval_eq_zero (map_monic_ne_zero hm)).mp hbr]
  let ε := IntermediateField.adjoin.powerBasis (hn.isIntegral (algebraMap B L a))
  let τ : L ≃ₐ[K] L := (ε.lift (algebraMap B L b) h).fieldRangeAlgEquiv.liftNormal L
  use galRestrict A K L B τ
  refine AlgEquiv.coe_algHom_injective <| separableClosure.restrictDomain_injective F E <|
    e.liftEquiv.injective <| Subtype.val_inj.mp ?_
  simp only [e.liftEquiv_apply_coe, AlgHom.restrictDomain_apply, IntermediateField.algebraMap_apply]
  nth_rw 1 [← ha]
  show ϕP ((galRestrict A K L B τ) a) = β.1
  rw [← hb]
  exact congrArg ϕP <| NoZeroSMulDivisors.algebraMap_injective B L <|
    (algebraMap_galRestrict_apply A τ a).trans <|
      ((ε.lift (algebraMap B L b) h).fieldRangeAlgEquiv.liftNormal_commutes L
        (AdjoinSimple.gen K (algebraMap B L a))).trans (ε.lift_gen (algebraMap B L b) h)

end

end Ideal

end

-- 之后都用 isMaximal_conjugates 取出 σ : B ≃ₐ[A] B, 不必取 σ : L ≃ₐ[K] L


/-
variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] (K L : Type*) [Field K] [Field L] [IsDedekindDomain A]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra K L]
  [FiniteDimensional K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L] (p : Ideal A) (hp0 : p ≠ ⊥) (P : Ideal B) [hpm : P.IsMaximal]
  [hp : P lies_over p] (Q : Ideal B) [hqm : Q.IsMaximal] [hq : Q lies_over p] [IsGalois K L] (σ : L ≃ₐ[K] L)

include p hp0 in
/-- The Galois group `Gal(K/L)` acts transitively on the set of all maximal ideals `P` of `𝓞 L`
lying above `p`, i.e., these prime ideals are all conjugates of each other. -/
theorem isMaximal_conjugates' : ∃ σ : L ≃ₐ[K] L, map (galRestrict A K L B σ) P = Q := by
  by_contra hs
  push_neg at hs
  let s : Finset (L ≃ₐ[K] L) := Finset.univ
  sorry/- have : ∃ y ∈ Q, ∃ z ∈ ∏ σ ∈ s, map (galRestrict A K L B σ) P, y + z = 1 := by
    apply Submodule.mem_sup.mp
    apply (eq_top_iff_one (Q ⊔ ∏ σ in s, map (galRestrict A K L B σ) P)).mp
    apply sup_prod_eq_top
    intro σ _
    apply IsMaximal.coprime_of_ne hqm
  rcases Submodule.mem_sup.mp <| (eq_top_iff_one (Q ⊔ ∏ σ in s, map (galRestrict A K L B σ) P)).mp <|
    sup_prod_eq_top <| fun σ _ ↦ IsMaximal.coprime_of_ne hqm (GalRingHom_map.isMaximal P σ)
      (hs σ).symm with ⟨x, hx, y, hy, hxy⟩
  let n : 𝓞 L := ∏ σ in s, (galRestrict A K L B σ) x
  have hnx : n = (algebraMap A B) (RingOfIntegers.norm K x) :=
    Subtype.val_inj.mp <| Eq.trans
      (Submonoid.coe_finset_prod (integralClosure ℤ L).toSubmonoid (fun i ↦ (GalRingHom i) x) s)
        (Algebra.norm_eq_prod_automorphisms K x.1).symm
  have hnk : RingOfIntegers.norm K x ∈ idealUnder K P := by
    rw [idealUnder, ← hp.over, hq.over]
    apply mem_comap.mpr
    rw [← hnx]
    refine (span_singleton_le_iff_mem Q).mp ?_
    rw [← prod_span_singleton]
    exact prod_le_inf.trans <| (@Finset.inf_le _ _ _ _ s (fun σ ↦ span {(galRestrict A K L B σ) x}) _
      (@Finset.mem_univ (L ≃ₐ[K] L) _ 1)).trans (Iff.mpr (span_singleton_le_iff_mem Q) hx)
  have hnp : n ∈ P := Eq.mpr (_root_.id (hnx ▸ Eq.refl (n ∈ P))) hnk
  rcases IsPrime.prod_mem hnp with ⟨⟨σ, _⟩, hs⟩
  have hxp : x ∈ map (GalRingHom σ⁻¹) P := Eq.mpr
    ((GalRingHom_inv_mul_cancel_mem σ x).symm ▸ Eq.refl _) (mem_map_of_mem (GalRingHom σ⁻¹) hs)
  have h := Ideal.add_mem (map (GalRingHom σ⁻¹) P) hxp <|
    (prod_le_inf.trans (Finset.inf_le (Finset.mem_univ σ⁻¹))) hy
  rw [hxy] at h
  exact IsMaximal.ne_top (GalRingHom_map.isMaximal P σ⁻¹) ((eq_top_iff_one _).mpr h) -/

include K L p hp0 in
theorem isMaximal_conjugates : ∃ σ : B ≃ₐ[A] B, map σ P = Q := by
  rcases isMaximal_conjugates' K L p hp0 P Q with ⟨σ, hs⟩
  exact ⟨galRestrict A K L B σ, hs⟩
 -/

/-
section

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
  [Module.Finite A B] [NoZeroSMulDivisors A B] [hn : Normal (FractionRing A) (FractionRing B)]
  (p : Ideal A) (P : Ideal B) [p.IsMaximal] [P.IsMaximal] [P.LiesOver p]
  (h : ∀ σ : B ≃ₐ[A] B, map σ P = P) [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]

theorem quotientAlgEquivHom_surjective' :
    Function.Surjective (quotientAlgEquivHom p P h) := by
  let K := FractionRing A
  let L := FractionRing B
  let F := A ⧸ p
  let E := B ⧸ P
  have e : PowerBasis F E := Field.powerBasisOfFiniteOfSeparable F E
  intro σ
  let β := (PowerBasis.liftEquiv e).toFun σ.toAlgHom
  rcases Quotient.exists_rep e.gen with ⟨a, ha⟩
  let f : A[X] := minpoly A a
  let fl : B[X] := f.map (algebraMap A B)
  let ϕp : A →+* F := Ideal.Quotient.mk p
  let ϕP : B →+* E := Ideal.Quotient.mk P
  have hq : ⟦a⟧ = ϕP a := rfl
  rw [hq] at ha
  have hai : IsIntegral A a := IsIntegral.isIntegral a
  have hm : f.Monic := minpoly.monic hai
  have h0 : (fl.map ϕP) ≠ 0 := map_monic_ne_zero (Monic.map (algebraMap A B) hm)
  have hbr : β.1 ∈ (fl.map ϕP).roots := by
    have h : aeval e.gen (f.map ϕp) = ϕP (aeval a f) := by
      rw [← ha]
      exact (@map_aeval_eq_aeval_map _ _ _ F E _ _ _ _ _ ϕp ϕP rfl f a).symm
    rw [minpoly.aeval, map_zero] at h
    apply (mem_roots_iff_aeval_eq_zero h0).mpr
    have hc : fl.map ϕP = (f.map ϕp).map (algebraMap F E) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      rfl
    have hbz := aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd F e.gen h) β.2
    simp only [Equiv.toFun_as_coe, AlgEquiv.toAlgHom_eq_coe, PowerBasis.liftEquiv_apply_coe,
      AlgHom.coe_coe, hc, aeval_map_algebraMap, ← hbz]
  have hfe : (Polynomial.map (algebraMap A K) f) = minpoly K (algebraMap B L a) := by
    refine minpoly.eq_of_irreducible_of_monic
      ((Monic.irreducible_iff_irreducible_map_fraction_map (minpoly.monic hai)).mp
        (minpoly.irreducible hai)) ?_ (Monic.map (algebraMap A K) (minpoly.monic hai))
    simp only [aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, minpoly.aeval, f]
  have h : fl.roots.map ϕP = (fl.map ϕP).roots := by
    have h := (natDegree_eq_card_roots' (hn.splits (algebraMap B L a))).symm
    rw [← hfe, natDegree_map, Monic.natDegree_map (minpoly.monic hai), Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq A K L,
      ← isIntegralClosure_root_card_eq_ofMonic B L (minpoly.monic hai),
      ← Monic.natDegree_map (minpoly.monic hai) (algebraMap A B)] at h
    exact roots_map_of_card_eq_natDegree h0 h
  rw [← h] at hbr
  rcases Multiset.mem_map.mp hbr with ⟨b, ⟨hbr, hb⟩⟩
  have h : aeval (algebraMap B L b) (minpoly K (AdjoinSimple.gen K (algebraMap B L a))) = 0 := by
    have he : minpoly K (AdjoinSimple.gen K (algebraMap B L a)) = minpoly K (algebraMap B L a) :=
      minpoly_eq (AdjoinSimple.gen K ((algebraMap B L) a))
    rw [he, ← hfe, aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, aeval_def, ← eval_map,
      ← coe_aeval_eq_eval, (mem_roots_iff_aeval_eq_zero (map_monic_ne_zero hm)).mp hbr]
  let ε := IntermediateField.adjoin.powerBasis (hn.isIntegral (algebraMap B L a))
  let τ : L ≃ₐ[K] L := (ε.lift (algebraMap B L b) h).fieldRangeAlgEquiv.liftNormal L
  use galRestrict A K L B τ
  refine AlgEquiv.coe_algHom_injective (e.liftEquiv.injective ?_)
  apply Subtype.val_inj.mp
  rw [e.liftEquiv_apply_coe, AlgHom.coe_coe]
  simp only [← ha, Equiv.toFun_as_coe, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
  show ϕP ((galRestrict A K L B τ) a) = β.1
  rw [← hb]
  exact congrArg ϕP <| NoZeroSMulDivisors.algebraMap_injective B L <|
    (algebraMap_galRestrict_apply A τ a).trans <|
      ((ε.lift (algebraMap B L b) h).fieldRangeAlgEquiv.liftNormal_commutes L
        (AdjoinSimple.gen K (algebraMap B L a))).trans (ε.lift_gen (algebraMap B L b) h)

end
 -/
