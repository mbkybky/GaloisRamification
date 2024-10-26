/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia

import GaloisRamification.ToMathlib

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 25000

/-!

# Hilbert's Ramification Theory

In this file, we discuss the ramification theory in Galois extensions of number fields.

## Main definitions and results

* `isMaximal_conjugates` : The Galois group `Gal(K/L)` acts transitively on the set of all maximal ideals.
* `ramificationIdx_eq_of_isGalois` : In the case of Galois extension,
all the `ramificationIdx` are the same.
* `inertiaDeg_eq_of_isGalois`: In the case of Galois extension, all the `inertiaDeg` are the same.
* `decompositionGroup` is consisting of all elements of the Galois group `L ≃ₐ[K] L` such
that keep `P` invariant.
* `inertiaDeg_of_decompositionideal_over_bot_eq_oneThe` : The residue class field corresponding to
`decompositionField p P` is isomorphic toresidue class field corresponding to `p`.
* `inertiaGroup` is the subgorup of `L ≃ₐ[K] L` that consists of all
the `σ : L ≃ₐ[K] L` that are identity modulo `P`.

## References

 * [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

-/

open Algebra Ideal

open scoped BigOperators

attribute [local instance] Ideal.Quotient.field

/-! ### Preliminary -/

namespace NumberField

open RingOfIntegers

section preparation

variable (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]
  (P : Ideal (𝓞 L)) (p : Ideal (𝓞 K))

/-- The ideal obtained by intersecting `𝓞 K` and `P`. -/
abbrev idealUnder : Ideal (𝓞 K) := comap (algebraMap (𝓞 K) (𝓞 L)) P

theorem idealUnder_def : idealUnder K P = comap (algebraMap (𝓞 K) (𝓞 L)) P := rfl

instance idealUnder.IsPrime [P.IsPrime] : IsPrime (idealUnder K P) :=
  IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (P : Ideal (𝓞 L)) (p : Ideal (𝓞 K))

/-- We say `P` lies over `p` if `p` is the preimage of `P` under the `algebraMap`. -/
-- We introduce this class to address the type class inference problem for `(B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P) `.
class ideal_lies_over : Prop where over : p = comap (algebraMap (𝓞 K) (𝓞 L)) P

@[inherit_doc] infix : 50 "lies_over" => ideal_lies_over

instance over_idealUnder : P lies_over (idealUnder K P) where over := rfl

class ideal_unique_lies_over extends ideal_lies_over P p : Prop where
  unique : ∀ Q : Ideal (𝓞 L), [Q.IsMaximal] → [Q lies_over p] → Q = P

infix : 50 "unique_lies_over" => ideal_unique_lies_over

variable [NumberField L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
[P lies_over p]

/-- If `P` is a maximal ideal of `𝓞 L`, then the intersection of `P` and `𝓞 K` is also
a maximal ideal. -/
instance idealUnder.IsMaximal : IsMaximal (idealUnder K P) :=
  isMaximal_comap_of_isIntegral_of_isMaximal P

/-- In particular, if `p` is a maximal ideal of `ringOfIntegers`, then
the intersection of `p` and `ℤ` is also a maximal ideal. -/
instance ideal_comap_int.IsMaximal [NumberField K] (p : Ideal (𝓞 K)) [p.IsMaximal] :
  IsMaximal (comap (algebraMap ℤ (𝓞 K)) p) := isMaximal_comap_of_isIntegral_of_isMaximal p

/-- For any maximal idela `p` in `𝓞 K`, there exists a maximal ideal in `𝓞 L` lying over `p`. -/
theorem exists_ideal_over_maximal_of_ringOfIntegers (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    ∃ (P : Ideal (𝓞 L)), IsMaximal P ∧ P lies_over p := by
  rcases exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) p
    (by simp only [ker_algebraMap_eq_bot K L, bot_le]) with ⟨P, hpm, hp⟩
  exact ⟨P, hpm, ideal_lies_over.mk hp.symm⟩

/-- Maximal Ideals in the ring of integers are non-zero. -/
theorem ne_bot_ofIsMaximal [NumberField K] : p ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField K)

/-- The image of a maximal ideal under the algebraMap between ring of integers is non-zero. -/
theorem map_isMaximal_ne_bot [NumberField K] (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [Algebra K L] : map (algebraMap (𝓞 K) (𝓞 L)) p ≠ ⊥ :=
  fun h ↦ (ne_bot_ofIsMaximal p) ((map_eq_bot_iff_of_injective (algebraMap.injective K L)).mp h)

theorem prime_iff_isMaximal (P : Ideal (𝓞 L)) : Prime P ↔ IsMaximal P :=
  ⟨fun hp ↦ IsPrime.isMaximal (isPrime_of_prime hp) (Prime.ne_zero hp),
    fun hp ↦ prime_of_isPrime (ne_bot_ofIsMaximal P) (IsMaximal.isPrime hp)⟩

open Classical in
/-- The `Finset` consists of all primes lying over `p : Ideal (𝓞 K)`. -/
noncomputable abbrev primes_over {K : Type*} [Field K] (p : Ideal (𝓞 K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L] : Finset (Ideal (𝓞 L)) :=
  (UniqueFactorizationMonoid.factors (map (algebraMap (𝓞 K) (𝓞 L)) p)).toFinset

open UniqueFactorizationMonoid

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
[Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal]

theorem primes_over_mem :
    P ∈ primes_over p L ↔ P.IsMaximal ∧ P lies_over p := by
  constructor
  · intro hp
    classical have hp := Multiset.mem_toFinset.mp hp
    have hpm := (prime_iff_isMaximal P).mp (prime_of_factor P hp)
    exact ⟨hpm, ideal_lies_over.mk <| IsMaximal.eq_of_le inferInstance (comap_ne_top _ (IsMaximal.ne_top hpm))
      (le_comap_of_map_le (le_of_dvd (dvd_of_mem_factors hp)))⟩
  · intro ⟨hpm, hp⟩
    have hd := dvd_iff_le.mpr (map_le_of_le_comap (le_of_eq hp.over))
    have hir := irreducible_iff_prime.mpr ((prime_iff_isMaximal P).mpr hpm)
    rcases exists_mem_factors_of_dvd (map_isMaximal_ne_bot p L) hir hd with ⟨_, hq, he⟩
    classical rw [Multiset.mem_toFinset, associated_iff_eq.mp he]
    exact hq

instance primes_over_instIsMaximal (Q : primes_over p L) : IsMaximal Q.1 :=
  ((primes_over_mem p Q.1).mp Q.2).1

instance primes_over_inst_lies_over (Q : primes_over p L) : Q.1 lies_over p :=
  ((primes_over_mem p Q.1).mp Q.2).2

/-- Given a maximal ideal `P lies_over p` in `𝓞 L`, `primes_over.mk` sends `P` to an element of
the subset `primes_over p L` of `Ideal (𝓞 L)`.  -/
abbrev primes_over.mk [P.IsMaximal] [P lies_over p] : primes_over p L :=
  ⟨P, (primes_over_mem p P).mpr ⟨inferInstance, inferInstance⟩⟩

theorem primes_over_card_ne_zero (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    Finset.card (primes_over p L) ≠ 0 := by
  rcases exists_ideal_over_maximal_of_ringOfIntegers p L with ⟨P, hp⟩
  exact Finset.card_ne_zero_of_mem ((primes_over_mem p P).mpr hp)

/-- Another form of the property `unique_lies_over`. -/
theorem unique_primes_over_card_eq_one (P : Ideal (𝓞 L)) [hp : P unique_lies_over p] :
    Finset.card (primes_over p L) = 1 := by
  apply Nat.le_antisymm _ (Nat.one_le_iff_ne_zero.mpr (primes_over_card_ne_zero p L))
  simp only [Finset.card_le_one, primes_over_mem, and_imp]
  intro a _ _ b _ _
  rw [hp.unique a, hp.unique b]



variable {K L : Type*} [Field K] [Field L] [Algebra K L] {E : Type*} [Field E]
  [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  (p : Ideal (𝓞 K)) (𝔓 : Ideal (𝓞 E)) (P : Ideal (𝓞 L))

theorem ideal_lies_over.trans [hp : 𝔓 lies_over p] [hP : P lies_over 𝔓] : P lies_over p where
  over := by rw [hp.over, hP.over, comap_comap, ← IsScalarTower.algebraMap_eq]

theorem ideal_lies_over_tower_bot [hp : P lies_over p] [hP : P lies_over 𝔓] : 𝔓 lies_over p where
  over := by rw [hp.over, hP.over, comap_comap, ← IsScalarTower.algebraMap_eq]

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] {E : Type*} [Field E]
  [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  (p : Ideal (𝓞 K)) (𝔓 : Ideal (𝓞 E)) (P : Ideal (𝓞 L))

omit [NumberField L] in
theorem ideal_unique_lies_over.trans [hp : 𝔓 unique_lies_over p] [hP : P unique_lies_over 𝔓] :
  P unique_lies_over p := { ideal_lies_over.trans p 𝔓 P with
    unique := fun Q _ _ ↦
      letI := ideal_lies_over_tower_bot p (idealUnder E Q) Q
      letI := ideal_lies_over.mk (hp.unique (idealUnder E Q)).symm
      hP.unique Q
}

theorem ideal_unique_lies_over_tower_bot [hp : P unique_lies_over p] [hP : P lies_over 𝔓] :
  𝔓 unique_lies_over p := { ideal_lies_over_tower_bot p 𝔓 P with
    unique := by
      intro 𝔔 _ _
      rcases exists_ideal_over_maximal_of_ringOfIntegers 𝔔 L with ⟨Q, ⟨hqm ,hq⟩⟩
      letI := ideal_lies_over.trans p 𝔔 Q
      letI := hp.unique Q
      rw [hq.over, hp.unique Q, hP.over]
}

theorem ideal_unique_lies_over_tower_top [𝔓.IsMaximal] [hP : P unique_lies_over p]
  [𝔓 lies_over p] : P unique_lies_over 𝔓 where
    over := by
      rcases exists_ideal_over_maximal_of_ringOfIntegers 𝔓 L with ⟨Q, ⟨_ ,hq⟩⟩
      letI := ideal_lies_over.trans p 𝔓 Q
      rw [← hP.unique Q, hq.over]
    unique := fun Q _ _ ↦
      letI := ideal_lies_over.trans p 𝔓 Q
      hP.unique Q

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
(p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [P lies_over p] (E : IntermediateField K L)

instance IntermediateField_ideal_lies_over : (idealUnder E P) lies_over p :=
  ideal_lies_over_tower_bot p (idealUnder E P) P

theorem ideal_comap_intermediateField : p = idealUnder K (idealUnder E P) :=
  (IntermediateField_ideal_lies_over p P E).over

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
  [P unique_lies_over p] (E : IntermediateField K L)

instance IntermediateField_ideal_unique_lies_over  : (idealUnder E P) unique_lies_over p :=
  ideal_unique_lies_over_tower_bot p (idealUnder E P) P

end preparation



section decomposition

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L))
[p.IsMaximal] [hpm : P.IsMaximal] [hp : P lies_over p]

instance : P.LiesOver p where over := hp.over

theorem inertiaDeg_pos {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
    [P lies_over p] : inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P > 0 := by
  rw [inertiaDeg_algebraMap]
  exact Module.finrank_pos


/-! ### Galois group `Gal(K/L)` acts transitively on the set of all maximal ideals -/

open NumberField.RingOfIntegers

theorem mapAlgEquiv_toAlgHom_toRingHom_eq_mapRingHom (σ : L ≃ₐ[K] L) :
  (mapAlgEquiv σ).toAlgHom.toRingHom = mapRingHom σ := rfl

theorem mapRingHom_one : mapRingHom (1 : L ≃ₐ[K] L) = RingHom.id (𝓞 L) := rfl

theorem mapRingHom_symm_comp_mapRingHom (σ : L ≃ₐ[K] L) : (mapRingHom σ.symm).comp (mapRingHom σ)
  = RingHom.id (𝓞 L) :=
  RingEquiv.symm_toRingHom_comp_toRingHom (mapRingEquiv σ)

theorem mapRingHom_symm_apply_apply (σ : L ≃ₐ[K] L) (x : 𝓞 L) :
    mapRingHom σ.symm (mapRingHom σ x) = x :=
  RingEquiv.symm_apply_apply (mapRingEquiv σ) x

theorem mapRingHom_comp_mapRingHom_symm (σ : L ≃ₐ[K] L) :
    (mapRingHom σ).comp (mapRingHom σ.symm) = RingHom.id (𝓞 L) :=
  RingEquiv.toRingHom_comp_symm_toRingHom (mapRingEquiv σ)

theorem mapRingHom_apply_symm_apply (σ : L ≃ₐ[K] L) (x : 𝓞 L) :
    mapRingHom σ (mapRingHom σ.symm x) = x :=
  RingEquiv.apply_symm_apply (mapRingEquiv σ) x

theorem mapRingEquiv_symm_apply_apply (σ : L ≃ₐ[K] L) (x : 𝓞 L) :
    mapRingEquiv σ.symm (mapRingEquiv σ x) = x :=
  RingEquiv.symm_apply_apply (mapRingEquiv σ) x

theorem mapRingEquiv_apply_symm_apply (σ : L ≃ₐ[K] L) (x : 𝓞 L) :
    mapRingEquiv σ (mapRingEquiv σ.symm x) = x :=
  RingEquiv.apply_symm_apply (mapRingEquiv σ) x

/-- The `mapRingHom σ` will send a maximal ideal to a maximal ideal. -/
instance mapRingHom_map.isMaximal (σ : L ≃ₐ[K] L) : (map (mapRingHom σ) P).IsMaximal :=
  Quotient.maximal_of_isField _ <| MulEquiv.isField _ (Field.toIsField ((𝓞 L) ⧸ P))
    (quotientEquiv P (map (mapRingHom σ) P) (mapAlgEquiv σ) rfl).symm.toMulEquiv

-- Propsition 9.1

/-- The Galois group `Gal(K/L)` acts transitively on the set of all maximal ideals `P` of `𝓞 L`
lying above `p`, i.e., these prime ideals are all conjugates of each other. -/
theorem isMaximal_conjugates {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [hpm : P.IsMaximal] [hp : P lies_over p]
    (Q : Ideal (𝓞 L)) [hqm : Q.IsMaximal] [hq : Q lies_over p]
    [IsGalois K L] : ∃ σ : L ≃ₐ[K] L, map (mapRingHom σ) P = Q := by
  by_contra hs
  push_neg at hs
  let s : Finset (L ≃ₐ[K] L) := Finset.univ
  rcases Submodule.mem_sup.mp <| (eq_top_iff_one (Q ⊔ ∏ σ in s, map (mapRingHom σ) P)).mp <|
    sup_prod_eq_top <| fun σ _ ↦ IsMaximal.coprime_of_ne hqm (mapRingHom_map.isMaximal P σ)
      (hs σ).symm with ⟨x, hx, y, hy, hxy⟩
  let n : 𝓞 L := ∏ σ in s, (mapRingHom σ) x
  have hnx : n = (algebraMap (𝓞 K) (𝓞 L)) (RingOfIntegers.norm K x) :=
    Subtype.val_inj.mp <| Eq.trans
      (Submonoid.coe_finset_prod (integralClosure ℤ L).toSubmonoid (fun i ↦ (mapRingHom i) x) s)
        (Algebra.norm_eq_prod_automorphisms K x.1).symm
  have hnk : RingOfIntegers.norm K x ∈ idealUnder K P := by
    rw [idealUnder, ← hp.over, hq.over]
    apply mem_comap.mpr
    rw [← hnx]
    refine (span_singleton_le_iff_mem Q).mp ?_
    rw [← prod_span_singleton]
    exact prod_le_inf.trans <| (@Finset.inf_le _ _ _ _ s (fun σ ↦ span {(mapRingHom σ) x}) _
      (@Finset.mem_univ (L ≃ₐ[K] L) _ 1)).trans (Iff.mpr (span_singleton_le_iff_mem Q) hx)
  have hnp : n ∈ P := Eq.mpr (_root_.id (hnx ▸ Eq.refl (n ∈ P))) hnk
  rcases IsPrime.prod_mem_iff.mp hnp with ⟨σ, _, hs⟩
  have hxp : x ∈ map (mapRingHom σ.symm) P := by
    rw [← mapRingEquiv_symm_apply_apply σ x]
    exact mem_map_of_mem (mapRingHom σ.symm) hs
  have h := Ideal.add_mem (map (mapRingHom σ.symm) P) hxp <|
    (prod_le_inf.trans (Finset.inf_le (Finset.mem_univ σ.symm))) hy
  rw [hxy] at h
  exact IsMaximal.ne_top (mapRingHom_map.isMaximal P σ.symm) ((eq_top_iff_one _).mpr h)

theorem IsMaximal_conjugates' {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {P : Ideal (𝓞 L)} [P.IsMaximal] {Q : Ideal (𝓞 L)} [Q.IsMaximal]
    [IsGalois K L] (h : idealUnder K P = idealUnder K Q) :
    ∃ σ : L ≃ₐ[K] L, map (mapRingHom σ) P = Q :=
  letI := ideal_lies_over.mk h
  isMaximal_conjugates (idealUnder K P) P Q



open UniqueFactorizationMonoid IsDedekindDomain

/-- The function normalizedFactors commutes with the function `map (mapRingHom σ)`. -/
theorem normalizedFactors_map_mapRingHom_commutes {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] {I : Ideal (𝓞 L)} (hI : I ≠ ⊥) (σ : L ≃ₐ[K] L) :
    normalizedFactors (map (mapRingHom σ) I) =
    Multiset.map (map (mapRingHom σ)) (normalizedFactors I) := by
  nth_rw 1 [← prod_normalizedFactors_eq_self hI]
  have h := Multiset.prod_hom (normalizedFactors I) (mapHom (mapRingHom σ))
  simp only [mapHom_apply] at h
  rw [← h, normalizedFactors_prod_of_prime]
  intro q hq
  rcases Multiset.mem_map.mp hq with ⟨p, hp, hpq⟩
  have : IsMaximal p := (prime_iff_isMaximal p).mp (prime_of_normalized_factor p hp)
  rw [← hpq]
  exact (prime_iff_isMaximal (map (mapRingHom σ) p)).mpr (mapRingHom_map.isMaximal p σ)

/-- The image of an ideal under the algebraMap between ring of integers remains invariant
under the action of `mapRingHom σ`. -/
theorem ideal_map_invariant_under_mapRingHom (p : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (map (mapRingHom σ)) (map (algebraMap (𝓞 K) (𝓞 L)) p) = map (algebraMap (𝓞 K) (𝓞 L)) p := by
  apply le_antisymm <| map_le_of_le_comap <| map_le_of_le_comap <|
    fun _ h ↦ by simp only [← mapAlgEquiv_toAlgHom_toRingHom_eq_mapRingHom,
      AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, mem_comap, RingHom.coe_coe,
        AlgHom.commutes, mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) h]
  apply map_le_of_le_comap
  intro x h
  rw [mem_comap, map_map]
  apply Set.mem_of_eq_of_mem _ (mem_map_of_mem ((mapRingHom σ).comp (algebraMap (𝓞 K) (𝓞 L))) h)
  rw [mapRingHom, ← AlgEquiv.commutes (mapAlgEquiv σ) x]
  rfl

/-- The map induced by `mapRingHom σ` on the ideals of `𝓞 L` is injective. -/
theorem mapRingHom_IdealMap.injective (σ : L ≃ₐ[K] L): Function.Injective (map (mapRingHom σ)) :=
  fun I J h ↦ by rw [← map_id I, ← mapRingHom_symm_comp_mapRingHom σ, ← map_map, h, map_map,
    mapRingHom_symm_comp_mapRingHom σ, map_id]

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
[Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [hp : P lies_over p]

/-- In the case of Galois extension, all the `ramificationIdx` are the same. -/
theorem ramificationIdx_eq_of_isGalois (Q : Ideal (𝓞 L)) [hqm : Q.IsMaximal] [Q lies_over p]
    [IsGalois K L] : ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P =
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p Q := by
  classical
  rcases isMaximal_conjugates p P Q with ⟨σ, hs⟩
  rw [ramificationIdx_eq_normalizedFactors_count (map_isMaximal_ne_bot p L) inferInstance
    (ne_bot_ofIsMaximal P), ramificationIdx_eq_normalizedFactors_count (map_isMaximal_ne_bot p L)
    (IsMaximal.isPrime hqm) (ne_bot_ofIsMaximal Q), ← hs]
  nth_rw 2 [← ideal_map_invariant_under_mapRingHom p σ]
  rw [normalizedFactors_map_mapRingHom_commutes (map_isMaximal_ne_bot p L) σ]
  rw [Multiset.count_map_eq_count' _ _ (mapRingHom_IdealMap.injective σ) _]

theorem ramificationIdx_eq_of_isGalois' [IsGalois K L] {P : Ideal (𝓞 L)} [P.IsMaximal]
    {Q : Ideal (𝓞 L)} [hqm : Q.IsMaximal] (h : idealUnder K P = idealUnder K Q) :
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) (idealUnder K P) P =
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) (idealUnder K Q) Q := by
  letI := ideal_lies_over.mk h
  rw [← h]
  exact ramificationIdx_eq_of_isGalois (idealUnder K P) P Q

theorem idealUnder_invariant_under_mapRingHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [hp : P lies_over p] (σ : L ≃ₐ[K] L) :
    p = idealUnder K (map (mapRingHom σ) P) := by
  ext x
  rw [mem_comap, hp.over, mem_comap]
  refine ⟨fun h ↦ Set.mem_of_eq_of_mem (by nth_rw 1 [← (mapAlgEquiv σ).commutes x]; rfl)
    (mem_map_of_mem (mapRingHom σ) h), fun h ↦ ?_⟩
  have h := mem_map_of_mem (mapRingHom σ.symm) h
  rw [map_map, mapRingHom_symm_comp_mapRingHom, map_id] at h
  exact Set.mem_of_eq_of_mem (by nth_rw 1 [← (mapAlgEquiv σ.symm).commutes x]; rfl) h

instance mapRingHom_map_lies_over (σ : L ≃ₐ[K] L) : (map (mapRingHom σ) P) lies_over p :=
  ⟨idealUnder_invariant_under_mapRingHom p P σ⟩

/-- The algebra equiv `((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ map (mapRingHom σ) P)`
induced by an algebra equiv `σ : L ≃ₐ[K] L`. -/
def residueField_mapAlgEquiv {P : Ideal (𝓞 L)} [P.IsMaximal] [P lies_over p] {Q : Ideal (𝓞 L)}
    [Q.IsMaximal] [Q lies_over p] {σ : L ≃ₐ[K] L} (hs: map (mapRingHom σ) P = Q) :
    ((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ Q) := {
  quotientEquiv P Q (mapAlgEquiv σ) (by rw [← hs]; rfl) with
  commutes' := by
    rintro ⟨x⟩
    exact congrArg (Ideal.Quotient.mk Q) (AlgEquiv.commutes (mapAlgEquiv σ) x)
}

/-- In the case of Galois extension, all the `inertiaDeg` are the same. -/
theorem inertiaDeg_eq_of_isGalois (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Q lies_over p] [IsGalois K L] :
    inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P = inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p Q := by
  rcases isMaximal_conjugates p P Q with ⟨σ, hs⟩
  rw [inertiaDeg_algebraMap, inertiaDeg_algebraMap]
  exact LinearEquiv.finrank_eq (residueField_mapAlgEquiv p hs).toLinearEquiv

/-- In the case of Galois extension, it can be seen from the Theorem `ramificationIdx_eq_of_IsGalois`
that all `ramificationIdx` are the same, which we define as the `ramificationIdx_of_isGalois`. -/
@[irreducible]
noncomputable def ramificationIdx_of_isGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] : ℕ :=
  ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p <|
    Classical.choose (exists_ideal_over_maximal_of_ringOfIntegers p L)

/-- In the case of Galois extension, it can be seen from the Theorem `inertiaDeg_eq_of_IsGalois`
that all `inertiaDeg` are the same, which we define as the `inertiaDeg_of_isGalois`. -/
@[irreducible]
noncomputable def inertiaDeg_of_isGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] : ℕ :=
  inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p <|
    Classical.choose (exists_ideal_over_maximal_of_ringOfIntegers p L)

/-- In the case of Galois extension, all ramification indices are equal to the
`ramificationIdx_of_isGalois`. This completes the property mentioned in our previous definition. -/
theorem ramificationIdx_eq_ramificationIdx_of_isGalois [IsGalois K L] :
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P = ramificationIdx_of_isGalois p L := by
  rcases Classical.choose_spec (exists_ideal_over_maximal_of_ringOfIntegers p L) with ⟨_, _⟩
  rw [ramificationIdx_of_isGalois]
  exact ramificationIdx_eq_of_isGalois p P _

/-- In the case of Galois extension, all inertia degrees are equal to the `inertiaDeg_of_isGalois`.
This completes the property mentioned in our previous definition. -/
theorem inertiaDeg_eq_inertiaDeg_of_isGalois [IsGalois K L] :
    inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P = inertiaDeg_of_isGalois p L := by
  rcases Classical.choose_spec (exists_ideal_over_maximal_of_ringOfIntegers p L) with ⟨_, _⟩
  rw [inertiaDeg_of_isGalois]
  exact inertiaDeg_eq_of_isGalois p P _

/-- The form of the **fundamental identity** in the case of Galois extension. -/
theorem ramificationIdx_mul_inertiaDeg_of_isGalois (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    Finset.card (primes_over p L) * (ramificationIdx_of_isGalois p L * inertiaDeg_of_isGalois p L) =
    Module.finrank K L := by
  rw [← smul_eq_mul, ← Finset.sum_const]
  rw [← sum_ramification_inertia (R := 𝓞 K) (S := 𝓞 L) p K L (ne_bot_ofIsMaximal p)]
  apply Finset.sum_congr rfl
  intro P hp
  letI := ((primes_over_mem p P).mp hp).1
  letI := ((primes_over_mem p P).mp hp).2
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois, inertiaDeg_eq_inertiaDeg_of_isGalois]



-- Definition 9.2
/-! ### decomposition Group -/

open MulAction

/-- The `MulAction` of the Galois group `L ≃ₐ[K] L` on the set `primes_over p L`,
given by `σ ↦ (P ↦ σ P)`. -/
instance Gal_MulAction_primes (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    MulAction (L ≃ₐ[K] L) (primes_over p L) where
  smul σ Q := primes_over.mk p (map (mapRingHom σ) Q.1)
  one_smul Q := by
    show primes_over.mk p (map (mapRingHom (1 : L ≃ₐ[K] L)) Q.1) = Q
    simp only [← Subtype.val_inj, mapRingHom_one, map_id]
  mul_smul σ τ Q := by
    show primes_over.mk p (map (mapRingHom (σ * τ)) Q.1) =
        primes_over.mk p (map (mapRingHom σ) (primes_over.mk p (map (mapRingHom τ) Q.1)).1)
    simp only [← Subtype.val_inj, map_map]
    rfl

theorem Gal_MulAction_primes_mk_coe (σ : L ≃ₐ[K] L) :
  (σ • primes_over.mk p P).1 = map (mapRingHom σ) P := rfl

/-- The decomposition group of `P` over `K`, is the stabilizer of `primes_over.mk p P`
  under the action `Gal_MulAction_primes`. -/
def decompositionGroup : Subgroup (L ≃ₐ[K] L) := stabilizer _ (primes_over.mk p P)

/-- The `decompositionGroup` is consisting of all elements of the Galois group `L ≃ₐ[K] L` such
that keep `P` invariant. -/
theorem decompositionGroup_mem (σ : L ≃ₐ[K] L) :
    σ ∈ decompositionGroup p P ↔ map (mapRingHom σ) P = P := by
  rw [decompositionGroup, mem_stabilizer_iff, ← Subtype.val_inj, Gal_MulAction_primes_mk_coe]

open IntermediateField FiniteDimensional

/-- The decomposition field of `P` over `K` is the fixed field of `decompositionGroup p P`. -/
def decompositionField : IntermediateField K L := fixedField (decompositionGroup p P)

/-- decompositionField is a Number Field. -/
instance decompositionField_NumberField : NumberField (decompositionField p P) :=
  of_intermediateField (decompositionField p P)

/-- The ideal equal to the intersection of `P` and `decompositionField p P`. -/
abbrev decompositionIdeal : Ideal (𝓞 (decompositionField p P)) :=
  idealUnder (decompositionField p P) P

instance decompositionIdeal.isMaximal : IsMaximal (decompositionIdeal p P) :=
  idealUnder.IsMaximal P




-- Proposition 9.3

open Classical

theorem decompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg [IsGalois K L] :
    Fintype.card (decompositionGroup p P) =
    ramificationIdx_of_isGalois p L * inertiaDeg_of_isGalois p L := by
  apply mul_left_cancel₀ (primes_over_card_ne_zero p L)
  have : Fintype (orbit (L ≃ₐ[K] L) (primes_over.mk p P)) :=
    Set.fintypeRange fun m ↦ m • primes_over.mk p P
  rw [ramificationIdx_mul_inertiaDeg_of_isGalois, ← IsGalois.card_aut_eq_finrank, decompositionGroup]
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (L ≃ₐ[K] L) (primes_over.mk p P)]
  congr 1
  · rw [Fintype.card_of_finset' (@Finset.univ (primes_over p L) _), Finset.card_univ]
    · exact (Fintype.card_coe (primes_over p L)).symm
    · intro Q
      simp only [Finset.univ_eq_attach, Finset.mem_attach, true_iff, MulAction.mem_orbit_iff]
      rcases isMaximal_conjugates p P Q.1 with ⟨σ, hs⟩
      exact ⟨σ, by rw [← Subtype.val_inj, ← hs]; rfl⟩
  · congr
    exact Subsingleton.elim (fun _ ↦ _) (fun _ ↦ _)

theorem finrank_over_decompositionField_eq_ramificationIdx_mul_inertiaDeg
    [IsGalois K L] : Module.finrank (decompositionField p P) L =
    ramificationIdx_of_isGalois p L * inertiaDeg_of_isGalois p L := by
  rw [decompositionField, finrank_fixedField_eq_card (decompositionGroup p P)]
  rw [decompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg p P]

/-- `P` is the unique ideal lying over `decompositionIdeal p P`. -/
theorem isMaximal_lies_over_decompositionideal_unique (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Q lies_over (decompositionIdeal p P)] [IsGalois K L] : Q = P := by
  rcases isMaximal_conjugates (decompositionIdeal p P) P Q with ⟨σ, hs⟩
  let τ := (subgroup_equiv_aut (decompositionGroup p P)).toFun σ
  have h : mapRingHom σ = mapRingHom τ.1 := rfl
  rw [← hs, h, (decompositionGroup_mem p P τ.1).mp τ.2]

/-- The instance form of `isMaximal_lies_over_decompositionideal_unique`. -/
instance unique_lies_over_decompositionIdeal [IsGalois K L] :
    P unique_lies_over (decompositionIdeal p P) :=
  { over_idealUnder P with unique := fun Q ↦ isMaximal_lies_over_decompositionideal_unique p P Q }

/-- An alternative statement of `isMaximal_lies_over_decompositionideal_unique`. -/
theorem primes_over_decompositionideal_card_eq_one [IsGalois K L] :
  Finset.card (primes_over (decompositionIdeal p P) L) = 1 :=
    unique_primes_over_card_eq_one (decompositionIdeal p P) P

private lemma ramificationIdx_and_inertiaDeg_of_decompositionIdeal [IsGalois K L] :
    ramificationIdx_of_isGalois (decompositionIdeal p P) L = ramificationIdx_of_isGalois p L ∧
    inertiaDeg_of_isGalois (decompositionIdeal p P) L = inertiaDeg_of_isGalois p L := by
  let Pz := idealUnder (decompositionField p P) P
  let E := { x // x ∈ decompositionField p P }
  have h := ramificationIdx_mul_inertiaDeg_of_isGalois Pz L
  rw [primes_over_decompositionideal_card_eq_one p P, one_mul,
    finrank_over_decompositionField_eq_ramificationIdx_mul_inertiaDeg p P] at h
  have h0 := Nat.pos_of_ne_zero <| IsDedekindDomain.ramificationIdx_ne_zero
    (map_isMaximal_ne_bot p L) inferInstance (map_le_of_le_comap (le_of_eq hp.over))
  have hr := Nat.le_of_dvd h0 <| Dvd.intro_left _ <| Eq.symm <|
    ramificationIdx_algebra_tower (map_isMaximal_ne_bot Pz L)
      (map_isMaximal_ne_bot p L) (map_le_iff_le_comap.mpr (le_of_eq rfl))
  have h0 : inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P > 0 := inertiaDeg_pos p P
  have hi := Nat.le_of_dvd h0 <| Dvd.intro_left _  <| Eq.symm <| inertiaDeg_algebra_tower
    (ideal_comap_intermediateField p P (decompositionField p P)) (idealUnder_def E P)
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois Pz P,
    ramificationIdx_eq_ramificationIdx_of_isGalois p P] at hr
  rw [inertiaDeg_eq_inertiaDeg_of_isGalois Pz P, inertiaDeg_eq_inertiaDeg_of_isGalois p P] at hi
  have hr0 := Nat.pos_of_ne_zero <| IsDedekindDomain.ramificationIdx_ne_zero
    (map_isMaximal_ne_bot Pz L) inferInstance (map_le_of_le_comap (le_of_eq rfl))
  rw [inertiaDeg_eq_inertiaDeg_of_isGalois p P] at h0
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois Pz P] at hr0
  exact (mul_eq_mul_iff_eq_and_eq_of_pos hr hi hr0 h0).mp h

theorem ramificationIdx_of_decompositionIdeal [IsGalois K L] :
  ramificationIdx_of_isGalois (decompositionIdeal p P) L = ramificationIdx_of_isGalois p L :=
    (ramificationIdx_and_inertiaDeg_of_decompositionIdeal p P).1

theorem inertiaDeg_of_decompositionIdeal [IsGalois K L] :
  inertiaDeg_of_isGalois (decompositionIdeal p P) L = inertiaDeg_of_isGalois p L :=
    (ramificationIdx_and_inertiaDeg_of_decompositionIdeal p P).2

theorem ramificationIdx_of_decompositionideal_over_bot_eq_one [IsGalois K L] : ramificationIdx
    (algebraMap (𝓞 K) (𝓞 (decompositionField p P))) p (decompositionIdeal p P) = 1 := by
  let Pz := idealUnder (decompositionField p P) P
  have h := ramificationIdx_algebra_tower (map_isMaximal_ne_bot Pz L)
    (map_isMaximal_ne_bot p L) (map_le_iff_le_comap.mpr (le_of_eq rfl))
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois Pz P, ramificationIdx_of_decompositionIdeal p P,
    ← ramificationIdx_eq_ramificationIdx_of_isGalois p P] at h
  nth_rw 1 [← one_mul (ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P)] at h
  exact mul_right_cancel₀ (IsDedekindDomain.ramificationIdx_ne_zero (map_isMaximal_ne_bot p L)
    inferInstance (map_le_of_le_comap (le_of_eq hp.over))) h.symm

/-- The residue class field corresponding to `decompositionField p P` is isomorphic to
residue class field corresponding to `p`. -/
theorem inertiaDeg_of_decompositionideal_over_bot_eq_one [IsGalois K L] : inertiaDeg
    (algebraMap (𝓞 K) (𝓞 (decompositionField p P))) p (decompositionIdeal p P) = 1 := by
  have h := inertiaDeg_algebra_tower (ideal_comap_intermediateField p P (decompositionField p P))
    (idealUnder_def (decompositionField p P) P)
  rw [inertiaDeg_eq_inertiaDeg_of_isGalois (idealUnder (decompositionField p P) P) P,
    inertiaDeg_of_decompositionIdeal p P, ← inertiaDeg_eq_inertiaDeg_of_isGalois p P] at h
  nth_rw 1 [← one_mul (inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P)] at h
  exact mul_right_cancel₀ (ne_of_gt (inertiaDeg_pos p P)) h.symm



-- Proposition 9.4
/-! ### inertia Group -/

/-- The residue class field of a number field is a finite field. -/
noncomputable instance residue_field_instFintype : Finite ((𝓞 K) ⧸ p) := inferInstance

/-- The extension between residue class fields of number fields is a Galois extension. -/
instance extension_of_residue_fields_instIsGalois : IsGalois ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  inferInstance

/-- The inertia group of `P` over `K` is the subgorup of `L ≃ₐ[K] L` that consists of all
the `σ : L ≃ₐ[K] L` that are identity modulo `P`. -/
def inertiaGroup (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (P : Ideal (𝓞 L)) : Subgroup (L ≃ₐ[K] L) where
  carrier := { σ | ∀ x : (𝓞 L), Ideal.Quotient.mk P (mapRingHom σ x) = Ideal.Quotient.mk P x }
  mul_mem' := by
    intro _ τ hs ht x
    rw [← ht x, ← hs (mapRingHom τ x)]
    rfl
  one_mem' _ := rfl
  inv_mem' := by
    intro σ hs x
    rw [show σ⁻¹ = σ.symm from rfl, ← hs (mapRingHom σ.symm x), mapRingHom_apply_symm_apply σ x]

theorem inertiaGroup_le_decompositionGroup : inertiaGroup K P ≤ decompositionGroup p P := by
  refine fun σ hs ↦ (decompositionGroup_mem p P σ).mpr <|
    le_antisymm (map_le_of_le_comap (fun x hx ↦ ?_)) (fun x hx ↦ ?_)
  · have h := add_mem (Ideal.Quotient.eq.mp (hs x)) hx
    rw [sub_add_cancel] at h
    exact mem_comap.mpr h
  · rw [← mapRingEquiv_apply_symm_apply σ x]
    have h := add_mem (Ideal.Quotient.eq.mp (((inertiaGroup K P).inv_mem hs) x)) hx
    rw [sub_add_cancel] at h
    exact mem_map_of_mem (mapRingHom σ) h



section unique

open FiniteDimensional IntermediateField Polynomial Module

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
(p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [hp : P unique_lies_over p]

/-- If `P` is the unique ideal lying over `p`, then `P` remains invariant under the action of `σ`. -/
theorem mapRingHom_map_eq_of_unique_lies_over {K L : Type*} [Field K] [Field L]
    [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsMaximal]
    [hp : P unique_lies_over p] (σ : L ≃ₐ[K] L) : map (mapRingHom σ) P = P :=
  hp.unique (map (mapRingHom σ) P)

/-- If `P` is the unique ideal lying over `p`, then the action of each element `σ` in `L ≃ₐ[K] L`
on the residue class field is an an automorphism of `(𝓞 L) ⧸ P` fixing `(𝓞 K) ⧸ p`, inducing a
homomorphism from `L ≃ₐ[K] L` to the Galois group `((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)`. -/
def residueGaloisHom : MonoidHom (L ≃ₐ[K] L) (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)) where
  toFun σ := residueField_mapAlgEquiv p (mapRingHom_map_eq_of_unique_lies_over p P σ)
  map_one' := by ext ⟨⟩; rfl
  map_mul' _ _ := by ext ⟨⟩; rfl

noncomputable abbrev powerBasis_of_residue : PowerBasis ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  letI : Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 L ⧸ P) := IsGalois.to_isSeparable
  Field.powerBasisOfFiniteOfSeparable ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P)

theorem residueGaloisHom_surjective [hn : Normal K L] :
    Function.Surjective (residueGaloisHom p P) := by
  let F := 𝓞 K ⧸ p
  let E := 𝓞 L ⧸ P
  letI : Algebra E E := Algebra.id E
  intro σ
  have e : PowerBasis F E := powerBasis_of_residue p P
  let β := (PowerBasis.liftEquiv e).toFun σ.toAlgHom
  rcases Quotient.exists_rep e.gen with ⟨a, ha⟩
  let f : (𝓞 K)[X] := minpoly (𝓞 K) a
  let fl : (𝓞 L)[X] := f.map (algebraMap (𝓞 K) (𝓞 L))
  let ϕp : (𝓞 K) →+* F := Ideal.Quotient.mk p
  let ϕP : (𝓞 L) →+* E := Ideal.Quotient.mk P
  have h : Quotient.mk (Submodule.quotientRel P) a = ϕP a := rfl
  rw [h] at ha
  have hai : IsIntegral (𝓞 K) a := IsIntegral.isIntegral a
  have hm : f.Monic := minpoly.monic hai
  have h0 : (fl.map ϕP) ≠ 0 := map_monic_ne_zero (Monic.map (algebraMap (𝓞 K) (𝓞 L)) hm)
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
  have hfe : (Polynomial.map (algebraMap (𝓞 K) K) f) = minpoly K a.1 := by
    refine minpoly.eq_of_irreducible_of_monic
      ((Monic.irreducible_iff_irreducible_map_fraction_map (minpoly.monic hai)).mp
        (minpoly.irreducible hai)) ?_ (Monic.map (algebraMap (𝓞 K) K) (minpoly.monic hai))
    have h : a.1 = algebraMap (𝓞 L) L a := rfl
    rw [h]
    simp only [aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, minpoly.aeval, f]
  have h : fl.roots.map ϕP = (fl.map ϕP).roots := by
    have h := (natDegree_eq_card_roots' (hn.splits a.1)).symm
    have hc : (algebraMap K L).comp (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) L := rfl
    have he := isIntegralClosure_root_card_eq_ofMonic (𝓞 L) L (minpoly.monic hai)
    rw [← hfe, natDegree_map, Monic.natDegree_map (minpoly.monic hai), Polynomial.map_map, hc, ← he,
      ← Monic.natDegree_map (minpoly.monic hai) (algebraMap (𝓞 K) (𝓞 L))] at h
    exact roots_map_of_card_eq_natDegree h0 h
  rw [← h] at hbr
  rcases Multiset.mem_map.mp hbr with ⟨b, ⟨hbr, hb⟩⟩
  have h : aeval b.1 (minpoly K (AdjoinSimple.gen K a.1)) = 0 := by
    have he : minpoly K (AdjoinSimple.gen K a.1) = minpoly K a.1 := by apply minpoly_eq
    have h : b.1 = algebraMap (𝓞 L) L b := rfl
    rw [he, ← hfe, h, aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, aeval_def, ← eval_map,
      ← coe_aeval_eq_eval, (mem_roots_iff_aeval_eq_zero (map_monic_ne_zero hm)).mp hbr]
  let ε := IntermediateField.adjoin.powerBasis (hn.isIntegral a.1)
  use (ε.lift b.1 h).fieldRangeAlgEquiv.liftNormal L
  refine AlgEquiv.coe_algHom_injective ((@PowerBasis.liftEquiv E _ F _ _ E _ _ e).injective ?_)
  apply Subtype.val_inj.mp
  rw [PowerBasis.liftEquiv_apply_coe, AlgHom.coe_coe]
  simp only [← ha, Equiv.toFun_as_coe, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
  show ϕP ((RingOfIntegers.mapAlgEquiv ((ε.lift b.1 h).fieldRangeAlgEquiv.liftNormal L)) a) = β.1
  rw [← hb]
  congr
  exact Subtype.val_inj.mp <| ((ε.lift b.1 h).fieldRangeAlgEquiv.liftNormal_commutes L
    (AdjoinSimple.gen K a.1)).trans (ε.lift_gen b.1 h)



-- Definition 9.5

open IsGalois

/-- If `P` is the unique ideal lying over `p`, then the `inertiaGroup` is equal to the
kernel of the homomorphism `residueGaloisHom`. -/
theorem inertiaGroup_eq_ker {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [hp : P unique_lies_over p] : inertiaGroup K P = MonoidHom.ker (residueGaloisHom p P) := by
  ext σ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  constructor
  · rintro h ⟨x⟩
    nth_rw 2 [Submodule.Quotient.quot_mk_eq_mk]
    rw [Quotient.mk_eq_mk, ← h x]
    rfl
  · intro h x
    have h := h (Ideal.Quotient.mk P x)
    rw [AlgEquiv.one_apply] at h
    rw [← h]
    rfl

/-- If `P` is the unique ideal lying over `p`, then the `inertiaGroup K P` is a normal subgroup. -/
theorem inertiaGroup_normal {K L : Type*} [Field K] [Field L] [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
    [hp : P unique_lies_over p] : Subgroup.Normal (inertiaGroup K P) := by
  rw [inertiaGroup_eq_ker p P]
  exact MonoidHom.normal_ker (residueGaloisHom p P)

noncomputable def aut_quoutient_inertiaGroup_equiv_residueField_aut [Normal K L] :
    @MulEquiv ((L ≃ₐ[K] L) ⧸ (inertiaGroup K P)) (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P))
    (letI := inertiaGroup_normal p P; inferInstance) _ :=
  letI := inertiaGroup_normal p P
  (QuotientGroup.quotientMulEquivOfEq (inertiaGroup_eq_ker p P)).trans <|
    QuotientGroup.quotientKerEquivOfSurjective _ (residueGaloisHom_surjective p P)

/-- The intermediate field fixed by `inertiaGroup K P`. -/
def inertiaField' (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (P : Ideal (𝓞 L)) [P.IsMaximal] : IntermediateField K L :=
  fixedField (inertiaGroup K P)

/-- `inertiaField' K P` is a Number Field. -/
instance inertiaField_NumberField : NumberField (inertiaField' K P) :=
  of_intermediateField (inertiaField' K P)

/-- The ideal equal to the intersection of `P` and `inertiaField' p P`. -/
abbrev inertiaIdeal' (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] (P : Ideal (𝓞 L)) [P.IsMaximal] : Ideal (𝓞 (inertiaField' K P)) :=
  idealUnder (inertiaField' K P) P

/-- `inertiaIdeal' p P` is a maximal Ideal. -/
instance inertiaideal_IsMaxiaml : IsMaximal (inertiaIdeal' K P) := idealUnder.IsMaximal P



-- Proposition 9.6

variable [IsGalois K L]

/-- `(inertiaField' p P) / K` is a Galois extension. -/
theorem inertiaField_isGalois_of_unique {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal]
    [P.IsMaximal] [P unique_lies_over p] : IsGalois K (inertiaField' K P) :=
  letI := inertiaGroup_normal p P
  of_fixedField_normal_subgroup (inertiaGroup K P)

/-- The Galois group `Gal((inertiaField' p P) / K)` is isomorphic to the
Galois group `Gal((𝓞 L) ⧸ P) / (𝓞 K) ⧸ p)`. -/
noncomputable def inertiaField_aut_equiv_ResidueField_aut :
    ((inertiaField' K P) ≃ₐ[K] (inertiaField' K P)) ≃* (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)) :=
  letI := inertiaGroup_normal p P
  (normal_aut_equiv_quotient (inertiaGroup K P)).trans <|
    aut_quoutient_inertiaGroup_equiv_residueField_aut p P

/-- The Galois group `Gal(L / (inertiaField' p P))` is isomorphic to `inertiaGroup K P`. -/
def inertiaField_aut_tower_top_equiv_inertiaGroup_of_unique :
  (L ≃ₐ[inertiaField' K P] L) ≃* inertiaGroup K P := subgroup_equiv_aut (inertiaGroup K P)

/-- The extension degree `[L : K]` is equal to the product of the ramification index
and the inertia degree of `p` in `L`. -/
theorem finrank_eq_ramificationIdx_mul_inertiaDeg (P : Ideal (𝓞 L))
    [P unique_lies_over p] : finrank K L =
    ramificationIdx_of_isGalois p L * inertiaDeg_of_isGalois p L := by
  have h := (ramificationIdx_mul_inertiaDeg_of_isGalois p L).symm
  rw [unique_primes_over_card_eq_one p P, one_mul] at h
  exact h

/-- The extension degree `[inertiaField' p P : K]` is equal to the inertia degree of `p` in `L`. -/
theorem finrank_bot_inertiaField_eq_inertiaDeg_of_unique :
    finrank K (inertiaField' K P) = inertiaDeg_of_isGalois p L := by
  letI := inertiaField_isGalois_of_unique p P
  rw [← inertiaDeg_eq_inertiaDeg_of_isGalois p P, inertiaDeg, ← card_aut_eq_finrank]
  rw [Fintype.card_of_bijective (inertiaField_aut_equiv_ResidueField_aut p P).bijective]
  rw [card_aut_eq_finrank, dif_pos hp.over.symm]

/-- The extension degree `[L : inertiaField' p P]` is equal to the
ramification index of `p` in `L`. -/
theorem finrank_inertiaField_top_eq_ramificationIdx_of_unique :
    finrank (inertiaField' K P) L = ramificationIdx_of_isGalois p L := by
  have h : finrank K (inertiaField' K P) ≠ 0 := ne_of_gt finrank_pos
  apply mul_left_cancel₀ h
  rw [finrank_mul_finrank K (inertiaField' K P) L, finrank_eq_ramificationIdx_mul_inertiaDeg p P,
    finrank_bot_inertiaField_eq_inertiaDeg_of_unique p P, mul_comm]

theorem inertiaGroup_card_eq_ramificationIdx_of_unique :
    Fintype.card (inertiaGroup K P) = ramificationIdx_of_isGalois p L := by
  rw [← finrank_fixedField_eq_card, ← finrank_inertiaField_top_eq_ramificationIdx_of_unique p P]
  rfl

theorem inertiaGroup_inertiaideal_top (K : Type*) {L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (P : Ideal (𝓞 L)) [P.IsMaximal] :
    inertiaGroup (inertiaField' K P) P = ⊤ := by
  refine (Subgroup.eq_top_iff' (inertiaGroup (inertiaField' K P) P)).mpr (fun σ x ↦ ?_)
  let τ := (subgroup_equiv_aut (inertiaGroup K P)).toFun σ
  have hst : (mapRingHom σ) x = (mapRingHom τ.1) x := rfl
  rw [hst, τ.2 x]

theorem inertiaDeg_over_inertiaideal_eq_one_of_unique (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L))
    [P.IsMaximal] [P unique_lies_over p]  :
    inertiaDeg_of_isGalois (inertiaIdeal' K P) L = 1 := by
  letI := ideal_unique_lies_over_tower_top p (inertiaIdeal' K P) P
  letI := inertiaGroup_normal (inertiaIdeal' K P) P
  rw [← inertiaDeg_eq_inertiaDeg_of_isGalois (inertiaIdeal' K P) P, inertiaDeg, dif_pos rfl]
  rw [← card_aut_eq_finrank, ← Fintype.card_of_bijective <| MulEquiv.bijective <|
    aut_quoutient_inertiaGroup_equiv_residueField_aut (inertiaIdeal' K P) P]
  have hm := Subgroup.card_eq_card_quotient_mul_card_subgroup (inertiaGroup (inertiaField' K P) P)
  nth_rw 1 [(Subgroup.card_eq_iff_eq_top (inertiaGroup (inertiaField' K P) P)).mpr <|
    inertiaGroup_inertiaideal_top K P, ← one_mul (Nat.card (L ≃ₐ[inertiaField' K P] L))] at hm
  simp only [Nat.card_eq_fintype_card] at hm
  exact mul_right_cancel₀ Fintype.card_ne_zero hm.symm

theorem ramificationIdx_over_inertiaideal_eq_ramificationIdx_of_unique :
    ramificationIdx_of_isGalois (inertiaIdeal' K P) L = ramificationIdx_of_isGalois p L := by
  letI := ideal_unique_lies_over_tower_top p (inertiaIdeal' K P) P
  rw [← finrank_inertiaField_top_eq_ramificationIdx_of_unique p P]
  rw [finrank_eq_ramificationIdx_mul_inertiaDeg (inertiaIdeal' K P) P]
  rw [inertiaDeg_over_inertiaideal_eq_one_of_unique p P, mul_one]

theorem ramificationIdx_below_inertiaideal_eq_one_of_unique :
    ramificationIdx_of_isGalois p (inertiaField' K P) = 1 := by
  let Pt := idealUnder (inertiaField' K P) P
  letI := inertiaField_isGalois_of_unique p P
  have h := ramificationIdx_algebra_tower (map_isMaximal_ne_bot Pt L)
    (map_isMaximal_ne_bot p L) (map_le_iff_le_comap.mpr (le_of_eq rfl))
  nth_rw 1 [ramificationIdx_eq_ramificationIdx_of_isGalois Pt P,
    ramificationIdx_over_inertiaideal_eq_ramificationIdx_of_unique p P,
    ← ramificationIdx_eq_ramificationIdx_of_isGalois p P,
    ← one_mul (ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P),
    ramificationIdx_eq_ramificationIdx_of_isGalois p Pt] at h
  exact mul_right_cancel₀ (IsDedekindDomain.ramificationIdx_ne_zero (map_isMaximal_ne_bot p L)
    (IsMaximal.isPrime inferInstance) (map_le_of_le_comap (le_of_eq hp.over))) h.symm

theorem inertiaDeg_below_inertiaideal_eq_inertiaDeg_of_unique :
    inertiaDeg_of_isGalois p (inertiaField' K P) = inertiaDeg_of_isGalois p L := by
  letI := inertiaField_isGalois_of_unique p P
  have h := inertiaDeg_algebra_tower (ideal_comap_intermediateField p P (inertiaField' K P))
    (idealUnder_def (inertiaField' K P) P)
  nth_rw 1 [inertiaDeg_eq_inertiaDeg_of_isGalois (inertiaIdeal' K P) P,
    inertiaDeg_over_inertiaideal_eq_one_of_unique p P, mul_one] at h
  simp_rw [inertiaDeg_eq_inertiaDeg_of_isGalois] at h
  exact h.symm

end unique



section inertia

/- TODO : The genral version of `inertiaField_aut_equiv_ResidueField_aut`, i.e.,
`((inertiaField p P) ≃ₐ[decompositionField p P] (inertiaField p P))` is isomorphic to
`(((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P))`. -/

open IntermediateField FiniteDimensional Classical

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
(p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [P lies_over p]

theorem inertiaGroup_eq :
    Subgroup.map (subgroup_equiv_aut (decompositionGroup p P)).symm.toMonoidHom
    ((inertiaGroup K P).subgroupOf (decompositionGroup p P)) =
    inertiaGroup (decompositionField p P) P := by
  ext σ
  rw [Subgroup.mem_map]
  refine ⟨fun ⟨τ, ht, he⟩ x ↦ by rw [← he, ← Subgroup.mem_subgroupOf.mp ht x]; rfl, fun hs ↦ ?_⟩
  refine ⟨(subgroup_equiv_aut (decompositionGroup p P)).toFun σ, fun x ↦ by rw [← hs x]; rfl, ?_⟩
  rw [MulEquiv.toEquiv_eq_coe]
  simp only [Equiv.toFun_as_coe, MulEquiv.coe_toEquiv, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

def inertiaGroup_equiv : inertiaGroup (decompositionField p P) P ≃* inertiaGroup K P :=
  (MulEquiv.subgroupCongr (inertiaGroup_eq p P)).symm.trans <|
    ((subgroup_equiv_aut (decompositionGroup p P)).symm.subgroupMap
      ((inertiaGroup K P).subgroupOf (decompositionGroup p P))).symm.trans <|
        (Subgroup.subgroupOfEquivOfLe (inertiaGroup_le_decompositionGroup p P))

/-- The intertia field of `P` over `K` is the intermediate field of `L / decompositionField p P`
fixed by the inertia group pf `P` over `K`. -/
def inertiaField : IntermediateField (decompositionField p P) L :=
  fixedField (inertiaGroup (decompositionField p P) P)

/-- The ideal equal to the intersection of `P` and `inertiaField p P`. -/
abbrev inertiaIdeal : Ideal (𝓞 (inertiaField p P)) := idealUnder (inertiaField p P) P

/-- `(inertiaField p P) / (decompositionField p P)` is a Galois extension. -/
instance inertiaField_isGalois [IsGalois K L] : IsGalois (decompositionField p P) (inertiaField p P) :=
  inertiaField_isGalois_of_unique (decompositionIdeal p P) P

/-- The Galois group `Gal(L / (inertiaField p P))` is isomorphic to `inertiaGroup K P`. -/
def inertiaField_aut_tower_top_equiv_inertiaGroup :
    (L ≃ₐ[inertiaField p P] L) ≃* inertiaGroup K P :=
  (subgroup_equiv_aut (inertiaGroup (decompositionField p P) P)).trans (inertiaGroup_equiv p P)

/-- The extension degree `[inertiaField p P : K]` is equal to the inertia degree of `p` in `L`. -/
theorem finrank_bot_inertiaField_eq_inertiaDeg [IsGalois K L] :
    Module.finrank (decompositionField p P) (inertiaField p P) = inertiaDeg_of_isGalois p L := by
  rw [← inertiaDeg_of_decompositionIdeal p P]
  exact finrank_bot_inertiaField_eq_inertiaDeg_of_unique (decompositionIdeal p P) P

/-- The extension degree `[L : inertiaField p P]` is equal to the
ramification index of `p` in `L`. -/
theorem finrank_inertiaField_top_eq_ramificationIdx [IsGalois K L] :
    Module.finrank (inertiaField p P) L = ramificationIdx_of_isGalois p L := by
  rw [← ramificationIdx_of_decompositionIdeal p P]
  exact finrank_inertiaField_top_eq_ramificationIdx_of_unique (decompositionIdeal p P) P

theorem inertiaGroup_card_eq_ramificationIdx [IsGalois K L] :
    Fintype.card (inertiaGroup K P) = ramificationIdx_of_isGalois p L := by
  rw [← ramificationIdx_of_decompositionIdeal p P]
  rw [Fintype.card_of_bijective (inertiaGroup_equiv p P).symm.bijective]
  rw [inertiaGroup_card_eq_ramificationIdx_of_unique (decompositionIdeal p P) P]

theorem inertiaDeg_over_inertiaideal_eq_one [IsGalois K L] :
    inertiaDeg_of_isGalois (inertiaIdeal p P) L = 1 :=
  inertiaDeg_over_inertiaideal_eq_one_of_unique (decompositionIdeal p P) P

theorem ramificationIdx_over_inertiaideal_eq_ramificationIdx [IsGalois K L] :
    ramificationIdx_of_isGalois (inertiaIdeal p P) L = ramificationIdx_of_isGalois p L := by
  rw [← ramificationIdx_of_decompositionIdeal p P]
  exact ramificationIdx_over_inertiaideal_eq_ramificationIdx_of_unique (decompositionIdeal p P) P

theorem ramificationIdx_below_inertiaideal_eq_one [IsGalois K L] :
    ramificationIdx_of_isGalois (decompositionIdeal p P) (inertiaField p P) = 1 :=
  ramificationIdx_below_inertiaideal_eq_one_of_unique (decompositionIdeal p P) P

theorem inertiaDeg_below_inertiaideal_eq_inertiaDeg [IsGalois K L] :
    inertiaDeg_of_isGalois (decompositionIdeal p P) (inertiaField p P) =
    inertiaDeg_of_isGalois p L := by
  rw [← inertiaDeg_of_decompositionIdeal p P]
  exact inertiaDeg_below_inertiaideal_eq_inertiaDeg_of_unique (decompositionIdeal p P) P

noncomputable def inertiaField_decompositionField_aut_equiv_ResidueField_aut [IsGalois K L] :
    ((inertiaField p P) ≃ₐ[decompositionField p P] (inertiaField p P)) ≃*
    (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)) :=
  letI : IsScalarTower (𝓞 K ⧸ p) (𝓞 (decompositionField p P) ⧸ decompositionIdeal p P) (𝓞 L ⧸ P) :=
    IsScalarTower.of_algebraMap_eq (by rintro ⟨_⟩; rfl)
  have h : Module.finrank ((𝓞 K) ⧸ p) ((𝓞 (decompositionField p P)) ⧸ (decompositionIdeal p P)) = 1 := by
    rw [← inertiaDeg_algebraMap]
    exact inertiaDeg_of_decompositionideal_over_bot_eq_one p P
  (inertiaField_aut_equiv_ResidueField_aut (decompositionIdeal p P) P).trans <|
    aut_equiv_of_finrank_eq_one _ h

end inertia
