/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.FieldTheory.PurelyInseparable

variable {A B C D : Type*} [CommSemiring A] [CommSemiring C] [CommSemiring D] [Algebra A C]
  [Algebra A D] [CommSemiring B] [Algebra A B] [Algebra B C] [IsScalarTower A B C] (f : C →ₐ[A] D)

#check IsPurelyInseparable.injective_restrictDomain

@[simp]
theorem AlgHom.restrictDomain_apply (x : B) : f.restrictDomain B x = f (algebraMap B C x) := rfl

namespace separableClosure

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Normal K L]

theorem restrictNormalHom_injective : Function.Injective
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) (separableClosure K L)) := by
  sorry

noncomputable def restrictNormalEquiv : (L ≃ₐ[K] L) ≃*
    (separableClosure K L) ≃ₐ[K] (separableClosure K L) :=
  MulEquiv.ofBijective _
    ⟨restrictNormalHom_injective K L, AlgEquiv.restrictNormalHom_surjective L⟩

example (e : PowerBasis K (separableClosure K L)) (σ τ : L ≃ₐ[K] L) (h : σ e.gen = τ e.gen) : σ = τ := by
  sorry

example [FiniteDimensional K L] : ∃ x : L, ∀ σ τ : L ≃ₐ[K] L, σ x = τ x → σ = τ := by
  sorry

end separableClosure
