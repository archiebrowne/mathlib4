/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

#align_import algebra.lie.universal_enveloping from "leanprover-community/mathlib"@"32b08ef840dd25ca2e47e035c5da03ce16d2dc3c"

/-!
# Universal enveloping algebra

Given a commutative ring `R` and a Lie algebra `L` over `R`, we construct the universal
enveloping algebra of `L`, together with its universal property.

## Main definitions

  * `UniversalEnvelopingAlgebra`: the universal enveloping algebra, endowed with an
    `R`-algebra structure.
  * `UniversalEnvelopingAlgebra.ι`: the Lie algebra morphism from `L` to its universal
    enveloping algebra.
  * `UniversalEnvelopingAlgebra.lift`: given an associative algebra `A`, together with a Lie
    algebra morphism `f : L →ₗ⁅R⁆ A`, `lift R L f : UniversalEnvelopingAlgebra R L →ₐ[R] A` is the
    unique morphism of algebras through which `f` factors.
  * `UniversalEnvelopingAlgebra.ι_comp_lift`: states that the lift of a morphism is indeed part
    of a factorisation.
  * `UniversalEnvelopingAlgebra.lift_unique`: states that lifts of morphisms are indeed unique.
  * `UniversalEnvelopingAlgebra.hom_ext`: a restatement of `lift_unique` as an extensionality
    lemma.

## Tags

lie algebra, universal enveloping algebra, tensor algebra
-/


universe u₁ u₂ u₃

variable (R : Type u₁) (L : Type u₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "ιₜ" => TensorAlgebra.ι R

namespace UniversalEnvelopingAlgebra

/-- The quotient by the ideal generated by this relation is the universal enveloping algebra.

Note that we have avoided using the more natural expression:
| lie_compat (x y : L) : rel (ιₜ ⁅x, y⁆) ⁅ιₜ x, ιₜ y⁆
so that our construction needs only the semiring structure of the tensor algebra. -/
inductive Rel : TensorAlgebra R L → TensorAlgebra R L → Prop
  | lie_compat (x y : L) : Rel (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) (ιₜ x * ιₜ y)
#align universal_enveloping_algebra.rel UniversalEnvelopingAlgebra.Rel

end UniversalEnvelopingAlgebra

/-- The universal enveloping algebra of a Lie algebra. -/
def UniversalEnvelopingAlgebra :=
  RingQuot (UniversalEnvelopingAlgebra.Rel R L)
#align universal_enveloping_algebra UniversalEnvelopingAlgebra

namespace UniversalEnvelopingAlgebra

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5020): the next three
-- instances were derived automatically in mathlib3.

instance instInhabited : Inhabited (UniversalEnvelopingAlgebra R L) :=
  inferInstanceAs (Inhabited (RingQuot (UniversalEnvelopingAlgebra.Rel R L)))
#align universal_enveloping_algebra.inhabited UniversalEnvelopingAlgebra.instInhabited

instance instRing : Ring (UniversalEnvelopingAlgebra R L) :=
  inferInstanceAs (Ring (RingQuot (UniversalEnvelopingAlgebra.Rel R L)))
#align universal_enveloping_algebra.ring UniversalEnvelopingAlgebra.instRing

instance instAlgebra : Algebra R (UniversalEnvelopingAlgebra R L) :=
  inferInstanceAs (Algebra R (RingQuot (UniversalEnvelopingAlgebra.Rel R L)))
#align universal_enveloping_algebra.algebra UniversalEnvelopingAlgebra.instAlgebra


/-- The quotient map from the tensor algebra to the universal enveloping algebra as a morphism of
associative algebras. -/
def mkAlgHom : TensorAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R L :=
  RingQuot.mkAlgHom R (Rel R L)
#align universal_enveloping_algebra.mk_alg_hom UniversalEnvelopingAlgebra.mkAlgHom

variable {L}

/-- The natural Lie algebra morphism from a Lie algebra to its universal enveloping algebra. -/
@[simps!] -- Porting note: added
def ι : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L :=
  { (mkAlgHom R L).toLinearMap.comp ιₜ with
    map_lie' := fun {x y} => by
      suffices mkAlgHom R L (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) = mkAlgHom R L (ιₜ x * ιₜ y) by
        rw [AlgHom.map_mul] at this; simp [LieRing.of_associative_ring_bracket, ← this]
      exact RingQuot.mkAlgHom_rel _ (Rel.lie_compat x y) }
#align universal_enveloping_algebra.ι UniversalEnvelopingAlgebra.ι

variable {A : Type u₃} [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)

/-- The universal property of the universal enveloping algebra: Lie algebra morphisms into
associative algebras lift to associative algebra morphisms from the universal enveloping algebra. -/
def lift : (L →ₗ⁅R⁆ A) ≃ (UniversalEnvelopingAlgebra R L →ₐ[R] A) where
  toFun f :=
    RingQuot.liftAlgHom R
      ⟨TensorAlgebra.lift R (f : L →ₗ[R] A), by
        intro a b h; induction' h with x y
        simp only [LieRing.of_associative_ring_bracket, map_add, TensorAlgebra.lift_ι_apply,
          LieHom.coe_toLinearMap, LieHom.map_lie, map_mul, sub_add_cancel]⟩
  invFun F := (F : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (ι R)
  left_inv f := by
    ext
    -- Porting note: was
    -- simp only [ι, mkAlgHom, TensorAlgebra.lift_ι_apply, LieHom.coe_toLinearMap,
    --   LinearMap.toFun_eq_coe, LinearMap.coe_comp, LieHom.coe_comp, AlgHom.coe_toLieHom,
    --   LieHom.coe_mk, Function.comp_apply, AlgHom.toLinearMap_apply,
    --   RingQuot.liftAlgHom_mkAlgHom_apply]
    simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom,
      UniversalEnvelopingAlgebra.ι_apply, mkAlgHom]
    rw [RingQuot.liftAlgHom_mkAlgHom_apply]
    simp only [TensorAlgebra.lift_ι_apply, LieHom.coe_toLinearMap]
  right_inv F := by
    apply RingQuot.ringQuot_ext'
    ext
    -- Porting note: was
    -- simp only [ι, mkAlgHom, TensorAlgebra.lift_ι_apply, LieHom.coe_toLinearMap,
    --   LinearMap.toFun_eq_coe, LinearMap.coe_comp, LieHom.coe_linearMap_comp,
    --   AlgHom.comp_toLinearMap, Function.comp_apply, AlgHom.toLinearMap_apply,
    --   RingQuot.liftAlgHom_mkAlgHom_apply, AlgHom.coe_toLieHom, LieHom.coe_mk]
    simp [mkAlgHom]
#align universal_enveloping_algebra.lift UniversalEnvelopingAlgebra.lift

@[simp]
theorem lift_symm_apply (F : UniversalEnvelopingAlgebra R L →ₐ[R] A) :
    (lift R).symm F = (F : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (ι R) :=
  rfl
#align universal_enveloping_algebra.lift_symm_apply UniversalEnvelopingAlgebra.lift_symm_apply

@[simp]
theorem ι_comp_lift : lift R f ∘ ι R = f :=
  funext <| LieHom.ext_iff.mp <| (lift R).symm_apply_apply f
#align universal_enveloping_algebra.ι_comp_lift UniversalEnvelopingAlgebra.ι_comp_lift

-- Porting note: moved `@[simp]` to the next theorem (LHS simplifies)
theorem lift_ι_apply (x : L) : lift R f (ι R x) = f x := by
  rw [← Function.comp_apply (f := lift R f) (g := ι R) (x := x), ι_comp_lift]
#align universal_enveloping_algebra.lift_ι_apply UniversalEnvelopingAlgebra.lift_ι_apply

@[simp]
theorem lift_ι_apply' (x : L) :
    lift R f ((UniversalEnvelopingAlgebra.mkAlgHom R L) (ιₜ x)) = f x := by
  simpa using lift_ι_apply R f x

theorem lift_unique (g : UniversalEnvelopingAlgebra R L →ₐ[R] A) : g ∘ ι R = f ↔ g = lift R f := by
  refine' Iff.trans _ (lift R).symm_apply_eq
  constructor <;> · intro h; ext; simp [← h]
#align universal_enveloping_algebra.lift_unique UniversalEnvelopingAlgebra.lift_unique

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {g₁ g₂ : UniversalEnvelopingAlgebra R L →ₐ[R] A}
    (h :
      (g₁ : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (ι R) =
        (g₂ : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (ι R)) :
    g₁ = g₂ :=
  have h' : (lift R).symm g₁ = (lift R).symm g₂ := by ext; simp [h]
  (lift R).symm.injective h'
#align universal_enveloping_algebra.hom_ext UniversalEnvelopingAlgebra.hom_ext

end UniversalEnvelopingAlgebra
