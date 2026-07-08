/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Hopf algebras

In this file we define `HopfAlgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toHopfAlgebra`

## Main definitions

* `HopfAlgebra R A` : the Hopf algebra structure on an `R`-bialgebra `A`.
* `HopfAlgebra.antipode` : the `R`-linear map `A →ₗ[R] A`.
* `HopfAlgebra.ofConvInverse` : construct a Hopf algebra from a two-sided convolution inverse
  of the identity.
* `HopfAlgebra.ofAlgHom` : the same for commutative `A`, with `AlgHom` hypotheses.

## Main results

* `HopfAlgebra.antipode_one` : the antipode of the unit is the unit.
* `HopfAlgebra.antipode_mul` : the antipode is an antihomomorphism: `S(ab) = S(b)S(a)`.

## TODO

* Uniqueness of Hopf algebra structure on a bialgebra (i.e. if the algebra and coalgebra structures
  agree then the antipodes must also agree).

* If `A` is commutative then `antipode` is an algebra homomorphism.

* If `A` is commutative then `antipode` is necessarily a bijection and its square is
  the identity.

(Note that all three facts have been proved for Hopf bimonoids in an arbitrary braided category,
so we could deduce the facts here from an equivalence `HopfAlgCat R ≌ Hopf (ModuleCat R)`.)

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

public section

open Bialgebra

universe u v w

/-- Isolates the antipode of a Hopf algebra, to allow API to be constructed before proving the
Hopf algebra axioms. See `HopfAlgebra` for documentation. -/
class HopfAlgebraStruct (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    extends Bialgebra R A where
  /-- The antipode of the Hopf algebra. -/
  antipode (R) : A →ₗ[R] A

-- i.e a hopf algaebra is a bialgebra with an antipode which is just an `R`-linear map `A → A`



/-- A Hopf algebra over a commutative (semi)ring `R` is a bialgebra over `R` equipped with an
`R`-linear endomorphism `antipode` satisfying the antipode axioms. -/
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    HopfAlgebraStruct R A where
  /-- One of the antipode axioms for a Hopf algebra. -/ -- a convolution
  mul_antipode_rTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  /-- One of the antipode axioms for a Hopf algebra. -/ -- a convolution
  mul_antipode_lTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

-- for the first axiom:

-- Let `antipode := S`
-- `LinearMap.mul' R A` is multiplication: `m : A ⊗[R] A → A`
-- `antipode.rTensor A` takes a map and gives the right tensor map with `A`
-- `comul` is the comulitplication `comul : A → A ⊗[R] A`

-- so LHS is: `A → A ⊗[R] A → A ⊗[R] A → A` where the first map
-- is `m`, second is `comul`  middle map is `S ⊗ id`
-- RHS is: `A → R → A` where the first is `counit` and the second is the cannonical algebraMap,
-- but packaged as a LinearMap

-- Second axiom says: `A → A ⊗[R] A → A ⊗[R] A → A` (with the second map `id ⊗ S` this time)
-- is the same as  `A → R → A` as before.

-- Jointly these say that the antipode is the inverse to the identity w.r.t convolution




namespace HopfAlgebra

export HopfAlgebraStruct (antipode) -- we can use antipode even though it's not in the namespace

variable {R : Type u} {A : Type v} {ι : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  {a : A}


/-
S ∘ m is a left convolution inverse of m:
`A → A ⊗ A → A ⊗ A → A` middle is `(S ∘ m) ⊗ m`, first is `comul` and last is `m`. This map is
the same as `unit ∘ counit`.
-/
example (R : Type u) (A : Type v) [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] :
    LinearMap.mul' R A ∘ₗ (TensorProduct.map ((antipode R) ∘ₗ LinearMap.mul' R A)
    (LinearMap.mul' R A)) ∘ₗ Coalgebra.comul = (Algebra.linearMap R A) ∘ₗ Coalgebra.counit := by
  ext a b

  sorry

@[simp] -- the first axiom applied to an element
theorem mul_antipode_rTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).rTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_rTensor_comul a

@[simp] -- the second axiom applied to an element
theorem mul_antipode_lTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).lTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_lTensor_comul a

@[simp] -- the antipode applied to 1 of the algebra is 1.
theorem antipode_one :
    HopfAlgebra.antipode R (1 : A) = 1 := by
  simpa [Algebra.TensorProduct.one_def] using mul_antipode_rTensor_comul_apply (R := R) (1 : A)

open Coalgebra -- coalgebras with an antipode


/-
If a is `a₁ ⊗ b₁ + a₂ ⊗ b₂ ⋯ aₙ ⊗ bₙ`, then:

`Σᵢⁿ S(aᵢ) * bᵢ = counit(a)` when you view `counit(a)` as an element of `A`.

This is really just the first axiom:

`Repr` is just the `comul` of `a`, and the first axiom states basically exaclty this
-/
lemma sum_antipode_mul_eq_algebraMap_counit (repr : Repr R a ι) :
-- a `Repr` in a Coalgebra represents the `comul` of some `a`.
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

/-
`Σᵢⁿ aᵢ * S(bᵢ) = counit(a)` this follows from the second axiom
-/
lemma sum_mul_antipode_eq_algebraMap_counit (repr : Repr R a ι) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

/-
`Σᵢⁿ S(aᵢ) * bᵢ = counit(a) • 1`: this is because this is exactly the cannonical `algebraMap`
-/
lemma sum_antipode_mul_eq_smul (repr : Repr R a ι) :
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      counit (R := R) a • 1 := by
  rw [sum_antipode_mul_eq_algebraMap_counit, Algebra.smul_def, mul_one]

/-
`Σᵢⁿ aᵢ * S(bᵢ) = counit(a) • 1`: this is because this is exactly the cannonical `algebraMap`
-/
lemma sum_mul_antipode_eq_smul (repr : Repr R a ι) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      counit (R := R) a • 1 := by
  rw [sum_mul_antipode_eq_algebraMap_counit, Algebra.smul_def, mul_one]

/-
`counit(S(a)) = counit(a)` note `ℛ` is an arbitrary `Repr` for `comul a`.
-/
@[simp] lemma counit_antipode (a : A) : counit (R := R) (antipode R a) = counit a := by
  calc
        counit (antipode R a)
-- `counit S(a) = counit (S (Σᵢⁿ aᵢ * bᵢ)) = Σᵢⁿ counit S(aᵢ * bᵢ) = `
    _ = counit (∑ i ∈ (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) := by
      simp_rw [map_sum, counit_mul, ← smul_eq_mul, ← map_smul, ← map_sum, sum_counit_smul]
    _ = counit a := by simpa using congr(counit (R := R) $(sum_mul_antipode_eq_smul (ℛ R a)))

-- the actual maps in the last lemma are equal
@[simp] lemma counit_comp_antipode : counit ∘ₗ antipode R = counit (A := A) := by
  ext; exact counit_antipode _

end HopfAlgebra

namespace CommSemiring

variable (R : Type u) [CommSemiring R]

open HopfAlgebra

/-- Every commutative (semi)ring is a Hopf algebra over itself -/
instance toHopfAlgebra : HopfAlgebra R R where
  antipode := .id
  mul_antipode_rTensor_comul := by ext; simp
  mul_antipode_lTensor_comul := by ext; simp

@[simp]
theorem antipode_eq_id : antipode R (A := R) = .id := rfl

end CommSemiring

namespace HopfAlgebra

variable {R A : Type*}

open Coalgebra WithConv LinearMap

/-- Upgrade a bialgebra to a Hopf algebra by specifying a convolution inverse of the identity. -/
noncomputable abbrev ofConvInverse [CommSemiring R] [Semiring A] [Bialgebra R A]
    (antipode : A →ₗ[R] A)
    (antipode_convMul_id : toConv antipode * toConv LinearMap.id = 1)
-- the antipode is both a left and right inverse to the identity when multiplication is convoliution
    (id_convMul_antipode : toConv LinearMap.id * toConv antipode = 1) :
    HopfAlgebra R A where
  antipode := antipode
  mul_antipode_rTensor_comul := by simpa using! congr(($antipode_convMul_id).ofConv)
  mul_antipode_lTensor_comul := by simpa using! congr(($id_convMul_antipode).ofConv)

/-- Upgrade a commutative bialgebra to a Hopf algebra by specifying the antipode `A →ₐ[R] A`
with appropriate conditions. -/
noncomputable abbrev ofAlgHom [CommSemiring R] [CommSemiring A] [Bialgebra R A]
    (antipode : A →ₐ[R] A)
    (mul_antipode_rTensor_comul :
      ((Algebra.TensorProduct.lift antipode (.id R A) fun _ ↦ Commute.all _).comp
        (Bialgebra.comulAlgHom R A)) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A))
    (mul_antipode_lTensor_comul :
      (Algebra.TensorProduct.lift (.id R A) antipode fun _ _ ↦ Commute.all _ _).comp
        (Bialgebra.comulAlgHom R A) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)) :
    HopfAlgebra R A :=
  ofConvInverse antipode.toLinearMap
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_rTensor_comul).toLinearMap))
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_lTensor_comul).toLinearMap))
-- * If `A` is commutative then `antipode` is an algebra homomorphism.


def comm_hom [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] : A →ₐ[R] A where
  toFun := antipode R
  map_one' := antipode_one
  map_mul' := sorry
  map_zero' := LinearMap.map_zero (antipode R)
  map_add' x y := LinearMap.map_add (antipode R) x y
  commutes' r := by sorry


/-

If `A` is commutative, then the antipode is a ring homomorhpism:


It's already a linear map by definition

S(x * y) =

-/




/-





`LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit`

m ∘ τ ∘ (S ⊗ S) is a right convolution inverse of m


This implies that S ∘ μ = μ ∘ τ ∘ (S ⊗ S), that S is an antihomomorphism
-/
end HopfAlgebra
