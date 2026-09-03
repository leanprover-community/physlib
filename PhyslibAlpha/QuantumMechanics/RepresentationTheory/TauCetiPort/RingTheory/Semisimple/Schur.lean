/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Schur's lemma for simple modules

This file packages the two forms of Schur's lemma used by the semisimple-algebra development.

For simple modules over an arbitrary ring, Mathlib proves that a linear map is either bijective or
zero (`LinearMap.bijective_or_eq_zero`). Consequently the entire hom group vanishes exactly when the
two modules are not linearly equivalent. When an equivalence does exist, Mathlib's
`LinearEquiv.arrowCongrAddEquiv` identifies the hom group with either endomorphism ring by
composition; no separate construction is needed here.

Over an algebraically closed field `k`, a domain algebra that is integral over `k` is `k` itself.
The proof uses Mathlib's theorem that the algebra map from an algebraically closed field into such
an algebra is bijective; a finite-dimensional division algebra is the special case that the roadmap
names, integrality there coming from finite dimensionality. The same collapse for the endomorphism
ring of a finite-dimensional simple module is
Mathlib's `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`, packaged here as an algebra
equivalence.

Both forms are then read as statements about dimensions, for a `k`-algebra `A` acting on modules
that are `k`-modules compatibly: the hom space between inequivalent simple modules has dimension
`0`, and between equivalent finite-dimensional simple modules it is a line. Transporting a hom
space along an isomorphism of its target, `TauCeti.homCongrRight`, is what carries the endomorphism
computation to an arbitrary equivalent target.

## Main definitions

* `TauCeti.homCongrRight`: isomorphic `A`-modules have `k`-isomorphic hom spaces out of a fixed
  module. This is `LinearEquiv.congrRight` for a noncommutative `A`, with the auxiliary scalars
  `k` supplying the linear structure that `A` cannot; it is assembled from Mathlib's
  `LinearMap.compRight`.

## Main results

* `TauCeti.hom_eq_zero_of_isEmpty_linearEquiv`: every map between inequivalent simple modules is
  zero.
* `TauCeti.subsingleton_linearMap_iff_isEmpty_linearEquiv`: the corresponding characterization of
  the whole hom group.
* `TauCeti.nontrivial_linearMap_iff_nonempty_linearEquiv`: two simple modules are equivalent exactly
  when their hom group is nontrivial.
* `TauCeti.nonempty_algEquiv_self_of_isIntegral`: a domain algebra over an algebraically closed
  field that is integral over that field is isomorphic to it as an algebra, with
  `TauCeti.nonempty_algEquiv_self_of_finiteDimensional_divisionRing` the finite-dimensional
  division algebra special case, also available under the name the roadmap pins,
  `TauCeti.algEquiv_self_of_finiteDimensional_divisionRing`.
* `TauCeti.endAlgEquivSelfOfIsSimpleModule`: the endomorphism ring of a finite-dimensional simple
  module over an algebraically closed field collapses to that field, canonically, as the inverse
  of the structure map; `TauCeti.nonempty_end_algEquiv_self_of_isSimpleModule` is its existence
  form.
* `TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv` and
  `TauCeti.finrank_linearMap_eq_one_of_nonempty_linearEquiv`: the two forms of Schur's lemma in
  dimensions, with `TauCeti.finiteDimensional_linearMap_of_isSimpleModule` recording that the hom
  space is finite-dimensional either way.

## References

This implements Layer 1, "Schur, assembled", of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See N. Jacobson, *Basic Algebra II*, Chapter 3, or T. Y. Lam, *A First Course in Noncommutative
Rings*, Chapter 1.
-/

public section

namespace TauCeti

universe u v w

/-! ### Maps between simple modules -/

section SimpleModules

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [IsSimpleModule R M] [IsSimpleModule R N]

/-- **Schur's lemma, vanishing form.** A linear map between simple modules is zero if the two
modules are not linearly equivalent.

The `IsEmpty` hypothesis is the constructive form of saying that no equivalence exists. -/
theorem hom_eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (M ≃ₗ[R] N)) (f : M →ₗ[R] N) :
    f = 0 := by
  rcases f.bijective_or_eq_zero with hf | hf
  · exact (h.false (LinearEquiv.ofBijective f hf)).elim
  · exact hf

/-- The hom group between simple modules is a subsingleton if the modules are not linearly
equivalent. -/
theorem subsingleton_linearMap_of_isEmpty_linearEquiv (h : IsEmpty (M ≃ₗ[R] N)) :
    Subsingleton (M →ₗ[R] N) :=
  ⟨fun f g ↦ sub_eq_zero.mp (hom_eq_zero_of_isEmpty_linearEquiv h (f - g))⟩

/-- The hom group between two simple modules is a subsingleton exactly when the modules are not
linearly equivalent. -/
theorem subsingleton_linearMap_iff_isEmpty_linearEquiv :
    Subsingleton (M →ₗ[R] N) ↔ IsEmpty (M ≃ₗ[R] N) := by
  constructor
  · intro h
    let := h
    exact ⟨fun e ↦ by
      have hzero : e.toLinearMap = 0 := Subsingleton.elim _ _
      have := IsSimpleModule.nontrivial R M
      exact e.toLinearMap.ne_zero_of_injective e.injective hzero⟩
  · exact subsingleton_linearMap_of_isEmpty_linearEquiv

/-- The hom group between two simple modules is nontrivial exactly when the modules are linearly
equivalent. This is the existence form of Schur's lemma. -/
theorem nontrivial_linearMap_iff_nonempty_linearEquiv :
    Nontrivial (M →ₗ[R] N) ↔ Nonempty (M ≃ₗ[R] N) := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_linearMap_iff_isEmpty_linearEquiv,
    not_isEmpty_iff]

end SimpleModules

/-! ### Domain algebras over algebraically closed fields -/

section IsAlgClosed

variable {k : Type u} {D : Type v} [Field k] [IsAlgClosed k]

section Domain

variable [Ring D] [IsDomain D] [Algebra k D]

/-- A domain algebra over an algebraically closed field `k` that is integral over `k` is `k`
itself, as an isomorphism of algebras.

Mathlib proves that the algebra map from an algebraically closed field to such an algebra is
bijective; this packages that bijection as an algebra equivalence. -/
theorem nonempty_algEquiv_self_of_isIntegral [Algebra.IsIntegral k D] : Nonempty (D ≃ₐ[k] k) :=
  ⟨(AlgEquiv.ofBijective (Algebra.ofId k D)
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩

end Domain

/-- A finite-dimensional division algebra over an algebraically closed field is the field itself,
as an isomorphism of algebras. Finite dimensionality supplies integrality, so this is the
special case of `nonempty_algEquiv_self_of_isIntegral` that the semisimple-algebra development
uses. -/
theorem nonempty_algEquiv_self_of_finiteDimensional_divisionRing [DivisionRing D] [Algebra k D]
    [FiniteDimensional k D] : Nonempty (D ≃ₐ[k] k) :=
  nonempty_algEquiv_self_of_isIntegral

/-- The roadmap pins the previous theorem under this name; it is available under both. -/
alias algEquiv_self_of_finiteDimensional_divisionRing :=
  nonempty_algEquiv_self_of_finiteDimensional_divisionRing

end IsAlgClosed

/-! ### Endomorphisms of a simple module over an algebraically closed field -/

section SimpleEnd

variable {k : Type u} {A : Type v} {S : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]

/-- **Schur's lemma over an algebraically closed field.** The endomorphism ring of a
finite-dimensional simple module over a `k`-algebra is the field `k` itself.

Mathlib's `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` proves that every such
endomorphism is a scalar; this packages that bijection as an algebra equivalence. Finite
dimensionality is needed: an infinite-dimensional simple module can have a larger division
endomorphism ring.

The equivalence involves no choices: it is the inverse of the structure map `k → End A S`, which
Schur's lemma proves bijective. Its inverse is therefore `algebraMap` on the nose, and the scalar
attached to an endomorphism is characterized by
`TauCeti.endAlgEquivSelfOfIsSimpleModule_smul`. -/
noncomputable def endAlgEquivSelfOfIsSimpleModule : Module.End A S ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (Module.End A S))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)).symm

/-- The inverse of the Schur equivalence is the structure map of the endomorphism algebra. -/
@[simp]
theorem endAlgEquivSelfOfIsSimpleModule_symm_apply (c : k) :
    (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).symm c =
      algebraMap k (Module.End A S) c :=
  (rfl)

/-- The scalar attached to an endomorphism of a simple module is the scalar it acts by. -/
@[simp]
theorem endAlgEquivSelfOfIsSimpleModule_smul (f : Module.End A S) (s : S) :
    endAlgEquivSelfOfIsSimpleModule (k := k) f • s = f s := by
  conv_rhs =>
    rw [← (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).symm_apply_apply f]
  rw [endAlgEquivSelfOfIsSimpleModule_symm_apply, Module.algebraMap_end_apply]

/-- The existence statement of Schur's lemma over an algebraically closed field, for consumers
that only need to know that some algebra equivalence exists. -/
theorem nonempty_end_algEquiv_self_of_isSimpleModule : Nonempty (Module.End A S ≃ₐ[k] k) :=
  ⟨endAlgEquivSelfOfIsSimpleModule⟩

end SimpleEnd

/-! ### Transporting a hom space along an isomorphism of the target -/

section CongrRight

variable (k : Type*) {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
variable {S : Type*} [AddCommMonoid S] [Module A S]
variable {N : Type*} [AddCommMonoid N] [Module A N] [Module k N] [IsScalarTower k A N]
variable {P : Type*} [AddCommMonoid P] [Module A P] [Module k P] [IsScalarTower k A P]

/-- **Isomorphic targets give isomorphic hom spaces.**  An `A`-linear isomorphism `e : N ≃ₗ[A] P`
carries `S →ₗ[A] N` to `S →ₗ[A] P` by postcomposition, `k`-linearly.

This is `LinearEquiv.congrRight` with the auxiliary scalars `k` in place of a commutativity
assumption on `A`: since `A` is not assumed commutative the hom spaces are not `A`-modules, and
`k`, acting on the targets compatibly with `A`, supplies the linear structure instead.  The two
directions are `LinearMap.compRight`. -/
def homCongrRight (e : N ≃ₗ[A] P) : (S →ₗ[A] N) ≃ₗ[k] (S →ₗ[A] P) :=
  LinearEquiv.ofLinearMap (LinearMap.compRight (M := S) k (e : N →ₗ[A] P))
    (LinearMap.compRight (M := S) k (e.symm : P →ₗ[A] N))
    (by ext f s; simp) (by ext f s; simp)

@[simp]
theorem homCongrRight_apply (e : N ≃ₗ[A] P) (f : S →ₗ[A] N) (s : S) :
    homCongrRight k (S := S) e f s = e (f s) :=
  (rfl)

@[simp]
theorem homCongrRight_symm_apply (e : N ≃ₗ[A] P) (f : S →ₗ[A] P) (s : S) :
    (homCongrRight k (S := S) e).symm f s = e.symm (f s) :=
  (rfl)

end CongrRight

/-! ### Schur's lemma in dimension form -/

section Vanishing

variable {k A S N : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module A S] [IsSimpleModule A S]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N] [IsSimpleModule A N]

/-- **Schur's lemma, vanishing form, in dimensions.**  Between inequivalent simple modules the
hom space is trivial, hence of dimension zero. -/
theorem finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] N)) :
    Module.finrank k (S →ₗ[A] N) = 0 := by
  have : Subsingleton (S →ₗ[A] N) := subsingleton_linearMap_of_isEmpty_linearEquiv h
  exact Module.finrank_zero_of_subsingleton

/-- The hom space between inequivalent simple modules is finite-dimensional, being trivial. -/
theorem finiteDimensional_linearMap_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] N)) :
    FiniteDimensional k (S →ₗ[A] N) := by
  have : Subsingleton (S →ₗ[A] N) := subsingleton_linearMap_of_isEmpty_linearEquiv h
  exact Module.Finite.of_surjective (0 : k →ₗ[k] (S →ₗ[A] N)) fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

end Vanishing

section SchurDimension

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [IsSimpleModule A N]

omit [IsSimpleModule A N] in
/-- **Schur's lemma over an algebraically closed field, in dimensions.**  Between equivalent
finite-dimensional simple modules the hom space is a line: every map is a scalar multiple of a
fixed isomorphism. -/
theorem finrank_linearMap_eq_one_of_nonempty_linearEquiv (e : S ≃ₗ[A] N) :
    Module.finrank k (S →ₗ[A] N) = 1 := by
  have hend : Module.finrank k (Module.End A S) = 1 := by
    rw [(endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  rw [← (homCongrRight k (S := S) e).finrank_eq]
  exact hend

/-- The hom space out of a finite-dimensional simple module into a simple module is
finite-dimensional: by Schur's lemma it is a line or trivial. -/
theorem finiteDimensional_linearMap_of_isSimpleModule : FiniteDimensional k (S →ₗ[A] N) := by
  by_cases h : Nonempty (S ≃ₗ[A] N)
  · have hend : FiniteDimensional k (S →ₗ[A] S) :=
      Module.Finite.equiv
        (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).toLinearEquiv.symm
    exact Module.Finite.equiv (homCongrRight k (S := S) h.some)
  · exact finiteDimensional_linearMap_of_isEmpty_linearEquiv (not_nonempty_iff.mp h)

end SchurDimension

end TauCeti
