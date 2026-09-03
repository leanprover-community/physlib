/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# The double centralizer theorem

Mathlib's Jacobson density theorem (`Module.Finite.toModuleEnd_moduleEnd_surjective`) says that for
a semisimple `R`-module `M` which is finite over its endomorphism ring `D = Module.End R M`, the
natural map `R → Module.End D M` is **surjective**. This file sharpens that to a **bijection** for
a faithful such `M`, so that `R` is recovered from its action: `R ≃+* Module.End D M`.

The half that is missing upstream is injectivity, and injectivity is exactly faithfulness of `M`.
Faithfulness is not automatic, but it is automatic in the case the structure theory cares about:
a nontrivial module over a **simple** ring is faithful, because the elements killing `M` form a
two-sided ideal not containing `1`. So over a simple ring every simple module finite over `D`
gives `R ≃+* Module.End D M`, which is the Wedderburn presentation of a simple ring in
module-internal form -- no ambient base field is involved, only finiteness over `D`.

The last section restates the theorem in the form a representation uses: for a subalgebra `A` of
`Module.End K N` over which `N` is semisimple, the double centralizer of `A` *inside*
`Module.End K N` is `A` itself. Here faithfulness is automatic, `A` being a set of endomorphisms,
so only Mathlib's surjectivity is needed; the centralizer `A'` is the ring of `A`-linear
endomorphisms of `N`, and an element of `A''` is exactly an `A'`-linear endomorphism. This is a
different theorem from `TauCeti.centralizer_centralizer` of
`TauCeti/Algebra/CentralSimple/Centralizer.lean`, which computes the double centralizer of a
*central simple* subalgebra of a central simple algebra by a dimension count; neither hypothesis
implies the other.

## Main results

* `TauCeti.faithfulSMul_of_isSimpleRing`: a nontrivial module over a simple ring is faithful.
* `TauCeti.toModuleEnd_moduleEnd_bijective`: **the double centralizer theorem**. For a faithful
  semisimple module `M` finite over `D = Module.End R M`, the map `R → Module.End D M` is bijective;
  `TauCeti.ringEquivEndEnd` packages it as a ring isomorphism, and
  `TauCeti.algEquivEndEnd` as an algebra isomorphism over a compatible base ring.
* `TauCeti.toModuleEnd_moduleEnd_bijective_of_isSimpleRing`: the specialization to a simple module
  over a simple ring, where faithfulness is automatic.
* `TauCeti.exists_smul_eq_of_linearIndependent`: the Jacobson-Chevalley form of density. Over a
  simple module, a single element of `R` carries any `D`-linearly independent family to an
  arbitrary family of targets.
* `TauCeti.finite_end_of_smulCommClass`: finiteness over a base ring acting compatibly supplies the
  finiteness hypothesis density needs.
* `TauCeti.algEquivEndEndOfIsSimpleRing`: the finite-dimensional-algebra form, where the finiteness
  hypothesis is supplied by finiteness over a commutative base ring acting compatibly.
* `TauCeti.centralizer_centralizer_of_isSemisimpleModule`: the **subalgebra form**. A subalgebra
  `A` of `Module.End K N` over which `N` is semisimple, `N` finite over `Module.End A N`, is its
  own double centralizer inside `Module.End K N`.
* `TauCeti.centralizer_centralizer_range`: the same statement for the image of a semisimple
  algebra, the form a representation supplies. The image, not the algebra itself, is what the
  double centralizer returns, since the representation need not be faithful.

## Implementation notes

The finiteness hypothesis is `Module.Finite (Module.End R M) M`, finiteness over the endomorphism
ring itself, rather than finite-dimensionality over an unrelated base ring. That is the hypothesis
density actually needs; when a base ring `K` acting compatibly is available, the `K`-scalars are
themselves `R`-linear endomorphisms, so `Module.Finite K M` gives it by
`TauCeti.finite_end_of_smulCommClass`.

A faithful simple module makes `R` a *primitive* ring, not necessarily a simple one, so
`TauCeti.toModuleEnd_moduleEnd_bijective` is genuinely more general than its simple-ring corollary.
It is also stated for a merely semisimple `M`, which is all that Mathlib's surjectivity needs.

The main theorem is named after the Mathlib lemma it sharpens,
`Module.Finite.toModuleEnd_moduleEnd_surjective`, keeping the surjective/bijective pair in step; the
roadmap calls the same statement `toModuleEnd_bijective`.

## References

This implements the Layer 3 target `toModuleEnd_bijective` of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
together with its Jacobson-Chevalley corollary. The subalgebra form is what Layer 8 of the
[Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md)
calls "a case of the double-centralizer theorem for the semisimple algebra `ℂ[Sₙ]`". See T. Y. Lam,
*A First Course in Noncommutative Rings*, GTM 131, Chapter 4, and N. Jacobson, *Basic Algebra II*,
Chapter 4.
-/

public section

namespace TauCeti

open Module

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-! ### Faithfulness over a simple ring -/

/-- A nontrivial module over a simple ring is faithful: the elements of `R` killing `M` are the
kernel of a ring homomorphism out of `R`, a two-sided ideal not containing `1`, hence `⊥`. -/
theorem faithfulSMul_of_isSimpleRing [IsSimpleRing R] [Nontrivial M] : FaithfulSMul R M where
  eq_of_smul_eq_smul {_ _} h :=
    (Module.toModuleEnd (Module.End R M) M (S := R)).injective (LinearMap.ext h)

/-! ### The double centralizer theorem -/

section Density

variable (R M)

/-- **The double centralizer theorem.** Let `M` be a faithful semisimple `R`-module which is finite
over its endomorphism ring `D = Module.End R M`. Then the natural map `R → Module.End D M` is
bijective: `R` is exactly the ring of `D`-linear endomorphisms of `M`.

This sharpens Mathlib's `Module.Finite.toModuleEnd_moduleEnd_surjective` from surjectivity to
bijectivity; the extra input is faithfulness, which is what makes the map injective. -/
theorem toModuleEnd_moduleEnd_bijective [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] :
    Function.Bijective (Module.toModuleEnd (Module.End R M) M (S := R)) :=
  ⟨fun _ _ h ↦ eq_of_smul_eq_smul (α := M) fun m ↦ LinearMap.congr_fun h m,
    Module.Finite.toModuleEnd_moduleEnd_surjective⟩

/-- The double centralizer theorem as a ring isomorphism: a faithful semisimple module finite over
its endomorphism ring `D` identifies `R` with `Module.End D M`. -/
noncomputable def ringEquivEndEnd [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] :
    R ≃+* Module.End (Module.End R M) M :=
  RingEquiv.ofBijective _ (toModuleEnd_moduleEnd_bijective R M)

variable {R M}

@[simp]
theorem ringEquivEndEnd_apply [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (r : R) (m : M) :
    ringEquivEndEnd R M r m = r • m := by
  simp [ringEquivEndEnd]

@[simp]
theorem ringEquivEndEnd_symm_smul [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (f : Module.End (Module.End R M) M) (m : M) :
    (ringEquivEndEnd R M).symm f • m = f m := by
  rw [← ringEquivEndEnd_apply ((ringEquivEndEnd R M).symm f) m, RingEquiv.apply_symm_apply]

variable (R M)

/-- The double centralizer isomorphism as an isomorphism of `K`-algebras, for a commutative base
ring `K` acting on `M` compatibly with `R`. -/
noncomputable def algEquivEndEnd (K : Type*) [CommSemiring K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] :
    R ≃ₐ[K] Module.End (Module.End R M) M :=
  AlgEquiv.ofRingEquiv (f := ringEquivEndEnd R M) fun k ↦ by
    ext m
    rw [ringEquivEndEnd_apply, algebraMap_smul, Module.algebraMap_end_apply]

variable {R M}

@[simp]
theorem algEquivEndEnd_apply (K : Type*) [CommSemiring K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (r : R) (m : M) :
    algEquivEndEnd R M K r m = r • m :=
  ringEquivEndEnd_apply r m

@[simp]
theorem algEquivEndEnd_symm_smul (K : Type*) [CommSemiring K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (f : Module.End (Module.End R M) M) (m : M) :
    (algEquivEndEnd R M K).symm f • m = f m := by
  rw [← algEquivEndEnd_apply K ((algEquivEndEnd R M K).symm f) m, AlgEquiv.apply_symm_apply]

variable (R M)

/-- **The double centralizer theorem for a simple ring.** Over a simple ring every simple module is
automatically faithful, so a simple module finite over its endomorphism ring `D` presents `R` as
`Module.End D M`. This is Wedderburn's theorem for a simple ring, stated without reference to any
base ring. -/
theorem toModuleEnd_moduleEnd_bijective_of_isSimpleRing [IsSimpleRing R] [IsSimpleModule R M]
    [Module.Finite (Module.End R M) M] :
    Function.Bijective (Module.toModuleEnd (Module.End R M) M (S := R)) :=
  have := IsSimpleModule.nontrivial R M
  have := faithfulSMul_of_isSimpleRing (R := R) (M := M)
  toModuleEnd_moduleEnd_bijective R M

end Density

/-! ### Jacobson-Chevalley density -/

/-- **Jacobson-Chevalley density.** For a simple module `M` finite over `D = Module.End R M`, a
`D`-linearly independent family in `M` can be carried to an arbitrary family of targets by a single
scalar from `R`.

Linear independence is essential: a `D`-linear relation among the `v i` is inherited by the
`r • v i`, so the targets could not be arbitrary. -/
theorem exists_smul_eq_of_linearIndependent [IsSimpleModule R M]
    [Module.Finite (Module.End R M) M] {ι : Type*} {v : ι → M}
    (hv : LinearIndependent (Module.End R M) v) (w : ι → M) :
    ∃ r : R, ∀ i, r • v i = w i := by
  classical
  -- `v` is a basis of its span, so it has the prescribed values under some `D`-linear map on that
  -- span; extend that map to all of `M` and let density realize the extension by a scalar.
  obtain ⟨f, hf⟩ := ((Basis.span hv).constr ℕ w).exists_extend
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) f
  refine ⟨r, fun i ↦ ?_⟩
  have hvi : f (v i) = w i := by
    -- `f` agrees on the span with `(Basis.span hv).constr ℕ w`, which sends the `i`-th basis
    -- vector to `w i`; that basis vector is `v i` viewed inside the span.
    have h := LinearMap.congr_fun hf ((Basis.span hv) i)
    rw [Basis.constr_basis] at h
    simpa using h
  simpa [hvi] using LinearMap.congr_fun hr (v i)

/-! ### The finite-dimensional algebra case -/

/-- Finiteness over a base ring `K` whose action on `M` commutes with the `R`-action gives the
finiteness hypothesis density needs: the `K`-scalars are themselves `R`-linear endomorphisms of `M`,
so `M` is finite over `Module.End R M` along the tower `K → Module.End R M → M`. -/
theorem finite_end_of_smulCommClass (K : Type*) [Semiring K] [Module K M] [SMulCommClass R K M]
    [Module.Finite K M] : Module.Finite (Module.End R M) M :=
  Module.Finite.of_restrictScalars_finite K (Module.End R M) M

variable (R M)

/-- **The double centralizer theorem for a finite module over a simple algebra.** If `R` is a
simple `K`-algebra and `M` a simple `R`-module which is finite as a `K`-module, then `M` presents
`R` as the algebra of `D`-linear endomorphisms of `M`, where `D = Module.End R M`. This is the form
in which Layer 3 of the roadmap is consumed by the central-simple theory. -/
noncomputable def algEquivEndEndOfIsSimpleRing (K : Type*) [CommSemiring K] [Algebra K R]
    [Module K M] [IsScalarTower K R M] [Module.Finite K M] [IsSimpleRing R] [IsSimpleModule R M] :
    R ≃ₐ[K] Module.End (Module.End R M) M :=
  have := IsSimpleModule.nontrivial R M
  have := faithfulSMul_of_isSimpleRing (R := R) (M := M)
  have := finite_end_of_smulCommClass (R := R) (M := M) K
  algEquivEndEnd R M K

variable {R M}

@[simp]
theorem algEquivEndEndOfIsSimpleRing_apply (K : Type*) [CommSemiring K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [Module.Finite K M] [IsSimpleRing R] [IsSimpleModule R M] (r : R)
    (m : M) :
    algEquivEndEndOfIsSimpleRing R M K r m = r • m :=
  have := IsSimpleModule.nontrivial R M
  have := faithfulSMul_of_isSimpleRing (R := R) (M := M)
  have := finite_end_of_smulCommClass (R := R) (M := M) K
  algEquivEndEnd_apply K r m

@[simp]
theorem algEquivEndEndOfIsSimpleRing_symm_smul (K : Type*) [CommSemiring K] [Algebra K R]
    [Module K M] [IsScalarTower K R M] [Module.Finite K M] [IsSimpleRing R] [IsSimpleModule R M]
    (f : Module.End (Module.End R M) M) (m : M) :
    (algEquivEndEndOfIsSimpleRing R M K).symm f • m = f m := by
  rw [← algEquivEndEndOfIsSimpleRing_apply K ((algEquivEndEndOfIsSimpleRing R M K).symm f) m,
    AlgEquiv.apply_symm_apply]

/-! ### The double centralizer of a subalgebra of an endomorphism algebra -/

section EndSubalgebra

variable {K : Type*} [CommRing K] {N : Type*} [AddCommGroup N] [Module K N]
  (A : Subalgebra K (Module.End K N))

/-- An `A`-linear endomorphism of `N`, for `A` a `K`-subalgebra of `Module.End K N`, commutes with
every element of `A`, so its restriction of scalars lies in the centralizer of `A`. -/
private theorem restrictScalars_mem_centralizer (g : Module.End A N) :
    g.restrictScalars K ∈ Subalgebra.centralizer K (A : Set (Module.End K N)) := by
  refine (Subalgebra.mem_centralizer_iff K).2 fun a ha => ?_
  ext m
  exact (g.map_smul ⟨a, ha⟩ m).symm

/-- **The double centralizer theorem inside an endomorphism algebra.** Let `A` be a `K`-subalgebra
of `Module.End K N`, and suppose `N` is semisimple as an `A`-module and finite over
`Module.End A N`. Then `A` is its own double centralizer: an endomorphism commuting with everything
that commutes with `A` already lies in `A`.

The inclusion `A ≤ A''` is formal (`Subalgebra.le_centralizer_centralizer`); the content is the
reverse one, which is Jacobson density. The centralizer `A'` is the ring of `A`-linear
endomorphisms of `N`, so an element of `A''` is an `A'`-linear endomorphism, and density writes
every such endomorphism as the action of an element of `A`.

Finiteness is over `Module.End A N`, the hypothesis density actually needs; a caller with a finite
`K`-module `N` gets it from `TauCeti.finite_end_of_smulCommClass`. -/
theorem centralizer_centralizer_of_isSemisimpleModule [Module.Finite (Module.End A N) N]
    [IsSemisimpleModule A N] :
    Subalgebra.centralizer K
        (Subalgebra.centralizer K (A : Set (Module.End K N)) : Set (Module.End K N)) = A := by
  refine le_antisymm (fun x hx => ?_) (Subalgebra.le_centralizer_centralizer K)
  rw [Subalgebra.mem_centralizer_iff] at hx
  -- `x` commutes with every `A`-linear endomorphism, so it is `A'`-linear.
  let f : Module.End (Module.End A N) N :=
    { toFun := x
      map_add' := x.map_add
      map_smul' := fun g m => by
        -- Evaluating the commutation of `x` with `g.restrictScalars K` at `m` gives
        -- `x (g m) = g (x m)`, which is the required `A'`-linearity once the scalar action of
        -- `Module.End ↥A N` on `N` is `Module.End.smul_def` and the restriction of scalars is
        -- `LinearMap.coe_restrictScalars`.
        have h := congrArg (fun t : Module.End K N => t m)
          (hx _ (restrictScalars_mem_centralizer A g))
        simpa only [Module.End.smul_def, RingHom.id_apply, Module.End.mul_apply,
          LinearMap.coe_restrictScalars] using h.symm }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := N) f
  have hx' : x = (a : Module.End K N) := by
    ext m
    exact (congrArg (fun t : Module.End (Module.End A N) N => t m) ha).symm
  exact hx' ▸ a.2

/-- **The double centralizer theorem for the image of a semisimple algebra.** The image of a
semisimple `K`-algebra `S` in `Module.End K N`, for a finite `K`-module `N`, is its own double
centralizer.

The image is a quotient of `S`, hence semisimple, so `N` is a semisimple module over it and
`TauCeti.centralizer_centralizer_of_isSemisimpleModule` applies, its finiteness hypothesis coming
from `TauCeti.finite_end_of_smulCommClass`. It is the image and not `S` that is recovered: the
representation `S → Module.End K N` need not be injective. -/
theorem centralizer_centralizer_range [Module.Finite K N] {S : Type*} [Ring S] [Algebra K S]
    [IsSemisimpleRing S] (ρ : S →ₐ[K] Module.End K N) :
    Subalgebra.centralizer K
        (Subalgebra.centralizer K (ρ.range : Set (Module.End K N)) : Set (Module.End K N)) =
      ρ.range := by
  have : IsSemisimpleRing ρ.range :=
    RingHom.isSemisimpleRing_of_surjective ρ.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  have : IsSemisimpleModule ρ.range N := IsSemisimpleRing.isSemisimpleModule
  have : Module.Finite (Module.End ρ.range N) N := finite_end_of_smulCommClass (R := ρ.range) K
  exact centralizer_centralizer_of_isSemisimpleModule _

end EndSubalgebra

end TauCeti
