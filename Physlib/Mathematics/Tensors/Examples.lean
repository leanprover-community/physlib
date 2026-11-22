/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Physlib.Mathematics.Tensors.IndexMaps

/-!

# Examples of colored tensors

Tests of the colors of tensors, of the group action on tensors and of `simp` at written-out colors.

## i. Overview

Each test fails if its guarantee breaks. The tests run on small species. `toy` has one kind with
vector space `ℝ`, standing for a Lorentz vector `v^μ` and a covector `α_μ`. `two` has two kinds
with the same vector space `ℝ`. `scale` has the vector space `ℝ` with a unit `r` acting by `r`, so
a vector `v ↦ r v` and a covector `α ↦ r⁻¹ α`. `units` and `circle` have the vector space `ℂ` with
the trivial action of `Scaling` and `Phase`, structures around the nonzero complex numbers and the
phases. `unitsRaw` takes `ℂˣ` itself. `plane` has the vector space
`Fin 2 → ℝ` with Mathlib's standard basis.

Section A checks that a vector and a covector have different types, so that one is rejected where
the other is expected. Section B records what the types do not check. They separate variance, not
kinds, so two kinds with the same vector space are not told apart, and a model with two such kinds
gives them different vector spaces. Section C checks the group action. For a structure around a
group of numbers `z • T` is the action of the species on tensors, on functions into tensors and on
pairs, and is rejected on linear maps into tensors (C.1). Over `ℂˣ` itself only the action on
tensors is the action of the species. The group does not act on a product of tensors through one
factor (C.2). Section D checks that a map at one index
is an intertwining map, which the copy of a vector to a covector is not. Section E checks that plain
`simp` closes goals at written-out colors such as `⟨κ, up⟩`, with the `simp` lemmas of `Color.lean`
and `Species.lean` and `Representation.Equiv.cast_apply`.

## ii. Key results

- `up`, `down` : the colors of the one kind of index with each variance.
- `toy` : a species with the vector space `ℝ` at its one kind.
- `two` : a species with two kinds that have the same vector space `ℝ`.
- `scale` : a species on which a unit `r` acts on vectors by `r`, so on covectors by `r⁻¹`.
- `scaleCopy` : the copy `α := v` of a vector to a covector, which does not commute with the group.
- `Scaling`, `Phase` : structures around `ℂˣ` and `Circle`, on which Mathlib defines no
  multiplication.
- `units`, `circle` : species on which `Scaling` and `Phase` act trivially.
- `unitsRaw` : a species on which `ℂˣ` itself acts trivially.
- `plane` : a species with the vector space `Fin 2 → ℝ` and Mathlib's standard basis, with
  `plane_basisW` : its basis is `Pi.basisFun`.

## iii. Table of contents

- A. Vectors and covectors
- B. Two kinds with the same vector space
- C. The group action
  - C.1. A group of numbers
  - C.2. A product of tensors
- D. Maps that change a color
- E. `simp` at written-out colors

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace Tensor.Examples

open Species TensorProduct

/-!

## A. Vectors and covectors

The species `toy` has the vector space `ℝ` at its one kind. A vector `v^μ` lies in `ℝ` and a
covector `α_μ` in `Module.Dual ℝ ℝ`, so Lean rejects one where the other is expected. The tests
reject a vector as a covector and a covector as a vector, for single vectors, inside `pure` and for
tensors, when all definitions unfold.

-/

/-- The species with the vector space `ℝ` at its one kind and the trivial action of `Unit`. -/
def toy : Species ℝ Unit Unit where
  W _ := ℝ
  repW _ := Representation.trivial ℝ Unit ℝ

/-- The color of variance `.up`. -/
abbrev up : Color Unit := ⟨(), .up⟩

/-- The color of variance `.down`. -/
abbrev down : Color Unit := ⟨(), .down⟩

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (v : toy.V up) : toy.V down := by
  with_unfolding_all exact v

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (w : toy.V down) : toy.V up := by
  with_unfolding_all exact w

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (v : toy.V up) : Tensor toy ![down] := by
  with_unfolding_all exact toy.pure fun | 0 => v

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (w : toy.V down) : Tensor toy ![up] := by
  with_unfolding_all exact toy.pure fun | 0 => w

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (t : Tensor toy ![up]) : Tensor toy ![down] := by
  with_unfolding_all exact t

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (s : Tensor toy ![down]) : Tensor toy ![up] := by
  with_unfolding_all exact s

/-!

## B. Two kinds with the same vector space

The species `two` has the kinds `true` and `false`, both with the vector space `ℝ`. The framework
separates variance, not kinds. The vector space of a color is `W κ` or its dual, so a vector of one
kind is accepted at the other. A model with two kinds on the same components must give them
different vector spaces `W κ`.

-/

/-- Two kinds `true` and `false` with the same vector space `ℝ`. -/
def two : Species ℝ Unit Bool where
  W _ := ℝ
  repW _ := Representation.trivial ℝ Unit ℝ

example (v : two.V ⟨true, .up⟩) : two.V ⟨false, .up⟩ := v

/-!

## C. The group action

### C.1. A group of numbers

The nonzero complex numbers `ℂˣ` and the phases `Circle` are groups of numbers, and Mathlib lets a
number act on every complex vector space by multiplication. The species `units` and `circle` take
`Scaling` and `Phase`, one-field structures around these groups, on which Mathlib defines no
multiplication. Their actions are trivial, so they differ from the multiplication by `z`. The tests
check that `z • T` is `tensorRep` on tensors, pointwise on functions into tensors, on families
`Fin 2 → Tensor` and on pairs, and that Mathlib's lemmas on actions rewrite it. They check that
`z • f` on a linear map into tensors is rejected, that a number `u : ℂˣ` still multiplies, and that
an element of `Circle` enters `Phase` only through its constructor.

The species `unitsRaw` takes `ℂˣ` itself. The action instances of `Tensor` have priority over
Mathlib's, so `z • T` is the action of the species, also through the instance `DistribMulAction`.
A test fails if any of these instances is found after Mathlib's. The types do not check the rest.
On a function or a linear map into tensors `z • φ` is the multiplication by `z`.

-/

/-- The nonzero complex numbers as the group of a species, a structure around `ℂˣ` on which
Mathlib defines no multiplication of vectors. -/
structure Scaling where
  /-- The element of `ℂˣ`. -/
  val : ℂˣ

/-- `Scaling` has the elements of `ℂˣ`. -/
def Scaling.equiv : Scaling ≃ ℂˣ := ⟨Scaling.val, Scaling.mk, fun _ => rfl, fun _ => rfl⟩

/-- `Scaling` is a group as `ℂˣ` is. -/
instance : CommGroup Scaling := Scaling.equiv.commGroup

/-- The phases as the group of a species, a structure around `Circle` on which Mathlib defines no
multiplication of vectors. -/
structure Phase where
  /-- The element of `Circle`. -/
  val : Circle

/-- `Phase` has the elements of `Circle`. -/
def Phase.equiv : Phase ≃ Circle := ⟨Phase.val, Phase.mk, fun _ => rfl, fun _ => rfl⟩

/-- `Phase` is a group as `Circle` is. -/
noncomputable instance : CommGroup Phase := Phase.equiv.commGroup

/-- The nonzero complex numbers acting trivially on `ℂ`. -/
def units : Species ℂ Scaling Unit where
  W _ := ℂ
  repW _ := Representation.trivial ℂ Scaling ℂ

/-- The phases acting trivially on `ℂ`. -/
noncomputable def circle : Species ℂ Phase Unit where
  W _ := ℂ
  repW _ := Representation.trivial ℂ Phase ℂ

/-- The nonzero complex numbers `ℂˣ` themselves acting trivially on `ℂ`. -/
def unitsRaw : Species ℂ ℂˣ Unit where
  W _ := ℂ
  repW _ := Representation.trivial ℂ ℂˣ ℂ

section Copy

variable (z w : Scaling) (t s : Tensor units ![up]) (φ : ℕ → Tensor units ![up])
  (ψ : Fin 2 → Tensor units ![up])

example : z • t = units.tensorRep ![up] z t := rfl

example : z • φ = fun n => units.tensorRep ![up] z (φ n) := rfl

example : z • ψ = fun i => units.tensorRep ![up] z (ψ i) := rfl

example : z • (t, s) = (units.tensorRep ![up] z t, units.tensorRep ![up] z s) := rfl

/--
error: failed to synthesize instance of type class
  SMul Scaling (ℂ →ₗ[ℂ] Tensor units ![up])
-/
#guard_msgs (substring := true) in
example : SMul Scaling (ℂ →ₗ[ℂ] Tensor units ![up]) := inferInstance

example : (z * w) • t = z • w • t := by rw [mul_smul]

example : (z * w) • φ = z • w • φ := by rw [mul_smul]

example : z • (t + s) = z • t + z • s := by rw [smul_add]

example : z • (0 : Tensor units ![up]) = 0 := by rw [smul_zero]

example (u : ℂˣ) : u • t = (u : ℂ) • t := rfl

/--
error: failed to synthesize instance of type class
  SMul Scaling (⨂[ℂ] (i : Fin 1), units.V (![up] i))
-/
#guard_msgs (substring := true) in
example : SMul Scaling (⨂[ℂ] i : Fin 1, units.V (![up] i)) := inferInstance

end Copy

section Phase

variable (z w : Phase) (t s : Tensor circle ![up]) (φ : ℕ → Tensor circle ![up])
  (ψ : Fin 2 → Tensor circle ![up])

example : z • t = circle.tensorRep ![up] z t := rfl

example : z • φ = fun n => circle.tensorRep ![up] z (φ n) := rfl

example : z • ψ = fun i => circle.tensorRep ![up] z (ψ i) := rfl

example : z • (t, s) = (circle.tensorRep ![up] z t, circle.tensorRep ![up] z s) := rfl

/--
error: failed to synthesize instance of type class
  SMul Phase (ℂ →ₗ[ℂ] Tensor circle ![up])
-/
#guard_msgs (substring := true) in
example : SMul Phase (ℂ →ₗ[ℂ] Tensor circle ![up]) := inferInstance

example : (z * w) • t = z • w • t := by rw [mul_smul]

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (v : Circle) : Phase := v

example (v : Circle) : (⟨v⟩ : Phase) • t = circle.tensorRep ![up] ⟨v⟩ t := rfl

end Phase

section Raw

variable (z : ℂˣ) (t : Tensor unitsRaw ![up]) (φ : ℕ → Tensor unitsRaw ![up])
  (f : ℂ →ₗ[ℂ] Tensor unitsRaw ![up])

example : z • t = unitsRaw.tensorRep ![up] z t := rfl

example : ℂˣ × Tensor unitsRaw ![up] := by
  fail_if_success have : z • t = (z : ℂ) • t := rfl
  exact (z, t)

example : (inferInstance : DistribMulAction ℂˣ (Tensor unitsRaw ![up])).toSMul.smul z t =
    unitsRaw.tensorRep ![up] z t := rfl

example : z • φ = fun n => (z : ℂ) • φ n := rfl

example : z • f = (z : ℂ) • f := rfl

end Raw

/-!

### C.2. A product of tensors

`SMulCommClass k G` is not an instance, so a group element `g` does not act on a product
`T ⊗ₜ U` through `T`. The test checks that `SMul G (Tensor S d ⊗[k] Tensor S d)` is not found.

-/

/--
error: failed to synthesize instance of type class
  SMul G (Tensor S d ⊗[k] Tensor S d)
-/
#guard_msgs (substring := true) in
example {k G : Type} [RCLike k] [Group G] (S : Species k G Unit)
    (d : Fin 1 → Color Unit) : SMul G (Tensor S d ⊗[k] Tensor S d) :=
  inferInstance

/-!

## D. Maps that change a color

On `scale` the copy `scaleCopy` of a vector to a covector is linear but does not commute with the
group. `intertwiningMapAt` takes an intertwining map, a linear map with the proof that it commutes
with the group. It rejects the linear map `scaleCopy`, for which no such proof exists on `scale`,
and accepts a map `f` that is an intertwining map.

-/

/-- The species with the vector space `ℝ`, on which a unit `r` acts by `r`. It acts on the linear
forms at `down` by `r⁻¹`. -/
def scale : Species ℝ ℝˣ Unit where
  W _ := ℝ
  repW _ := Representation.ofDistribMulAction ℝ ℝˣ ℝ

/-- The copy `α := v` of a vector to a covector, `v ↦ (u ↦ v u)`. It does not commute with the
group. -/
def scaleCopy : scale.V up →ₗ[ℝ] scale.V down :=
  LinearMap.mul ℝ ℝ

example : ¬ ∀ (g : ℝˣ) (x : scale.V up),
    scaleCopy (scale.rep up g x) = scale.rep down g (scaleCopy x) := by
  intro h
  have := LinearMap.congr_fun (h (Units.mk0 2 two_ne_zero) (1 : ℝ)) (1 : ℝ)
  change (2 : ℝ) * 1 * 1 = (1 : ℝ) * ((2 : ℝ)⁻¹ * 1) at this
  norm_num at this

noncomputable example (f : (scale.rep up).IntertwiningMap (scale.rep down)) :
    (scale.tensorRep ![up]).IntertwiningMap (scale.tensorRep ![down]) := by
  fail_if_success
    exact scale.intertwiningMapAt 0 scaleCopy fun x hx => absurd (Subsingleton.elim x 0) hx
  exact scale.intertwiningMapAt 0 f fun x hx => absurd (Subsingleton.elim x 0) hx

/-!

## E. `simp` at written-out colors

At a written-out color `⟨κ, up⟩` the goal has the vector space `S.W κ` where a lemma has
`S.V ⟨κ, up⟩`. The goals on the contraction, on `dualEquiv` and on the components of `plane` at
`up` close by plain `simp` only if the `simp` lemmas of `Species.lean` carry `no_index` where
needed. The goals on the dual of a written-out color need the `simp` lemmas of `Color.lean`, and
the goals on `S.cast` need `Representation.Equiv.cast_apply`. The last goal of the first group is
the action on a pure tensor, by `smul_pure`. The first group is for a general species `S` with a
basis, the last two tests are for `plane`.

-/

section Simp

variable {k G K : Type} [RCLike k] [Group G] {basisIdx : K → Type} [∀ κ, Fintype (basisIdx κ)]
  [∀ κ, DecidableEq (basisIdx κ)] (S : Species k G K) [S.HasBasis basisIdx] (κ : K)

example (μ : basisIdx κ) : S.basis (⟨κ, .down⟩ : Color K).dual μ = S.basisW κ μ := by simp

example (μ : basisIdx κ) :
    S.basis (⟨κ, .up⟩ : Color K).dual μ = (S.basisW κ).dualBasis μ := by simp

example (v : S.V ⟨κ, .up⟩) (μ : basisIdx κ) :
    (S.basis ⟨κ, .up⟩).repr v μ = (S.basisW κ).repr v μ := by simp

example (w : S.V ⟨κ, .down⟩) (μ : basisIdx κ) :
    (S.basis ⟨κ, .down⟩).repr w μ = w (S.basis ⟨κ, .up⟩ μ) := by simp

example (x : S.V ⟨κ, .up⟩) (y : S.V ⟨κ, .down⟩) : S.contr ⟨κ, .up⟩ (x ⊗ₜ y) = y x := by simp

example (x : S.V ⟨κ, .down⟩) (y : S.V ⟨κ, .up⟩) : S.contr ⟨κ, .down⟩ (x ⊗ₜ y) = x y := by simp

example (w w' : S.V (⟨κ, .up⟩ : Color K).dual) (v : S.V ⟨κ, .up⟩) :
    (w + w') v = w v + w' v := by simp

example (α : S.V ⟨κ, .down⟩) (u : S.V ⟨κ, .up⟩) : S.dualEquiv ⟨κ, .up⟩ α u = α u := by simp

example (a : Color K) (p : a = ⟨κ, .up⟩) (x : S.V a) :
    S.cast p x = cast (congrArg S.V p) x := by simp

example {ι : Type} (c : ι → Color K) (g : G) (f : Π i, S.V (c i)) :
    g • S.pure f = S.pure fun i => S.rep (c i) g (f i) := by simp

end Simp

/-- A species with the vector space `Fin 2 → ℝ`, as an abbrev, so that `simp` sees its vector
space. -/
abbrev plane : Species ℝ Unit Unit where
  W _ := Fin 2 → ℝ
  repW _ := Representation.trivial ℝ Unit (Fin 2 → ℝ)

/-- Mathlib's standard basis `Pi.basisFun` of `plane`. -/
noncomputable instance : plane.HasBasis fun _ => Fin 2 := ⟨fun _ => Pi.basisFun ℝ (Fin 2)⟩

/-- The basis of `plane` is `Pi.basisFun`. `simp` does not look into the instance, so a model
states its basis as a `simp` lemma. -/
@[simp] lemma plane_basisW : plane.basisW () = Pi.basisFun ℝ (Fin 2) := rfl

example (v : plane.V up) (i : Fin 2) : (plane.basis up).repr v i = v i := by simp

example (w : plane.V down) (i : Fin 2) : (plane.basis down).repr w i = w (Pi.single i 1) := by
  simp

end Tensor.Examples
