/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Tactic.NoncommRing
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Observable

/-!

# Jordan algebra structure on self-adjoint elements

Quantum observables live in `selfAdjoint A` for `A` the (typically non-commutative) algebra of
bounded operators, but the raw associative product `a * b` of two self-adjoint elements is
generally not self-adjoint itself — `star (a * b) = b * a`, which equals `a * b` only when `a`
and `b` commute. What survives is the *symmetrized* product
$$ a \circ b := a * b + b * a, $$
the anticommutator. It is self-adjoint for any self-adjoint `a`, `b` (commuting or not), it is
manifestly commutative, and — the substantive fact — it satisfies the Jordan identity, the weak
associativity law that lets one recover much of the algebraic structure of quantum mechanics
(spectral theory, order, the observable ladder in `OVERVIEW.md`) without ever multiplying two
non-commuting observables together. This is the historically earlier (Jordan–von Neumann–Wigner,
1934) route to the same territory that full associative multiplication reaches, and the more
minimal one: it only ever uses the symmetric product.

Mathlib already has the abstract axioms for this in `Mathlib.Algebra.Jordan.Basic`
(`IsJordan`/`IsCommJordan`, stated for a bare `Mul` satisfying the Jordan axioms) together with
their canonical source of examples, `SymAlg` (`Mathlib.Algebra.Symmetrized`): symmetrizing the
product of any associative ring by `a ↦ ½(ab + ba)` makes it a commutative Jordan ring, *provided*
`2` is invertible. We instead use the unscaled anticommutator `a * b + b * a`, which needs no such
hypothesis and — since the Jordan identity is homogeneous in `∘`, so invariant under a global
rescaling of the product — satisfies exactly the same axioms.

We do not give `selfAdjoint A` a plain top-level `Mul` instance for this product: when `A` is
commutative, mathlib already equips `selfAdjoint A` with the *ordinary* product (`selfAdjoint`'s
`NonUnitalCommRing` instance), and `a ∘ b = 2 * (a * b) ≠ a * b` there in general, so a global
instance would silently create a diamond. Instead the `Mul`/`CommMagma`/`IsCommJordan` instances
below are `scoped` to the `selfAdjoint` namespace: `open scoped selfAdjoint` (or `open
selfAdjoint`) opts in to them exactly where the Jordan product, rather than the ordinary one, is
wanted.

## Main definitions

- `selfAdjoint.jordanMul` : the anticommutator `a * b + b * a`, landing back in `selfAdjoint A`.
- `selfAdjoint.jordanMul_comm` : the Jordan product is commutative.
- `selfAdjoint.jordanMul_add_left`/`jordanMul_add_right` : the Jordan product distributes over `+`.
- `selfAdjoint.instMul`/`instCommMagma`/`instIsCommJordan` (all `scoped`) : the Jordan product
  makes `selfAdjoint A` a commutative Jordan ring in mathlib's sense.
- `Observable.jordanMul` : the same product, spelled for `Observable A := selfAdjoint A`.

-/

@[expose] public section

namespace selfAdjoint

variable {A : Type*} [Ring A] [StarRing A]

/-- The Jordan (symmetrized) product of two self-adjoint elements: the anticommutator
`a ∘ b := a * b + b * a`. Self-adjoint regardless of whether `a` and `b` commute, since
`star (a * b + b * a) = star b * star a + star a * star b = b * a + a * b`. -/
def jordanMul (a b : selfAdjoint A) : selfAdjoint A :=
  ⟨(a : A) * (b : A) + (b : A) * (a : A), by
    rw [mem_iff, star_add, star_mul, star_mul, star_val_eq, star_val_eq, add_comm]⟩

@[simp]
theorem val_jordanMul (a b : selfAdjoint A) :
    ((jordanMul a b : selfAdjoint A) : A) = (a : A) * (b : A) + (b : A) * (a : A) :=
  rfl

/-- The Jordan product is commutative. -/
theorem jordanMul_comm (a b : selfAdjoint A) : jordanMul a b = jordanMul b a :=
  Subtype.ext (add_comm _ _)

/-- The Jordan product distributes over addition in its right argument. -/
theorem jordanMul_add_right (a b c : selfAdjoint A) :
    jordanMul a (b + c) = jordanMul a b + jordanMul a c := by
  apply Subtype.ext
  show (a : A) * ((b : A) + c) + ((b : A) + c) * a = _
  simp only [val_jordanMul, AddSubgroup.coe_add]
  noncomm_ring

/-- The Jordan product distributes over addition in its left argument. -/
theorem jordanMul_add_left (a b c : selfAdjoint A) :
    jordanMul (a + b) c = jordanMul a c + jordanMul b c := by
  rw [jordanMul_comm (a + b) c, jordanMul_comm a c, jordanMul_comm b c]
  exact jordanMul_add_right c a b

/-- The Jordan identity: `∘`-multiplication by `a` and by `a ∘ a` commute, i.e.
`(a ∘ b) ∘ (a ∘ a) = a ∘ (b ∘ (a ∘ a))`. This is the "weak associativity" law that survives
symmetrization of a possibly non-commutative, associative product. -/
theorem jordanMul_jordanMul_jordanMul_self (a b : selfAdjoint A) :
    jordanMul (jordanMul a b) (jordanMul a a) = jordanMul a (jordanMul b (jordanMul a a)) := by
  apply Subtype.ext
  simp only [val_jordanMul]
  noncomm_ring

/-- The Jordan product on `selfAdjoint A`, scoped to avoid clashing with the ordinary-product
`Mul (selfAdjoint A)` instance mathlib provides when `A` is commutative (there, `a ∘ b = 2 * a * b`
disagrees with `a * b`). Bring this into scope with `open scoped selfAdjoint`. -/
scoped instance instMul : Mul (selfAdjoint A) := ⟨jordanMul⟩

@[simp]
theorem mul_def (a b : selfAdjoint A) : a * b = jordanMul a b := rfl

/-- The Jordan product is commutative. -/
scoped instance instCommMagma : CommMagma (selfAdjoint A) where
  mul_comm := jordanMul_comm

/-- The Jordan product makes `selfAdjoint A` a commutative Jordan ring, in the sense of mathlib's
`IsCommJordan`: this is the connection from the abstract axioms in `Mathlib.Algebra.Jordan.Basic`
to the self-adjoint elements of an associative `StarRing`. -/
scoped instance instIsCommJordan : IsCommJordan (selfAdjoint A) where
  lmul_comm_rmul_rmul := jordanMul_jordanMul_jordanMul_self

end selfAdjoint

/-- The Jordan product is available on `Observable A` with no extra work: since
`Observable A := selfAdjoint A` is an `abbrev`, `selfAdjoint.jordanMul` applies to observables
verbatim, once the ambient `A` also carries the ring and star-ring structure this file assumes
(on top of the bare `AddGroup`/`StarAddMonoid` that `Observable` itself needs). -/
abbrev Observable.jordanMul {A : Type*} [Ring A] [StarRing A] (a b : Observable A) :
    Observable A :=
  selfAdjoint.jordanMul a b
