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
$$ a \circ b := \tfrac12(a * b + b * a), $$
the normalized anticommutator. It is self-adjoint for any self-adjoint `a`, `b` (commuting or
not), it is
manifestly commutative, and — the substantive fact — it satisfies the Jordan identity, the weak
associativity law that lets one recover much of the algebraic structure of quantum mechanics
(spectral theory, order, the observable ladder in `OVERVIEW.md`) without ever multiplying two
non-commuting observables together. This is the historically earlier (Jordan–von Neumann–Wigner,
1934) route to the same territory that full associative multiplication reaches, and the more
minimal one: it only ever uses the symmetric product.

Mathlib already has the abstract axioms for this in `Mathlib.Algebra.Jordan.Basic`
(`IsJordan`/`IsCommJordan`, stated for a bare `Mul` satisfying the Jordan axioms). We install the
standard normalized product directly on `selfAdjoint A`; the real-module hypotheses provide the
factor `1/2`. Consequently every stronger realization, including a C⋆-algebra, inherits one and
the same Jordan multiplication instead of rebuilding a second product in a bridge file.

We do not give `selfAdjoint A` a plain top-level `Mul` instance for this product: when `A` is
commutative, mathlib already equips `selfAdjoint A` with the ordinary product. Instead the full
nonassociative-ring and Jordan structure below is scoped to `selfAdjoint`: `open scoped
selfAdjoint` opts in exactly where the Jordan product is wanted.

## Main definitions

- `selfAdjoint.jordanMul` : the normalized product `½(ab + ba)`, landing back in `selfAdjoint A`.
- `selfAdjoint.jordanMul_comm` : the Jordan product is commutative.
- `selfAdjoint.jordanMul_add_left`/`jordanMul_add_right` : the Jordan product distributes over `+`.
- `selfAdjoint.instMul`/`instCommMagma`/`instIsCommJordan` (all `scoped`) : the Jordan product
  makes `selfAdjoint A` a commutative Jordan ring in mathlib's sense.
- `Observable.jordanMul` : the same product, spelled for `Observable A := selfAdjoint A`.

-/

@[expose] public section

namespace selfAdjoint

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [StarModule ℝ A]

/-- The unnormalized anticommutator, retained as a low-level formula while `jordanMul` is the
canonical normalized Jordan product. -/
def anticommutator (a b : selfAdjoint A) : selfAdjoint A :=
  ⟨(a : A) * (b : A) + (b : A) * (a : A), by
    rw [mem_iff, star_add, star_mul, star_mul, star_val_eq, star_val_eq, add_comm]⟩

omit [Module ℝ A] [StarModule ℝ A] in
@[simp]
theorem coe_anticommutator (a b : selfAdjoint A) :
    ((anticommutator a b : selfAdjoint A) : A) = (a : A) * (b : A) + (b : A) * (a : A) :=
  rfl

/-- The normalized Jordan product of two self-adjoint elements,
`a ∘ b := ½(ab + ba)`. It is self-adjoint regardless of whether `a` and `b` commute, since
`star (a * b + b * a) = star b * star a + star a * star b = b * a + a * b`. -/
noncomputable def jordanMul (a b : selfAdjoint A) : selfAdjoint A :=
  (2 : ℝ)⁻¹ • anticommutator a b

@[simp]
theorem val_jordanMul (a b : selfAdjoint A) :
    ((jordanMul a b : selfAdjoint A) : A) =
      (2 : ℝ)⁻¹ • ((a : A) * (b : A) + (b : A) * (a : A)) :=
  rfl

/-- The Jordan product is commutative. -/
theorem jordanMul_comm (a b : selfAdjoint A) : jordanMul a b = jordanMul b a :=
  Subtype.ext <| by simp only [val_jordanMul, add_comm]

/-- The unit of the ambient algebra is a unit for the normalized Jordan product. -/
@[simp]
theorem one_jordanMul (a : selfAdjoint A) : jordanMul 1 a = a := by
  apply Subtype.ext
  change (2 : ℝ)⁻¹ • ((1 : A) * (a : A) + (a : A) * (1 : A)) = (a : A)
  rw [_root_.one_mul, _root_.mul_one, ← two_smul ℝ (a : A), smul_smul,
    inv_mul_cancel₀ (two_ne_zero), one_smul]

/-- The normalized Jordan product has the same unit in its right argument. -/
@[simp]
theorem jordanMul_one (a : selfAdjoint A) : jordanMul a 1 = a := by
  rw [jordanMul_comm, one_jordanMul]

/-- The Jordan product distributes over addition in its right argument. -/
theorem jordanMul_add_right (a b c : selfAdjoint A) :
    jordanMul a (b + c) = jordanMul a b + jordanMul a c := by
  apply Subtype.ext
  simp only [val_jordanMul, AddSubgroup.coe_add, mul_add, add_mul, smul_add]
  module

/-- The Jordan product distributes over addition in its left argument. -/
theorem jordanMul_add_left (a b c : selfAdjoint A) :
    jordanMul (a + b) c = jordanMul a c + jordanMul b c := by
  rw [jordanMul_comm (a + b) c, jordanMul_comm a c, jordanMul_comm b c]
  exact jordanMul_add_right c a b

private theorem anticommutator_smul_left [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (c : ℝ) (a b : selfAdjoint A) :
    anticommutator (c • a) b = c • anticommutator a b := by
  apply Subtype.ext
  simp only [coe_anticommutator, val_smul, mul_smul_comm, smul_mul_assoc, smul_add]

private theorem anticommutator_smul_right [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (a : selfAdjoint A) (c : ℝ) (b : selfAdjoint A) :
    anticommutator a (c • b) = c • anticommutator a b := by
  apply Subtype.ext
  simp only [coe_anticommutator, val_smul, mul_smul_comm, smul_mul_assoc, smul_add]

omit [Module ℝ A] [StarModule ℝ A] in
private theorem anticommutator_identity (a b : selfAdjoint A) :
    anticommutator (anticommutator a b) (anticommutator a a) =
      anticommutator a (anticommutator b (anticommutator a a)) := by
  apply Subtype.ext
  simp only [coe_anticommutator]
  noncomm_ring

/-- The Jordan identity: `∘`-multiplication by `a` and by `a ∘ a` commute, i.e.
`(a ∘ b) ∘ (a ∘ a) = a ∘ (b ∘ (a ∘ a))`. This is the "weak associativity" law that survives
symmetrization of a possibly non-commutative, associative product. -/
theorem jordanMul_jordanMul_jordanMul_self [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (a b : selfAdjoint A) :
    jordanMul (jordanMul a b) (jordanMul a a) = jordanMul a (jordanMul b (jordanMul a a)) := by
  simp only [jordanMul, anticommutator_smul_left, anticommutator_smul_right, smul_smul]
  congr 1
  exact anticommutator_identity a b

/-- The normalized Jordan product on `selfAdjoint A`, scoped to avoid clashing with the ordinary
product instance mathlib provides when `A` is commutative. -/
noncomputable scoped instance instMul : Mul (selfAdjoint A) := ⟨jordanMul⟩

@[simp]
theorem mul_def (a b : selfAdjoint A) : a * b = jordanMul a b := rfl

/-- Coercing the canonical Jordan product back to the ambient algebra gives the normalized
anticommutator. -/
theorem coe_mul (a b : selfAdjoint A) :
    ((a * b : selfAdjoint A) : A) =
      (2 : ℝ)⁻¹ • ((a : A) * (b : A) + (b : A) * (a : A)) :=
  val_jordanMul a b

/-- Real scalars pull out of the left argument of the normalized Jordan product. -/
theorem jordanMul_smul_left [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (c : ℝ) (a b : selfAdjoint A) : jordanMul (c • a) b = c • jordanMul a b := by
  apply Subtype.ext
  simp only [val_jordanMul, val_smul, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul]
  module

/-- Real scalars pull out of the right argument of the normalized Jordan product. -/
theorem jordanMul_smul_right [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (a : selfAdjoint A) (c : ℝ) (b : selfAdjoint A) :
    jordanMul a (c • b) = c • jordanMul a b := by
  rw [jordanMul_comm, jordanMul_smul_left, jordanMul_comm]

/-- Expanding one right-nested Jordan product produces a common factor `1 / 4` and a nested
unnormalized anticommutator. This is useful for associative calculations in concrete
realizations while keeping the normalized Jordan product canonical. -/
theorem jordanMul_jordanMul_right [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (a b x : selfAdjoint A) :
    jordanMul a (jordanMul b x) =
      ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • anticommutator a (anticommutator b x) := by
  simp only [jordanMul, anticommutator_smul_right, smul_smul]

section AlgebraStructure

variable [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
theorem jordanMul_zero (a : selfAdjoint A) : jordanMul a 0 = 0 := by
  apply Subtype.ext
  simp [val_jordanMul]

/-- The normalized product gives the self-adjoint part its canonical commutative,
nonassociative ring structure. -/
noncomputable scoped instance instNonUnitalNonAssocCommRing :
    NonUnitalNonAssocCommRing (selfAdjoint A) where
  __ := (inferInstance : AddCommGroup (selfAdjoint A))
  mul := jordanMul
  left_distrib := jordanMul_add_right
  right_distrib := jordanMul_add_left
  zero_mul a := (jordanMul_comm 0 a).trans (jordanMul_zero a)
  mul_zero := jordanMul_zero
  mul_comm := jordanMul_comm

/-- The canonical Jordan product is unital with the inherited self-adjoint unit. Bundling this as
`NonAssocCommRing` prevents stronger layers from carrying an unrelated `One` plus duplicated unit
laws. -/
noncomputable scoped instance instNonAssocRing : NonAssocRing (selfAdjoint A) :=
  NonAssocRing.mk (toNatCast := ⟨fun n => n • (1 : selfAdjoint A)⟩)
    (toIntCast := ⟨fun z => z • (1 : selfAdjoint A)⟩)
    one_jordanMul jordanMul_one
    (natCast_zero := by simp)
    (natCast_succ := by intro n; simp [add_nsmul])
    (intCast_ofNat := by
      intro n
      change (n : ℤ) • (1 : selfAdjoint A) = n • (1 : selfAdjoint A)
      simp)
    (intCast_negSucc := by
      intro n
      change (Int.negSucc n) • (1 : selfAdjoint A) = -((n + 1) • (1 : selfAdjoint A))
      simp)

/-- The coherent unital commutative nonassociative ring structure on the self-adjoint part. -/
noncomputable scoped instance instNonAssocCommRing : NonAssocCommRing (selfAdjoint A) where
  __ := instNonAssocRing
  mul_comm := jordanMul_comm

/-- Real scalar multiplication commutes with Jordan multiplication. -/
scoped instance instSMulCommClass : SMulCommClass ℝ (selfAdjoint A) (selfAdjoint A) where
  smul_comm c a b := (jordanMul_smul_right a c b).symm

/-- Real scalar multiplication is a tower over Jordan multiplication. -/
scoped instance instIsScalarTower : IsScalarTower ℝ (selfAdjoint A) (selfAdjoint A) where
  smul_assoc c a b := jordanMul_smul_left c a b

/-- The Jordan product makes `selfAdjoint A` a commutative Jordan ring, in the sense of mathlib's
`IsCommJordan`: this is the connection from the abstract axioms in `Mathlib.Algebra.Jordan.Basic`
to the self-adjoint elements of an associative `StarRing`. -/
scoped instance instIsCommJordan : IsCommJordan (selfAdjoint A) where
  lmul_comm_rmul_rmul := jordanMul_jordanMul_jordanMul_self

end AlgebraStructure

end selfAdjoint

/-- The Jordan product is available on `Observable A` with no extra work: since
`Observable A := selfAdjoint A` is an `abbrev`, `selfAdjoint.jordanMul` applies to observables
verbatim, once the ambient `A` also carries the ring and star-ring structure this file assumes
(on top of the bare `AddGroup`/`StarAddMonoid` that `Observable` itself needs). -/
noncomputable abbrev Observable.jordanMul {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [StarModule ℝ A] (a b : Observable A) :
    Observable A :=
  selfAdjoint.jordanMul a b
