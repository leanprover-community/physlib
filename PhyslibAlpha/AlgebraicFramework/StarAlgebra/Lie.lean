/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.NoncommRing
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Jordan

/-!

# Lie structure on observables

Dually to the Jordan product `a ∘ b := a * b + b * a` of `StarAlgebra/Jordan.lean`, which
symmetrizes the associative product of two self-adjoint elements, the *antisymmetric* part of the
same product is self-adjoint once corrected by a factor of `i`:
$$ \mathrm{star}(ab - ba) = b a - a b = -(ab - ba), $$
so `ab - ba` is *skew*-adjoint, and multiplying a skew-adjoint element by `i` (or any purely
imaginary scalar) makes it self-adjoint. This gives the observable Lie bracket
$$ ⁅a, b⁆ := -(i / 2) (ab - ba), $$
the (negative, half of the) imaginary part of `a * b`. Together, the Jordan product and the Lie
bracket are the symmetric and antisymmetric halves of the raw associative product: `2 * (a * b) =
(a ∘ b) + 2 i ⁅a, b⁆`, `mul_decomposition` below. The bracket measures noncommutativity of the two
observables and, as a real Lie algebra, governs infinitesimal unitary dynamics (Heisenberg's
equation of motion is literally `dȧ/dt = ⁅H, a⁆` for a suitably normalized Hamiltonian `H`).

## Why these hypotheses (and no more)

Unlike the Jordan product, the bracket cannot be stated over a bare `[Ring A] [StarRing A]`: it
genuinely needs to *scale* by the complex number `-i/2`, so `A` must at least carry a compatible
action of `ℂ` respecting the star operation, i.e. `[Module ℂ A] [StarModule ℂ A]`. This is far
below the old `OperatorAlgebra A` bundle (a complete, ordered, C⋆-normed algebra): no norm,
completeness, or order enters anywhere in this file. Only `leibniz_bracket` (and the `LieRing`
instance packaging it) and `bracket_smul` (and the `LieAlgebra` instance packaging it) need scalar
multiplication by `ℂ` to interact with the ring product of `A` itself — moving the constant scalar
`-i/2` across a product `a * (c • b) = c • (a * b) = (c • a) * b` — which is exactly the content of
`[SMulCommClass ℂ A A] [IsScalarTower ℂ A A]`. Every other lemma, including the definition of the
bracket itself, needs nothing beyond `[Module ℂ A] [StarModule ℂ A]`, so those two extra instances
are added only on the declarations that use them rather than on the whole file (mirroring this
codebase's `omit [...] in` idiom for the reverse situation, where a lemma needs *less* than the
ambient section: see `isSelfAdjoint_mul_iff_commute` below, which needs no `ℂ`-module structure at
all).

As in `StarAlgebra/Jordan.lean`, the product-like structure (`Bracket`, `LieRing`, `LieAlgebra`) is
kept `scoped` to the `selfAdjoint` namespace rather than made a global instance, in case mathlib or
downstream code ever registers a competing Lie bracket on `selfAdjoint A` (e.g. via the ordinary
commutator when `A` itself is already a Lie ring). `open scoped selfAdjoint` opts in.

## Main definitions

- `selfAdjoint.lieMul` : the Lie bracket `-(i / 2) (ab - ba)`, landing back in `selfAdjoint A`.
- `selfAdjoint.isSelfAdjoint_mul_iff_commute` : `a * b` is self-adjoint iff `a` and `b` commute.
- `selfAdjoint.mul_decomposition` : `a * b` splits into its Jordan and Lie parts.
- `selfAdjoint.instBracket`/`instLieRing`/`instLieAlgebra` (all `scoped`) : `selfAdjoint A` is a
  real Lie algebra under `lieMul`.
- `Observable.lieMul` : the same bracket, spelled for `Observable A := selfAdjoint A`.

-/

@[expose] public section

namespace selfAdjoint

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]

/-! ## The Lie bracket -/

/-- The Lie (antisymmetrized) product of two self-adjoint elements: `-(i / 2) (ab - ba)`, the
negative half of the imaginary part of `a * b`. Self-adjoint regardless of whether `a` and `b`
commute: `ab - ba` is skew-adjoint since `star (ab - ba) = star b * star a - star a * star b =
ba - ab = -(ab - ba)`, and scaling a skew-adjoint element by the purely imaginary `-i/2` restores
self-adjointness. -/
noncomputable def lieMul (a b : selfAdjoint A) : selfAdjoint A :=
  ⟨(-(Complex.I / 2)) • ((a : A) * b - (b : A) * a), by
    rw [mem_iff, star_smul, star_sub, star_mul, star_mul, a.property.star_eq, b.property.star_eq]
    have hI : star (-(Complex.I / 2) : ℂ) = Complex.I / 2 := by
      simp [Complex.ext_iff]
      norm_num
    rw [hI]
    module⟩

@[simp]
theorem val_lieMul (a b : selfAdjoint A) :
    ((lieMul a b : selfAdjoint A) : A) = (-(Complex.I / 2)) • ((a : A) * b - (b : A) * a) :=
  rfl

omit [Module ℂ A] [StarModule ℂ A] in
/-- The product of two self-adjoint elements is self-adjoint exactly when they commute. This is a
fact about `A` alone; it does not involve the Lie bracket (or any complex scalar structure) at
all, unlike every other lemma in this file. -/
theorem isSelfAdjoint_mul_iff_commute (a b : selfAdjoint A) :
    IsSelfAdjoint ((a : A) * (b : A)) ↔ Commute (a : A) (b : A) := by
  rw [isSelfAdjoint_iff, star_mul, a.property.star_eq, b.property.star_eq, commute_iff_eq, eq_comm]

/-- The ambient product of two self-adjoint elements splits into its Jordan and Lie parts:
`2 (a * b) = (a ∘ b) + 2 i ⁅a, b⁆`, or equivalently (avoiding division by clearing denominators on
both the Jordan and Lie side) as stated here. -/
theorem mul_decomposition (a b : selfAdjoint A) :
    (a : A) * b =
      (2 : ℂ)⁻¹ • (jordanMul a b : A) + Complex.I • ((lieMul a b : selfAdjoint A) : A) := by
  rw [val_jordanMul, val_lieMul, smul_smul]
  have h2 : Complex.I * -(Complex.I / 2) = (2 : ℂ)⁻¹ := by
    rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I]
    norm_num
  rw [h2]
  module

/-! ## Antisymmetry and additivity -/

/-- The Lie bracket is antisymmetric. -/
theorem lieMul_swap (a b : selfAdjoint A) : lieMul a b = -lieMul b a := by
  apply Subtype.ext
  simp only [val_lieMul, AddSubgroup.coe_neg]
  module

theorem lieMul_add_left (a b c : selfAdjoint A) :
    lieMul (a + b) c = lieMul a c + lieMul b c := by
  apply Subtype.ext
  simp only [val_lieMul, AddSubgroup.coe_add]
  rw [show ((a : A) + b) * c - (c : A) * ((a : A) + b) =
      ((a : A) * c - (c : A) * a) + ((b : A) * c - (c : A) * b) by noncomm_ring, smul_add]

theorem lieMul_add_right (a b c : selfAdjoint A) :
    lieMul a (b + c) = lieMul a b + lieMul a c := by
  apply Subtype.ext
  simp only [val_lieMul, AddSubgroup.coe_add]
  rw [show (a : A) * ((b : A) + c) - ((b : A) + c) * a =
      ((a : A) * b - (b : A) * a) + ((a : A) * c - (c : A) * a) by noncomm_ring, smul_add]

theorem lieMul_self (a : selfAdjoint A) : lieMul a a = 0 := by
  apply Subtype.ext
  simp [val_lieMul]

/-- The Lie bracket on `selfAdjoint A`, scoped (like `selfAdjoint.instMul` in `Jordan.lean`) so it
never silently competes with some other bracket mathlib or downstream code might register on
`selfAdjoint A`. Bring this into scope with `open scoped selfAdjoint`. -/
noncomputable scoped instance instBracket : Bracket (selfAdjoint A) (selfAdjoint A) := ⟨lieMul⟩

@[simp]
theorem bracket_def (a b : selfAdjoint A) : ⁅a, b⁆ = lieMul a b := rfl

theorem coe_bracket (a b : selfAdjoint A) :
    ((⁅a, b⁆ : selfAdjoint A) : A) = (-(Complex.I / 2)) • ((a : A) * b - (b : A) * a) :=
  val_lieMul a b

/-! ## Lie ring -/

section LieRing

variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

theorem leibniz_bracket (a b c : selfAdjoint A) :
    ⁅a, ⁅b, c⁆⁆ = ⁅⁅a, b⁆, c⁆ + ⁅b, ⁅a, c⁆⁆ := by
  apply Subtype.ext
  simp only [bracket_def, val_lieMul, AddSubgroup.coe_add]
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    ← smul_sub, ← smul_sub, ← smul_sub, smul_smul, smul_smul, smul_smul, ← smul_add]
  congr 1
  noncomm_ring

/-- Together with the Lie ring axioms, `selfAdjoint A` becomes a Lie ring under `lieMul`: the
`ℂ`-scalar structure is only used to move the fixed scalar `-i/2` across products
(`SMulCommClass`/`IsScalarTower`), never to invoke a `LieAlgebra` instance on `A` itself, so this
does not need `A` to literally be a `ℂ`-algebra in mathlib's bundled sense. -/
noncomputable scoped instance instLieRing : LieRing (selfAdjoint A) where
  add_lie := lieMul_add_left
  lie_add := lieMul_add_right
  lie_self := lieMul_self
  leibniz_lie := leibniz_bracket

/-! ## Real Lie algebra -/

theorem bracket_smul (t : ℝ) (a b : selfAdjoint A) :
    ⁅a, t • b⁆ = t • ⁅a, b⁆ := by
  apply Subtype.ext
  simp only [bracket_def, val_lieMul, selfAdjoint.val_smul, ← Complex.coe_smul]
  rw [mul_smul_comm, smul_mul_assoc]
  module

/-- The Lie bracket is compatible with the real scalar structure. -/
noncomputable scoped instance instLieAlgebra : LieAlgebra ℝ (selfAdjoint A) where
  toModule := inferInstance
  lie_smul := bracket_smul

end LieRing

/-! ## Elementary identities -/

theorem bracket_one_right (a : selfAdjoint A) : ⁅a, (1 : selfAdjoint A)⁆ = 0 := by
  apply Subtype.ext
  rw [coe_bracket]
  simp

theorem bracket_one_left (a : selfAdjoint A) : ⁅(1 : selfAdjoint A), a⁆ = 0 := by
  apply Subtype.ext
  rw [coe_bracket]
  simp

end selfAdjoint

/-- The Lie bracket is available on `Observable A` with no extra work: since `Observable A :=
selfAdjoint A` is an `abbrev`, `selfAdjoint.lieMul` applies to observables verbatim, once the
ambient `A` carries the ring, star-ring, and complex-module structure this file assumes (on top of
the bare `AddGroup`/`StarAddMonoid` that `Observable` itself needs). -/
noncomputable abbrev Observable.lieMul {A : Type*} [Ring A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] (a b : Observable A) : Observable A :=
  selfAdjoint.lieMul a b
