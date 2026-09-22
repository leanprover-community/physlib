/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Observable
public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Quadratic.Fundamental

/-!
# Quadratic compression by Jordan projections

For an idempotent `p` in a real Jordan algebra, its quadratic representation `U p` is itself an
idempotent linear map.  This is the algebraic core of the Peirce-`1` compression.  The results
here deliberately make no positivity, norm, or order assertion: those require genuinely JB-level
input.

The elementary values `U_p(p) = p`, `U_p(1) = p`, and `U_p(q) = 0` for `p ∘ q = 0` are provided
by `Observable.lean`; this module builds the nontrivial operator-idempotence consequence without
duplicating them.
-/

@[expose] public section

namespace JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [Module ℝ E]

open scoped JordanAlgebra

/-! ## The Peirce polynomial -/

/-- If `p` is idempotent, multiplication by `p` obeys the Peirce polynomial
`2 L_p^3 - 3 L_p^2 + L_p = 0`.  This is a specialization of the polarized Jordan identity and
is the exact algebraic fact needed to make `U_p` an idempotent compression. -/
theorem IsJordanProjection.peirce_polynomial [IsCommJordan E] {p : E}
    (hp : IsJordanProjection p) (x : E) :
    (2 : ℝ) • (p * (p * (p * x))) - (3 : ℝ) • (p * (p * x)) + p * x = 0 := by
  have h := linearized_mul_sq p p x
  rw [hp, hp] at h
  let A : E := p * (p * (p * x))
  let B : E := p * (p * x)
  let C : E := p * x
  have h' : C = -(2 : ℝ) • A + B + (2 : ℝ) • B := by
    simpa only [A, B, C] using h
  change (2 : ℝ) • A - (3 : ℝ) • B + C = 0
  rw [h']
  module

/-! ## The Peirce-`1` compression -/

/-- The Peirce-`1` eigenspace of a Jordan projection: the fixed submodule of multiplication by
`p`.  This is purely algebraic; no order or norm structure is involved. -/
def IsJordanProjection.peirceOne [SMulCommClass ℝ E E] (p : E) : Submodule ℝ E :=
  LinearMap.ker (L p - LinearMap.id)

/-- Membership in the Peirce-`1` space is exactly the eigenvalue-one equation. -/
theorem IsJordanProjection.mem_peirceOne_iff [SMulCommClass ℝ E E] (p x : E) :
    x ∈ IsJordanProjection.peirceOne p ↔ p * x = x := by
  change (L p - (LinearMap.id : E →ₗ[ℝ] E)) x = 0 ↔ _
  simp only [LinearMap.sub_apply, LinearMap.id_apply, mulLeft_apply, sub_eq_zero]

/-- The Peirce-`0` eigenspace of a projection. -/
def IsJordanProjection.peirceZero [SMulCommClass ℝ E E] (p : E) : Submodule ℝ E :=
  LinearMap.ker (L p)

/-- Membership in the Peirce-`0` space is exactly annihilation by `p`. -/
theorem IsJordanProjection.mem_peirceZero_iff [SMulCommClass ℝ E E] (p x : E) :
    x ∈ IsJordanProjection.peirceZero p ↔ p * x = 0 := by
  change L p x = 0 ↔ _
  rfl

/-- The Peirce-`1/2` eigenspace of a projection.  The equation is written without division so it
works directly with the real linear-map structure. -/
def IsJordanProjection.peirceHalf [SMulCommClass ℝ E E] (p : E) : Submodule ℝ E :=
  LinearMap.ker ((2 : ℝ) • L p - LinearMap.id)

/-- Membership in the Peirce-`1/2` space is exactly `2 (p ∘ x) = x`. -/
theorem IsJordanProjection.mem_peirceHalf_iff [SMulCommClass ℝ E E] (p x : E) :
    x ∈ IsJordanProjection.peirceHalf p ↔ (2 : ℝ) • (p * x) = x := by
  change ((2 : ℝ) • L p - (LinearMap.id : E →ₗ[ℝ] E)) x = 0 ↔ _
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, mulLeft_apply,
    sub_eq_zero]

/-- The Peirce-`0` and Peirce-`1/2` spaces intersect only at zero. -/
theorem IsJordanProjection.disjoint_peirceZero_peirceHalf [SMulCommClass ℝ E E] (p : E) :
    Disjoint (IsJordanProjection.peirceZero p) (IsJordanProjection.peirceHalf p) := by
  refine Submodule.disjoint_def.mpr fun x hx₀ hxhalf => ?_
  have h₀ := (IsJordanProjection.mem_peirceZero_iff p x).mp hx₀
  have hhalf := (IsJordanProjection.mem_peirceHalf_iff p x).mp hxhalf
  rw [h₀] at hhalf
  simpa using hhalf.symm

/-- The Peirce-`0` and Peirce-`1` spaces intersect only at zero. -/
theorem IsJordanProjection.disjoint_peirceZero_peirceOne [SMulCommClass ℝ E E] (p : E) :
    Disjoint (IsJordanProjection.peirceZero p) (IsJordanProjection.peirceOne p) := by
  refine Submodule.disjoint_def.mpr fun x hx₀ hx₁ => ?_
  have h₀ := (IsJordanProjection.mem_peirceZero_iff p x).mp hx₀
  have h₁ := (IsJordanProjection.mem_peirceOne_iff p x).mp hx₁
  rw [h₀] at h₁
  simpa using h₁.symm

/-- The Peirce-`1/2` and Peirce-`1` spaces intersect only at zero. -/
theorem IsJordanProjection.disjoint_peirceHalf_peirceOne [SMulCommClass ℝ E E] (p : E) :
    Disjoint (IsJordanProjection.peirceHalf p) (IsJordanProjection.peirceOne p) := by
  refine Submodule.disjoint_def.mpr fun x hxhalf hx₁ => ?_
  have hhalf := (IsJordanProjection.mem_peirceHalf_iff p x).mp hxhalf
  have h₁ := (IsJordanProjection.mem_peirceOne_iff p x).mp hx₁
  rw [h₁] at hhalf
  have h : (2 : ℝ) • x - x = 0 := sub_eq_zero.mpr hhalf
  calc
    x = (2 : ℝ) • x - x := by module
    _ = 0 := h

/-- The three Peirce eigenspaces are jointly direct: a vanishing sum of a `0`, `1/2`, and `1`
eigenvector has all three summands equal to zero. -/
theorem IsJordanProjection.eq_zero_of_peirce_sum_eq_zero [SMulCommClass ℝ E E] (p : E)
    {x₀ xhalf x₁ : E} (hx₀ : x₀ ∈ IsJordanProjection.peirceZero p)
    (hxhalf : xhalf ∈ IsJordanProjection.peirceHalf p)
    (hx₁ : x₁ ∈ IsJordanProjection.peirceOne p) (hsum : x₀ + xhalf + x₁ = 0) :
    x₀ = 0 ∧ xhalf = 0 ∧ x₁ = 0 := by
  have h₀ := (IsJordanProjection.mem_peirceZero_iff p x₀).mp hx₀
  have hhalf := (IsJordanProjection.mem_peirceHalf_iff p xhalf).mp hxhalf
  have h₁ := (IsJordanProjection.mem_peirceOne_iff p x₁).mp hx₁
  have hpSum : p * xhalf + x₁ = 0 := by
    have h := congrArg (fun z : E => p * z) hsum
    simpa only [mul_add, h₀, h₁, zero_add, mul_zero] using h
  have hppSum : p * (p * xhalf) + x₁ = 0 := by
    have h := congrArg (fun z : E => p * z) hpSum
    simpa only [mul_add, h₁, zero_add, mul_zero] using h
  have hhalfP : (2 : ℝ) • (p * (p * xhalf)) = p * xhalf := by
    have h := congrArg (fun z : E => p * z) hhalf
    simpa only [mul_smul_comm] using h
  have hAB : p * xhalf = p * (p * xhalf) := by
    apply sub_eq_zero.mp
    calc
      p * xhalf - p * (p * xhalf) =
          (p * xhalf + x₁) - (p * (p * xhalf) + x₁) := by module
      _ = 0 := by rw [hpSum, hppSum]; module
  rw [← hAB] at hhalfP
  have hpxhalf : p * xhalf = 0 := by
    calc
      p * xhalf = (2 : ℝ) • (p * xhalf) - p * xhalf := by module
      _ = 0 := sub_eq_zero.mpr hhalfP
  have hxhalf : xhalf = 0 := by
    calc
      xhalf = (2 : ℝ) • (p * xhalf) := hhalf.symm
      _ = 0 := by rw [hpxhalf, smul_zero]
  have hx₁ : x₁ = 0 := by simpa only [hpxhalf, zero_add] using hpSum
  have hx₀ : x₀ = 0 := by simpa only [hxhalf, hx₁, add_zero] using hsum
  exact ⟨hx₀, hxhalf, hx₁⟩

/-- The algebraic Peirce-`0` component of `x` relative to `p`. -/
def IsJordanProjection.peirceZeroPart (p x : E) : E :=
  x - (3 : ℝ) • (p * x) + (2 : ℝ) • (p * (p * x))

/-- The algebraic Peirce-`1/2` component of `x` relative to `p`. -/
def IsJordanProjection.peirceHalfPart (p x : E) : E :=
  (4 : ℝ) • (p * x - p * (p * x))

/-- The Peirce-`0` component is annihilated by `p`. -/
theorem IsJordanProjection.mul_peirceZeroPart [SMulCommClass ℝ E E] [IsCommJordan E] {p : E}
    (hp : IsJordanProjection p) (x : E) : p * IsJordanProjection.peirceZeroPart p x = 0 := by
  simp only [IsJordanProjection.peirceZeroPart, mul_add, mul_sub, mul_smul_comm]
  let A₁ : E := p * x
  let A₂ : E := p * A₁
  let A₃ : E := p * A₂
  have hP := hp.peirce_polynomial x
  change A₁ - (3 : ℝ) • A₂ + (2 : ℝ) • A₃ = 0
  calc
    A₁ - (3 : ℝ) • A₂ + (2 : ℝ) • A₃ =
        (2 : ℝ) • A₃ - (3 : ℝ) • A₂ + A₁ := by module
    _ = 0 := by simpa only [A₁, A₂, A₃] using hP

/-- The algebraic zero component belongs to the Peirce-`0` subspace. -/
theorem IsJordanProjection.peirceZeroPart_mem [SMulCommClass ℝ E E] [IsCommJordan E] {p : E}
    (hp : IsJordanProjection p) (x : E) :
    IsJordanProjection.peirceZeroPart p x ∈ IsJordanProjection.peirceZero p :=
  (IsJordanProjection.mem_peirceZero_iff p _).mpr (hp.mul_peirceZeroPart x)

/-- The Peirce-`1/2` component has eigenvalue `1/2` for multiplication by `p`. -/
theorem IsJordanProjection.two_smul_mul_peirceHalfPart [SMulCommClass ℝ E E] [IsCommJordan E]
    {p : E} (hp : IsJordanProjection p) (x : E) :
    (2 : ℝ) • (p * IsJordanProjection.peirceHalfPart p x) =
      IsJordanProjection.peirceHalfPart p x := by
  rw [IsJordanProjection.peirceHalfPart, mul_smul_comm]
  let A₁ : E := p * x
  let A₂ : E := p * A₁
  let A₃ : E := p * A₂
  let P : E := (2 : ℝ) • A₃ - (3 : ℝ) • A₂ + A₁
  have hP : P = 0 := by
    simpa only [P, A₁, A₂, A₃] using hp.peirce_polynomial x
  simp only [mul_sub]
  change (2 : ℝ) • ((4 : ℝ) • (A₂ - A₃)) = (4 : ℝ) • (A₁ - A₂)
  apply sub_eq_zero.mp
  calc
    (2 : ℝ) • ((4 : ℝ) • (A₂ - A₃)) - (4 : ℝ) • (A₁ - A₂) = -(4 : ℝ) • P := by
      dsimp only [P]
      module
    _ = 0 := by rw [hP]; module

/-- The algebraic half component belongs to the Peirce-`1/2` subspace. -/
theorem IsJordanProjection.peirceHalfPart_mem [SMulCommClass ℝ E E] [IsCommJordan E] {p : E}
    (hp : IsJordanProjection p) (x : E) :
    IsJordanProjection.peirceHalfPart p x ∈ IsJordanProjection.peirceHalf p :=
  (IsJordanProjection.mem_peirceHalf_iff p _).mpr (hp.two_smul_mul_peirceHalfPart x)

/-- Every element has a canonical algebraic Peirce decomposition.  The three summands have
eigenvalues `0`, `1/2`, and `1` respectively; the `1` summand is `U_p x`. -/
theorem IsJordanProjection.peirce_decomposition [SMulCommClass ℝ E E] {p : E}
    (hp : IsJordanProjection p) (x : E) :
    IsJordanProjection.peirceZeroPart p x + IsJordanProjection.peirceHalfPart p x + U p x = x := by
  rw [IsJordanProjection.peirceZeroPart, IsJordanProjection.peirceHalfPart, quadRep_apply,
    jpow_two, hp]
  module

/-- Quadratic compression by a projection lands in the Peirce-`1` eigenspace. -/
theorem IsJordanProjection.mul_quadRep [SMulCommClass ℝ E E] [IsCommJordan E] {p : E}
    (hp : IsJordanProjection p) (x : E) : p * U p x = U p x := by
  rw [quadRep_apply, jpow_two, hp]
  let A₁ : E := p * x
  let A₂ : E := p * A₁
  let A₃ : E := p * A₂
  let P : E := (2 : ℝ) • A₃ - (3 : ℝ) • A₂ + A₁
  have hP : P = 0 := by
    simpa only [P, A₁, A₂, A₃] using hp.peirce_polynomial x
  simp only [mul_sub, mul_smul_comm]
  change (2 : ℝ) • A₃ - A₂ = (2 : ℝ) • A₂ - A₁
  apply sub_eq_zero.mp
  calc
    (2 : ℝ) • A₃ - A₂ - ((2 : ℝ) • A₂ - A₁) = P := by
      dsimp only [P]
      module
    _ = 0 := hP

/-- The `U_p` summand in `peirce_decomposition` belongs to the Peirce-`1` subspace. -/
theorem IsJordanProjection.quadRep_mem_peirceOne [SMulCommClass ℝ E E] [IsCommJordan E] {p : E}
    (hp : IsJordanProjection p) (x : E) : U p x ∈ IsJordanProjection.peirceOne p :=
  (IsJordanProjection.mem_peirceOne_iff p _).mpr (hp.mul_quadRep x)

/-- Quadratic compression fixes every Peirce-`1` element. -/
theorem IsJordanProjection.quadRep_eq_self_of_mul_eq_self [SMulCommClass ℝ E E]
    {p x : E} (hp : IsJordanProjection p) (hx : p * x = x) : U p x = x := by
  rw [quadRep_apply, jpow_two, hp, hx, hx]
  module

/-- For a projection, quadratic compression is exactly the algebraic projection onto the
Peirce-`1` eigenspace. -/
theorem IsJordanProjection.quadRep_range_eq_peirceOne [SMulCommClass ℝ E E] [IsCommJordan E]
    {p : E} (hp : IsJordanProjection p) :
    LinearMap.range (U p) = IsJordanProjection.peirceOne p := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (IsJordanProjection.mem_peirceOne_iff p _).mpr (hp.mul_quadRep y)
  · intro hx
    exact ⟨x, hp.quadRep_eq_self_of_mul_eq_self ((IsJordanProjection.mem_peirceOne_iff p x).mp hx)⟩

/-- Quadratic compression by an idempotent is idempotent: `U_p ∘ U_p = U_p`.
Consequently, `U_p` is a purely algebraic projection onto its range. -/
theorem IsJordanProjection.quadRep_comp_self [SMulCommClass ℝ E E] [IsCommJordan E] {p : E}
    (hp : IsJordanProjection p) (x : E) :
    U p (U p x) = U p x := by
  rw [quadRep_apply, quadRep_apply, jpow_two, hp]
  let A₁ : E := p * x
  let A₂ : E := p * A₁
  let A₃ : E := p * A₂
  let A₄ : E := p * A₃
  let P : E := (2 : ℝ) • A₃ - (3 : ℝ) • A₂ + A₁
  let Q : E := (2 : ℝ) • A₄ - (3 : ℝ) • A₃ + A₂
  have hP : P = 0 := by
    simpa only [P, A₁, A₂, A₃] using hp.peirce_polynomial x
  have hQ : Q = 0 := by
    simpa only [Q, A₂, A₃, A₄] using hp.peirce_polynomial A₁
  simp only [mul_sub, mul_smul_comm]
  change (2 : ℝ) • ((2 : ℝ) • A₄ - A₃) - ((2 : ℝ) • A₃ - A₂) =
    (2 : ℝ) • A₂ - A₁
  apply sub_eq_zero.mp
  calc
    (2 : ℝ) • ((2 : ℝ) • A₄ - A₃) - ((2 : ℝ) • A₃ - A₂) -
        ((2 : ℝ) • A₂ - A₁) = (2 : ℝ) • Q + P := by
      dsimp only [P, Q]
      module
    _ = 0 := by rw [hQ, hP]; module

/-- Every element in the range of `U_p` is fixed by `U_p`. -/
theorem IsJordanProjection.quadRep_eq_self_of_mem_range [SMulCommClass ℝ E E] [IsCommJordan E]
    {p x : E}
    (hp : IsJordanProjection p) (y : E) (hy : x = U p y) : U p x = x := by
  rw [hy, hp.quadRep_comp_self]

/-- The residual after quadratic compression lies in the kernel of that compression. -/
theorem IsJordanProjection.quadRep_sub_quadRep [SMulCommClass ℝ E E] [IsCommJordan E]
    {p x : E} (hp : IsJordanProjection p) :
    U p (x - U p x) = 0 := by
  rw [map_sub, hp.quadRep_comp_self, sub_self]

/-- Every element splits algebraically into its quadratic-image part and residual.  For an
idempotent `p`, `quadRep_sub_quadRep` says that the latter is in the kernel of `U_p`. This is a
linear decomposition only; no claim of positivity or a full Peirce eigenspace decomposition is
made here. -/
theorem quadRep_add_sub_quadRep [SMulCommClass ℝ E E] (p x : E) :
    U p x + (x - U p x) = x := by
  abel

end JordanAlgebra
