/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Trace
public import Mathlib.Analysis.RCLike.Basic

@[expose] public section

namespace HermitianMat

open ComplexOrder
open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι]
variable {A B C : HermitianMat n 𝕜}
variable {M : Matrix m n 𝕜} {N : Matrix n n 𝕜}

open MatrixOrder in
/-- The `MatrixOrder` instance for Matrix (the Loewner order) we keep open for
HermitianMat, always. -/
instance : PartialOrder (HermitianMat n 𝕜) :=
  inferInstanceAs (PartialOrder (selfAdjoint _))

open MatrixOrder in
instance : IsOrderedAddMonoid (HermitianMat n 𝕜) :=
  inferInstanceAs (IsOrderedAddMonoid (selfAdjoint _))

omit [Fintype n] in
theorem le_iff : A ≤ B ↔ (B - A).mat.PosSemidef := by
  rfl

omit [Fintype n] in
theorem zero_le_iff : 0 ≤ A ↔ A.mat.PosSemidef := by
  rw [le_iff, sub_zero]

theorem le_iff_mulVec_le : A ≤ B ↔
    ∀ x, star x ⬝ᵥ A.mat *ᵥ x ≤ star x ⬝ᵥ B.mat *ᵥ x := by
  simp [le_iff, Matrix.posSemidef_iff_dotProduct_mulVec, B.H.sub A.H, Matrix.sub_mulVec]

instance [DecidableEq n] : ZeroLEOneClass (HermitianMat n 𝕜) where
  zero_le_one := by
    rw [zero_le_iff]
    exact Matrix.PosSemidef.one

omit [Fintype n] in
theorem lt_iff_posdef : A < B ↔ (B - A).mat.PosSemidef ∧ A ≠ B :=
  lt_iff_le_and_ne

instance : IsStrictOrderedModule ℝ (HermitianMat n 𝕜) where
  smul_lt_smul_of_pos_left a ha b b₂ hb := by
    rw [HermitianMat.lt_iff_posdef] at hb ⊢
    simp only [← smul_sub, ne_eq, smul_right_inj ha.ne']
    exact ⟨hb.left.smul ha.le, hb.right⟩
  smul_lt_smul_of_pos_right a ha b b2 hb := by
    rw [HermitianMat.lt_iff_posdef] at ha ⊢
    rw [sub_zero] at ha
    rw [← sub_pos] at hb
    convert And.intro (ha.left.smul hb.le) ha.right using 1
    · simp [← sub_smul]
    simp only [ne_eq, not_iff_not]
    constructor
    · intro h
      rw [eq_comm, ← sub_eq_zero, ← sub_smul] at h
      simpa [eq_comm, hb.ne'] using h
    · rintro rfl; simp

theorem posSemidef_iff_spectrum_Ici [DecidableEq n] (A : HermitianMat n 𝕜) :
    0 ≤ A ↔ spectrum ℝ A.mat ⊆ Set.Ici 0 := by
  rw [zero_le_iff, Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
  simp [A.H, Set.Ici.eq_1]

theorem posSemidef_iff_spectrum_nonneg [DecidableEq n] (A : HermitianMat n 𝕜) :
    0 ≤ A ↔ ∀ x ∈ spectrum ℝ A.mat, 0 ≤ x := by
  exact A.posSemidef_iff_spectrum_Ici

theorem trace_nonneg (hA : 0 ≤ A) : 0 ≤ A.trace := by
  exact (RCLike.nonneg_iff.mp (zero_le_iff.mp hA).trace_nonneg).1

theorem trace_pos (hA : 0 < A) : 0 < A.trace := by
  open ComplexOrder in
  have hA' := hA.le
  rw [HermitianMat.zero_le_iff] at hA'
  have h_pos := Matrix.PosSemidef.trace_pos hA' (by simpa [HermitianMat.ext_iff] using hA.ne')
  rw [HermitianMat.trace_eq_re_trace]
  rw [RCLike.pos_iff] at h_pos
  exact h_pos.left

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.trace`: nonneg when the matrix is nonneg,
positive when the matrix is positive. -/
@[positivity HermitianMat.trace _]
meta def evalHermitianMatTrace : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with
  | none => pure .none
  | some _ => do
    let .app _tr (A : Expr) ← whnfR e | throwError "not HermitianMat.trace"
    let (isStrict, pfA) ← bestResult A
    if isStrict then
      pure (.positive (← mkAppM ``HermitianMat.trace_pos #[pfA]))
    else
      pure (.nonnegative (← mkAppM ``HermitianMat.trace_nonneg #[pfA]))

--Without these shortcut instances, `gcongr` fails to close certain goals...? Why? TODO
instance : PosSMulMono ℝ (HermitianMat n 𝕜) := inferInstance

instance : SMulPosMono ℝ (HermitianMat n 𝕜) := inferInstance

--Without explicitly giving this instance, Lean times out trying to find it sometimes.
instance : PosSMulReflectLE ℝ (HermitianMat n 𝕜) :=
  PosSMulMono.toPosSMulReflectLE

theorem le_trace_smul_one [DecidableEq n] (hA : 0 ≤ A) : A ≤ A.trace • 1 := by
  have hA' : A.mat.PosSemidef := zero_le_iff.mp hA
  refine (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hA'.1 A.trace).mp ?_
  rw [← A.sum_eigenvalues_eq_trace]
  intro i
  exact Finset.single_le_sum (fun j _ ↦ hA'.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- The Kronecker product of two nonnegative Hermitian matrices is nonnegative. -/
theorem kronecker_nonneg {A : HermitianMat m 𝕜} (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ A ⊗ₖ B := by
  rw [zero_le_iff, kronecker_mat]
  classical exact (zero_le_iff.mp hA).PosSemidef_kronecker (zero_le_iff.mp hB)

/-- The self-Kronecker map `A ↦ A ⊗ₖ A` is monotone on nonnegative Hermitian matrices. -/
theorem kronecker_self_mono (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A ≤ B) :
    A ⊗ₖ A ≤ B ⊗ₖ B := by
  rw [← sub_nonneg]
  have hAC : A ⊗ₖ B + -(A ⊗ₖ A) = A ⊗ₖ (B - A) := by
    rw [show -(A ⊗ₖ A) = A ⊗ₖ (-A) by
      symm
      ext1
      simpa using (Matrix.kronecker_smul (-1 : 𝕜) A.mat A.mat)]
    simpa [sub_eq_add_neg] using
      (HermitianMat.kronecker_add (A := A) (B := B) (C := -A)).symm
  have hEq : B ⊗ₖ B - A ⊗ₖ A = A ⊗ₖ (B - A) + (B - A) ⊗ₖ B := by
    calc
      B ⊗ₖ B - A ⊗ₖ A = (A + (B - A)) ⊗ₖ B - A ⊗ₖ A := by
        rw [show A + (B - A) = B by abel]
      _ = (A ⊗ₖ B + (B - A) ⊗ₖ B) - A ⊗ₖ A := by rw [HermitianMat.add_kronecker]
      _ = (A ⊗ₖ B + -(A ⊗ₖ A)) + (B - A) ⊗ₖ B := by abel
      _ = A ⊗ₖ (B - A) + (B - A) ⊗ₖ B := by rw [hAC]
  simpa [hEq] using add_nonneg
    (HermitianMat.kronecker_nonneg hA (sub_nonneg.mpr hAB))
    (HermitianMat.kronecker_nonneg (sub_nonneg.mpr hAB) hB)

/-- The Kronecker product of two positive Hermitian matrices is positive. -/
theorem kronecker_pos {A : HermitianMat m 𝕜} (hA : 0 < A) (hB : 0 < B) : 0 < A ⊗ₖ B := by
  apply lt_of_le_of_ne (kronecker_nonneg hA.le hB.le)
  intro h
  replace h := congr(trace $h)
  simp only [trace_zero, trace_kronecker, zero_eq_mul] at h
  apply trace_pos at hA
  apply trace_pos at hB
  grind only [cases Or]

omit [Fintype n] in
open MatrixOrder in
theorem posSemidef_to_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) : 0 ≤ A := by
  exact hA.nonneg

open MatrixOrder in
theorem posDef_to_pos {A : Matrix n n 𝕜} (hA : A.PosDef) [Nonempty n] : 0 < A := by
  apply lt_of_le_of_ne hA.posSemidef.nonneg
  rintro rfl
  classical simpa [Matrix.det_zero] using hA.det_pos

open Lean Meta in
/-- Given an expression `e` (a matrix) and a proof expression `p` whose type may be
`Matrix.PosSemidef A`, `Matrix.PosDef A`, or `And P Q` (syntactically), attempt to
find a proof of nonnegativity or positivity for `e`. Only syntactic matching on the
head constant is used; `isDefEq` is used only to compare the matrix argument. -/
meta partial def findMatrixPSDInExpr (e : Expr) (p : Expr) (ty : Expr) :
    MetaM (Option (Bool × Expr)) := do
  let head := ty.getAppFn
  if head.isConst then
    let name := head.constName!
    if name == ``Matrix.PosSemidef then
      -- Last argument is the matrix
      let args := ty.getAppArgs
      let A := args.back!
      if ← isDefEq A e then
        let pf ← mkAppM ``HermitianMat.posSemidef_to_nonneg #[p]
        return some (false, pf)
    if name == ``Matrix.PosDef then
      let args := ty.getAppArgs
      let A := args.back!
      if ← isDefEq A e then
        -- Try strict (needs Nonempty n); extract the index type from PosDef args
        -- PosDef args: [n, R, Fintype n, Ring R, PartialOrder R, StarRing R, A]
        let nType := args[0]!
        let nonemptyType ← mkAppM ``Nonempty #[nType]
        match ← try? (synthInstance nonemptyType) with
        | some nonemptyInst =>
          -- posDef_to_pos : {𝕜} → [RCLike 𝕜] → {n} → [Fintype n] → {A} → (hA : A.PosDef) → [Nonempty n] → 0 < A
          let pf ← mkAppOptM ``HermitianMat.posDef_to_pos #[none, none, none, none, none, p, nonemptyInst]
          return some (true, pf)
        | none =>
          let pSemidef ← mkAppM ``Matrix.PosDef.posSemidef #[p]
          let pf ← mkAppM ``HermitianMat.posSemidef_to_nonneg #[pSemidef]
          return some (false, pf)
    if name == ``And then
      let args := ty.getAppArgs
      if args.size == 2 then
        -- Recurse on left and right
        let pLeft ← mkAppM ``And.left #[p]
        if let some result ← findMatrixPSDInExpr e pLeft args[0]! then
          return some result
        let pRight ← mkAppM ``And.right #[p]
        if let some result ← findMatrixPSDInExpr e pRight args[1]! then
          return some result
  return none

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `Matrix`: looks for `A.PosSemidef` or `A.PosDef` in the
local context (including syntactic `And` conjunctions) to prove `0 ≤ A` or `0 < A`. -/
@[positivity (_ : HermitianMat _ _)]
meta def evalMatrixPSD : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _pα => do
  let lctx ← getLCtx
  let mut best : Strictness _zα e (some _pα) := .none
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    let ty := ldecl.type
    let p : Expr := .fvar ldecl.fvarId
    if let some (isStrict, pf) ← findMatrixPSDInExpr e p ty then
      if isStrict then
        return .positive pf
      else
        best := .nonnegative pf
  match best with
  | .none => throwError "evalMatrixPSD: no PosSemidef or PosDef hypothesis found for {e}"
  | other => return other


omit [Fintype n] in
theorem mat_posSemidef_to_nonneg (hA : A.mat.PosSemidef) : 0 ≤ A :=
  zero_le_iff.mpr hA

theorem mat_posDef_to_pos [Nonempty n] (hA : A.mat.PosDef) : 0 < A := by
  exact posDef_to_pos hA

open Lean Meta in
/-- Given an expression `e` (a `HermitianMat`) and a proof expression `p` whose type may be
`Matrix.PosSemidef A.mat`, `Matrix.PosDef A.mat`, or `And P Q` (syntactically), attempt to
find a proof of nonnegativity or positivity for `e`. Only syntactic matching on the
head constant is used; `isDefEq` is used only to compare the `HermitianMat` argument. -/
meta partial def findHermitianMatPSDInExpr (e : Expr) (p : Expr) (ty : Expr) :
    MetaM (Option (Bool × Expr)) := do
  let head := ty.getAppFn
  if head.isConst then
    let name := head.constName!
    if name == ``Matrix.PosSemidef || name == ``Matrix.PosDef then
      -- Last argument should be `A.mat` i.e. `HermitianMat.mat A`
      let args := ty.getAppArgs
      let matExpr := args.back!
      -- Check if matExpr is `HermitianMat.mat A` (or equivalently `Subtype.val A`)
      let matHead := matExpr.getAppFn
      if matHead.isConst && (matHead.constName! == ``HermitianMat.mat ||
          matHead.constName! == ``Subtype.val) then
        let matArgs := matExpr.getAppArgs
        let A := matArgs.back!
        if ← isDefEq A e then
          if name == ``Matrix.PosSemidef then
            let pf ← mkAppM ``HermitianMat.mat_posSemidef_to_nonneg #[p]
            return some (false, pf)
          else
            -- PosDef: try strict (needs Nonempty n)
            let psdArgs := ty.getAppArgs
            let nType := psdArgs[0]!
            let nonemptyType ← mkAppM ``Nonempty #[nType]
            match ← try? (synthInstance nonemptyType) with
            | some nonemptyInst =>
              -- mat_posDef_to_pos : {𝕜} → [RCLike 𝕜] → {n} → [Fintype n] → {A} → [Nonempty n] → (hA : A.mat.PosDef) → 0 < A
              let pf ← mkAppOptM ``HermitianMat.mat_posDef_to_pos #[none, none, none, none, none, nonemptyInst, p]
              return some (true, pf)
            | none =>
              let pSemidef ← mkAppM ``Matrix.PosDef.posSemidef #[p]
              let pf ← mkAppM ``HermitianMat.mat_posSemidef_to_nonneg #[pSemidef]
              return some (false, pf)
    if name == ``And then
      let args := ty.getAppArgs
      if args.size == 2 then
        let pLeft ← mkAppM ``And.left #[p]
        if let some result ← findHermitianMatPSDInExpr e pLeft args[0]! then
          return some result
        let pRight ← mkAppM ``And.right #[p]
        if let some result ← findHermitianMatPSDInExpr e pRight args[1]! then
          return some result
  return none

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat`: looks for `A.mat.PosSemidef` or `A.mat.PosDef` in
the local context (including syntactic `And` conjunctions) to prove `0 ≤ A` or `0 < A`. -/
@[positivity (_ : HermitianMat _ _)]
meta def evalHermitianMatPSD : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _pα => do
  trace[Tactic.positivity] "evalHermitianMatPSD: {e}"
  let lctx ← getLCtx
  let mut best : Strictness _zα e (some _pα) := .none
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    let ty := ldecl.type
    let p : Expr := .fvar ldecl.fvarId
    if let some (isStrict, pf) ← findHermitianMatPSDInExpr e p ty then
      if isStrict then
        return .positive pf
      else
        best := .nonnegative pf
  match best with
  | .none => throwError "evalHermitianMatPSD: no A.mat.PosSemidef or A.mat.PosDef hypothesis found for {e}"
  | other => return other

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.kronecker`: nonneg when both factors are. -/
@[positivity HermitianMat.kronecker _ _]
meta def evalHermitianMatKronecker : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  let .app (.app _kron A) B ← whnfR e | throwError "not HermitianMat.kronecker"
  let (isStrictA, pfA) ← bestResult A
  let (isStrictB, pfB) ← bestResult B
  if isStrictA && isStrictB then
    pure (.positive (← mkAppM ``HermitianMat.kronecker_pos #[pfA, pfB]))
  else
    let pfA' ← try mkAppM ``le_of_lt #[pfA] catch _ => pure pfA
    let pfB' ← try mkAppM ``le_of_lt #[pfB] catch _ => pure pfB
    let pfAB' ← mkAppM ``HermitianMat.kronecker_nonneg #[pfA', pfB']
    pure (.nonnegative pfAB')

variable (M) in
open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.conj`: nonneg when the inner matrix is. -/
theorem conj_nonneg (hA : 0 ≤ A) : 0 ≤ A.conj M := by
  rw [zero_le_iff] at hA ⊢
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hA M

theorem conj_pos [DecidableEq n] {A : HermitianMat n 𝕜} {M : Matrix m n 𝕜} (hA : 0 < A)
    (h : LinearMap.ker M.toEuclideanLin ≤ A.ker) : 0 < A.conj M := by
  classical exact (A.conj_nonneg M hA.le).lt_of_ne' (A.conj_ne_zero hA.ne' h)

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.conj`: nonneg when the inner matrix is. -/
@[positivity HermitianMat.conj _ _]
meta def evalHermitianMatConj : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  let .app (.app _coe conjM) (A : Expr) ← whnfR e | throwError "not conj application"
  let M := conjM.appArg!
  let (_, pfA) ← bestResult A
  let pfNonneg ← try mkAppM ``le_of_lt #[pfA] catch _ => pure pfA
  pure (.nonnegative (← mkAppM ``HermitianMat.conj_nonneg #[M, pfNonneg]))

open MatrixOrder in
example {A : Matrix n n ℂ} (hA : A.PosSemidef) : 0 ≤ A := by
  positivity

open MatrixOrder in
example {A : Matrix n n ℂ} [Nonempty n] (hA : A.PosDef) : 0 < A := by
  positivity

example (hA : A.mat.PosSemidef) : 0 ≤ A := by
  positivity

example [Nonempty n] (hA : A.mat.PosDef) : 0 < A := by
  positivity

example [DecidableEq n] [DecidableEq m] [Nonempty n] [Nonempty m]
  (A B : HermitianMat n ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B) (M : Matrix m n ℂ) :
    0 < (2 : HermitianMat (n × m) ℂ) + (3 • A) ⊗ₖ (Real.pi • B).conj M := by
  positivity

example (A B : HermitianMat n ℂ) (hA : 0 < A) (hB : 0 < B) :
    0 < ((37 • A) ⊗ₖ ((38 : ℝ) • B)).trace := by
  positivity

omit [Fintype n] in
theorem convex_cone (hA : 0 ≤ A) (hB : 0 ≤ B) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    0 ≤ (c₁ • A + c₂ • B) := by
  rw [zero_le_iff] at hA hB ⊢
  exact (hA.smul hc₁).add (hB.smul hc₂)

theorem sq_nonneg [DecidableEq n] : 0 ≤ A ^ 2 := by
  simp [zero_le_iff, pow_two]
  nth_rewrite 1 [←Matrix.IsHermitian.eq A.H]
  exact Matrix.posSemidef_conjTranspose_mul_self A.mat

theorem ker_antitone [DecidableEq n] (hA : 0 ≤ A) : A ≤ B → B.ker ≤ A.ker := by
  intro h x hB
  replace h := (le_iff_mulVec_le.mp h) x
  rw [HermitianMat.mem_ker_iff_mulVec_zero] at hB ⊢
  rw [hB, dotProduct_zero] at h
  rw [zero_le_iff] at hA
  rw [← hA.dotProduct_mulVec_zero_iff]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hA
  exact le_antisymm h (hA.right x)

theorem conj_mono (h : A ≤ B) : A.conj M ≤ B.conj M := by
  have h_conj_pos : (M * (B - A).mat * Mᴴ).PosSemidef :=
    Matrix.PosSemidef.mul_mul_conjTranspose_same h M
  constructor;
  · simp [conj, Matrix.IsHermitian, Matrix.mul_assoc]
  · simpa [Matrix.mul_sub, Matrix.sub_mul] using h_conj_pos.2

lemma conj_posDef [DecidableEq n] (hA : A.mat.PosDef) (hN : IsUnit N) :
    (A.conj N).mat.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hA ⊢
  use HermitianMat.H _
  intro x hx_ne_zero
  open Matrix in
  have h_pos : 0 < star (Nᴴ *ᵥ x) ⬝ᵥ A *ᵥ (Nᴴ *ᵥ x) := by
    apply hA.2
    intro h
    apply hx_ne_zero
    simpa [ hN ] using Matrix.eq_zero_of_mulVec_eq_zero
      (by simpa [Matrix.det_conjTranspose] using hN.map Matrix.detMonoidHom) h
  convert h_pos using 1
  simp only [conj_apply_mat, mulVec_mulVec, Matrix.mul_assoc]
  simp [dotProduct_mulVec, mulVec_conjTranspose]

set_option backward.isDefEq.respectTransparency false in
lemma inv_conj [DecidableEq n] {M : Matrix n n 𝕜} (hM : IsUnit M) :
    (A.conj M)⁻¹ = A⁻¹.conj (M⁻¹)ᴴ := by
  have h_inv : (M⁻¹)ᴴ * Mᴴ = 1 := by
    simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq] at hM
    simp [Matrix.conjTranspose_nonsing_inv, hM]
  ext1
  simp only [conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.conjTranspose_conjTranspose]
  simp only [mat_inv, mat_mk]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv h_inv, mul_assoc]

theorem le_iff_mulVec_le_mulVec (A B : HermitianMat n 𝕜) :
    A ≤ B ↔ ∀ v : n → 𝕜, star v ⬝ᵥ A.mat *ᵥ v ≤ star v ⬝ᵥ B.mat *ᵥ v := by
  rw [← sub_nonneg, HermitianMat.zero_le_iff]
  conv_rhs => enter [v]; rw [← sub_nonneg]
  have h := (B - A).H
  simp only [HermitianMat.mat_sub] at h
  simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.sub_mulVec, h]

theorem inner_mulVec_nonneg (hA : 0 ≤ A) (v : n → 𝕜) :
    0 ≤ star v ⬝ᵥ A.mat *ᵥ v := by
  rw [le_iff_mulVec_le_mulVec] at hA
  simpa using hA v

theorem mem_ker_of_inner_mulVec_zero [DecidableEq n] (hA : 0 ≤ A) (v : EuclideanSpace 𝕜 n)
    (h : star v ⬝ᵥ A.mat *ᵥ v = 0) : v ∈ A.ker := by
  have := ((zero_le_iff.mp hA).dotProduct_mulVec_zero_iff v).mp h
  exact congr(WithLp.toLp 2 $this)

theorem ker_add [DecidableEq n] (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A + B).ker = A.ker ⊓ B.ker := by
  have hA' := zero_le_iff.mp hA
  have hB' := zero_le_iff.mp hB
  ext v; simp only [Submodule.mem_inf, mem_ker_iff_mulVec_zero]
  constructor
  · intro hv
    have h3 : star v ⬝ᵥ A.mat *ᵥ v + star v ⬝ᵥ B.mat *ᵥ v = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, ← mat_add, hv, dotProduct_zero]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hA' hB'
    obtain ⟨hzA, hzB⟩ := (add_eq_zero_iff_of_nonneg (hA'.2 v) (hB'.2 v)).mp h3
    rw [← Matrix.posSemidef_iff_dotProduct_mulVec] at hA' hB'
    exact ⟨(hA'.dotProduct_mulVec_zero_iff v).mp hzA,
           (hB'.dotProduct_mulVec_zero_iff v).mp hzB⟩
  · simp +contextual [Matrix.add_mulVec]

theorem ker_sum [DecidableEq n] (f : ι → HermitianMat n 𝕜) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f i).ker = ⨅ i, (f i).ker := by
  ext v
  simp only [Submodule.mem_iInf, mem_ker_iff_mulVec_zero]
  constructor
  · intro hv i
    have hfi := zero_le_iff.mp (hf i)
    rw [← hfi.dotProduct_mulVec_zero_iff]
    have hge : ∀ j, 0 ≤ star v ⬝ᵥ (f j).mat *ᵥ v := by
      intro j
      have := zero_le_iff.mp (hf j)
      rw [Matrix.posSemidef_iff_dotProduct_mulVec] at this
      exact this.2 v
    have hsum : ∑ j, star v ⬝ᵥ (f j).mat *ᵥ v = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, ← mat_finset_sum, hv, dotProduct_zero]
    exact le_antisymm
      (hsum ▸ Finset.single_le_sum (fun j _ => hge j) (Finset.mem_univ i))
      (hge i)
  · intro h
    simp [Matrix.sum_mulVec, h]

set_option backward.isDefEq.respectTransparency false in
theorem ker_conj [DecidableEq n] (hA : 0 ≤ A) (B : Matrix n n 𝕜) :
    (A.conj B).ker = Submodule.comap (Matrix.toEuclideanLin B.conjTranspose) A.ker := by

  ext v; simp [HermitianMat.conj];
  constructor <;> intro h;
  · have := Matrix.PosSemidef.dotProduct_mulVec_zero_iff ( show Matrix.PosSemidef A.mat from zero_le_iff.mp hA );
    convert this ( Bᴴ.mulVec v ) |>.1 _ using 1;
    · rw [ mem_ker_iff_mulVec_zero ];
      congr! 2;
    · convert congr_arg ( fun x : EuclideanSpace _ _ => star v.ofLp ⬝ᵥ x ) h using 1
      simp [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      · simp [Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, lin]
      · simp [dotProduct]
  · simp only [ker, Matrix.mul_assoc, LinearMap.mem_ker]
    convert congr_arg B.toEuclideanLin h using 1
    · simp [HermitianMat.lin, Matrix.toEuclideanLin]
    · exact Eq.symm (LinearMap.map_zero (Matrix.toEuclideanLin B))

theorem ker_le_of_le_smul {α : ℝ} [DecidableEq n] (hα : α ≠ 0) (hA : 0 ≤ A) (hAB : A ≤ α • B) : B.ker ≤ A.ker := by
  rw [← ker_pos_smul B hα]
  exact ker_antitone hA hAB

/-- If a Hermitian matrix is bounded by `M * I`, then all its eigenvalues are at most `M`. -/
theorem le_smul_one_imp_eigenvalues_le [DecidableEq n] (A : HermitianMat n ℂ) (M : ℝ)
    (h : A ≤ M • (1 : HermitianMat n ℂ)) (i : n) :
    A.H.eigenvalues i ≤ M := by
  let v : n → ℂ := (A.H.eigenvectorBasis i).ofLp
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by
    rw [show v = (A.H.eigenvectorBasis i).ofLp from rfl]
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp [A.H.eigenvectorBasis.orthonormal.1 i]
  have hquad := (le_iff_mulVec_le_mulVec A (M • (1 : HermitianMat n ℂ))).mp h v
  rw [show A.mat.mulVec v = (A.H.eigenvalues i : ℂ) • v from by
    simpa [v] using A.H.mulVec_eigenvectorBasis i] at hquad
  rw [dotProduct_smul, hv] at hquad
  change (A.H.eigenvalues i : ℂ) • 1 ≤
    star v ⬝ᵥ ((M : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v at hquad
  have hquadC : (A.H.eigenvalues i : ℂ) ≤ (M : ℂ) := by
    have hright : star v ⬝ᵥ ((M : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v = (M : ℂ) := by
      simp [Matrix.smul_mulVec, hv]
    simpa [Matrix.smul_mulVec, hv] using hquad.trans_eq hright
  exact_mod_cast hquadC

open MatrixOrder in
/-- If all eigenvalues of a Hermitian matrix are at most `M`, then it is bounded by `M * I`. -/
theorem eigenvalues_le_imp_le_smul_one [DecidableEq n] (A : HermitianMat n ℂ) (M : ℝ)
    (h : ∀ i, A.H.eigenvalues i ≤ M) :
    A ≤ M • (1 : HermitianMat n ℂ) := by
  exact
    (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff A.H M).mp h

/-- Containment of kernels is preserved by the partial trace, provided the smaller one is PSD.

Given `x` in the kernel of `A.traceRight`, each of the vectors `v b := x ⊗ eᵦ` has
`⟪v b, A v b⟫ ≥ 0`, and these terms sum to `⟪x, A.traceRight x⟫ = 0`; so each one vanishes and
each `v b` lies in `ker A ≤ ker B`. Summing `B *ᵥ v b` over `b` recovers `B.traceRight *ᵥ x`. -/
theorem ker_traceRight_le {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dA]
    [DecidableEq dB] {A B : HermitianMat (dA × dB) 𝕜} (hA : 0 ≤ A) (h : A.ker ≤ B.ker) :
    A.traceRight.ker ≤ B.traceRight.ker := by
  intro x hx
  rw [mem_ker_iff_mulVec_zero] at hx ⊢
  set v : dB → EuclideanSpace 𝕜 (dA × dB) := fun b ↦
    WithLp.toLp 2 fun p ↦ if p.2 = b then x.ofLp p.1 else 0 with hv
  have key : ∀ (M : HermitianMat (dA × dB) 𝕜) (a : dA),
      (M.traceRight.mat *ᵥ x.ofLp) a = ∑ b, (M.mat *ᵥ (v b).ofLp) (a, b) := by
    intro M a
    have hR : ∀ j : dB, (M.mat *ᵥ (v j).ofLp) (a, j) = ∑ b, M.mat (a, j) (b, j) * x.ofLp b := by
      intro j
      simp only [hv, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
        mul_ite, mul_zero]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl]
      · intro k _ hk
        rw [if_neg hk]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [show (∑ b, (M.mat *ᵥ (v b).ofLp) (a, b)) = ∑ j, ∑ b, M.mat (a, j) (b, j) * x.ofLp b from
      Finset.sum_congr rfl fun j _ ↦ hR j]
    simp only [Matrix.mulVec, dotProduct, traceRight_mat, Matrix.traceRight,
      Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hnn : ∀ b, 0 ≤ star (v b).ofLp ⬝ᵥ A.mat *ᵥ (v b).ofLp :=
    fun b ↦ inner_mulVec_nonneg hA _
  have hsum0 : ∑ b, star (v b).ofLp ⬝ᵥ A.mat *ᵥ (v b).ofLp = 0 := by
    have h1 : ∀ b, star (v b).ofLp ⬝ᵥ A.mat *ᵥ (v b).ofLp
        = ∑ a, star (x.ofLp a) * (A.mat *ᵥ (v b).ofLp) (a, b) := by
      intro b
      simp only [dotProduct, hv, WithLp.ofLp_toLp, Fintype.sum_prod_type, Pi.star_apply]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.sum_eq_single b]
      · rw [if_pos rfl]
      · intro k _ hk
        simp [hk]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    simp only [h1]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← key A, hx, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have hker : ∀ b, v b ∈ A.ker := by
    intro b
    refine mem_ker_of_inner_mulVec_zero hA _ ?_
    exact le_antisymm (hsum0 ▸ Finset.single_le_sum (fun j _ ↦ hnn j) (Finset.mem_univ b)) (hnn b)
  funext a
  rw [key B a]
  refine Finset.sum_eq_zero fun b _ ↦ ?_
  have := (mem_ker_iff_mulVec_zero _ _).mp (h (hker b))
  rw [this]
  rfl

--TODO: Positivity extensions for traceLeft, traceRight, rpow, nat powers, inverse function,
-- the various `proj` function (in Proj.lean), and the inner product.

/-! ## Positivity extensions connecting HermitianMat and Matrix -/
section MatrixPositivity
open Lean Meta Mathlib.Meta.Positivity

/-- If a HermitianMat is PSD, then its eigenvalues are nonneg. -/
theorem eigenvalues_nonneg [DecidableEq n] (hA : 0 ≤ A) (i : n) :
    0 ≤ A.H.eigenvalues i :=
  (zero_le_iff.mp hA).eigenvalues_nonneg i

omit [Fintype n] in
open MatrixOrder in
/-- If a HermitianMat is PSD, its underlying matrix is nonneg in the Loewner order. -/
theorem mat_nonneg (hA : 0 ≤ A) : 0 ≤ A.mat :=
  Matrix.nonneg_iff_posSemidef.mpr (zero_le_iff.mp hA)

omit [Fintype n] in
open MatrixOrder in
/-- If a HermitianMat is positive, its underlying matrix is positive in the Loewner order. -/
theorem mat_pos (hA : 0 < A) : 0 < A.mat :=
  hA

open MatrixOrder in
/-- `Mᴴ * M` is nonneg in the Loewner order, for any matrix `M`. -/
theorem _root_.Matrix.nonneg_conjTranspose_mul_self {m : Type*} [Fintype m]
    (M : Matrix m n 𝕜) : 0 ≤ M.conjTranspose * M :=
  Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self M)

open MatrixOrder in
/-- `M * Mᴴ` is nonneg in the Loewner order, for any matrix `M`. -/
theorem _root_.Matrix.nonneg_self_mul_conjTranspose {m : Type*} [Fintype m]
    (M : Matrix n m 𝕜) : 0 ≤ M * M.conjTranspose :=
  Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_self_mul_conjTranspose M)

omit [Fintype m] in
open MatrixOrder in
theorem subtype_mk_nonneg {M : Matrix m m 𝕜} (h : 0 ≤ M) :
    0 ≤ (⟨M, (Matrix.LE.le.posSemidef h).isHermitian⟩ : HermitianMat m 𝕜) :=
  h

omit [Fintype m] in
open MatrixOrder in
theorem subtype_mk_pos {M : Matrix m m 𝕜} (h : 0 < M) :
    0 < (⟨M, (Matrix.LE.le.posSemidef h.le).isHermitian⟩ : HermitianMat m 𝕜) :=
  h

open MatrixOrder in
private theorem _root_.Matrix.eigenvalues_nonneg [DecidableEq n] {M : Matrix n n 𝕜} (h : 0 ≤ M) (i : n) :
    0 ≤ (Matrix.LE.le.posSemidef h).isHermitian.eigenvalues i :=
  (Matrix.LE.le.posSemidef h).eigenvalues_nonneg i

/-- Positivity extension for `A.mat` where `A : HermitianMat`: nonneg when `0 ≤ A`. -/
@[positivity HermitianMat.mat _]
meta def evalHermitianMatMat : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  let .app _matFn (A : Expr) ← whnfR e | throwError "not HermitianMat.mat"
  match ← bestResult A with
  | (true, pa) =>
    pure (.positive (← mkAppM ``HermitianMat.mat_pos #[pa]))
  | (false, pa) =>
    pure (.nonnegative (← mkAppM ``HermitianMat.mat_nonneg #[pa]))

/-- Positivity extension for `A.mat` where `A : HermitianMat`: nonneg when `0 ≤ A`. -/
@[positivity Subtype.val (_ : HermitianMat _ _)]
meta def evalHermitianMatVal : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  /- Note: we must not call `whnf` on `e` because `Subtype.val` is a structure
  projection (reducible), so `whnf` would reduce it and destroy the pattern. -/
  let A := e.appArg!
  match ← bestResult A with
  | (true, pa) =>
    pure (.positive (← mkAppM ``HermitianMat.mat_pos #[pa]))
  | (false, pa) =>
    pure (.nonnegative (← mkAppM ``HermitianMat.mat_nonneg #[pa]))

/-- Positivity extension for `M * Mᴴ` as a Matrix: always nonneg. -/
@[positivity HMul.hMul _ (Matrix.conjTranspose _)]
meta def evalMatrixSelfMulConjTranspose : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  let .app (.app _hmul _M) Mstar ← whnfR e | throwError "not HMul application"
  let .app _conjTranspose M' ← whnfR Mstar | throwError "not M * conjTranspose"
  pure (.nonnegative (← mkAppM ``Matrix.nonneg_self_mul_conjTranspose #[M']))

/-- Positivity extension for `Mᴴ * M` as a Matrix: always nonneg. -/
@[positivity HMul.hMul (Matrix.conjTranspose _) _]
meta def evalMatrixConjTransposeMulSelf : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  let .app (.app _hmul Mstar) _M ← whnfR e | throwError "not HMul application"
  let .app _conjTranspose M' ← whnfR Mstar | throwError "not conjTranspose * M"
  pure (.nonnegative (← mkAppM ``Matrix.nonneg_conjTranspose_mul_self #[M']))

/-- Positivity extension for `⟨M, (pf : M.IsHermitian)⟩` as a HermitianMat:
equivalent to `0 ≤ M` in `MatrixOrder`. -/
@[positivity (Subtype.mk _ _ : HermitianMat _ _)]
meta def evalHermitianMatMk : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  let .app (.app _mkFn val) _proof ← whnfR e | throwError "not Subtype.mk"
  match ← bestResult val with
  | (true, pa) =>
    pure (.positive (← mkAppM ``HermitianMat.subtype_mk_pos #[pa]))
  | (false, pa) =>
    pure (.nonnegative (← mkAppM ``HermitianMat.subtype_mk_nonneg #[pa]))

/-- Positivity extension for eigenvalues of a Matrix: `0 ≤ (_ : M.IsHermitian).eigenvalues i`.
Will try to prove `0 ≤ M` in the `MatrixOrder`. If the proof is `A.H`, i.e. M comes from a
HermitianMat, this will give `0 ≤ A.mat` which becomes `0 ≤ A` later. -/
@[positivity Matrix.IsHermitian.eigenvalues _ _]
meta def evalMatrixEigenvalues : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  let .app (.app _eigenvaluesFn hProof) _i ← whnfR e | throwError "not eigenvalues application"
  let pType ← inferType hProof
  if pType.isAppOf  ``Matrix.IsHermitian then
    let M ← pure pType.appArg!
    let (_, pa) ← bestResult M
    let pa ← try mkAppM ``le_of_lt #[pa] catch _ => pure pa
    pure (.nonnegative (← mkAppM ``Matrix.eigenvalues_nonneg #[pa, _i]))
  else
    throwError "not a Matrix.IsHermitian"

-- Tests
section tests

variable [DecidableEq n] [DecidableEq m]
open MatrixOrder

-- Test: eigenvalues nonneg from PSD HermitianMat
example (A : HermitianMat n ℂ) (hA : 0 < A) (i : n) : 0 ≤ A.H.eigenvalues i := by
  positivity

-- Test: A.mat nonneg from A nonneg
example (A : HermitianMat n ℂ) (hA : 0 ≤ A) : 0 ≤ A.mat := by positivity
example (A : HermitianMat n ℂ) (hA : 0 < A) : 0 < A.mat := by positivity
example (A : HermitianMat n ℂ) (hA : 0 ≤ A) : 0 ≤ A.val := by positivity
example (A : HermitianMat n ℂ) (hA : 0 < A) : 0 < A.val := by positivity

-- Test: Mᴴ * M nonneg as Matrix
example (M : Matrix m n ℂ) : 0 ≤ M.conjTranspose * M := by positivity

-- Test: M * Mᴴ nonneg as Matrix
example (M : Matrix n m ℂ) : 0 ≤ M * M.conjTranspose := by positivity

-- Test: ⟨Mᴴ * M, _⟩ nonneg as HermitianMat
set_option backward.isDefEq.respectTransparency false in
example (M : Matrix m n ℂ) :
    (0 : HermitianMat n ℂ) ≤ ⟨M.conjTranspose * M, Matrix.isHermitian_conjTranspose_mul_self M⟩ := by
  positivity

-- Test: ⟨M * Mᴴ, _⟩ nonneg as HermitianMat
set_option backward.isDefEq.respectTransparency false in
example (M : Matrix n m ℝ) :
    (0 : HermitianMat n ℝ) ≤ ⟨M * M.conjTranspose, Matrix.isHermitian_mul_conjTranspose_self M⟩ := by
  positivity

example (M : Matrix n n ℂ) (i : n) (A : HermitianMat n ℂ) (hA : 0 ≤ A) :
    0 ≤ (A + ⟨_, M.isHermitian_mul_conjTranspose_self⟩ + 0).H.eigenvalues i := by
  positivity

end tests
end MatrixPositivity
