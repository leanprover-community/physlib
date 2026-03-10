/-
Copyright (c) 2026 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import PhysLean.SpaceAndTime.Time.Basic
/-!
# Configuration space of the harmonic oscillator

The configuration space is defined as a one-dimensional smooth manifold,
modeled on `ℝ`, with a chosen coordinate.
-/

@[expose] public section

namespace ClassicalMechanics

namespace HarmonicOscillator

/-- The configuration space of the harmonic oscillator. -/
structure ConfigurationSpace where
  /-- The underlying real coordinate. -/
  val : ℝ

namespace ConfigurationSpace

@[ext]
lemma ext {x y : ConfigurationSpace} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simp at h
  simp [h]

/-!
## Algebraic and analytical structure
-/

instance : Zero ConfigurationSpace := { zero := ⟨0⟩ }

instance : OfNat ConfigurationSpace 0 := { ofNat := ⟨0⟩ }

@[simp]
lemma zero_val : (0 : ConfigurationSpace).val = 0 := rfl

instance : Add ConfigurationSpace where
  add x y := ⟨x.val + y.val⟩

@[simp]
lemma add_val (x y : ConfigurationSpace) : (x + y).val = x.val + y.val := rfl

instance : Neg ConfigurationSpace where
  neg x := ⟨-x.val⟩

@[simp]
lemma neg_val (x : ConfigurationSpace) : (-x).val = -x.val := rfl

instance : Sub ConfigurationSpace where
  sub x y := ⟨x.val - y.val⟩

@[simp]
lemma sub_val (x y : ConfigurationSpace) : (x - y).val = x.val - y.val := rfl

instance : SMul ℝ ConfigurationSpace where
  smul r x := ⟨r * x.val⟩

@[simp]
lemma smul_val (r : ℝ) (x : ConfigurationSpace) : (r • x).val = r * x.val := rfl

instance : CoeFun ConfigurationSpace (fun _ => Fin 1 → ℝ) where
  coe x := fun _ => x.val

@[simp]
lemma apply_zero (x : ConfigurationSpace) : x 0 = x.val := rfl

@[simp]
lemma apply_eq_val (x : ConfigurationSpace) (i : Fin 1) : x i = x.val := rfl

instance : AddGroup ConfigurationSpace where
  add_assoc x y z := by ext; simp [add_assoc]
  zero_add x := by ext; simp [zero_add]
  add_zero x := by ext; simp [add_zero]
  neg_add_cancel x := by ext; simp [neg_add_cancel]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : AddCommGroup ConfigurationSpace where
  add_comm x y := by ext; simp [add_comm]

instance : Module ℝ ConfigurationSpace where
  one_smul x := by ext; simp
  smul_add r x y := by ext; simp [mul_add]
  smul_zero r := by ext; simp [mul_zero]
  add_smul r s x := by ext; simp [add_mul]
  mul_smul r s x := by ext; simp [mul_assoc]
  zero_smul x := by ext; simp

instance : Norm ConfigurationSpace where
  norm x := ‖x.val‖

instance : Dist ConfigurationSpace where
  dist x y := ‖x - y‖

lemma dist_eq_val (x y : ConfigurationSpace) :
    dist x y = ‖x.val - y.val‖ := rfl

instance : SeminormedAddCommGroup ConfigurationSpace where
  dist_self x := by simp [dist_eq_val]
  dist_comm x y := by
    simpa [dist_eq_val, Real.dist_eq] using (dist_comm x.val y.val)
  dist_triangle x y z := by
    simpa [dist_eq_val, Real.dist_eq] using (dist_triangle x.val y.val z.val)

instance : NormedAddCommGroup ConfigurationSpace where
  eq_of_dist_eq_zero := by
    intro a b h
    ext
    have h' : dist a.val b.val = 0 := by
      simpa [dist_eq_val, Real.dist_eq] using h
    exact dist_eq_zero.mp h'

instance : NormedSpace ℝ ConfigurationSpace where
  norm_smul_le r x := by
    simp [norm, smul_val, abs_mul]

open InnerProductSpace

instance : Inner ℝ ConfigurationSpace where
  inner x y := x.val * y.val

@[simp]
lemma inner_def (x y : ConfigurationSpace) : ⟪x, y⟫_ℝ = x.val * y.val := rfl

noncomputable instance : InnerProductSpace ℝ ConfigurationSpace where
  norm_sq_eq_re_inner := by
    intro x
    have hx : ‖x‖ ^ 2 = x.val ^ 2 := by
      simp [norm, sq_abs]
    simpa [inner_def, pow_two] using hx
  conj_inner_symm := by
    intro x y
    simp [inner_def]
    ring
  add_left := by
    intro x y z
    simp [inner_def, add_mul]
  smul_left := by
    intro x y r
    simp [inner_def]
    ring

@[fun_prop]
lemma differentiable_inner_self :
    Differentiable ℝ (fun x : ConfigurationSpace => ⟪x, x⟫_ℝ) := by
  have h_id : Differentiable ℝ (fun x : ConfigurationSpace => x) := differentiable_id
  simpa using (Differentiable.inner (𝕜:=ℝ) (f:=fun x : ConfigurationSpace => x)
    (g:=fun x : ConfigurationSpace => x) h_id h_id)

@[fun_prop]
lemma differentiableAt_inner_self (x : ConfigurationSpace) :
    DifferentiableAt ℝ (fun y : ConfigurationSpace => ⟪y, y⟫_ℝ) x := by
  have h_id : DifferentiableAt ℝ (fun y : ConfigurationSpace => y) x := differentiableAt_id
  simpa using (DifferentiableAt.inner (𝕜:=ℝ) (f:=fun y : ConfigurationSpace => y)
    (g:=fun y : ConfigurationSpace => y) h_id h_id)

@[fun_prop]
lemma contDiff_inner_self (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : ConfigurationSpace => ⟪x, x⟫_ℝ) := by
  have h_id : ContDiff ℝ n (fun x : ConfigurationSpace => x) := contDiff_id
  simpa using (ContDiff.inner (𝕜:=ℝ) (f:=fun x : ConfigurationSpace => x)
    (g:=fun x : ConfigurationSpace => x) h_id h_id)

/-- Linear map sending a configuration space element to its underlying real value. -/
noncomputable def toRealLM : ConfigurationSpace →ₗ[ℝ] ℝ :=
  { toFun := ConfigurationSpace.val
    map_add' := by simp
    map_smul' := by simp }

/-- Linear map embedding a real value into the configuration space. -/
noncomputable def fromRealLM : ℝ →ₗ[ℝ] ConfigurationSpace :=
  { toFun := fun x => ⟨x⟩
    map_add' := by
      intro x y
      ext
      simp
    map_smul' := by
      intro r x
      ext
      simp }

/-- Continuous linear map sending a configuration space element to its underlying real value. -/
noncomputable def toRealCLM : ConfigurationSpace →L[ℝ] ℝ :=
  toRealLM.mkContinuous 1 (by
    intro x
    simp [toRealLM, norm])

/-- Continuous linear map embedding a real value into the configuration space. -/
noncomputable def fromRealCLM : ℝ →L[ℝ] ConfigurationSpace :=
  fromRealLM.mkContinuous 1 (by
    intro x
    simp [fromRealLM, norm])

/-- Homeomorphism between configuration space and `ℝ` given by `ConfigurationSpace.val`. -/
noncomputable def valHomeomorphism : ConfigurationSpace ≃ₜ ℝ where
  toFun := ConfigurationSpace.val
  invFun := fun t => ⟨t⟩
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro t
    rfl
  continuous_toFun := by
    simpa [toRealCLM, toRealLM] using toRealCLM.continuous
  continuous_invFun := by
    simpa [fromRealCLM, fromRealLM] using fromRealCLM.continuous

/-- The structure of a charted space on `ConfigurationSpace`. -/
noncomputable instance : ChartedSpace ℝ ConfigurationSpace where
  atlas := { valHomeomorphism.toOpenPartialHomeomorph }
  chartAt _ := valHomeomorphism.toOpenPartialHomeomorph
  mem_chart_source := by
    simp
  chart_mem_atlas := by
    intro x
    simp

open Manifold ContDiff

/-- The structure of a smooth manifold on `ConfigurationSpace`. -/
noncomputable instance : IsManifold 𝓘(ℝ, ℝ) ω ConfigurationSpace where
  compatible := by
    intro e1 e2 h1 h2
    simp [atlas, ChartedSpace.atlas] at h1 h2
    subst h1 h2
    exact symm_trans_mem_contDiffGroupoid valHomeomorphism.toOpenPartialHomeomorph

instance : FiniteDimensional ℝ ConfigurationSpace := by
  classical
  refine FiniteDimensional.of_injective toRealLM ?_
  intro x y h
  ext
  simpa using h

instance : CompleteSpace ConfigurationSpace := by
  classical
  simpa using (FiniteDimensional.complete ℝ ConfigurationSpace)

/-!
## Map to space
-/

/-- The position in one-dimensional space associated to the configuration. -/
def toSpace (q : ConfigurationSpace) : Space 1 := ⟨fun _ => q.val⟩

@[simp]
lemma toSpace_apply (q : ConfigurationSpace) (i : Fin 1) : q.toSpace i = q.val := rfl

end ConfigurationSpace

end HarmonicOscillator

end ClassicalMechanics
