/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.ClassicalMechanics.RigidBody.Basic
public import Physlib.Mathematics.Modules.CrossProduct
/-!

# Angular momentum of a rigid body

For a rigid body rotating with angular velocity `ω` about its reference point, each body point at
position `r` moves with velocity `ω × r`, so the body's angular momentum about that point is
`L = ∫ r × (ω × r) dm`. Expanding the double cross product,
`r × (ω × r) = |r|² ω − (r · ω) r`, shows that `L` is linear in `ω` with matrix the inertia tensor:
`L = I ω`.

## References

* Landau and Lifshitz, Mechanics, Section 32. [ref: landau_mechanics]
-/

@[expose] public section

open Manifold Matrix

namespace RigidBody

/-- The angular momentum `L = ∫ r × (ω × r) dm` of a rigid body rotating with angular velocity `ω`
about its reference point (each body point at `r` moving with velocity `ω × r`). Its `i`-th
component is `ρ` applied to the scalar field `[r × (ω × r)]ᵢ`. -/
noncomputable def angularMomentum (R : RigidBody 3) (ω : Fin 3 → ℝ) : Fin 3 → ℝ := fun i =>
  R.ρ ⟨fun x => ((x : Fin 3 → ℝ) ⨯₃ (ω ⨯₃ (x : Fin 3 → ℝ))) i, ContDiff.contMDiff <| by
    have h : (fun x : Space 3 => ((x : Fin 3 → ℝ) ⨯₃ (ω ⨯₃ (x : Fin 3 → ℝ))) i)
        = fun x => (∑ k, (x k) ^ 2) * ω i - (∑ j, x j * ω j) * x i :=
      funext fun x => cross_cross_self_apply (x : Fin 3 → ℝ) ω i
    rw [h]; fun_prop⟩

set_option backward.isDefEq.respectTransparency false in
/-- The angular momentum of a rigid body equals its inertia tensor applied to the angular velocity:
`L = I ω`. -/
theorem angularMomentum_eq_inertiaTensor_mulVec (R : RigidBody 3) (ω : Fin 3 → ℝ) :
    R.angularMomentum ω = R.inertiaTensor *ᵥ ω := by
  funext i
  simp only [angularMomentum, mulVec, dotProduct, inertiaTensor]
  have hsmul : ∀ j : Fin 3,
      R.ρ ⟨fun x => (if i = j then 1 else 0) * ∑ k, (x k) ^ 2 - x i * x j,
        ContDiff.contMDiff <| by fun_prop⟩ * ω j
      = R.ρ (ω j • ⟨fun x => (if i = j then 1 else 0) * ∑ k, (x k) ^ 2 - x i * x j,
        ContDiff.contMDiff <| by fun_prop⟩) := by
    intro j
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun j _ => hsmul j), ← map_sum]
  congr 1
  ext x
  simp only [ContMDiffMap.coeFn_mk]
  rw [cross_cross_self_apply, ← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum,
    Finset.sum_apply]
  simp only [ContMDiffMap.coeFnAddMonoidHom_apply, ContMDiffMap.coe_smul, Pi.smul_apply,
    ContMDiffMap.coeFn_mk, smul_eq_mul]
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

end RigidBody
