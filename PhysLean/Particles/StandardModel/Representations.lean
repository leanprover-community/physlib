/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Instances.Real
/-!
# Representations appearing in the Standard Model

This file defines the basic representations which appear in the Standard Model.

-/

namespace StandardModel

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The 2d representation of U(1) with charge 3 as a map from U(1) to `unitaryGroup (Fin 2) ℂ`. -/
@[simps!]
noncomputable def repU1Map (g : unitary ℂ) : unitaryGroup (Fin 2) ℂ :=
  ⟨g ^ 3 • 1, by
    rw [mem_unitaryGroup_iff, smul_one_mul, show g = ⟨g.1, g.prop⟩ from rfl]
    simp only [SubmonoidClass.mk_pow, Submonoid.mk_smul, star_smul, star_pow, RCLike.star_def,
      star_one]
    rw [smul_smul, ← mul_pow]
    erw [(Unitary.mem_iff.mp g.prop).2]
    simp only [one_pow, one_smul]⟩

/-- The 2d representation of U(1) with charge 3 as a homomorphism
  from U(1) to `unitaryGroup (Fin 2) ℂ`. -/
@[simps!]
noncomputable def repU1 : unitary ℂ →* unitaryGroup (Fin 2) ℂ where
  toFun g := repU1Map g
  map_mul' g h := by
    simp only [repU1Map, Submonoid.mk_mul_mk, mul_smul_one, smul_smul, mul_comm, ← mul_pow]
  map_one' := by
    simp only [repU1Map, one_pow, one_smul, Submonoid.mk_eq_one]

/-- The fundamental representation of SU(2) as a homomorphism to `unitaryGroup (Fin 2) ℂ`. -/
@[simps!]
def fundamentalSU2 : specialUnitaryGroup (Fin 2) ℂ →* unitaryGroup (Fin 2) ℂ where
  toFun g := ⟨g.1, g.prop.1⟩
  map_mul' _ _ := Subtype.ext rfl
  map_one' := Subtype.ext rfl

lemma repU1_fundamentalSU2_commute (u1 : unitary ℂ) (g : specialUnitaryGroup (Fin 2) ℂ) :
    repU1 u1 * fundamentalSU2 g = fundamentalSU2 g * repU1 u1 := by
  apply Subtype.ext
  simp

end StandardModel
