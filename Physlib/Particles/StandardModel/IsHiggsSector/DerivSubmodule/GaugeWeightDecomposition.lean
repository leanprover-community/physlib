/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsHiggsSector.DerivSubmodule.Basic
/-!
# The gauge weight decomposition of the Higgs sector

The Higgs and conjugate-Higgs submodules carrying `n` derivatives each come with a gauge
weight decomposition, and the two join to one of `derivSubmodule n`.  The weights that
occur are the two Higgs weights `(0, 0, ∓1, -3)` and the two conjugate-Higgs weights
`(0, 0, ±1, 3)`; they do not depend on the number of derivatives.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace IsHiggsSector

set_option linter.unusedVariables false

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {hrep_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B), rep g (b₁ * b₂) = rep g b₁ * rep g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {H : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) →
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsHiggsSector B rep hrep_mul repLorentz hrepLorentz_mul H barH
      massWeightPoly)

/-- **The gauge weight decomposition of the Higgs derivative submodules**: the join of
  the decompositions of the Higgs and conjugate-Higgs submodules, whose weights are
  `(0, 0, ∓1, -3)` and `(0, 0, ±1, 3)` respectively.

  This is an instance: its statement mentions `h`, so unification against the goal
  recovers the sector and with it the rest of the structure's implicit data. -/
@[implicit_reducible]
noncomputable instance derivSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition rep (h.derivSubmodule n) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup (d := h.higgsSubmoduleGaugeWeight n)
      (d' := h.barHiggsSubmoduleGaugeWeight n))
    _ (by rw [derivSubmodule])

/-- The gauge weights occurring in the Higgs derivative submodules: the two Higgs
  weights `(0, 0, ∓1, -3)` and the two conjugate-Higgs weights `(0, 0, ±1, 3)`. -/
lemma derivSubmoduleGaugeWeight_supp (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).supp
      = {((0, 0, -1, -3) : GaugeWeight), (0, 0, 1, -3), (0, 0, 1, 3), (0, 0, -1, 3)} :=
  rfl

end IsHiggsSector

end StandardModel
