/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.StandardModel.HiggsBoson.Potential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
/-!

# The Two Higgs Doublet Model

The two Higgs doublet model is the standard model plus an additional Higgs doublet.

## i. Overview

The two Higgs doublet model (2HDM) is an extension of the Standard Model which adds a second Higgs
doublet.

## References

- https://arxiv.org/abs/hep-ph/0605184
- https://arxiv.org/abs/1605.03237

-/

open StandardModel

/-!

## A. The configuration space

-/

/-- The configuration space of the two Higgs doublet model.
  In otherwords, the underlying vector space associated with the model. -/
structure TwoHiggsDoublet where
  /-- The first Higgs doublet. -/
  Φ1 : HiggsVec
  /-- The second Higgs doublet. -/
  Φ2 : HiggsVec

namespace TwoHiggsDoublet

open InnerProductSpace

@[ext]
lemma ext_of_fst_snd {H1 H2 : TwoHiggsDoublet}
    (h1 : H1.Φ1 = H2.Φ1) (h2 : H1.Φ2 = H2.Φ2) : H1 = H2 := by
  cases H1
  cases H2
  congr
/-!

## B. Gauge group actions

-/

noncomputable instance : SMul StandardModel.GaugeGroupI TwoHiggsDoublet where
  smul g H :=
    { Φ1 := g • H.Φ1
      Φ2 := g • H.Φ2 }

@[simp]
lemma gaugeGroupI_smul_fst (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).Φ1 = g • H.Φ1 := rfl

@[simp]
lemma gaugeGroupI_smul_snd (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).Φ2 = g • H.Φ2 := rfl

noncomputable instance : MulAction StandardModel.GaugeGroupI TwoHiggsDoublet where
  one_smul H := by
    ext <;> simp
  mul_smul g1 g2 H := by
    ext <;> simp [mul_smul]

end TwoHiggsDoublet
