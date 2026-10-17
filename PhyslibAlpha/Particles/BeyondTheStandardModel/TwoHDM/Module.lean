/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.Basic
/-!

# The Module structure on the two Higgs doublet model

The complex vector space (module) structure on two Higgs doublet configurations.

## i. Overview

Configurations of the two Higgs doublet model are pairs of Higgs vectors `(Φ1, Φ2)`. This file
defines addition, zero, negation and complex scalar multiplication componentwise, and assembles
them into an additive commutative group and a `ℂ`-module structure on `TwoHiggsDoublet`.

## ii. Key results

- `AddCommGroup TwoHiggsDoublet` : the additive commutative group structure (an instance).
- `Module ℂ TwoHiggsDoublet` : the `ℂ`-module structure (an instance).

## iii. Table of contents

- A. The structure of a module

## iv. References

* None.

-/
@[expose] public section
/-!

## A. The structure of a module

-/

namespace TwoHiggsDoublet

instance : Add TwoHiggsDoublet where
  add H1 H2 := { Φ1 := H1.Φ1 + H2.Φ1, Φ2 := H1.Φ2 + H2.Φ2 }

@[simp]
lemma add_fst (H1 H2 : TwoHiggsDoublet) : (H1 + H2).Φ1 = H1.Φ1 + H2.Φ1 := rfl

@[simp]
lemma add_snd (H1 H2 : TwoHiggsDoublet) : (H1 + H2).Φ2 = H1.Φ2 + H2.Φ2 := rfl

instance : Zero TwoHiggsDoublet where
  zero := { Φ1 := 0, Φ2 := 0 }

@[simp]
lemma zero_fst : (0 : TwoHiggsDoublet).Φ1 = 0 := rfl

@[simp]
lemma zero_snd : (0 : TwoHiggsDoublet).Φ2 = 0 := rfl

instance : SMul ℂ TwoHiggsDoublet where
  smul c H := { Φ1 := c • H.Φ1, Φ2 := c • H.Φ2 }

@[simp]
lemma smul_fst (c : ℂ) (H : TwoHiggsDoublet) : (c • H).Φ1 = c • H.Φ1 := rfl

@[simp]
lemma smul_snd (c : ℂ) (H : TwoHiggsDoublet) : (c • H).Φ2 = c • H.Φ2 := rfl

instance : Neg TwoHiggsDoublet where
  neg H := { Φ1 := -H.Φ1, Φ2 := -H.Φ2 }

@[simp]
lemma neg_fst (H : TwoHiggsDoublet) : (-H).Φ1 = -H.Φ1 := rfl

@[simp]
lemma neg_snd (H : TwoHiggsDoublet) : (-H).Φ2 = -H.Φ2 := rfl

instance : AddCommGroup TwoHiggsDoublet where
  add_assoc H1 H2 H3 := by
    ext <;> simp [add_assoc]
  zero_add H := by
    ext <;> simp
  add_zero H := by
    ext <;> simp
  nsmul := nsmulRec
  add_comm H1 H2 := by
    ext <;> simp [add_comm]
  zsmul := zsmulRec
  neg_add_cancel H := by
    ext <;> simp [neg_add_cancel]

instance : Module ℂ TwoHiggsDoublet where
  smul_add c H1 H2 := by
    ext <;> simp [smul_add]
  add_smul c1 c2 H := by
    ext <;> simp [add_smul]
  one_smul H := by
    ext <;> simp [one_smul]
  mul_smul c1 c2 H := by
    ext <;> simp [mul_smul]
  smul_zero c := by
    ext <;> simp [smul_zero]
  zero_smul H := by
    ext <;> simp [zero_smul]

end TwoHiggsDoublet
