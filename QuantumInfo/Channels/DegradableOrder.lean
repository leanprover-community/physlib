/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled

/-! # The Degradable Order

We define the "degradable order" on channels, where M ≤ N if N can be degraded to M. This is a
scoped instance, because there are other reasonable orders on channels.

The degradable order is actually only a preorder, because channels that are degradable to each other
are not necessarily equal. (For instance, unitary channels are degradable to the identity and vice
versa.) It can compare channels of different output dimensions, but they must have the same input
dimension. For this reason the `DegradablePreorder` is parameterized by the channel input type.

One might hope that if this was defined on the quotient type of "channels up to unitary equivalence"
that it would become an order; but this is not the case. That is, there are channels `A → B` that
are degradable to each other, but cannot be degraded to each other by unitary operations. For
instance, let A be the replacement channel that goes to a mixed state, and B be a replacement
channel that goes to a pure state.

Technical notes: to model "channels of different output types", the preorder is on the Sigma type of
channels parameterized by their output type. And since the output type needs to be a Fintype and
DecidableEq, the argument is also a Sigma to bring this along.

-/

@[expose] public section

section

@[reducible]
def DegradablePreorder (dIn : Type*) [Fintype dIn] [DecidableEq dIn] : Preorder
    (Σ dOut : (Σ t, Fintype t × DecidableEq t), let _ := dOut.snd.1; CPTPMap dIn dOut.fst) where
  le Λ₁ Λ₂ :=
    let _ := Λ₁.fst.snd.1;
    let _ := Λ₂.fst.snd.1;
    let _ := Λ₂.fst.snd.2;
    Λ₂.snd.IsDegradableTo Λ₁.snd;
  le_refl Λ :=
    let _ := Λ.fst.snd.1;
    let _ := Λ.fst.snd.2;
    ⟨CPTPOp.id, CPTPOp.compose_id Λ.snd⟩
  le_trans Λ₁ Λ₂ Λ₃ h₁₂ h₂₃ := by
    let _ := Λ₁.fst.snd.1;
    let _ := Λ₁.fst.snd.2;
    let _ := Λ₂.fst.snd.1;
    let _ := Λ₂.fst.snd.2;
    let _ := Λ₃.fst.snd.1;
    let _ := Λ₃.fst.snd.2;
    obtain ⟨D₁₂, hD₁₂⟩ := h₁₂;
    obtain ⟨D₂₃, hD₂₃⟩ := h₂₃;
    use D₁₂.compose D₂₃
    rwa [CPTPOp.compose_assoc, hD₂₃]

end
