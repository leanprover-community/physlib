/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Irreducible
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Intertwining

/-!
# Schur's lemma for continuous intertwiners

Schur's lemma has two halves. Between inequivalent irreducible representations every intertwiner
vanishes; and, over an algebraically closed field, every self-intertwiner of a finite-dimensional
irreducible representation is scalar. This file records both halves for Mathlib's bundled
continuous intertwining maps, which is the form the analytic theory uses.

No topology on the acting monoid and no invariant measure are involved: both proofs forget the
continuity of the intertwiner and apply Mathlib's algebraic Schur lemma, in the form of the
instance `Representation.IsIrreducible.instSubsingletonIntertwiningMap` for the vanishing half and
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed` for the scalar
half.

Forgetting continuity is only sound in the direction "continuous intertwiner ↦ intertwiner"; the
hypothesis of the vanishing half is inequivalence as *continuous* representations, which is the
weaker of the two hypotheses to discharge. `ContRepresentation.nonempty_equiv_iff` is what
closes the gap: in finite dimensions over a complete field the two notions of equivalence agree,
because every linear map out of a finite-dimensional Hausdorff topological vector space is
continuous.

## Main statements

* `TauCeti.ContRepresentation.eq_zero_of_isEmpty_equiv`: every continuous intertwiner between
  inequivalent irreducible finite-dimensional representations is zero.
* `TauCeti.ContRepresentation.exists_eq_smul_one_of_irreducible`: every continuous self-intertwiner
  of an irreducible finite-dimensional representation over an algebraically closed normed field is
  scalar.
* `ContRepresentation.eq_finrank_inv_mul_trace_smul_id_of_irreducible`: when the dimension is
  invertible in `𝕜` that scalar is pinned by the trace — it is the normalized trace
  `(finrank 𝕜 V)⁻¹ * trace f` of the intertwiner.

The mathematical argument follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

namespace TauCeti

namespace ContRepresentation

section Vanishing

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

variable {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}

/-- **Schur's lemma, vanishing half.** A continuous intertwiner between inequivalent irreducible
finite-dimensional continuous representations is zero.

Inequivalence is asked of the continuous representations, which by
`_root_.ContRepresentation.nonempty_equiv_iff` is the same
condition as inequivalence of the underlying abstract representations. No hypothesis on the field
beyond completeness is needed: this half of Schur's lemma does not need eigenvalues, so it does not
need algebraic closedness. -/
theorem eq_zero_of_isEmpty_equiv (hπ : Representation.IsIrreducible π.toRepresentation)
    (hρ : Representation.IsIrreducible ρ.toRepresentation)
    (hne : IsEmpty (_root_.ContRepresentation.Equiv π ρ)) (f : ContIntertwiningMap π ρ) :
    f = 0 := by
  let : Representation.IsIrreducible π.toRepresentation := hπ
  let : Representation.IsIrreducible ρ.toRepresentation := hρ
  have : IsEmpty (Representation.Equiv π.toRepresentation ρ.toRepresentation) :=
    ⟨fun φ ↦ hne.false (_root_.ContRepresentation.nonempty_equiv_iff.2 ⟨φ⟩).some⟩
  exact ContIntertwiningMap.toIntertwiningMap_injective (Subsingleton.elim _ _)

end Vanishing

section Scalar

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [IsAlgClosed 𝕜] [Monoid G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

variable (π : ContRepresentation 𝕜 G V)

/-- Every continuous self-intertwiner of an irreducible finite-dimensional representation over an
algebraically closed normed field is a scalar multiple of the identity. -/
theorem exists_eq_smul_one_of_irreducible (hirr : Representation.IsIrreducible π.toRepresentation)
    (f : ContIntertwiningMap π π) :
    ∃ c : 𝕜, f = c • 1 := by
  let : Representation.IsIrreducible π.toRepresentation := hirr
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := π.toRepresentation)).2 f.toIntertwiningMap
  refine ⟨c, ContIntertwiningMap.toIntertwiningMap_injective ?_⟩
  -- Forgetting continuity is compatible with scalar multiplication and with the identity, so it
  -- sends the scalar continuous intertwiner `c • 1` to the algebra map's value at `c`.
  have hsmul : (c • (1 : ContIntertwiningMap π π)).toIntertwiningMap
      = c • (1 : ContIntertwiningMap π π).toIntertwiningMap := rfl
  have hone : (1 : ContIntertwiningMap π π).toIntertwiningMap
      = (1 : Representation.IntertwiningMap π.toRepresentation π.toRepresentation) := rfl
  simp only [hsmul, hone]
  rw [← Algebra.algebraMap_eq_smul_one, hc]

/-- **The Schur scalar is the normalized trace.** A continuous self-intertwiner of an irreducible
finite-dimensional representation over an algebraically closed normed field is not merely *some*
scalar multiple of the identity: taking traces pins the scalar down to `(finrank 𝕜 V)⁻¹ * trace f`.

This is the form the analytic theory uses, where the intertwiner is produced by averaging and its
trace is computed independently — against a character, or as the trace of the averaged operator.
The conclusion is stated about the underlying continuous linear map rather than about the
intertwiner, because that is the form those consumers rewrite with.

The dimension must be invertible in `𝕜`, and that hypothesis is unavoidable: when the
characteristic of `𝕜` divides `dim V` the scalar `(finrank 𝕜 V)⁻¹ * trace f` collapses to zero
and says nothing about `f`. It is stated as `(finrank 𝕜 V : 𝕜) ≠ 0` rather than `CharZero 𝕜`
because that is all the proof needs; over an `RCLike` field it follows from `Module.finrank_pos`.
The vanishing and scalar halves of Schur's lemma above need no such hypothesis. -/
theorem _root_.ContRepresentation.eq_finrank_inv_mul_trace_smul_id_of_irreducible
    (hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0)
    (hirr : Representation.IsIrreducible π.toRepresentation) (f : ContIntertwiningMap π π) :
    f.toContinuousLinearMap
      = ((Module.finrank 𝕜 V : 𝕜)⁻¹ *
          LinearMap.trace 𝕜 V (f.toContinuousLinearMap : V →ₗ[𝕜] V)) •
        ContinuousLinearMap.id 𝕜 V := by
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_irreducible π hirr f
  have hc := congrArg ContIntertwiningMap.toContinuousLinearMap hc
  simp only [ContIntertwiningMap.toContinuousLinearMap_smul,
    ContIntertwiningMap.toContinuousLinearMap_one, ContinuousLinearMap.one_def] at hc
  -- Tracing the scalar form multiplies the scalar by the dimension, which `hdim` cancels again.
  have htrace : LinearMap.trace 𝕜 V (f.toContinuousLinearMap : V →ₗ[𝕜] V)
      = c * Module.finrank 𝕜 V := by simp [hc]
  rw [htrace, mul_comm c, inv_mul_cancel_left₀ hdim]
  exact hc

end Scalar

end ContRepresentation

end TauCeti
