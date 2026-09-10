/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.GaugeInvariance
public import Physlib.Mathematics.MvPolynomialTranslation
/-!
# Completeness of the field strength for gauge invariance

## i. Overview

The classification of the gauge invariants of the photon jet algebra:
**an element of the photon jet algebra is invariant under every gauge
transformation if and only if it is a polynomial in the derivatives
`∂_s F_{μν}` of the field strength** —
`gaugeInvariant_iff_mem_adjoin_fieldStrength`.

One direction is the gauge invariance of the field strength.  For the other,
the gauge action translates all jet coordinates with the same symmetrized
index class `s + {μ}` by a common arbitrary amount, so an invariant is a
polynomial in differences of same-class coordinates
(`MvPolynomial.mem_adjoin_range_X_sub_X_of_forall_aeval_add_eq`), and every
such difference is a derivative of the field strength.

This is the abelian counterpart of the fixed-algebra theorems of
`Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness`.

This file contains no definitions, only theorems about the jet algebras of
`Physlib.Particles.QED.Basic`.

## ii. Key results

- `Photon.JetAlgebra.gaugeInvariant_iff_mem_adjoin_fieldStrength` : **the
  gauge invariants of the photon jet algebra are exactly the polynomials in
  the derivatives of the field strength**.

## iii. Table of contents

- A. The symmetrized-index class projection
- B. Differences of same-class coordinates are field strengths
- C. The completeness theorem

## iv. References

The class projection is defined in `Physlib.Particles.QED.Basic`; the
translation-invariance engine is `Physlib.Mathematics.MvPolynomialTranslation`;
the non-abelian analogue is
`Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness`.

-/

@[expose] public section

/-! TODO: Classify the gauge- and Lorentz-invariant elements of mass dimension at most four of -/
/-! TODO: the full QED jet algebra: the analogue for the Dirac electron of the classification -/
/-! TODO: `LeptonGaugeSector.JetAlgebra.MassDimFour.Classification`, showing the QED Lagrangian -/
/-! TODO: is the most general renormalizable choice. -/

namespace QED

namespace Photon

open MvPolynomial

/-!

## A. The symmetrized-index class projection

-/

namespace JetGenerators

lemma indexClass_dA (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    (JetGenerators.dA s μ).indexClass = s + {μ} := rfl

lemma indexClass_ne_zero (j : JetGenerators) : j.indexClass ≠ 0 := by
  obtain ⟨s, μ⟩ := j
  rw [indexClass_dA]
  intro h
  have := congrArg Multiset.card h
  simp at this

/-- Erasing the class representative and putting it back as the Lorentz index
  preserves the class. -/
lemma indexClass_classProj (j : JetGenerators) :
    j.classProj.indexClass = j.indexClass := by
  rw [classProj, indexClass_dA, Multiset.add_comm, Multiset.singleton_add,
    Multiset.cons_erase (classRep_mem (indexClass_ne_zero j))]

/-- The class projection is idempotent. -/
lemma classProj_idem (j : JetGenerators) : j.classProj.classProj = j.classProj := by
  conv_lhs => rw [classProj]
  rw [indexClass_classProj]
  rfl

/-- Two jet coordinates have the same class projection exactly when they lie
  in the same symmetrized-index class. -/
lemma classProj_eq_classProj_iff (j j' : JetGenerators) :
    j.classProj = j'.classProj ↔ j.indexClass = j'.indexClass := by
  constructor
  · intro h
    rw [← indexClass_classProj j, ← indexClass_classProj j', h]
  · intro h
    rw [classProj, classProj, h]

end JetGenerators

namespace JetAlgebra

/-!

## B. Differences of same-class coordinates are field strengths

-/

/-- A jet coordinate minus the canonical coordinate of its class is a
  derivative of the field strength. -/
lemma coord_sub_classProj (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (h : (JetGenerators.dA s μ).classProj ≠ JetGenerators.dA s μ) :
    (X (JetGenerators.dA s μ) : JetAlgebra) - X ((JetGenerators.dA s μ).classProj) =
      fieldStrength (s.erase (classRep (s + {μ}))) (classRep (s + {μ})) μ := by
  set r := classRep (s + {μ}) with hr
  have hrs : r ∈ s := by
    have hmem : r ∈ s + {μ} :=
      classRep_mem (JetGenerators.indexClass_ne_zero (.dA s μ))
    rcases Multiset.mem_add.mp hmem with hmem | hmem
    · exact hmem
    · exfalso
      refine h ?_
      rw [Multiset.mem_singleton] at hmem
      rw [JetGenerators.classProj, JetGenerators.indexClass_dA, ← hr, hmem,
        show (s + {μ}).erase μ = s from by
          rw [Multiset.add_comm, Multiset.singleton_add, Multiset.erase_cons_head]]
  have h1 : s.erase r + {r} = s := by
    rw [Multiset.add_comm, Multiset.singleton_add, Multiset.cons_erase hrs]
  have h2 : s.erase r + {μ} = (s + {μ}).erase r := by
    rw [Multiset.erase_add_left_pos _ hrs]
  rw [fieldStrength, h1, h2, JetGenerators.classProj, JetGenerators.indexClass_dA]
  rfl

/-- Every field-strength jet lies in the range of the field-strength family. -/
lemma fieldStrength_mem_range (t : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength t μ ν ∈ Set.range (fun p :
        Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrength p.1 p.2.1 p.2.2) :=
  ⟨⟨t, μ, ν⟩, rfl⟩

/-!

## C. The completeness theorem

-/

set_option maxHeartbeats 1600000 in
/-- **Completeness of the field strength for gauge invariance**: an element of
  the photon jet algebra is invariant under every gauge transformation if and
  only if it is a polynomial in the derivatives `∂_s F_{μν}` of the field
  strength.  The field strength does not just provide *some* gauge invariants
  — it generates *all* of them. -/
theorem gaugeInvariant_iff_mem_adjoin_fieldStrength (x : JetAlgebra) :
    (∀ c : GaugeJet, gaugeAction c x = x) ↔
      x ∈ Algebra.adjoin ℝ (Set.range fun p :
        Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrength p.1 p.2.1 p.2.2) := by
  constructor
  · intro hx
    have key := MvPolynomial.mem_adjoin_range_X_sub_X_of_forall_aeval_add_eq
      (R := ℝ) (I := JetGenerators) JetGenerators.classProj
      JetGenerators.classProj_idem x ?_
    · refine Algebra.adjoin_le ?_ key
      rintro y ⟨j, rfl⟩
      obtain ⟨s, μ⟩ := j
      show (X (JetGenerators.dA s μ) : JetAlgebra) -
        X (JetGenerators.dA s μ).classProj ∈ _
      rcases eq_or_ne (JetGenerators.dA s μ).classProj (JetGenerators.dA s μ) with
        hproj | hproj
      · rw [hproj, sub_self]
        exact Subalgebra.zero_mem _
      · rw [coord_sub_classProj s μ hproj]
        exact Algebra.subset_adjoin (fieldStrength_mem_range _ _ _)
    · intro i₀ r
      obtain ⟨s₀, μ₀⟩ := i₀
      have hfun : (fun i => (X i : JetAlgebra) +
          C (if i.classProj = (JetGenerators.dA s₀ μ₀).classProj then r else 0)) =
          fun j => match j with
            | JetGenerators.dA s μ => coord s μ +
                C ((fun t => if t = s₀ + {μ₀} then r else 0) (s + {μ})) := by
        funext j
        obtain ⟨s, μ⟩ := j
        show (X (JetGenerators.dA s μ) : JetAlgebra) + _ = coord s μ + _
        rw [coord]
        congr 1
        exact congrArg C (if_congr (Iff.trans
          (JetGenerators.classProj_eq_classProj_iff _ _)
          (by rw [JetGenerators.indexClass_dA, JetGenerators.indexClass_dA])) rfl rfl)
      rw [congrArg MvPolynomial.aeval hfun]
      exact hx fun t => if t = s₀ + {μ₀} then r else 0
  · intro hx c
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨⟨s, μ, ν⟩, rfl⟩
      exact gaugeAction_fieldStrength c s μ ν
    · intro a
      exact (gaugeAction c).commutes a
    · intro a b _ _ ha hb
      rw [map_add, ha, hb]
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb]

end JetAlgebra

end Photon

end QED
