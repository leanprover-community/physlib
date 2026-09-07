/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.AlgebraRealization.Basic
/-!
# The mass weights of the fields of an algebra realization

Every derivative symbol of an algebra realization is an eigenvector of `massWeightPoly`, of
pure monomial weight equal to twice its mass dimension.  The bosons have mass dimension
`1 + |s|` and the fermions `3/2 + |s|`, where `|s|` counts the derivatives.  Each law is the
corresponding law of the jet algebra, pushed along the defining algebra map.

- A. The mass weights of the fields

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace AlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : AlgebraRealization B repJet repLorentz massWeightPoly)

/-!

## A. The mass weights of the fields

Every derivative symbol is a `massWeightPoly`-eigenvector of pure monomial weight — twice
its mass dimension. The bosons have mass dimension `1 + |s|`, the fermions `3/2 + |s|`.

-/

/-- A monomial mass-weight eigenvalue transports along the defining map: the map carries
  the mass-weight polynomial to the mass-weight polynomial, and a monomial to a monomial. -/
private lemma map_massWeight_monomial {x : JetAlgebra} {n : ℕ}
    (hx : JetAlgebra.massWeightPoly x = Polynomial.monomial n x) :
    massWeightPoly (h.toAlgHom x) = Polynomial.monomial n (h.toAlgHom x) := by
  rw [h.map_massWeight, hx, Polynomial.mapAlgHom_monomial]

/-- The law `massWeight_H` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_H : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.H s φ) = Polynomial.monomial (2 * (1 + Multiset.card s)) (h.H s φ) :=
  fun s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_higgsField s φ)

/-- The law `massWeight_barH` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_barH : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.barH s φ) = Polynomial.monomial (2 * (1 + Multiset.card s)) (h.barH s φ) :=
  fun s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_conjHiggsField s φ)

/-- The law `massWeight_A` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_A : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) μ φ,
    massWeightPoly (h.A s μ φ) = Polynomial.monomial (2 * (1 + Multiset.card s)) (h.A s μ φ) :=
  fun s μ φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_gaugeField s μ φ)

/-- The law `massWeight_d` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_d : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.d i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.d i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_downSingletField i s φ)

/-- The law `massWeight_bard` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_bard : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.bard i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.bard i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_conjDownSingletField i s φ)

/-- The law `massWeight_u` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_u : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.u i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.u i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_upSingletField i s φ)

/-- The law `massWeight_baru` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_baru : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.baru i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.baru i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_conjUpSingletField i s φ)

/-- The law `massWeight_Q` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_Q : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.Q i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.Q i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_quarkDoubletField i s φ)

/-- The law `massWeight_barQ` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_barQ : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.barQ i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.barQ i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_conjQuarkDoubletField i s φ)

/-- The law `massWeight_L` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_L : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.L i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.L i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_leptonDoubletField i s φ)

/-- The law `massWeight_barL` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_barL : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.barL i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.barL i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_conjLeptonDoubletField i s φ)

/-- The law `massWeight_e` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_e : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.e i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.e i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_leptonSingletField i s φ)

/-- The law `massWeight_bare` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma massWeight_bare : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (h.bare i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (h.bare i s φ) :=
  fun i s φ => h.map_massWeight_monomial (JetAlgebra.massWeightPoly_conjLeptonSingletField i s φ)

end AlgebraRealization

end StandardModel
