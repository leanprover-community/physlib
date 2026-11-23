/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Symbols
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.MassDim
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.MassWeightPoly
public import PhyslibAlpha.Mathematics.ForMathlib.Algebra.Polynomial.Commute
public import PhyslibAlpha.Mathematics.ForMathlib.Algebra.Polynomial.SumSmulPow
/-!
# The mass-weight filtration and the invariants of a local field algebra

The grading of the local field algebra by mass weight, and its gauge and Lorentz invariants of
bounded mass weight.

## i. Overview

The local field algebra of a field datum is graded by mass weight: a generator `∂_s φ_α`
of a field of mass weight `w` has weight `w + 2 |s|`, a connection generator `∂_s A_μ` has
weight `2 + 2 |s|`. The grading is recorded by the algebra endomorphisms scaling each
generator by `c` to its weight, for real `c`.

The same grading is also recorded with the scalar replaced by a formal variable. The
mass-weight polynomial is the algebra map into the polynomials over the local field algebra
sending a generator of weight `n` to `X ^ n` times itself. It is built from the universal
property of the local field algebra. The polynomials over a noncommutative algebra are
noncommutative, so the statistics of the images have to be checked, and they follow from
those of the coefficients. The weight-`n` piece is the eigenspace on which the mass-weight
polynomial is `X ^ n`, and the filtration is the join of the pieces of weight at most `w`.
Setting the formal variable to a real number `c` gives back the scaling by `c`, so the
weight-`n` piece is also the set of elements scaled by `c ^ n` for every `c`.

Together with the actions of the jet gauge group and of the Lorentz group this gives the
submodule of gauge and Lorentz invariants of mass weight at most `w`, which is what a
Lagrangian classification describes. Everything here is generic: a model contributes only
its datum.

## ii. Key results

- `GaugeFieldData.massWeightScale` : the scaling of the local field algebra by `c` to the
  mass weight of each generator.
- `GaugeFieldData.massWeightPoly` : the mass-weight polynomial, sending a generator of
  weight `n` to `X ^ n` times itself.
- `GaugeFieldData.massWeightPoly_fermionSymbol`, `massWeightPoly_bosonSymbol` and their
  conjugates : the symbols `∂_s ψ` of a species of mass weight `w` have weight `w + 2 |s|`.
- `GaugeFieldData.massWeightPoly_gaugeField` : the gauge-field symbols `∂_s A_μ`
  have weight `2 (1 + |s|)`.
- `GaugeFieldData.massWeightScale_eq_polyEval_comp_massWeightPoly` : the scaling by `c` is
  the mass-weight polynomial evaluated at `c`.
- `GaugeFieldData.massWeightSubmodule`, `massWeightSubmoduleLE` : the graded pieces and
  the filtration.
- `GaugeFieldData.mem_massWeightSubmodule_iff_massWeightScale` : the weight-`n` piece is the
  set of elements scaled by `c ^ n` under the scaling by every real `c`.
- `GaugeFieldData.gaugeInvariants`, `lorentzInvariants`, `invariantsLE` : the invariants,
  and the invariants of mass weight at most `w`.
- `GaugeFieldData.bosonNormSq` : the contraction `φ† φ` of a bosonic species with its
  conjugate through a basis of its value space, the simplest invariant.
- `GaugeFieldData.invariantsLE_map` : an isomorphism of local field algebras respecting the
  actions and the mass-weight polynomial carries the invariants of one datum onto those of the
  other.

## iii. Table of contents

- A. The mass-weight scaling
- B. The mass-weight polynomial
  - B.1. The grading of a component function
  - B.2. The images of the generators
  - B.3. The mass-weight polynomial and its generators
  - B.4. Evaluation at a real number
- C. The graded pieces and the filtration
- D. The invariants
- E. The contraction of a boson with its conjugate
- F. Transport along an isomorphism

## iv. References

* None.

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (T : GaugeFieldData G)

/-!

## A. The mass-weight scaling

-/

/-- The assignment scaling each generator by `c` to its mass weight. A component function
  `∂_s φ_α` of a species of mass weight `w` by `c ^ (w + 2 |s|)`, a connection generator
  `∂_s A_μ` by `c ^ (2 + 2 |s|)`. The relations hold because the images are generators of
  the same kind. -/
noncomputable def massWeightAssignment (c : ℝ) : T.Assignment T.LocalFieldAlgebra where
  fermion i := T.ιFermion i ∘ₗ FieldDerivSpace.massWeightScale (T.fermion i).massWeight (c : ℂ)
  boson j := T.ιBoson j ∘ₗ FieldDerivSpace.massWeightScale (T.boson j).massWeight (c : ℂ)
  connection := T.ιConnection ∘ₗ GaugeBoson.FieldDerivSpace.massWeightScale G c
  fermion_mul_self i _ := ιFermion_mul_self i _
  fermion_mul_swap i j _ _ := ιFermion_mul_swap i j _ _
  boson_commute i j _ _ := ιBoson_commute i j _ _
  connection_commute _ _ := ιConnection_commute _ _
  boson_commute_connection _ _ _ := ιBoson_commute_ιConnection _ _ _
  boson_commute_fermion j i _ _ := ιBoson_commute_ιFermion j i _ _
  connection_commute_fermion _ _ _ := ιConnection_commute_ιFermion _ _ _

/-- The mass-weight scaling of the local field algebra, the algebra endomorphism
  scaling each generator by `c` to its mass weight. -/
noncomputable def massWeightScale (c : ℝ) : T.LocalFieldAlgebra →ₐ[ℂ] T.LocalFieldAlgebra :=
  (T.massWeightAssignment c).lift

@[simp]
lemma massWeightScale_ιFermion (c : ℝ) (i : T.FermionSpecies)
    (x : FieldDerivSpace (T.fermion i)) :
    T.massWeightScale c (T.ιFermion i x)
      = T.ιFermion i (FieldDerivSpace.massWeightScale (T.fermion i).massWeight (c : ℂ) x) :=
  (T.massWeightAssignment c).lift_ιFermion i x

@[simp]
lemma massWeightScale_ιBoson (c : ℝ) (j : T.BosonSpecies)
    (y : FieldDerivSpace (T.boson j)) :
    T.massWeightScale c (T.ιBoson j y)
      = T.ιBoson j (FieldDerivSpace.massWeightScale (T.boson j).massWeight (c : ℂ) y) :=
  (T.massWeightAssignment c).lift_ιBoson j y

@[simp]
lemma massWeightScale_ιConnection (c : ℝ) (v : GaugeBoson.FieldDerivSpace G) :
    T.massWeightScale c (T.ιConnection v)
      = T.ιConnection (GaugeBoson.FieldDerivSpace.massWeightScale G c v) :=
  (T.massWeightAssignment c).lift_ιConnection v

/-!

## B. The mass-weight polynomial

Replacing the scalar `c` of the scaling by a formal variable `X` turns the scaling into a
grading. The image of a generator is a polynomial over the local field algebra whose
coefficients are generators of the same species, so the relations among the generators hold
for their images coefficient by coefficient. That is what makes the images a compatible
assignment, and the grading the algebra map it induces.

-/

/-!

### B.1. The grading of a component function

-/

/-- The polynomials over the local field algebra form a ring. The instance is recorded here
  so that it is found directly, without searching through the tensor-product structure of
  the local field algebra once more. -/
noncomputable instance instRingPolynomialLocalFieldAlgebra :
    Ring (Polynomial T.LocalFieldAlgebra) :=
  AddMonoidAlgebra.ring (R := T.LocalFieldAlgebra) (M := ℕ)

/-- The monomial of degree `n` over the local field algebra, as a map of complex vector
  spaces rather than of modules over the local field algebra. -/
noncomputable def monomialₗ (n : ℕ) :
    T.LocalFieldAlgebra →ₗ[ℂ] Polynomial T.LocalFieldAlgebra :=
  (Polynomial.monomial n).restrictScalars ℂ

/-- One half of the grading of a component space, for a species of mass weight `w`. It
  sends the symbol `∂_s φ` to `X ^ (w + 2 |s|)` times its image under `k`, and is defined on
  the multiset basis of the derivative labels. -/
noncomputable def halfPoly {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W →ₗ[ℂ] T.LocalFieldAlgebra) :
    SpaceTimeDerivAlgebraℂ ⊗[ℂ] W →ₗ[ℂ] Polynomial T.LocalFieldAlgebra :=
  TensorProduct.lift (SpaceTimeDerivAlgebraℂ.basis.constr ℂ fun s =>
    (T.monomialₗ (w + 2 * Multiset.card s)).comp
      (k.comp (TensorProduct.mk ℂ SpaceTimeDerivAlgebraℂ W (SpaceTimeDerivAlgebraℂ.basis s))))

variable {T}

@[simp]
lemma monomialₗ_apply (n : ℕ) (x : T.LocalFieldAlgebra) :
    T.monomialₗ n x = Polynomial.monomial n x := rfl

/-- On the symbol `∂_s φ` the half grading is the monomial of degree `w + 2 |s|`, since the
  field contributes `w` and each derivative two. -/
lemma halfPoly_basis_tmul {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W →ₗ[ℂ] T.LocalFieldAlgebra)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (x : W) :
    T.halfPoly w k (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] x) =
      Polynomial.monomial (w + 2 * Multiset.card s)
        (k (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] x)) := by
  rw [halfPoly, TensorProduct.lift.tmul, Module.Basis.constr_basis]
  rfl

/-- Every coefficient of the half grading lies in the range of `k`. The derivative monomials
  span the derivative labels, and on each of them the half grading is a single monomial
  whose coefficient is in the range. -/
lemma halfPoly_coeff_mem {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W →ₗ[ℂ] T.LocalFieldAlgebra)
    (z : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W) (n : ℕ) :
    (T.halfPoly w k z).coeff n ∈ LinearMap.range k := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb =>
    rw [map_add, Polynomial.coeff_add]
    exact add_mem ha hb
  | tmul a x =>
    have ha : a ∈ Submodule.span ℂ (Set.range SpaceTimeDerivAlgebraℂ.basis) := by
      rw [SpaceTimeDerivAlgebraℂ.basis.span_eq]
      trivial
    induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨s, rfl⟩ := hb
      rw [halfPoly_basis_tmul, Polynomial.coeff_monomial_apply]
      split_ifs
      · exact LinearMap.mem_range_self k _
      · exact zero_mem _
    | zero =>
      rw [TensorProduct.zero_tmul, map_zero, Polynomial.coeff_zero]
      exact zero_mem _
    | add b c _ _ hb hc =>
      rw [TensorProduct.add_tmul, map_add, Polynomial.coeff_add]
      exact add_mem hb hc
    | smul c b _ hb =>
      rw [← TensorProduct.smul_tmul', map_smul, AddMonoidAlgebra.coeff_smul_apply]
      exact Submodule.smul_mem _ c hb

/-!

### B.2. The images of the generators

The image of a matter generator is the sum of the two half gradings of its component
space, at the mass weight of its species, with the symbol maps of the species as the maps
`k`. The image of a connection generator is the grading of the complexified gauge-boson
algebra, pushed into the local field algebra coefficient by coefficient.

-/

variable (T)

/-- The grading of the component space of a fermionic species, the half gradings of the
  symbols and of the conjugate symbols, at the mass weight of the species. -/
noncomputable def fermionPoly (i : T.FermionSpecies) :
    FieldDerivSpace (T.fermion i) →ₗ[ℂ] Polynomial T.LocalFieldAlgebra :=
  (T.halfPoly (T.fermion i).massWeight (T.fermionSymbolMap i)).comp (LinearMap.fst ℂ _ _) +
    (T.halfPoly (T.fermion i).massWeight (T.conjFermionSymbolMap i)).comp
      (LinearMap.snd ℂ _ _)

/-- The grading of the component space of a bosonic species, the half gradings of the
  symbols and of the conjugate symbols, at the mass weight of the species. -/
noncomputable def bosonPoly (j : T.BosonSpecies) :
    FieldDerivSpace (T.boson j) →ₗ[ℂ] Polynomial T.LocalFieldAlgebra :=
  (T.halfPoly (T.boson j).massWeight (T.bosonSymbolMap j)).comp (LinearMap.fst ℂ _ _) +
    (T.halfPoly (T.boson j).massWeight (T.conjBosonSymbolMap j)).comp (LinearMap.snd ℂ _ _)

/-- An algebra map out of the complexified connection factor, read on the connection
  generators, `v ↦ h (1 ⊗ v)`. It is stated for an arbitrary complex algebra `C`, so that
  the real structure of `C` is the one the generator assignments use. -/
noncomputable def connectionOfAlgHom {C : Type*} [Ring C] [Algebra ℂ C]
    (h : (ℂ ⊗[ℝ] SymmetricAlgebra ℝ (GaugeBoson.FieldDerivSpace G)) →ₐ[ℂ] C) :
    GaugeBoson.FieldDerivSpace G →ₗ[ℝ] C :=
  (h.restrictScalars ℝ).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ)
      (B := SymmetricAlgebra ℝ (GaugeBoson.FieldDerivSpace G))).toLinearMap ∘ₗ
    SymmetricAlgebra.ι ℝ (GaugeBoson.FieldDerivSpace G)

/-- The grading of the connection generators, a real-linear map from
  `GaugeBoson.FieldDerivSpace G` to `Polynomial T.LocalFieldAlgebra`, the grading of the
  complexified gauge-boson algebra, pushed into the local field algebra coefficient by
  coefficient. Its type is left to be inferred, so that the real structure on the
  polynomials is the one `connectionOfAlgHom` and the generator assignments use. -/
noncomputable def connectionPoly :=
  connectionOfAlgHom (G := G) (C := Polynomial T.LocalFieldAlgebra)
    ((Polynomial.mapAlgHom T.includeConnection).comp
    (LocalGaugeFieldAlgebra.complexMassWeightPoly (G := G)))

variable {T}

lemma fermionPoly_apply (i : T.FermionSpecies) (x : FieldDerivSpace (T.fermion i)) :
    T.fermionPoly i x = T.halfPoly (T.fermion i).massWeight (T.fermionSymbolMap i) x.1
      + T.halfPoly (T.fermion i).massWeight (T.conjFermionSymbolMap i) x.2 := rfl

lemma bosonPoly_apply (j : T.BosonSpecies) (y : FieldDerivSpace (T.boson j)) :
    T.bosonPoly j y = T.halfPoly (T.boson j).massWeight (T.bosonSymbolMap j) y.1
      + T.halfPoly (T.boson j).massWeight (T.conjBosonSymbolMap j) y.2 := rfl

lemma connectionPoly_apply (v : GaugeBoson.FieldDerivSpace G) :
    T.connectionPoly v = Polynomial.mapAlgHom T.includeConnection
      (LocalGaugeFieldAlgebra.complexMassWeightPoly (G := G)
        ((1 : ℂ) ⊗ₜ[ℝ] SymmetricAlgebra.ι ℝ (GaugeBoson.FieldDerivSpace G) v)) := rfl

/-- On an unconjugated symbol `∂_s ψ^φ` of a fermionic species of mass weight `w` the
  grading is the monomial of degree `w + 2 |s|`. -/
lemma fermionPoly_inl (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.fermionPoly i (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0)
      = Polynomial.monomial ((T.fermion i).massWeight + 2 * Multiset.card s)
          (T.fermionSymbol i s φ) := by
  rw [fermionPoly_apply, halfPoly_basis_tmul, map_zero, add_zero]
  rfl

/-- On a conjugate symbol `∂_s ψ̄^φ` the grading is the monomial of the same degree. -/
lemma fermionPoly_inr (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.fermionPoly i (0, SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ)
      = Polynomial.monomial ((T.fermion i).massWeight + 2 * Multiset.card s)
          (T.conjFermionSymbol i s φ) := by
  rw [fermionPoly_apply, halfPoly_basis_tmul, map_zero, zero_add]
  rfl

/-- On an unconjugated symbol `∂_s φ^χ` of a bosonic species of mass weight `w` the
  grading is the monomial of degree `w + 2 |s|`. -/
lemma bosonPoly_inl (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.bosonPoly j (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0)
      = Polynomial.monomial ((T.boson j).massWeight + 2 * Multiset.card s)
          (T.bosonSymbol j s φ) := by
  rw [bosonPoly_apply, halfPoly_basis_tmul, map_zero, add_zero]
  rfl

/-- On a conjugate symbol `∂_s φ̄^χ` the grading is the monomial of the same degree. -/
lemma bosonPoly_inr (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.bosonPoly j (0, SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ)
      = Polynomial.monomial ((T.boson j).massWeight + 2 * Multiset.card s)
          (T.conjBosonSymbol j s φ) := by
  rw [bosonPoly_apply, halfPoly_basis_tmul, map_zero, zero_add]
  rfl

/-- Every coefficient of the image of a fermionic generator is a generator of the same
  species. -/
lemma fermionPoly_coeff_mem (i : T.FermionSpecies) (x : FieldDerivSpace (T.fermion i))
    (n : ℕ) : (T.fermionPoly i x).coeff n ∈ LinearMap.range (T.ιFermion i) := by
  rw [fermionPoly_apply, Polynomial.coeff_add]
  exact add_mem
    (LinearMap.range_comp_le_range (LinearMap.inl ℂ _ _) (T.ιFermion i)
      (halfPoly_coeff_mem _ (T.fermionSymbolMap i) x.1 n))
    (LinearMap.range_comp_le_range (LinearMap.inr ℂ _ _) (T.ιFermion i)
      (halfPoly_coeff_mem _ (T.conjFermionSymbolMap i) x.2 n))

/-- Every coefficient of the image of a bosonic generator is a generator of the same
  species. -/
lemma bosonPoly_coeff_mem (j : T.BosonSpecies) (y : FieldDerivSpace (T.boson j))
    (n : ℕ) : (T.bosonPoly j y).coeff n ∈ LinearMap.range (T.ιBoson j) := by
  rw [bosonPoly_apply, Polynomial.coeff_add]
  exact add_mem
    (LinearMap.range_comp_le_range (LinearMap.inl ℂ _ _) (T.ιBoson j)
      (halfPoly_coeff_mem _ (T.bosonSymbolMap j) y.1 n))
    (LinearMap.range_comp_le_range (LinearMap.inr ℂ _ _) (T.ιBoson j)
      (halfPoly_coeff_mem _ (T.conjBosonSymbolMap j) y.2 n))

/-- The images of two fermionic generators anticommute, because their coefficients are
  fermionic generators. -/
lemma fermionPoly_mul_swap (i j : T.FermionSpecies) (x : FieldDerivSpace (T.fermion i))
    (y : FieldDerivSpace (T.fermion j)) :
    T.fermionPoly i x * T.fermionPoly j y = -(T.fermionPoly j y * T.fermionPoly i x) := by
  refine Polynomial.mul_eq_neg_mul_of_coeff (R := T.LocalFieldAlgebra) fun a b => ?_
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp (fermionPoly_coeff_mem i x a)
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (fermionPoly_coeff_mem j y b)
  rw [← hu, ← hv]
  exact ιFermion_mul_swap i j u v

/-- The image of a bosonic generator is central, because its coefficients are. -/
lemma commute_bosonPoly (j : T.BosonSpecies) (y : FieldDerivSpace (T.boson j))
    (q : Polynomial T.LocalFieldAlgebra) : Commute (T.bosonPoly j y) q := by
  refine Polynomial.commute_of_commute_coeff fun a b => ?_
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp (bosonPoly_coeff_mem j y a)
  rw [← hu]
  exact commute_ιBoson j u (q.coeff b)

/-- A polynomial with coefficients in the connection factor is central, because the
  connection factor is. -/
lemma commute_mapAlgHom_includeConnection
    (p : Polynomial (ℂ ⊗[ℝ] SymmetricAlgebra ℝ (GaugeBoson.FieldDerivSpace G)))
    (q : Polynomial T.LocalFieldAlgebra) :
    Commute (Polynomial.mapAlgHom T.includeConnection p) q := by
  refine Polynomial.commute_of_commute_coeff fun a b => ?_
  rw [Polynomial.coe_mapAlgHom, Polynomial.coeff_map]
  exact includeConnection_commute (p.coeff a) (q.coeff b)

/-- The image of a connection generator is central. -/
lemma commute_connectionPoly (v : GaugeBoson.FieldDerivSpace G)
    (q : Polynomial T.LocalFieldAlgebra) : Commute (T.connectionPoly v) q := by
  rw [connectionPoly_apply]
  exact commute_mapAlgHom_includeConnection _ q

/-!

### B.3. The mass-weight polynomial and its generators

-/

variable (T)

/-- The grading of the generators as a compatible assignment in the polynomials over the
  local field algebra. The fermionic images anticommute and the bosonic and connection
  images are central, because their coefficients do and are. -/
noncomputable def massWeightPolyAssignment :
    T.Assignment (Polynomial T.LocalFieldAlgebra) where
  fermion := T.fermionPoly
  boson := T.bosonPoly
  connection := T.connectionPoly
  -- a square equal to its own negative vanishes, two being invertible in `ℂ`
  fermion_mul_self i x :=
    have h2 : (2 : ℂ) • (T.fermionPoly i x * T.fermionPoly i x) = 0 :=
      (two_smul ℂ _).trans (eq_neg_iff_add_eq_zero.mp (fermionPoly_mul_swap i i x x))
    (inv_smul_smul₀ (two_ne_zero : (2 : ℂ) ≠ 0) _).symm.trans
      ((congrArg (fun y => (2 : ℂ)⁻¹ • y) h2).trans (smul_zero _))
  fermion_mul_swap i j x y := fermionPoly_mul_swap i j x y
  boson_commute i _ x _ := commute_bosonPoly i x _
  connection_commute v _ := commute_connectionPoly v _
  boson_commute_connection j y _ := commute_bosonPoly j y _
  boson_commute_fermion j _ y _ := commute_bosonPoly j y _
  connection_commute_fermion v _ _ := commute_connectionPoly v _

/-- The mass-weight polynomial of the local field algebra, the algebra map sending a
  generator of mass weight `n` to `X ^ n` times itself, so that the coefficient of `X ^ n`
  in the image of an element is its part of mass weight `n`. -/
noncomputable def massWeightPoly : T.LocalFieldAlgebra →ₐ[ℂ] Polynomial T.LocalFieldAlgebra :=
  T.massWeightPolyAssignment.lift

variable {T}

@[simp]
lemma massWeightPoly_ιFermion (i : T.FermionSpecies) (x : FieldDerivSpace (T.fermion i)) :
    T.massWeightPoly (T.ιFermion i x) = T.fermionPoly i x :=
  T.massWeightPolyAssignment.lift_ιFermion i x

@[simp]
lemma massWeightPoly_ιBoson (j : T.BosonSpecies) (y : FieldDerivSpace (T.boson j)) :
    T.massWeightPoly (T.ιBoson j y) = T.bosonPoly j y :=
  T.massWeightPolyAssignment.lift_ιBoson j y

@[simp]
lemma massWeightPoly_ιConnection (v : GaugeBoson.FieldDerivSpace G) :
    T.massWeightPoly (T.ιConnection v) = T.connectionPoly v :=
  T.massWeightPolyAssignment.lift_ιConnection v

/-- The symbol `∂_s ψ^φ` of a fermionic species of mass weight `w` has weight
  `w + 2 |s|`. -/
lemma massWeightPoly_fermionSymbol (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.massWeightPoly (T.fermionSymbol i s φ)
      = Polynomial.monomial ((T.fermion i).massWeight + 2 * Multiset.card s)
          (T.fermionSymbol i s φ) :=
  (massWeightPoly_ιFermion i (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0)).trans
    (fermionPoly_inl i s φ)

/-- The conjugate symbol `∂_s ψ̄^φ` has the same weight `w + 2 |s|`. -/
lemma massWeightPoly_conjFermionSymbol (i : T.FermionSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.massWeightPoly (T.conjFermionSymbol i s φ)
      = Polynomial.monomial ((T.fermion i).massWeight + 2 * Multiset.card s)
          (T.conjFermionSymbol i s φ) :=
  (massWeightPoly_ιFermion i (0, SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ)).trans
    (fermionPoly_inr i s φ)

/-- The symbol `∂_s φ^χ` of a bosonic species of mass weight `w` has weight `w + 2 |s|`. -/
lemma massWeightPoly_bosonSymbol (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.massWeightPoly (T.bosonSymbol j s φ)
      = Polynomial.monomial ((T.boson j).massWeight + 2 * Multiset.card s)
          (T.bosonSymbol j s φ) :=
  (massWeightPoly_ιBoson j (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0)).trans
    (bosonPoly_inl j s φ)

/-- The conjugate symbol `∂_s φ̄^χ` has the same weight `w + 2 |s|`. -/
lemma massWeightPoly_conjBosonSymbol (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.massWeightPoly (T.conjBosonSymbol j s φ)
      = Polynomial.monomial ((T.boson j).massWeight + 2 * Multiset.card s)
          (T.conjBosonSymbol j s φ) :=
  (massWeightPoly_ιBoson j (0, SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ)).trans
    (bosonPoly_inr j s φ)

/-- The gauge-field symbol `∂_s A_μ^φ` has mass weight `2 (1 + |s|)`, since the gauge field has
  mass dimension one and each derivative adds one more. This is the form of the hypothesis
  that the mass weights of the covariant towers take. -/
lemma massWeightPoly_gaugeField (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.massWeightPoly (T.gaugeField s μ φ)
      = Polynomial.monomial (2 * (1 + Multiset.card s)) (T.gaugeField s μ φ) := by
  have hg : T.gaugeField s μ φ = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
      LocalGaugeFieldAlgebra.iteratedJetDeriv G s (LocalGaugeFieldAlgebra.ofA G μ φ)) :=
    (gaugeField_apply s μ φ).trans (congrArg T.includeConnection
      (LocalGaugeFieldAlgebra.iteratedD_complexJetDeriv_one_tmul s
        (LocalGaugeFieldAlgebra.ofA G μ φ)))
  have hv := LocalGaugeFieldAlgebra.iteratedJetDeriv_ofA (G := G) s μ φ
  have hc := LocalGaugeFieldAlgebra.complexMassWeightPoly_tmul_iteratedJetDeriv_ofA
    (G := G) 1 s μ φ
  have key := massWeightPoly_ιConnection (T := T)
    (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ]
      (GaugeBoson.componentDual G) (Lorentz.CoVector.basis.dualBasis μ) φ)
  rw [hv] at hc
  rw [hg, hv]
  refine (key.trans (connectionPoly_apply _)).trans
    ((congrArg (Polynomial.mapAlgHom T.includeConnection) hc).trans
      ((Polynomial.mapAlgHom_monomial T.includeConnection _ _).trans ?_))
  rw [show 2 + 2 * Multiset.card s = 2 * (1 + Multiset.card s) by ring]

/-!

### B.4. Evaluation at a real number

Setting the formal variable of the mass-weight polynomial to a real number `c` gives back the
mass-weight scaling by `c`. The scalar `c` is central, so evaluation at it is an algebra map,
and it is enough to compare the two algebra maps on the generators.

-/

variable (T) in
/-- Evaluation of a polynomial over the local field algebra at a real number `c`. It is an
  algebra map because `c` is central. -/
noncomputable def polyEval (c : ℝ) :
    Polynomial T.LocalFieldAlgebra →ₐ[ℂ] T.LocalFieldAlgebra :=
  Polynomial.eval₂AlgHom (AlgHom.id ℂ T.LocalFieldAlgebra) (algebraMap ℂ _ (c : ℂ))
    fun a => Algebra.commute_algebraMap_right (c : ℂ) a

/-- Evaluating the monomial `x X ^ n` at `c` gives `c ^ n x`. -/
lemma polyEval_monomial (c : ℝ) (n : ℕ) (x : T.LocalFieldAlgebra) :
    T.polyEval c (Polynomial.monomial n x) = ((c : ℂ) ^ n) • x := by
  change Polynomial.eval₂ (RingHom.id T.LocalFieldAlgebra)
    (algebraMap ℂ T.LocalFieldAlgebra (c : ℂ)) (Polynomial.monomial n x) = _
  rw [Polynomial.eval₂_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  rfl

/-- Evaluation at `c` as a sum over the coefficients. -/
lemma polyEval_eq_sum (c : ℝ) (q : Polynomial T.LocalFieldAlgebra) :
    T.polyEval c q = ∑ m ∈ Finset.range (q.natDegree + 1), ((c : ℂ) ^ m) • q.coeff m := by
  conv_lhs => rw [q.as_sum_range' (q.natDegree + 1) (Nat.lt_succ_self _)]
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => polyEval_monomial c m (q.coeff m)

/-- A polynomial over the local field algebra vanishing at every real number is zero, its
  coefficients being those of an identically vanishing polynomial function. -/
lemma eq_zero_of_forall_polyEval_eq_zero {q : Polynomial T.LocalFieldAlgebra}
    (h : ∀ c : ℝ, T.polyEval c q = 0) : q = 0 := by
  have hq := eq_zero_of_forall_sum_smul_pow_eq_zero (n := q.natDegree + 1) (b := q.coeff)
    fun c => (Finset.sum_congr rfl fun m _ => (Complex.coe_smul (c ^ m) (q.coeff m)).symm.trans
      (by rw [Complex.ofReal_pow])).trans ((polyEval_eq_sum c q).symm.trans (h c))
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hk : k < q.natDegree + 1
  · exact hq k (Finset.mem_range.mpr hk)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- The half grading evaluated at `c` is the mass-weight scaling of the half component space,
  `c ^ w` times the derivative-degree scaling by `c ^ 2`. -/
lemma polyEval_halfPoly (c : ℝ) {W : Type} [AddCommGroup W] [Module ℂ W] (w : ℕ)
    (k : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W →ₗ[ℂ] T.LocalFieldAlgebra)
    (z : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W) :
    T.polyEval c (T.halfPoly w k z) = ((c : ℂ) ^ w) • k (TensorProduct.map
      (SpaceTimeDerivAlgebraℂ.gradeScale ((c : ℂ) ^ 2)).toLinearMap LinearMap.id z) := by
  have h : (T.polyEval c).toLinearMap ∘ₗ T.halfPoly w k = ((c : ℂ) ^ w) • (k ∘ₗ
      TensorProduct.map (SpaceTimeDerivAlgebraℂ.gradeScale ((c : ℂ) ^ 2)).toLinearMap
        LinearMap.id) :=
    TensorProduct.ext (SpaceTimeDerivAlgebraℂ.basis.ext fun s => LinearMap.ext fun x => by
      change T.polyEval c (T.halfPoly w k (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] x)) =
        ((c : ℂ) ^ w) • k (TensorProduct.map
          (SpaceTimeDerivAlgebraℂ.gradeScale ((c : ℂ) ^ 2)).toLinearMap LinearMap.id
          (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] x))
      rw [halfPoly_basis_tmul, polyEval_monomial, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, SpaceTimeDerivAlgebraℂ.gradeScale_basis, LinearMap.id_apply,
        ← TensorProduct.smul_tmul', map_smul, smul_smul, ← pow_mul, ← pow_add])
  exact LinearMap.congr_fun h z

/-- The image of a fermionic generator evaluated at `c` is its mass-weight scaling by `c`. -/
lemma polyEval_fermionPoly (c : ℝ) (i : T.FermionSpecies) (x : FieldDerivSpace (T.fermion i)) :
    T.polyEval c (T.fermionPoly i x)
      = T.ιFermion i (FieldDerivSpace.massWeightScale (T.fermion i).massWeight (c : ℂ) x) := by
  have h (y : FieldDerivSpace (T.fermion i)) :
      T.ιFermion i y = T.fermionSymbolMap i y.1 + T.conjFermionSymbolMap i y.2 := by
    rw [fermionSymbolMap, conjFermionSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply,
      ← map_add]
    exact congrArg _ (Prod.ext (add_zero _).symm (zero_add _).symm)
  rw [h, fermionPoly_apply, map_add, polyEval_halfPoly, polyEval_halfPoly,
    FieldDerivSpace.massWeightScale_fst, FieldDerivSpace.massWeightScale_snd, map_smul, map_smul]

/-- The image of a bosonic generator evaluated at `c` is its mass-weight scaling by `c`. -/
lemma polyEval_bosonPoly (c : ℝ) (j : T.BosonSpecies) (y : FieldDerivSpace (T.boson j)) :
    T.polyEval c (T.bosonPoly j y)
      = T.ιBoson j (FieldDerivSpace.massWeightScale (T.boson j).massWeight (c : ℂ) y) := by
  have h (z : FieldDerivSpace (T.boson j)) :
      T.ιBoson j z = T.bosonSymbolMap j z.1 + T.conjBosonSymbolMap j z.2 := by
    rw [bosonSymbolMap, conjBosonSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply,
      ← map_add]
    exact congrArg _ (Prod.ext (add_zero _).symm (zero_add _).symm)
  rw [h, bosonPoly_apply, map_add, polyEval_halfPoly, polyEval_halfPoly,
    FieldDerivSpace.massWeightScale_fst, FieldDerivSpace.massWeightScale_snd, map_smul, map_smul]

/-- The image of a connection generator evaluated at `c` is its mass-weight scaling by `c`.
  The evaluation is pushed through the inclusion of the connection factor, where it is the
  evaluation of the gauge-boson grading. -/
lemma polyEval_connectionPoly (c : ℝ) (v : GaugeBoson.FieldDerivSpace G) :
    T.polyEval c (T.connectionPoly v)
      = T.ιConnection (GaugeBoson.FieldDerivSpace.massWeightScale G c v) := by
  rw [connectionPoly_apply, LocalGaugeFieldAlgebra.complexMassWeightPoly_tmul,
    ← Algebra.TensorProduct.one_def, Polynomial.C_1, one_mul,
    LocalGaugeFieldAlgebra.massWeightPoly_ι, Polynomial.coe_mapAlgHom]
  have h1 : algebraMap ℂ T.LocalFieldAlgebra (c : ℂ) = T.includeConnection
      (algebraMap ℝ (ℂ ⊗[ℝ] SymmetricAlgebra ℝ (GaugeBoson.FieldDerivSpace G)) c) :=
    (T.includeConnection.commutes (c : ℂ)).symm.trans (congrArg T.includeConnection
      (IsScalarTower.algebraMap_apply ℝ ℂ _ c).symm)
  -- term mode: rewriting the evaluation point in the goal is prohibitively slow
  exact (Polynomial.eval₂_map _ _ _).trans
    ((congrArg (fun y => Polynomial.eval₂ T.includeConnection.toRingHom y
        (LocalGaugeFieldAlgebra.jetComponentPoly v)) h1).trans
      ((Polynomial.eval₂_at_apply _ _).trans (congrArg T.includeConnection
        (LocalGaugeFieldAlgebra.jetComponentPoly_eval_algebraMap c v))))

/-- The mass-weight scaling by `c` is the mass-weight polynomial evaluated at `c`, since both are
  algebra maps, and they agree on the generators. -/
lemma massWeightScale_eq_polyEval_comp_massWeightPoly (c : ℝ) :
    T.massWeightScale c = (T.polyEval c).comp T.massWeightPoly :=
  algHom_ext
    (fun i x => by
      rw [massWeightScale_ιFermion, AlgHom.comp_apply, massWeightPoly_ιFermion,
        polyEval_fermionPoly])
    (fun j y => by
      rw [massWeightScale_ιBoson, AlgHom.comp_apply, massWeightPoly_ιBoson, polyEval_bosonPoly])
    (fun v => by
      rw [massWeightScale_ιConnection, AlgHom.comp_apply, massWeightPoly_ιConnection,
        polyEval_connectionPoly])

lemma massWeightScale_apply (c : ℝ) (x : T.LocalFieldAlgebra) :
    T.massWeightScale c x = T.polyEval c (T.massWeightPoly x) :=
  AlgHom.congr_fun (massWeightScale_eq_polyEval_comp_massWeightPoly c) x

variable (T)

/-!

## C. The graded pieces and the filtration

-/

/-- The weight-`n` piece of the local field algebra, the eigenspace on which the
  mass-weight polynomial is the monomial `X ^ n`. -/
noncomputable def massWeightSubmodule (n : ℕ) : Submodule ℂ T.LocalFieldAlgebra where
  carrier := {x | T.massWeightPoly x = Polynomial.monomial n x}
  zero_mem' :=
    (map_zero T.massWeightPoly).trans (Polynomial.monomial_zero_right n).symm
  add_mem' {x y} hx hy :=
    (map_add T.massWeightPoly x y).trans
      ((congrArg₂ (fun p q : Polynomial T.LocalFieldAlgebra => p + q) hx hy).trans
        ((Polynomial.monomial n).map_add x y).symm)
  smul_mem' c x hx :=
    (map_smul T.massWeightPoly c x).trans
      ((congrArg (fun p : Polynomial T.LocalFieldAlgebra => c • p) hx).trans
        (Polynomial.smul_monomial c n x))

variable {T} in
/-- Membership of the weight-`n` piece is the eigenvalue equation. -/
@[simp]
lemma mem_massWeightSubmodule {n : ℕ} {x : T.LocalFieldAlgebra} :
    x ∈ T.massWeightSubmodule n ↔ T.massWeightPoly x = Polynomial.monomial n x := Iff.rfl

variable {T} in
/-- The mass-weight scaling by `c` multiplies the weight-`n` piece by `c ^ n`. -/
lemma massWeightScale_of_mem_massWeightSubmodule {n : ℕ} {x : T.LocalFieldAlgebra}
    (hx : x ∈ T.massWeightSubmodule n) (c : ℝ) :
    T.massWeightScale c x = ((c : ℂ) ^ n) • x := by
  rw [massWeightScale_apply, mem_massWeightSubmodule.mp hx, polyEval_monomial]

variable {T} in
/-- The weight-`n` piece is the set of elements scaled by `c ^ n` under the mass-weight
  scaling by every real `c`. Conversely to the eigenvalue equation, the difference of the two
  sides of it is a polynomial vanishing at every real number. -/
lemma mem_massWeightSubmodule_iff_massWeightScale {n : ℕ} {x : T.LocalFieldAlgebra} :
    x ∈ T.massWeightSubmodule n ↔ ∀ c : ℝ, T.massWeightScale c x = ((c : ℂ) ^ n) • x := by
  refine ⟨fun hx c => massWeightScale_of_mem_massWeightSubmodule hx c, fun h => ?_⟩
  refine mem_massWeightSubmodule.mpr (sub_eq_zero.mp (eq_zero_of_forall_polyEval_eq_zero
    fun c => ?_))
  rw [map_sub, polyEval_monomial, ← massWeightScale_apply, h, sub_self]

/-- The mass-weight filtration, the join of the pieces of weight at most `w`. An element
  lies in it exactly when it is a sum of eigenvectors of the mass-weight polynomial of weight at
  most `w`. -/
noncomputable def massWeightSubmoduleLE (w : ℕ) : Submodule ℂ T.LocalFieldAlgebra :=
  ⨆ k ∈ Finset.range (w + 1), T.massWeightSubmodule k

lemma massWeightSubmodule_le_massWeightSubmoduleLE {k w : ℕ} (h : k ≤ w) :
    T.massWeightSubmodule k ≤ T.massWeightSubmoduleLE w :=
  le_iSup₂ (f := fun k _ => T.massWeightSubmodule k) k (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

variable {T} in
/-- An element of the filtration up to weight `w` has no component above `w`, so the
  coefficient of `X ^ n` in its image under the mass-weight polynomial vanishes for `n > w`. -/
lemma coeff_massWeightPoly_eq_zero_of_mem_massWeightSubmoduleLE {w n : ℕ} (hn : w < n)
    {x : T.LocalFieldAlgebra} (hx : x ∈ T.massWeightSubmoduleLE w) :
    (T.massWeightPoly x).coeff n = 0 := by
  let K : Submodule ℂ T.LocalFieldAlgebra :=
    { carrier := {y | (T.massWeightPoly y).coeff n = 0}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        show (T.massWeightPoly (a + b)).coeff n = 0
        rw [map_add, Polynomial.coeff_add, ha, hb, add_zero]
      smul_mem' := fun c a ha => by
        show (T.massWeightPoly (c • a)).coeff n = 0
        rw [map_smul, AddMonoidAlgebra.coeff_smul_apply, ha, smul_zero] }
  have hle : T.massWeightSubmoduleLE w ≤ K := iSup₂_le fun k hk y hy => by
    show (T.massWeightPoly y).coeff n = 0
    rw [mem_massWeightSubmodule.mp hy,
      Polynomial.coeff_monomial_of_ne _ (by have := Finset.mem_range.mp hk; omega)]
  exact hle hx

/-!

## D. The invariants

-/

/-- The gauge invariants, the elements fixed by every jet of gauge transformations. -/
noncomputable def gaugeInvariants : Submodule ℂ T.LocalFieldAlgebra :=
  ⨅ U : G.gaugeJetGroup, LinearMap.eqLocus (T.repJet U)
    (LinearMap.id : T.LocalFieldAlgebra →ₗ[ℂ] T.LocalFieldAlgebra)

lemma mem_gaugeInvariants_iff {x : T.LocalFieldAlgebra} :
    x ∈ T.gaugeInvariants ↔ ∀ U : G.gaugeJetGroup, T.repJet U x = x := by
  simp only [gaugeInvariants, Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]

/-- The Lorentz invariants, the elements fixed by every Lorentz transformation. -/
noncomputable def lorentzInvariants : Submodule ℂ T.LocalFieldAlgebra :=
  ⨅ Λ : SL(2,ℂ), LinearMap.eqLocus (T.repLorentzGroup Λ)
    (LinearMap.id : T.LocalFieldAlgebra →ₗ[ℂ] T.LocalFieldAlgebra)

lemma mem_lorentzInvariants_iff {x : T.LocalFieldAlgebra} :
    x ∈ T.lorentzInvariants ↔ ∀ Λ : SL(2,ℂ), T.repLorentzGroup Λ x = x := by
  simp only [lorentzInvariants, Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]

/-- The invariants of mass weight at most `w`, the gauge and Lorentz invariants in the
  filtration. A Lagrangian of mass dimension at most `w / 2` is an element of it. -/
noncomputable def invariantsLE (w : ℕ) : Submodule ℂ T.LocalFieldAlgebra :=
  T.massWeightSubmoduleLE w ⊓ (T.gaugeInvariants ⊓ T.lorentzInvariants)

lemma mem_invariantsLE_iff {w : ℕ} {x : T.LocalFieldAlgebra} :
    x ∈ T.invariantsLE w ↔ x ∈ T.massWeightSubmoduleLE w
      ∧ (∀ U : G.gaugeJetGroup, T.repJet U x = x) ∧ ∀ Λ : SL(2,ℂ), T.repLorentzGroup Λ x = x := by
  simp only [invariantsLE, Submodule.mem_inf, mem_gaugeInvariants_iff, mem_lorentzInvariants_iff]

/-!

## E. The contraction of a boson with its conjugate

-/

/-- The contraction `φ† φ` of a bosonic species with its conjugate, through a basis of
  its value space, the sum over the basis of the conjugate coordinate times the coordinate.
  For a scalar in a unitary representation it is the mass term. -/
noncomputable def bosonNormSq (j : T.BosonSpecies) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ (T.BosonValue j)) : T.LocalFieldAlgebra :=
  ∑ i, T.conjBosonSymbol j 0 ((Basis.conj b).dualBasis i) * T.bosonSymbol j 0 (b.dualBasis i)

/-!

## F. Transport along an isomorphism

An isomorphism of local field algebras intertwining the jet gauge action, the Lorentz
action and the mass-weight polynomial carries the graded pieces, the filtration and the
invariants of one datum onto those of the other. This is what relates two presentations
of the same field content, such as a model's table and a hand-built datum.

-/

section Transport

variable {T} {T' : GaugeFieldData G} (e : T.LocalFieldAlgebra ≃ₐ[ℂ] T'.LocalFieldAlgebra)

/-- The mass-weight polynomial is respected, so the weight-`n` piece is carried onto the
  weight-`n` piece. -/
lemma mem_massWeightSubmodule_apply_iff
    (hpoly : ∀ x, (T.massWeightPoly x).map (e : T.LocalFieldAlgebra →+* T'.LocalFieldAlgebra)
      = T'.massWeightPoly (e x))
    (n : ℕ) (x : T.LocalFieldAlgebra) :
    e x ∈ T'.massWeightSubmodule n ↔ x ∈ T.massWeightSubmodule n := by
  have h : Polynomial.monomial n (e x) = (Polynomial.monomial n x).map
      (e : T.LocalFieldAlgebra →+* T'.LocalFieldAlgebra) := by
    rw [Polynomial.map_monomial]
    rfl
  -- term mode: `rw` on polynomials over the local field algebra is slow
  exact (Eq.congr (hpoly x).symm h).trans (Polynomial.map_injective _ e.injective).eq_iff

lemma massWeightSubmodule_map
    (hpoly : ∀ x, (T.massWeightPoly x).map (e : T.LocalFieldAlgebra →+* T'.LocalFieldAlgebra)
      = T'.massWeightPoly (e x)) (n : ℕ) :
    (T.massWeightSubmodule n).map (e : T.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = T'.massWeightSubmodule n := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Submodule.mem_map_equiv (e := e.toLinearEquiv)]
  simp [mem_massWeightSubmodule_apply_iff e hpoly]

lemma massWeightSubmoduleLE_map
    (hpoly : ∀ x, (T.massWeightPoly x).map (e : T.LocalFieldAlgebra →+* T'.LocalFieldAlgebra)
      = T'.massWeightPoly (e x)) (w : ℕ) :
    (T.massWeightSubmoduleLE w).map (e : T.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = T'.massWeightSubmoduleLE w := by
  simp only [massWeightSubmoduleLE, Submodule.map_iSup, massWeightSubmodule_map e hpoly]

/-- The filtration is respected, element by element. -/
lemma mem_massWeightSubmoduleLE_apply_iff
    (hpoly : ∀ x, (T.massWeightPoly x).map (e : T.LocalFieldAlgebra →+* T'.LocalFieldAlgebra)
      = T'.massWeightPoly (e x)) (w : ℕ)
    (x : T.LocalFieldAlgebra) :
    e x ∈ T'.massWeightSubmoduleLE w ↔ x ∈ T.massWeightSubmoduleLE w := by
  rw [← massWeightSubmoduleLE_map e hpoly w, Submodule.mem_map_equiv (e := e.toLinearEquiv)]
  simp

/-- The invariants of mass weight at most `w` are respected, element by element. -/
lemma mem_invariantsLE_apply_iff
    (hjet : ∀ (U : G.gaugeJetGroup) x, e (T.repJet U x) = T'.repJet U (e x))
    (hlor : ∀ (Λ : SL(2,ℂ)) x, e (T.repLorentzGroup Λ x) = T'.repLorentzGroup Λ (e x))
    (hpoly : ∀ x, (T.massWeightPoly x).map (e : T.LocalFieldAlgebra →+* T'.LocalFieldAlgebra)
      = T'.massWeightPoly (e x)) (w : ℕ)
    (x : T.LocalFieldAlgebra) :
    e x ∈ T'.invariantsLE w ↔ x ∈ T.invariantsLE w := by
  simp only [mem_invariantsLE_iff, mem_massWeightSubmoduleLE_apply_iff e hpoly, ← hjet, ← hlor,
    EmbeddingLike.apply_eq_iff_eq]

/-- The invariants of mass weight at most `w` are carried onto the invariants of mass
  weight at most `w` by an isomorphism respecting the two actions and the mass-weight
  polynomial. -/
lemma invariantsLE_map (hjet : ∀ (U : G.gaugeJetGroup) x, e (T.repJet U x) = T'.repJet U (e x))
    (hlor : ∀ (Λ : SL(2,ℂ)) x, e (T.repLorentzGroup Λ x) = T'.repLorentzGroup Λ (e x))
    (hpoly : ∀ x, (T.massWeightPoly x).map (e : T.LocalFieldAlgebra →+* T'.LocalFieldAlgebra)
      = T'.massWeightPoly (e x)) (w : ℕ) :
    (T.invariantsLE w).map (e : T.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = T'.invariantsLE w := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Submodule.mem_map_equiv (e := e.toLinearEquiv), mem_invariantsLE_apply_iff e hjet hlor hpoly]
  simp

end Transport

end GaugeFieldData
