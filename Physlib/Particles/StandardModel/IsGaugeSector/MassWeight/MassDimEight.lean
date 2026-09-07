/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3BiAdjoint
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiAdjoint
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsU1BiAdjoint
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3Adjoint
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2Adjoint
public import Physlib.Relativity.LorentzGroup.Invariants.IsQuadLorentz
public import Mathlib.RepresentationTheory.Invariants
/-!
# Products of two field strengths as bi-adjoint gauge tensors

A single field-strength symbol of the gauge sector carries one adjoint index of the gauge
algebra, so a product of two of them carries two. Restricting the value index to one
factor of the gauge group turns such a product into a family indexed by two adjoint
indices of that factor, and the gauge transformation law of the sector says exactly that
these families are bi-adjoint in the sense of `IsSU3BiAdjoint`, `IsSU2BiAdjoint` and
`IsU1BiAdjoint`.

The gauge invariant those propositions supply is the trace contraction, the Kronecker
contraction of the two adjoint indices; for the underived field strength it is the
familiar kinetic pairing of two field strengths. Its mass weight is the sum of the mass
weights of the two factors, so it lies in the corresponding mass-weight submodule, and it
is gauge invariant, so it lies in the zero-weight piece of the gauge weight decomposition
of that submodule.

The bi-adjoint subspaces themselves, the spans of the components of these families, are
related to the mass-weight submodules in both directions. Each such span lies inside the
mass-weight submodule of the sum of the two mass weights, and conversely the colour and
isospin generators of the zero-weight piece of mass weight eight lie inside the spans of
the underived gluon and `W`-boson families.

- A. The gauge transformation of the gauge-factor field strengths
- B. Products of two field strengths as bi-adjoint families
- C. The bi-adjoint spans inside the mass-weight submodules
- D. The trace contractions and their mass weights
- E. The underived trace contractions at mass weight eight
- F. The weight vectors of mass weight eight inside the bi-adjoint spans
- G. The gauge invariants of mass weight eight
- H. The Lorentz classification of the mass-weight eight invariants
- I. The spans as invariants of mass weight eight
- J. The classifications as equivalences

Putting the two directions together classifies the gauge invariants of mass weight eight
modulo any gauge-stable submodule: such an invariant is a combination of the three
underived trace contractions and the twice-derived hypercharge field strengths. What
carries an unpaired non-abelian adjoint index contributes nothing, by `IsSU3Adjoint` and
`IsSU2Adjoint`, and needs no hypothesis.
Mass weight eight has exactly two shapes, a product of two underived symbols and a single
twice-derived one, and both carry four covector indices and no others, so both are
quadruple Lorentz tensors and the Lorentz classification cuts the combinations down
further, to the four Lorentz contractions of each of the four families.

Both classifications are one-directional as stated, and section I supplies the converse:
each of the two spans consists of invariants of mass weight eight already, the gauge one
because its generators are fixed by the gauge group and carry the right mass weight, and
the Lorentz one because it sits inside the gauge span and is spanned by contractions that
`IsQuadLorentz` shows to be Lorentz invariant. Section J puts the two directions together
as the equivalences `mem_massWeightSubmodule_eight_sup_and_invariant_iff` and
`mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff`.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups Lorentz

namespace IsGaugeSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      F massWeightPoly)

/-!

## A. The gauge transformation of the gauge-factor field strengths

-/

include h in
/-- The field-strength symbol evaluated on a standard-basis coordinate transforms under
  the gauge group through the column of `adjointMatrix` indexed by that coordinate. -/
lemma repGauge_F_coord (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    repGauge g (F l μ ν (GaugeAlgebra.stdBasis.coord c))
      = ∑ b, ((GaugeAlgebra.adjointMatrix g b c : ℝ) : ℂ) •
          F l μ ν (GaugeAlgebra.stdBasis.coord b) := by
  rw [h.repGauge_F g l μ ν,
    show GaugeAlgebra.adjointMap g⁻¹
      = (GaugeAlgebra.adjoint g⁻¹ : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra) from rfl,
    GaugeAlgebra.adjoint_dualMap_coord, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, GaugeAlgebra.adjointMatrix_inv_apply, Complex.coe_smul]

/-- The gluon field strength transforms in the adjoint representation of the `su(3)`
  factor of the gauge group. -/
lemma repGauge_gluonField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 8) :
    repGauge g (h.gluonField l μ ν c)
      = ∑ a : Fin 8, ((GaugeAlgebra.adjointMatrix g (Sum.inl a) (Sum.inl c) : ℝ) : ℂ) •
          h.gluonField l μ ν a := by
  rw [gluonField, h.repGauge_F_coord g l μ ν (Sum.inl c), Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp [gluonField]

/-- The `W`-boson field strength transforms in the adjoint representation of the `su(2)`
  factor of the gauge group. -/
lemma repGauge_wField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 3) :
    repGauge g (h.wField l μ ν c)
      = ∑ i : Fin 3, ((GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl i))
          (Sum.inr (Sum.inl c)) : ℝ) : ℂ) • h.wField l μ ν i := by
  rw [wField, h.repGauge_F_coord g l μ ν (Sum.inr (Sum.inl c)), Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp [wField]

/-- The hypercharge field strength is gauge invariant: the adjoint action of the gauge
  group on the `u(1)` factor of the gauge algebra is trivial. -/
lemma repGauge_hyperchargeField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    repGauge g (h.hyperchargeField l μ ν) = h.hyperchargeField l μ ν := by
  rw [hyperchargeField, h.repGauge_F_coord g l μ ν (Sum.inr (Sum.inr 0)),
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp

/-!

## B. Products of two field strengths as bi-adjoint families

-/

/-- A gauge transformation moves a product of two gluon field strengths as the `SU(3)`
  factor of that gauge group element moves a tensor with two `su(3)` adjoint indices. -/
lemma isSU3BiAdjointMat_gluonField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (g : GaugeGroupI) :
    IsSU3BiAdjointMat (GaugeGroupI.toSU3 g) (repGauge g)
      (fun a : Fin 2 → Fin 8 => h.gluonField l μ ν (a 0) * h.gluonField l' μ' ν' (a 1)) := by
  intro d
  rw [hrepGauge_mul, h.repGauge_gluonField, h.repGauge_gluonField,
    Fintype.sum_mul_sum, IsSU3BiAdjoint.sum_pi_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp [Fin.prod_univ_two]

/-- A product of two gluon field strengths, viewed as a family indexed by the two `su(3)`
  adjoint indices it carries, is a bi-adjoint `su(3)` tensor. -/
lemma isSU3BiAdjoint_gluonField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    IsSU3BiAdjoint B repGauge
      (fun a : Fin 2 → Fin 8 => h.gluonField l μ ν (a 0) * h.gluonField l' μ' ν' (a 1)) :=
  ⟨fun U => h.isSU3BiAdjointMat_gluonField_mul l μ ν l' μ' ν' (U, 1, 1)⟩

/-- A gauge transformation moves a product of two `W`-boson field strengths as the `SU(2)`
  factor of that gauge group element moves a tensor with two `su(2)` adjoint indices. -/
lemma isSU2BiAdjointMat_wField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (g : GaugeGroupI) :
    IsSU2BiAdjointMat (GaugeGroupI.toSU2 g) (repGauge g)
      (fun a : Fin 2 → Fin 3 => h.wField l μ ν (a 0) * h.wField l' μ' ν' (a 1)) := by
  intro d
  rw [hrepGauge_mul, h.repGauge_wField, h.repGauge_wField,
    Fintype.sum_mul_sum, IsSU2BiAdjoint.sum_pi_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp [Fin.prod_univ_two]

/-- A product of two `W`-boson field strengths, viewed as a family indexed by the two
  `su(2)` adjoint indices it carries, is a bi-adjoint `su(2)` tensor. -/
lemma isSU2BiAdjoint_wField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    IsSU2BiAdjoint B repGauge
      (fun a : Fin 2 → Fin 3 => h.wField l μ ν (a 0) * h.wField l' μ' ν' (a 1)) :=
  ⟨fun U => h.isSU2BiAdjointMat_wField_mul l μ ν l' μ' ν' (1, U, 1)⟩

/-- A gauge transformation moves a product of two hypercharge field strengths as the
  `U(1)` factor of that gauge group element moves a tensor with two `u(1)` adjoint
  indices. -/
lemma isU1BiAdjointMat_hyperchargeField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (g : GaugeGroupI) :
    IsU1BiAdjointMat (GaugeGroupI.toU1 g) (repGauge g)
      (fun _ : Fin 2 → Fin 1 => h.hyperchargeField l μ ν * h.hyperchargeField l' μ' ν') :=
  (isU1BiAdjointMat_iff _ _ _).2 fun _ => by
    rw [hrepGauge_mul, h.repGauge_hyperchargeField, h.repGauge_hyperchargeField]

/-- A product of two hypercharge field strengths, viewed as a family indexed by the two
  `u(1)` adjoint indices it carries, is a bi-adjoint `u(1)` tensor. -/
lemma isU1BiAdjoint_hyperchargeField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    IsU1BiAdjoint B repGauge
      (fun _ : Fin 2 → Fin 1 => h.hyperchargeField l μ ν * h.hyperchargeField l' μ' ν') :=
  ⟨fun u => h.isU1BiAdjointMat_hyperchargeField_mul l μ ν l' μ' ν' (1, 1, u)⟩

/-!

## C. The bi-adjoint spans inside the mass-weight submodules

Every component of one of the three families of section B is a product of two
field-strength symbols, one carrying `n` covariant derivatives and one carrying `m`.
Such a product lies in `derivSubmodule n * derivSubmodule m`, and so in the mass-weight
submodule of weight `2 * (2 + n) + 2 * (2 + m)`; a span is the smallest submodule
containing its generators, so the whole bi-adjoint subspace lies there too.

What holds is an inclusion and not an equality. The mass-weight submodule of that weight
also contains the towers carrying more covariant derivatives, and the products mixing
two different gauge factors, and none of those is a component of any of the three
families. For the `u(1)` family the inclusion sharpens, so that its span meets the
mass-weight submodule inside the gauge invariants. That sharpening does not come from
`IsU1BiAdjoint`, which constrains the hypercharge factor alone; it comes from
`repGauge_hyperchargeField`, the transformation law of the hypercharge field strength
itself, which fixes it under every gauge element and so makes every component of the
family gauge invariant.

-/

/-- Every field-strength symbol lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma F_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : F l μ ν φ ∈ h.derivSubmodule n := by
  rw [derivSubmodule]
  exact Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ
    (Submodule.mem_iSup_of_mem ν (Submodule.subset_span ⟨φ, rfl⟩)))

/-- The gluon field strength lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma gluonField_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (a : Fin 8) : h.gluonField l μ ν a ∈ h.derivSubmodule n :=
  h.F_mem_derivSubmodule l μ ν _

/-- The `W`-boson field strength lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma wField_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (i : Fin 3) : h.wField l μ ν i ∈ h.derivSubmodule n :=
  h.F_mem_derivSubmodule l μ ν _

/-- The hypercharge field strength lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma hyperchargeField_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) : h.hyperchargeField l μ ν ∈ h.derivSubmodule n :=
  h.F_mem_derivSubmodule l μ ν _

/-- A product of two derivative submodules lies in the mass-weight submodule of the sum
  of the two mass weights. -/
lemma derivSubmodule_mul_le_massWeightSubmodule (n m : ℕ) :
    h.derivSubmodule n * h.derivSubmodule m
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  Submodule.mul_le.mpr fun _ hx _ hy =>
    h.massWeightSubmodule_mul_le _ _ (Submodule.mul_mem_mul
      (h.derivSubmodule_le_massWeightSubmodule n hx)
      (h.derivSubmodule_le_massWeightSubmodule m hy))

/-- A product of two field-strength symbols with `n` and `m` covariant derivatives has
  mass weight the sum of the two individual mass weights. -/
lemma F_mul_F_mem_massWeightSubmodule {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) (φ' : Module.Dual ℝ GaugeAlgebra) :
    F l μ ν φ * F l' μ' ν' φ'
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  h.derivSubmodule_mul_le_massWeightSubmodule n m (Submodule.mul_mem_mul
    (h.F_mem_derivSubmodule l μ ν φ) (h.F_mem_derivSubmodule l' μ' ν' φ'))

/-- The bi-adjoint subspace of a product of two gluon field strengths lies in the
  product of the two derivative submodules the factors come from. -/
lemma isSU3BiAdjoint_gluonField_mul_span_le_derivSubmodule_mul {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').span
      ≤ h.derivSubmodule n * h.derivSubmodule m := by
  intro x hx
  obtain ⟨c, rfl⟩ :=
    ((h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').mem_span_iff x).1 hx
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
    (Submodule.mul_mem_mul (h.gluonField_mem_derivSubmodule l μ ν (d 0))
      (h.gluonField_mem_derivSubmodule l' μ' ν' (d 1)))

/-- The bi-adjoint subspace of a product of two `W`-boson field strengths lies in the
  product of the two derivative submodules the factors come from. -/
lemma isSU2BiAdjoint_wField_mul_span_le_derivSubmodule_mul {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').span
      ≤ h.derivSubmodule n * h.derivSubmodule m := by
  intro x hx
  obtain ⟨c, rfl⟩ := ((h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').mem_span_iff x).1 hx
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
    (Submodule.mul_mem_mul (h.wField_mem_derivSubmodule l μ ν (d 0))
      (h.wField_mem_derivSubmodule l' μ' ν' (d 1)))

/-- The bi-adjoint subspace of a product of two hypercharge field strengths lies in the
  product of the two derivative submodules the factors come from. -/
lemma isU1BiAdjoint_hyperchargeField_mul_span_le_derivSubmodule_mul {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').span
      ≤ h.derivSubmodule n * h.derivSubmodule m := by
  intro x hx
  obtain ⟨c, rfl⟩ :=
    ((h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').mem_span_iff x).1 hx
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
    (Submodule.mul_mem_mul (h.hyperchargeField_mem_derivSubmodule l μ ν)
      (h.hyperchargeField_mem_derivSubmodule l' μ' ν'))

/-- The bi-adjoint subspace of a product of two gluon field strengths lies in the
  mass-weight submodule of the sum of the two mass weights. -/
lemma isSU3BiAdjoint_gluonField_mul_span_le_massWeightSubmodule {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').span
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  (h.isSU3BiAdjoint_gluonField_mul_span_le_derivSubmodule_mul l μ ν l' μ' ν').trans
    (h.derivSubmodule_mul_le_massWeightSubmodule n m)

/-- The bi-adjoint subspace of a product of two `W`-boson field strengths lies in the
  mass-weight submodule of the sum of the two mass weights. -/
lemma isSU2BiAdjoint_wField_mul_span_le_massWeightSubmodule {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').span
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  (h.isSU2BiAdjoint_wField_mul_span_le_derivSubmodule_mul l μ ν l' μ' ν').trans
    (h.derivSubmodule_mul_le_massWeightSubmodule n m)

/-- The bi-adjoint subspace of a product of two hypercharge field strengths lies in the
  mass-weight submodule of the sum of the two mass weights. -/
lemma isU1BiAdjoint_hyperchargeField_mul_span_le_massWeightSubmodule {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').span
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  (h.isU1BiAdjoint_hyperchargeField_mul_span_le_derivSubmodule_mul l μ ν l' μ' ν').trans
    (h.derivSubmodule_mul_le_massWeightSubmodule n m)

/-- The bi-adjoint subspace of a product of two hypercharge field strengths is a space of
  gauge invariants of the expected mass weight, each hypercharge field strength being
  fixed by the whole gauge group on its own. -/
lemma isU1BiAdjoint_hyperchargeField_mul_span_le_inf {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').span
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants :=
  le_inf (h.isU1BiAdjoint_hyperchargeField_mul_span_le_massWeightSubmodule l μ ν l' μ' ν')
    (IsU1BiAdjoint.span_le_invariants _
      fun g => h.isU1BiAdjointMat_hyperchargeField_mul l μ ν l' μ' ν' g)

/-!

## D. The trace contractions and their mass weights

-/

/-- The trace contraction of a product of two gluon field strengths is the Kronecker
  contraction of the two `su(3)` adjoint indices. -/
lemma traceContraction_gluonField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').traceContraction
      = ∑ a : Fin 8, h.gluonField l μ ν a * h.gluonField l' μ' ν' a := by
  simp [IsSU3BiAdjoint.traceContraction]

/-- The trace contraction of a product of two `W`-boson field strengths is the Kronecker
  contraction of the two `su(2)` adjoint indices. -/
lemma traceContraction_wField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').traceContraction
      = ∑ i : Fin 3, h.wField l μ ν i * h.wField l' μ' ν' i := by
  simp [IsSU2BiAdjoint.traceContraction]

/-- The trace contraction of a product of two hypercharge field strengths is that
  product itself, the `u(1)` factor being one dimensional. -/
lemma traceContraction_hyperchargeField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').traceContraction
      = h.hyperchargeField l μ ν * h.hyperchargeField l' μ' ν' := by
  simp [IsU1BiAdjoint.traceContraction]

/-- The gluon trace contraction is a gauge invariant of the expected mass weight: it lies
  in the mass-weight submodule of weight the sum of the two individual mass weights, and
  it is fixed by the whole gauge group. -/
lemma traceContraction_gluonField_mul_mem {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').traceContraction
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [h.traceContraction_gluonField_mul]
    exact Submodule.sum_mem _ fun a _ => h.F_mul_F_mem_massWeightSubmodule l μ ν _ l' μ' ν' _
  · exact (Representation.mem_invariants _ _).mpr fun g =>
      IsSU3BiAdjoint.map_traceContraction _
        (h.isSU3BiAdjointMat_gluonField_mul l μ ν l' μ' ν' g)

/-- The `W`-boson trace contraction is a gauge invariant of the expected mass weight. -/
lemma traceContraction_wField_mul_mem {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').traceContraction
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [h.traceContraction_wField_mul]
    exact Submodule.sum_mem _ fun i _ => h.F_mul_F_mem_massWeightSubmodule l μ ν _ l' μ' ν' _
  · exact (Representation.mem_invariants _ _).mpr fun g =>
      IsSU2BiAdjoint.map_traceContraction _
        (h.isSU2BiAdjointMat_wField_mul l μ ν l' μ' ν' g)

/-- The hypercharge trace contraction is a gauge invariant of the expected mass weight. -/
lemma traceContraction_hyperchargeField_mul_mem {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').traceContraction
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [h.traceContraction_hyperchargeField_mul]
    exact h.F_mul_F_mem_massWeightSubmodule l μ ν _ l' μ' ν' _
  · exact (Representation.mem_invariants _ _).mpr fun g =>
      IsU1BiAdjoint.map_traceContraction _
        (h.isU1BiAdjointMat_hyperchargeField_mul l μ ν l' μ' ν' g)

/-!

## E. The underived trace contractions at mass weight eight

The product of two underived field strengths has mass weight eight, the `F · F` half of
`massWeightSubmodule_eight_eq`.  Each of the three trace contractions there is a gauge
invariant, so by `GaugeWeightDecomposition.mem_zero_of_invariant` each lies in the
zero-weight piece of the gauge weight decomposition of mass weight eight, computed by
`massWeightSubmoduleGaugeWeightEight_piece_zero`.

-/

/-- The trace contraction of two underived gluon field strengths lies in the mass-weight
  eight submodule and is gauge invariant. -/
lemma traceContraction_gluonField_mul_mem_eight (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ h.massWeightSubmodule 8 ⊓ repGauge.invariants := by
  have hmem := h.traceContraction_gluonField_mul_mem (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ ν
    (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ' ν'
  rwa [show 2 * (2 + 0) + 2 * (2 + 0) = 8 from by norm_num] at hmem

/-- The trace contraction of two underived `W`-boson field strengths lies in the
  mass-weight eight submodule and is gauge invariant. -/
lemma traceContraction_wField_mul_mem_eight (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ h.massWeightSubmodule 8 ⊓ repGauge.invariants := by
  have hmem := h.traceContraction_wField_mul_mem (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ ν
    (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ' ν'
  rwa [show 2 * (2 + 0) + 2 * (2 + 0) = 8 from by norm_num] at hmem

/-- The trace contraction of two underived hypercharge field strengths lies in the
  mass-weight eight submodule and is gauge invariant. -/
lemma traceContraction_hyperchargeField_mul_mem_eight (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ h.massWeightSubmodule 8 ⊓ repGauge.invariants := by
  have hmem := h.traceContraction_hyperchargeField_mul_mem (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ ν
    (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ' ν'
  rwa [show 2 * (2 + 0) + 2 * (2 + 0) = 8 from by norm_num] at hmem

/-- The trace contraction of two underived gluon field strengths lies in the zero-weight
  piece of the gauge weight decomposition of mass weight eight. -/
lemma traceContraction_gluonField_mul_mem_piece_zero (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _
    (Submodule.mem_inf.mp (h.traceContraction_gluonField_mul_mem_eight μ ν μ' ν')).1
    fun g => IsSU3BiAdjoint.map_traceContraction _
      (h.isSU3BiAdjointMat_gluonField_mul ![] μ ν ![] μ' ν' g)

/-- The trace contraction of two underived `W`-boson field strengths lies in the
  zero-weight piece of the gauge weight decomposition of mass weight eight. -/
lemma traceContraction_wField_mul_mem_piece_zero (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _
    (Submodule.mem_inf.mp (h.traceContraction_wField_mul_mem_eight μ ν μ' ν')).1
    fun g => IsSU2BiAdjoint.map_traceContraction _
      (h.isSU2BiAdjointMat_wField_mul ![] μ ν ![] μ' ν' g)

/-- The trace contraction of two underived hypercharge field strengths lies in the
  zero-weight piece of the gauge weight decomposition of mass weight eight. -/
lemma traceContraction_hyperchargeField_mul_mem_piece_zero (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _
    (Submodule.mem_inf.mp (h.traceContraction_hyperchargeField_mul_mem_eight μ ν μ' ν')).1
    fun g => IsU1BiAdjoint.map_traceContraction _
      (h.isU1BiAdjointMat_hyperchargeField_mul ![] μ ν ![] μ' ν' g)

/-!

## F. The weight vectors of mass weight eight inside the bi-adjoint spans

Section C runs from the bi-adjoint side to the mass-weight side. The opposite direction
is available for the parts of the mass-weight submodules that see a single gauge factor.
The gauge weight decomposition of the derivative submodules is built from the weight
vectors `adjVec` of one adjoint index, and on a colour direction such a vector is a
combination of gluon field strengths, on the isospin directions a combination of
`W`-boson field strengths, and on the hypercharge direction the hypercharge field
strength itself. A product of two of them is then a bi-adjoint weight vector of the
matching family, so it lies in the span of that family.

At mass weight eight this covers the gluon root part and the isospin root part of the
zero-weight piece computed by `massWeightSubmoduleGaugeWeightEight_piece_zero`. It does
not cover the neutral Cartan part, whose generators may pair a Cartan direction of one
gauge factor with a Cartan direction of another, and such a mixed product is a component
of none of the three bi-adjoint families.

-/

/-- The `su(3)` adjoint weight indices read as weight indices of the whole gauge
  algebra: the three colour roots and the two colour Cartan directions. -/
def su3AdjIdx : IsSU3BiAdjoint.WeightIdx → Fin 4 ⊕ Fin 4 ⊕ Fin 4
  | Sum.inl r => Sum.inl r.castSucc
  | Sum.inr (Sum.inl r) => Sum.inr (Sum.inl r.castSucc)
  | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c.castSucc.castSucc)

/-- The `su(2)` adjoint weight indices read as weight indices of the whole gauge
  algebra: the isospin root and the isospin Cartan direction. -/
def su2AdjIdx : IsSU2BiAdjoint.WeightIdx → Fin 4 ⊕ Fin 4 ⊕ Fin 4
  | Sum.inl _ => Sum.inl 3
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl 3)
  | Sum.inr (Sum.inr _) => Sum.inr (Sum.inr 2)

/-- A weight vector of the colour part of the adjoint is the matching combination of
  gluon field strengths. -/
lemma sum_wtCoeff_smul_gluonField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (k : IsSU3BiAdjoint.WeightIdx) :
    ∑ a : Fin 8, IsSU3BiAdjoint.wtCoeff k a • h.gluonField l μ ν a
      = h.adjVec l μ ν (su3AdjIdx k) := by
  match k with
  | Sum.inl r =>
    rw [show h.adjVec l μ ν (su3AdjIdx (Sum.inl r))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx r.castSucc).1)
          + Complex.I •
            F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx r.castSucc).2)
        from rfl, IsSU3BiAdjoint.rootIdx_castSucc]
    simp only [IsSU3BiAdjoint.wtCoeff, add_smul, ite_smul, one_smul, zero_smul, mul_ite,
      mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rfl
  | Sum.inr (Sum.inl r) =>
    rw [show h.adjVec l μ ν (su3AdjIdx (Sum.inr (Sum.inl r)))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx r.castSucc).1)
          - Complex.I •
            F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx r.castSucc).2)
        from rfl, IsSU3BiAdjoint.rootIdx_castSucc]
    simp only [IsSU3BiAdjoint.wtCoeff, sub_smul, ite_smul, one_smul, zero_smul, mul_ite,
      mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rfl
  | Sum.inr (Sum.inr c) =>
    rw [show h.adjVec l μ ν (su3AdjIdx (Sum.inr (Sum.inr c)))
        = F l μ ν (GaugeAlgebra.stdBasis.coord
            (GaugeAlgebra.cartanIdx c.castSucc.castSucc)) from rfl,
      IsSU3BiAdjoint.cartanIdx_castSucc]
    simp only [IsSU3BiAdjoint.wtCoeff, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl

/-- A weight vector of the isospin part of the adjoint is the matching combination of
  `W`-boson field strengths. -/
lemma sum_wtCoeff_smul_wField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (k : IsSU2BiAdjoint.WeightIdx) :
    ∑ i : Fin 3, IsSU2BiAdjoint.wtCoeff k i • h.wField l μ ν i
      = h.adjVec l μ ν (su2AdjIdx k) := by
  match k with
  | Sum.inl r =>
    rw [show h.adjVec l μ ν (su2AdjIdx (Sum.inl r))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx 3).1)
          + Complex.I • F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx 3).2)
        from rfl, IsSU2BiAdjoint.rootIdx_three]
    simp only [IsSU2BiAdjoint.wtCoeff, add_smul, ite_smul, one_smul, zero_smul, mul_ite,
      mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rfl
  | Sum.inr (Sum.inl r) =>
    rw [show h.adjVec l μ ν (su2AdjIdx (Sum.inr (Sum.inl r)))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx 3).1)
          - Complex.I • F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx 3).2)
        from rfl, IsSU2BiAdjoint.rootIdx_three]
    simp only [IsSU2BiAdjoint.wtCoeff, sub_smul, ite_smul, one_smul, zero_smul, mul_ite,
      mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rfl
  | Sum.inr (Sum.inr c) =>
    rw [show h.adjVec l μ ν (su2AdjIdx (Sum.inr (Sum.inr c)))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.cartanIdx 2)) from rfl,
      IsSU2BiAdjoint.cartanIdx_two]
    simp only [IsSU2BiAdjoint.wtCoeff, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl

/-- A bi-adjoint weight vector of a product of two gluon field strengths is the product
  of the two contracted field strengths. -/
lemma biVec_gluonField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) (c₀ c₁ : Fin 8 → ℂ) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').biVec c₀ c₁
      = (∑ a : Fin 8, c₀ a • h.gluonField l μ ν a)
        * ∑ b : Fin 8, c₁ b • h.gluonField l' μ' ν' b := by
  rw [IsSU3BiAdjoint.biVec, IsSU3BiAdjoint.sum_pi_two, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp

/-- A bi-adjoint weight vector of a product of two `W`-boson field strengths is the
  product of the two contracted field strengths. -/
lemma biVec_wField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) (c₀ c₁ : Fin 3 → ℂ) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').biVec c₀ c₁
      = (∑ i : Fin 3, c₀ i • h.wField l μ ν i)
        * ∑ j : Fin 3, c₁ j • h.wField l' μ' ν' j := by
  rw [IsSU2BiAdjoint.biVec, IsSU2BiAdjoint.sum_pi_two, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp

/-- A product of two colour weight vectors of the adjoint is a bi-adjoint weight vector
  of the corresponding family of two gluon field strengths. -/
lemma adjVec_mul_adjVec_eq_biVec_gluonField {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (k₀ k₁ : IsSU3BiAdjoint.WeightIdx) :
    h.adjVec l μ ν (su3AdjIdx k₀) * h.adjVec l' μ' ν' (su3AdjIdx k₁)
      = (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').biVec
          (IsSU3BiAdjoint.wtCoeff k₀) (IsSU3BiAdjoint.wtCoeff k₁) := by
  rw [h.biVec_gluonField_mul, h.sum_wtCoeff_smul_gluonField,
    h.sum_wtCoeff_smul_gluonField]

/-- A product of two isospin weight vectors of the adjoint is a bi-adjoint weight vector
  of the corresponding family of two `W`-boson field strengths. -/
lemma adjVec_mul_adjVec_eq_biVec_wField {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (k₀ k₁ : IsSU2BiAdjoint.WeightIdx) :
    h.adjVec l μ ν (su2AdjIdx k₀) * h.adjVec l' μ' ν' (su2AdjIdx k₁)
      = (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').biVec
          (IsSU2BiAdjoint.wtCoeff k₀) (IsSU2BiAdjoint.wtCoeff k₁) := by
  rw [h.biVec_wField_mul, h.sum_wtCoeff_smul_wField, h.sum_wtCoeff_smul_wField]

/-- A product of two colour weight vectors of the adjoint lies in the bi-adjoint subspace
  of the corresponding family of two gluon field strengths. -/
lemma adjVec_mul_adjVec_mem_isSU3BiAdjoint_span {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (k₀ k₁ : IsSU3BiAdjoint.WeightIdx) :
    h.adjVec l μ ν (su3AdjIdx k₀) * h.adjVec l' μ' ν' (su3AdjIdx k₁)
      ∈ (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').span := by
  rw [h.adjVec_mul_adjVec_eq_biVec_gluonField, IsSU3BiAdjoint.span_eq_wtSpan,
    IsSU3BiAdjoint.wtSpan]
  exact Submodule.mem_iSup_of_mem (k₀, k₁) (Submodule.mem_span_singleton_self _)

/-- A product of two isospin weight vectors of the adjoint lies in the bi-adjoint
  subspace of the corresponding family of two `W`-boson field strengths. -/
lemma adjVec_mul_adjVec_mem_isSU2BiAdjoint_span {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (k₀ k₁ : IsSU2BiAdjoint.WeightIdx) :
    h.adjVec l μ ν (su2AdjIdx k₀) * h.adjVec l' μ' ν' (su2AdjIdx k₁)
      ∈ (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').span := by
  rw [h.adjVec_mul_adjVec_eq_biVec_wField, IsSU2BiAdjoint.span_eq_wtSpan,
    IsSU2BiAdjoint.wtSpan]
  exact Submodule.mem_iSup_of_mem (k₀, k₁) (Submodule.mem_span_singleton_self _)

/-- The hypercharge weight vector of the adjoint is the hypercharge field strength, the
  adjoint action of the gauge group on the `u(1)` factor being trivial. -/
lemma adjVec_hyperchargeIdx {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    h.adjVec l μ ν (Sum.inr (Sum.inr 3)) = h.hyperchargeField l μ ν := rfl

/-- A product of two hypercharge weight vectors of the adjoint lies in the bi-adjoint
  subspace of the corresponding family of two hypercharge field strengths. -/
lemma adjVec_mul_adjVec_mem_isU1BiAdjoint_span {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    h.adjVec l μ ν (Sum.inr (Sum.inr 3)) * h.adjVec l' μ' ν' (Sum.inr (Sum.inr 3))
      ∈ (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').span := by
  rw [h.adjVec_hyperchargeIdx, h.adjVec_hyperchargeIdx, IsU1BiAdjoint.span]
  exact Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)

/-- The gluon contribution to the zero-weight piece of mass weight eight lies in the join
  of the bi-adjoint subspaces of the products of two underived gluon field strengths. -/
lemma gluonRootPart_le_iSup_isSU3BiAdjoint_span :
    h.gluonRootPart ≤ ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (μ' : Fin 1 ⊕ Fin 3)
      (ν' : Fin 1 ⊕ Fin 3), (h.isSU3BiAdjoint_gluonField_mul ![] μ ν ![] μ' ν').span := by
  have key : ∀ r : Fin 3, h.rootRaisingSpan r.castSucc * h.rootLoweringSpan r.castSucc
      ≤ ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (μ' : Fin 1 ⊕ Fin 3)
        (ν' : Fin 1 ⊕ Fin 3), (h.isSU3BiAdjoint_gluonField_mul ![] μ ν ![] μ' ν').span := by
    intro r
    rw [rootRaisingSpan, rootLoweringSpan]
    simp only [Submodule.iSup_mul, Submodule.mul_iSup]
    refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun l' =>
      iSup_le fun μ' => iSup_le fun ν' => ?_
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
      Submodule.span_singleton_le_iff_mem, Subsingleton.elim l ![],
      Subsingleton.elim l' ![]]
    exact Submodule.mem_iSup_of_mem μ' (Submodule.mem_iSup_of_mem ν'
      (Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem ν
        (h.adjVec_mul_adjVec_mem_isSU3BiAdjoint_span ![] μ' ν' ![] μ ν
          (Sum.inl r) (Sum.inr (Sum.inl r))))))
  rw [gluonRootPart]
  exact sup_le (key 0) (sup_le (key 1) (key 2))

/-- The isospin contribution to the zero-weight piece of mass weight eight lies in the
  join of the bi-adjoint subspaces of the products of two underived `W`-boson field
  strengths. -/
lemma isospinRootPart_le_iSup_isSU2BiAdjoint_span :
    h.isospinRootPart ≤ ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (μ' : Fin 1 ⊕ Fin 3)
      (ν' : Fin 1 ⊕ Fin 3), (h.isSU2BiAdjoint_wField_mul ![] μ ν ![] μ' ν').span := by
  rw [isospinRootPart, rootRaisingSpan, rootLoweringSpan]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun l' =>
    iSup_le fun μ' => iSup_le fun ν' => ?_
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
    Submodule.span_singleton_le_iff_mem, Subsingleton.elim l ![],
    Subsingleton.elim l' ![]]
  exact Submodule.mem_iSup_of_mem μ' (Submodule.mem_iSup_of_mem ν'
    (Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem ν
      (h.adjVec_mul_adjVec_mem_isSU2BiAdjoint_span ![] μ' ν' ![] μ ν
        (Sum.inl 0) (Sum.inr (Sum.inl 0))))))

/-!

## G. The gauge invariants of mass weight eight

A gauge invariant of mass weight eight lies in the zero-weight piece of the gauge weight
decomposition, and `massWeightSubmoduleGaugeWeightEight_piece_zero` splits that piece into
four parts: the twice-derived symbols on the four weight-zero directions of the adjoint,
the gluon root part, the isospin root part and the neutral part. Section F puts the two
root parts inside the joins of the bi-adjoint subspaces of the underived gluon and
`W`-boson families. The neutral part splits further by gauge group factor: a colour Cartan
direction against a colour Cartan direction is a bi-adjoint weight vector of a gluon
family, the isospin Cartan direction against itself of a `W`-boson family, and hypercharge
against itself of a hypercharge family; what is left pairs a weight-zero direction of one
factor with a weight-zero direction of another.

The three joins are peeled off one at a time by
`IsSU3BiAdjoint.mem_span_sup_invariant_iff` and its `su(2)` twin, each time with the joins
not yet peeled off adjoined to the stable submodule `S`. That is what those sup lemmas
are for, and it is why no independence of the four parts is needed. Each join is itself
gauge stable, so the enlarged submodule stays stable, and the remainder is gauge invariant
for free, being the difference of two invariants. The `u(1)` join needs no classification
at all: a hypercharge field strength is fixed by the whole gauge group, so each of those
subspaces is already the line through its own trace contraction.

What is left over carries an unpaired adjoint index of a non-abelian factor: a
twice-derived symbol on a colour or isospin Cartan direction, and a mixed neutral product,
which pairs a weight-zero direction of one factor with a weight-zero direction of another.
Neither contributes to a gauge invariant, the adjoint representation of `su(3)` and of
`su(2)` having no invariant vector, and `IsSU3Adjoint` and `IsSU2Adjoint` say exactly
that. Section G.5 assembles the families and kills both parts, so nothing about them has
to be assumed.

The twice-derived hypercharge field strengths are the one part of the twice-derived tower
that survives: hypercharge is fixed by the whole gauge group at every derivative order, so
those are genuine gauge invariants of mass weight eight, and they are not combinations of
trace contractions. They are the second summand of the conclusion.

The hypothesis is membership of the zero-weight piece joined with `S`. An element of the
mass-weight submodule joined with `S` need not have its mass-weight eight part invariant,
so nothing places it in the zero-weight piece directly; `mem_piece_zero_sup_of_invariant`
of section G.4 supplies that step for any gauge-stable `S`, and
`exists_mem_of_invariant_massWeightSubmodule_eight_sup` is the resulting statement about
`massWeightSubmodule 8 ⊔ S`.

-/

/-!

## G.1. Peeling a join of bi-adjoint subspaces

-/

/-- A linear map obeying the `su(3)` bi-adjoint transformation law carries the span of the
  components into itself: each component goes to a combination of components. -/
lemma isSU3BiAdjoint_span_stable {T : (Fin 2 → Fin 8) → B}
    (hT : IsSU3BiAdjoint B repGauge T) {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU3BiAdjointMat U f T) {y : B} (hy : y ∈ hT.span) : f y ∈ hT.span := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [map_smul, hf d]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.mem_iSup_of_mem b (Submodule.mem_span_singleton_self _)

/-- A linear map obeying the `su(2)` bi-adjoint transformation law carries the span of the
  components into itself. -/
lemma isSU2BiAdjoint_span_stable {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU2BiAdjoint B repGauge T) {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}
    (hf : IsSU2BiAdjointMat U f T) {y : B} (hy : y ∈ hT.span) : f y ∈ hT.span := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [map_smul, hf d]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.mem_iSup_of_mem b (Submodule.mem_span_singleton_self _)

/-- Peeling a finite join of `su(3)` bi-adjoint subspaces off a gauge-stable submodule:
  a gauge invariant of the join together with `S` is a combination of the trace
  contractions of the families plus a gauge-invariant remainder in `S`. -/
lemma exists_mem_of_invariant_biSup_isSU3BiAdjoint_span {ι : Type} [DecidableEq ι]
    {T : ι → (Fin 2 → Fin 8) → B} (hT : ∀ i, IsSU3BiAdjoint B repGauge (T i))
    (hmat : ∀ (i : ι) (g : GaugeGroupI),
      IsSU3BiAdjointMat (GaugeGroupI.toSU3 g) (repGauge g) (T i))
    (hmul : IsMulRep repGauge) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) (s : Finset ι) {x : B}
    (hx : x ∈ (⨆ i ∈ s, (hT i).span) ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ x - y ∈ ⨆ i ∈ s, ℂ ∙ (hT i).traceContraction := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), (hT i).span) = ⊥ from by simp, bot_sup_eq] at hx
    exact ⟨x, hx, hinv, by simp⟩
  | insert a s ha ih =>
    rw [Finset.iSup_insert, sup_assoc] at hx
    have hstab : ∀ g : GaugeGroupI, ∀ y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S,
        repGauge g y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S := by
      intro g y hy
      have key : ((⨆ i ∈ s, (hT i).span) ⊔ S)
          ≤ Submodule.comap (repGauge g) ((⨆ i ∈ s, (hT i).span) ⊔ S) :=
        sup_le (iSup_le fun i => iSup_le fun hi => fun z hz =>
            Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i
              (Submodule.mem_iSup_of_mem hi
                (isSU3BiAdjoint_span_stable (hT i) (hmat i g) hz))))
          fun z hz => Submodule.mem_sup_right (hS g z hz)
      exact key hy
    obtain ⟨c, y', hy', hxy', hy'inv⟩ :=
      (hT a).mem_span_sup_invariant_iff hmul x _ hstab
        (fun g => IsSU3BiAdjoint.map_traceContraction _ (hmat a g)) hx hinv
    obtain ⟨y, hyS, hyinv, hy'y⟩ := ih hy' hy'inv
    refine ⟨y, hyS, hyinv, ?_⟩
    rw [Finset.iSup_insert, show x - y = c • (hT a).traceContraction + (y' - y) from by
      rw [hxy']; abel]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_right hy'y)

/-- Peeling a finite join of `su(2)` bi-adjoint subspaces off a gauge-stable submodule:
  a gauge invariant of the join together with `S` is a combination of the trace
  contractions of the families plus a gauge-invariant remainder in `S`. -/
lemma exists_mem_of_invariant_biSup_isSU2BiAdjoint_span {ι : Type} [DecidableEq ι]
    {T : ι → (Fin 2 → Fin 3) → B} (hT : ∀ i, IsSU2BiAdjoint B repGauge (T i))
    (hmat : ∀ (i : ι) (g : GaugeGroupI),
      IsSU2BiAdjointMat (GaugeGroupI.toSU2 g) (repGauge g) (T i))
    (hmul : IsMulRep repGauge) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) (s : Finset ι) {x : B}
    (hx : x ∈ (⨆ i ∈ s, (hT i).span) ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ x - y ∈ ⨆ i ∈ s, ℂ ∙ (hT i).traceContraction := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), (hT i).span) = ⊥ from by simp, bot_sup_eq] at hx
    exact ⟨x, hx, hinv, by simp⟩
  | insert a s ha ih =>
    rw [Finset.iSup_insert, sup_assoc] at hx
    have hstab : ∀ g : GaugeGroupI, ∀ y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S,
        repGauge g y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S := by
      intro g y hy
      have key : ((⨆ i ∈ s, (hT i).span) ⊔ S)
          ≤ Submodule.comap (repGauge g) ((⨆ i ∈ s, (hT i).span) ⊔ S) :=
        sup_le (iSup_le fun i => iSup_le fun hi => fun z hz =>
            Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i
              (Submodule.mem_iSup_of_mem hi
                (isSU2BiAdjoint_span_stable (hT i) (hmat i g) hz))))
          fun z hz => Submodule.mem_sup_right (hS g z hz)
      exact key hy
    obtain ⟨c, y', hy', hxy', hy'inv⟩ :=
      (hT a).mem_span_sup_invariant_iff hmul x _ hstab
        (fun g => IsSU2BiAdjoint.map_traceContraction _ (hmat a g)) hx hinv
    obtain ⟨y, hyS, hyinv, hy'y⟩ := ih hy' hy'inv
    refine ⟨y, hyS, hyinv, ?_⟩
    rw [Finset.iSup_insert, show x - y = c • (hT a).traceContraction + (y' - y) from by
      rw [hxy']; abel]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_right hy'y)

/-- The subspace of a bi-adjoint `u(1)` family is the line through its trace contraction:
  there is a single pair of `u(1)` adjoint indices, and the trace contraction is the
  component it names. -/
lemma isU1BiAdjoint_span_eq_span_traceContraction {T : (Fin 2 → Fin 1) → B}
    (hT : IsU1BiAdjoint B repGauge T) : hT.span = ℂ ∙ hT.traceContraction := by
  have htc : hT.traceContraction = T ![0, 0] := by
    show ∑ a : Fin 1, T ![a, a] = _
    simp
  show (⨆ d, ℂ ∙ T d) = _
  rw [htc]
  exact le_antisymm (iSup_le fun d => by rw [Subsingleton.elim d ![0, 0]])
    (le_iSup (fun d => ℂ ∙ T d) ![0, 0])

/-- Peeling a join of `u(1)` bi-adjoint subspaces off a submodule needs no classification:
  every component of such a family is fixed by the whole gauge group once the
  transformation law holds at every gauge element, so the join is a join of lines through
  the trace contractions and the remainder is invariant for free. -/
lemma exists_mem_of_invariant_iSup_isU1BiAdjoint_span {ι : Type}
    {T : ι → (Fin 2 → Fin 1) → B} (hT : ∀ i, IsU1BiAdjoint B repGauge (T i))
    (hmat : ∀ (i : ι) (g : GaugeGroupI),
      IsU1BiAdjointMat (GaugeGroupI.toU1 g) (repGauge g) (T i))
    (S : Submodule ℂ B) {x : B} (hx : x ∈ (⨆ i, (hT i).span) ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ x - y ∈ ⨆ i, ℂ ∙ (hT i).traceContraction := by
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
  have huinv : ∀ g : GaugeGroupI, repGauge g u = u := by
    intro g
    refine Submodule.iSup_induction (motive := fun v => repGauge g v = v)
      (fun i => (hT i).span) hu (fun i v hv => (hT i).map_of_mem_span (hmat i g) hv)
      (map_zero _) fun v w hv hw => by rw [map_add, hv, hw]
  refine ⟨z, hz, fun g => ?_, ?_⟩
  · have hg := hinv g
    rw [← huz, map_add, huinv g, add_right_inj] at hg
    exact hg
  · rw [← huz, add_sub_cancel_right]
    refine Submodule.iSup_induction (motive := fun v => v ∈ ⨆ i, ℂ ∙ (hT i).traceContraction)
      (fun i => (hT i).span) hu (fun i v hv => ?_) (Submodule.zero_mem _)
      fun v w hv hw => Submodule.add_mem _ hv hw
    rw [isU1BiAdjoint_span_eq_span_traceContraction (hT i)] at hv
    exact Submodule.mem_iSup_of_mem i hv

/-!

## G.2. The neutral part split by gauge group factor

-/

/-- The span of the underived colour Cartan vectors: the two weight-zero directions of the
  `su(3)` factor of the gauge algebra. -/
noncomputable def colourCartanSpan : Submodule ℂ B :=
  ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (c : Fin 2),
    ℂ ∙ h.adjVec (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ ν
      (Sum.inr (Sum.inr c.castSucc.castSucc))

/-- The span of the underived isospin Cartan vectors: the weight-zero direction of the
  `su(2)` factor of the gauge algebra. -/
noncomputable def isospinCartanSpan : Submodule ℂ B :=
  ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
    ℂ ∙ h.adjVec (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ ν (Sum.inr (Sum.inr 2))

/-- The span of the underived hypercharge vectors: the `u(1)` direction of the gauge
  algebra, which carries weight zero on its own. -/
noncomputable def hyperchargeCartanSpan : Submodule ℂ B :=
  ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
    ℂ ∙ h.adjVec (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ ν (Sum.inr (Sum.inr 3))

/-- The weight-zero directions of the adjoint split by gauge group factor: the two colour
  Cartan directions, the isospin Cartan direction and hypercharge. -/
lemma cartanSpan_le_sup :
    h.cartanSpan
      ≤ h.colourCartanSpan ⊔ (h.isospinCartanSpan ⊔ h.hyperchargeCartanSpan) := by
  rw [cartanSpan, colourCartanSpan, isospinCartanSpan, hyperchargeCartanSpan]
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun c => ?_
  rw [Subsingleton.elim l ![]]
  fin_cases c
  · refine le_sup_of_le_left (le_iSup_of_le μ ?_)
    refine le_iSup_of_le ν ?_
    exact le_iSup_of_le (0 : Fin 2) le_rfl
  · refine le_sup_of_le_left (le_iSup_of_le μ ?_)
    refine le_iSup_of_le ν ?_
    exact le_iSup_of_le (1 : Fin 2) le_rfl
  · refine le_sup_of_le_right (le_sup_of_le_left (le_iSup_of_le μ ?_))
    exact le_iSup_of_le ν le_rfl
  · refine le_sup_of_le_right (le_sup_of_le_right (le_iSup_of_le μ ?_))
    exact le_iSup_of_le ν le_rfl

/-- The index of a product of two underived field strengths: the two covector indices of
  the first factor followed by the two covector indices of the second, read as one family
  of four four-vector indices so that the Lorentz classification applies to it. -/
abbrev EightIdx : Type := Fin 4 → Fin 1 ⊕ Fin 3

/-- The join, over all pairs of covector indices, of the bi-adjoint subspaces of the
  products of two underived gluon field strengths. -/
noncomputable def gluonPairSpan : Submodule ℂ B :=
  ⨆ p : EightIdx,
    (h.isSU3BiAdjoint_gluonField_mul ![] (p 0) (p 1) ![] (p 2) (p 3)).span

/-- The join, over all pairs of covector indices, of the bi-adjoint subspaces of the
  products of two underived `W`-boson field strengths. -/
noncomputable def wPairSpan : Submodule ℂ B :=
  ⨆ p : EightIdx,
    (h.isSU2BiAdjoint_wField_mul ![] (p 0) (p 1) ![] (p 2) (p 3)).span

/-- The join, over all pairs of covector indices, of the bi-adjoint subspaces of the
  products of two underived hypercharge field strengths. -/
noncomputable def hyperchargePairSpan : Submodule ℂ B :=
  ⨆ p : EightIdx,
    (h.isU1BiAdjoint_hyperchargeField_mul ![] (p 0) (p 1) ![] (p 2) (p 3)).span

/-- The mixed neutral products: a weight-zero direction of one gauge group factor against
  a weight-zero direction of another. Such a product carries an unpaired adjoint index of
  each of the two factors, so it is a component of none of the three bi-adjoint
  families. -/
noncomputable def mixedCartanPart : Submodule ℂ B :=
  h.colourCartanSpan * (h.isospinCartanSpan ⊔ h.hyperchargeCartanSpan)
    ⊔ ((h.isospinCartanSpan ⊔ h.hyperchargeCartanSpan) * h.colourCartanSpan
      ⊔ (h.isospinCartanSpan * h.hyperchargeCartanSpan
        ⊔ h.hyperchargeCartanSpan * h.isospinCartanSpan))

/-- A product of two colour Cartan directions is a bi-adjoint weight vector of a family of
  two gluon field strengths. -/
lemma colourCartanSpan_mul_self_le : h.colourCartanSpan * h.colourCartanSpan
    ≤ h.gluonPairSpan := by
  rw [colourCartanSpan, gluonPairSpan]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun μ => iSup_le fun ν => iSup_le fun c => iSup_le fun μ' =>
    iSup_le fun ν' => iSup_le fun c' => ?_
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
    Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_iSup_of_mem ![μ', ν', μ, ν]
    (h.adjVec_mul_adjVec_mem_isSU3BiAdjoint_span ![] μ' ν' ![] μ ν
      (Sum.inr (Sum.inr c')) (Sum.inr (Sum.inr c)))

/-- A product of two isospin Cartan directions is a bi-adjoint weight vector of a family
  of two `W`-boson field strengths. -/
lemma isospinCartanSpan_mul_self_le : h.isospinCartanSpan * h.isospinCartanSpan
    ≤ h.wPairSpan := by
  rw [isospinCartanSpan, wPairSpan]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun μ => iSup_le fun ν => iSup_le fun μ' => iSup_le fun ν' => ?_
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
    Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_iSup_of_mem ![μ', ν', μ, ν]
    (h.adjVec_mul_adjVec_mem_isSU2BiAdjoint_span ![] μ' ν' ![] μ ν
      (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0)))

/-- A product of two hypercharge directions is a component of a family of two hypercharge
  field strengths. -/
lemma hyperchargeCartanSpan_mul_self_le :
    h.hyperchargeCartanSpan * h.hyperchargeCartanSpan ≤ h.hyperchargePairSpan := by
  rw [hyperchargeCartanSpan, hyperchargePairSpan]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun μ => iSup_le fun ν => iSup_le fun μ' => iSup_le fun ν' => ?_
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
    Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_iSup_of_mem ![μ', ν', μ, ν]
    (h.adjVec_mul_adjVec_mem_isU1BiAdjoint_span ![] μ' ν' ![] μ ν)

/-- The gluon contribution to the zero-weight piece lies in the join of the bi-adjoint
  subspaces of the products of two underived gluon field strengths. -/
lemma gluonRootPart_le_gluonPairSpan : h.gluonRootPart ≤ h.gluonPairSpan :=
  h.gluonRootPart_le_iSup_isSU3BiAdjoint_span.trans
    (iSup_le fun μ => iSup_le fun ν => iSup_le fun μ' => iSup_le fun ν' =>
      le_iSup (fun p : EightIdx =>
        (h.isSU3BiAdjoint_gluonField_mul ![] (p 0) (p 1) ![] (p 2) (p 3)).span)
        ![μ, ν, μ', ν'])

/-- The isospin contribution to the zero-weight piece lies in the join of the bi-adjoint
  subspaces of the products of two underived `W`-boson field strengths. -/
lemma isospinRootPart_le_wPairSpan : h.isospinRootPart ≤ h.wPairSpan :=
  h.isospinRootPart_le_iSup_isSU2BiAdjoint_span.trans
    (iSup_le fun μ => iSup_le fun ν => iSup_le fun μ' => iSup_le fun ν' =>
      le_iSup (fun p : EightIdx =>
        (h.isSU2BiAdjoint_wField_mul ![] (p 0) (p 1) ![] (p 2) (p 3)).span)
        ![μ, ν, μ', ν'])

/-- The neutral contribution to the zero-weight piece splits by gauge group factor: the
  products pairing a factor with itself lie in the matching bi-adjoint subspaces, and what
  is left is the mixed part, carrying an unpaired adjoint index of two different
  factors. -/
lemma neutralCartanPart_le :
    h.neutralCartanPart
      ≤ h.mixedCartanPart ⊔ (h.gluonPairSpan ⊔ (h.wPairSpan ⊔ h.hyperchargePairSpan)) := by
  have hmono : ∀ P P' Q Q' : Submodule ℂ B, P ≤ P' → Q ≤ Q' → P * Q ≤ P' * Q' :=
    fun _ _ _ _ hp hq => Submodule.mul_le.mpr fun _ hx _ hy =>
      Submodule.mul_mem_mul (hp hx) (hq hy)
  have expand : ∀ P Q P' Q' : Submodule ℂ B,
      (P ⊔ Q) * (P' ⊔ Q') = (P * P' ⊔ Q * P') ⊔ (P * Q' ⊔ Q * Q') := fun P Q P' Q' => by
    rw [Submodule.mul_sup, Submodule.sup_mul, Submodule.sup_mul]
  rw [neutralCartanPart]
  refine le_trans (hmono _ _ _ _ h.cartanSpan_le_sup h.cartanSpan_le_sup) ?_
  rw [mixedCartanPart, expand]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · exact le_sup_of_le_right (le_sup_of_le_left h.colourCartanSpan_mul_self_le)
  · exact le_sup_of_le_left (le_sup_of_le_right le_sup_left)
  · exact le_sup_of_le_left le_sup_left
  · rw [expand]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact le_sup_of_le_right (le_sup_of_le_right
        (le_sup_of_le_left h.isospinCartanSpan_mul_self_le))
    · exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_right le_sup_right))
    · exact le_sup_of_le_left (le_sup_of_le_right (le_sup_of_le_right le_sup_left))
    · exact le_sup_of_le_right (le_sup_of_le_right
        (le_sup_of_le_right h.hyperchargeCartanSpan_mul_self_le))

/-- The twice-derived hypercharge field strengths, indexed by the two derivative slots and
  the two covector indices. The hypercharge field strength is fixed by the whole gauge
  group at every derivative order, so these are genuine gauge invariants of mass weight
  eight, and they are not products of two field strengths. -/
noncomputable def hyperchargeDerivSpan : Submodule ℂ B :=
  ⨆ d : EightIdx, ℂ ∙ h.hyperchargeField ![d 0, d 1] (d 2) (d 3)

/-- The twice-derived symbols on the colour and isospin Cartan directions: the part of the
  twice-derived tower that carries an unpaired adjoint index of a non-abelian factor. -/
noncomputable def derivCartanNonAbelianPart : Submodule ℂ B :=
  ⨆ (l : Fin 2 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (c : Fin 3),
    ℂ ∙ h.adjVec l μ ν (Sum.inr (Sum.inr c.castSucc))

/-- A vector of two covector indices is the tuple of its own two entries. -/
lemma etaExpand_two (l : Fin 2 → Fin 1 ⊕ Fin 3) : ![l 0, l 1] = l := by
  funext i
  fin_cases i <;> simp

/-- The twice-derived hypercharge field strengths are fixed pointwise by the gauge group,
  the adjoint action on the `u(1)` factor being trivial. -/
lemma repGauge_of_mem_hyperchargeDerivSpan (g : GaugeGroupI) {y : B}
    (hy : y ∈ h.hyperchargeDerivSpan) : repGauge g y = y := by
  rw [hyperchargeDerivSpan] at hy
  refine Submodule.iSup_induction (motive := fun v => repGauge g v = v) _ hy
    (fun d v hv => ?_) (map_zero _) fun v w hv hw => by rw [map_add, hv, hw]
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [map_smul, h.repGauge_hyperchargeField]

/-- The twice-derived hypercharge span is stable under the gauge group. -/
lemma hyperchargeDerivSpan_stable (g : GaugeGroupI) {y : B}
    (hy : y ∈ h.hyperchargeDerivSpan) : repGauge g y ∈ h.hyperchargeDerivSpan := by
  rw [h.repGauge_of_mem_hyperchargeDerivSpan g hy]
  exact hy

/-- Splitting off a submodule the gauge group fixes pointwise: the remainder is gauge
  invariant for free, being the difference of two invariants. -/
lemma exists_mem_of_invariant_sup_fixed (V S : Submodule ℂ B)
    (hV : ∀ g : GaugeGroupI, ∀ v ∈ V, repGauge g v = v) {x : B} (hx : x ∈ V ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y) ∧ x - y ∈ V := by
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
  refine ⟨z, hz, fun g => ?_, ?_⟩
  · have hg := hinv g
    rw [← huz, map_add, hV g u hu, add_right_inj] at hg
    exact hg
  · rw [← huz, add_sub_cancel_right]
    exact hu

/-- The zero-weight piece of mass weight eight, bounded by the parts carrying an unpaired
  non-abelian adjoint index on the one side, and the three bi-adjoint joins together with
  the twice-derived hypercharge span on the other. -/
lemma massWeightSubmoduleGaugeWeightEight_piece_zero_le :
    (h.massWeightSubmoduleGaugeWeightEight).piece 0
      ≤ (h.derivCartanNonAbelianPart ⊔ h.mixedCartanPart)
        ⊔ (h.gluonPairSpan ⊔ (h.wPairSpan ⊔ (h.hyperchargePairSpan
          ⊔ h.hyperchargeDerivSpan))) := by
  rw [h.massWeightSubmoduleGaugeWeightEight_piece_zero]
  refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_))
  · refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun c => ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have hcart : ∀ c' : Fin 3, F l μ ν (GaugeAlgebra.stdBasis.coord
        (GaugeAlgebra.cartanIdx c'.castSucc)) ∈ h.derivCartanNonAbelianPart := by
      intro c'
      exact Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ
        (Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem c'
          (Submodule.mem_span_singleton_self _))))
    fin_cases c
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (hcart 0))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (hcart 1))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (hcart 2))
    · refine Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_sup_right
        (Submodule.mem_sup_right ?_)))
      refine Submodule.mem_iSup_of_mem ![l 0, l 1, μ, ν] ?_
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, etaExpand_two]
      exact Submodule.mem_span_singleton_self _
  · exact le_sup_of_le_right (le_sup_of_le_left h.gluonRootPart_le_gluonPairSpan)
  · exact le_sup_of_le_right (le_sup_of_le_right
      (le_sup_of_le_left h.isospinRootPart_le_wPairSpan))
  · refine h.neutralCartanPart_le.trans (sup_le (le_sup_of_le_left le_sup_right) ?_)
    exact sup_le (le_sup_of_le_right le_sup_left) (sup_le
      (le_sup_of_le_right (le_sup_of_le_right le_sup_left))
      (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_left))))

/-!

## G.5. The unpaired non-abelian adjoint indices

A twice-derived symbol on a colour or isospin Cartan direction carries one unpaired
adjoint index of a non-abelian factor, and `IsSU3Adjoint` and `IsSU2Adjoint` say that such
a family has no gauge invariant in its span at all. Their sup forms therefore push a gauge
invariant of such a span joined with a stable submodule into the stable submodule: the
whole contribution of those directions to an invariant is nothing. Peeling a finite join
of them off works as for the bi-adjoint families, and needs the same stability, which each
span has because the transformation law holds at every gauge element.

-/

/-- The gluon field strengths at fixed derivative slots and covector indices form a family
  of one `su(3)` adjoint index. -/
lemma isSU3Adjoint_gluonField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    IsSU3Adjoint B repGauge (fun a : Fin 8 => h.gluonField l μ ν a) where
  repGauge_T U c := h.repGauge_gluonField (U, 1, 1) l μ ν c

/-- The transformation law of the gluon family at every gauge element, not only at the
  colour ones. -/
lemma isSU3AdjointMat_gluonField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (g : GaugeGroupI) :
    IsSU3AdjointMat (GaugeGroupI.toSU3 g) (repGauge g)
      (fun a : Fin 8 => h.gluonField l μ ν a) :=
  fun c => h.repGauge_gluonField g l μ ν c

/-- The `W`-boson field strengths at fixed derivative slots and covector indices form a
  family of one `su(2)` adjoint index. -/
lemma isSU2Adjoint_wField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    IsSU2Adjoint B repGauge (fun i : Fin 3 => h.wField l μ ν i) where
  repGauge_T U c := h.repGauge_wField (1, U, 1) l μ ν c

/-- The transformation law of the `W`-boson family at every gauge element. -/
lemma isSU2AdjointMat_wField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (g : GaugeGroupI) :
    IsSU2AdjointMat (GaugeGroupI.toSU2 g) (repGauge g)
      (fun i : Fin 3 => h.wField l μ ν i) :=
  fun c => h.repGauge_wField g l μ ν c

/-- A linear map obeying the `su(3)` adjoint transformation law carries the span of the
  components into itself. -/
lemma isSU3Adjoint_span_stable {T : Fin 8 → B} (hT : IsSU3Adjoint B repGauge T)
    {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B} (hf : IsSU3AdjointMat U f T)
    {y : B} (hy : y ∈ hT.span) : f y ∈ hT.span := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [map_smul, hf d]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.mem_iSup_of_mem b (Submodule.mem_span_singleton_self _)

/-- A linear map obeying the `su(2)` adjoint transformation law carries the span of the
  components into itself. -/
lemma isSU2Adjoint_span_stable {T : Fin 3 → B} (hT : IsSU2Adjoint B repGauge T)
    {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B} (hf : IsSU2AdjointMat U f T)
    {y : B} (hy : y ∈ hT.span) : f y ∈ hT.span := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [map_smul, hf d]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.mem_iSup_of_mem b (Submodule.mem_span_singleton_self _)

/-- A finite join of indexed suprema over a `Finset.univ` is the plain supremum. -/
lemma biSup_univ {ι : Type} [Fintype ι] (f : ι → Submodule ℂ B) :
    (⨆ i ∈ (Finset.univ : Finset ι), f i) = ⨆ i, f i := by simp

/-- Peeling a finite join of `su(3)` adjoint subspaces off a colour-stable submodule: a
  colour invariant of the join together with `S` lies in `S`, the adjoint representation
  of `su(3)` having no invariant vector. Only colour stability is needed, and each adjoint
  span has it from the transformation law itself. -/
lemma mem_of_su3_invariant_biSup_isSU3Adjoint_span {ι : Type} [DecidableEq ι]
    {T : ι → Fin 8 → B} (hT : ∀ i, IsSU3Adjoint B repGauge (T i)) (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S)
    (s : Finset ι) {x : B} (hx : x ∈ (⨆ i ∈ s, (hT i).span) ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) : x ∈ S := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    rwa [show (⨆ i ∈ (∅ : Finset ι), (hT i).span) = ⊥ from by simp, bot_sup_eq] at hx
  | insert a s ha ih =>
    rw [Finset.iSup_insert, sup_assoc] at hx
    have hstab : ∀ U : specialUnitaryGroup (Fin 3) ℂ,
        ∀ y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S,
        repGauge (U, 1, 1) y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S := by
      intro U y hy
      have key : ((⨆ i ∈ s, (hT i).span) ⊔ S)
          ≤ Submodule.comap (repGauge (U, 1, 1)) ((⨆ i ∈ s, (hT i).span) ⊔ S) :=
        sup_le (iSup_le fun i => iSup_le fun hi => fun z hz =>
            Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i
              (Submodule.mem_iSup_of_mem hi
                (isSU3Adjoint_span_stable (hT i) ((hT i).repGauge_T U) hz))))
          fun z hz => Submodule.mem_sup_right (hS U z hz)
      exact key hy
    exact ih ((hT a).mem_of_mem_span_sup_su3_invariant x _ hstab hx hinv) hinv

/-- Peeling a finite join of `su(2)` adjoint subspaces off an isospin-stable submodule. -/
lemma mem_of_su2_invariant_biSup_isSU2Adjoint_span {ι : Type} [DecidableEq ι]
    {T : ι → Fin 3 → B} (hT : ∀ i, IsSU2Adjoint B repGauge (T i)) (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, U, 1) y ∈ S)
    (s : Finset ι) {x : B} (hx : x ∈ (⨆ i ∈ s, (hT i).span) ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) : x ∈ S := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    rwa [show (⨆ i ∈ (∅ : Finset ι), (hT i).span) = ⊥ from by simp, bot_sup_eq] at hx
  | insert a s ha ih =>
    rw [Finset.iSup_insert, sup_assoc] at hx
    have hstab : ∀ U : specialUnitaryGroup (Fin 2) ℂ,
        ∀ y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S,
        repGauge (1, U, 1) y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S := by
      intro U y hy
      have key : ((⨆ i ∈ s, (hT i).span) ⊔ S)
          ≤ Submodule.comap (repGauge (1, U, 1)) ((⨆ i ∈ s, (hT i).span) ⊔ S) :=
        sup_le (iSup_le fun i => iSup_le fun hi => fun z hz =>
            Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i
              (Submodule.mem_iSup_of_mem hi
                (isSU2Adjoint_span_stable (hT i) ((hT i).repGauge_T U) hz))))
          fun z hz => Submodule.mem_sup_right (hS U z hz)
      exact key hy
    exact ih ((hT a).mem_of_mem_span_sup_su2_invariant x _ hstab hx hinv) hinv

/-- The `W`-boson field strengths are fixed by the colour factor of the gauge group: the
  adjoint action on the `su(2)` block reads the isospin factor alone. -/
lemma repGauge_su3_wField (U : specialUnitaryGroup (Fin 3) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (i : Fin 3) :
    repGauge (U, 1, 1) (h.wField l μ ν i) = h.wField l μ ν i := by
  rw [h.repGauge_wField (U, 1, 1) l μ ν i]
  have hM : ∀ j : Fin 3, GaugeAlgebra.adjointMatrix ((U, 1, 1) : GaugeGroupI)
      (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inl i)) = if j = i then 1 else 0 := by
    intro j
    have h1 : GaugeAlgebra.adjointMatrix ((U, 1, 1) : GaugeGroupI)
        (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inl i))
        = GaugeAlgebra.adjointMatrix (1 : GaugeGroupI)
          (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inl i)) := rfl
    rw [h1, GaugeAlgebra.adjointMatrix_one, Matrix.one_apply]
    simp
  simp only [hM]
  simp

/-- The two neutral underived directions that pair with a colour index in the mixed
  neutral products: the isospin Cartan direction and hypercharge. -/
noncomputable def neutralVec (μ ν : Fin 1 ⊕ Fin 3) : Fin 2 → B
  | 0 => h.wField ![] μ ν GaugeAlgebra.su2CartanId
  | 1 => h.hyperchargeField ![] μ ν

/-- The neutral directions are fixed by the colour factor of the gauge group. -/
lemma repGauge_su3_neutralVec (U : specialUnitaryGroup (Fin 3) ℂ) (μ ν : Fin 1 ⊕ Fin 3)
    (j : Fin 2) : repGauge (U, 1, 1) (h.neutralVec μ ν j) = h.neutralVec μ ν j := by
  fin_cases j
  · exact h.repGauge_su3_wField U ![] μ ν GaugeAlgebra.su2CartanId
  · exact h.repGauge_hyperchargeField (U, 1, 1) ![] μ ν

/-- The index of a twice-derived symbol: the two derivative slots and the two covector
  indices. -/
abbrev DerivIdx : Type :=
  (Fin 2 → Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)

/-- The index of a mixed neutral product: the two covector indices of the colour factor,
  the two of the neutral factor, and which of the two neutral directions it is. -/
abbrev MixIdx : Type :=
  (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × Fin 2

/-- The index of a family carrying one unpaired `su(3)` adjoint index at mass weight
  eight: a twice-derived gluon tower, or an underived gluon field strength against a
  neutral underived factor on either side. -/
abbrev ColourIdx : Type := DerivIdx ⊕ (MixIdx ⊕ MixIdx)

/-- The families carrying one unpaired `su(3)` adjoint index. -/
noncomputable def colourFamily : ColourIdx → Fin 8 → B
  | Sum.inl p => fun a => h.gluonField p.1 p.2.1 p.2.2 a
  | Sum.inr (Sum.inl q) =>
      fun a => h.gluonField ![] q.1 q.2.1 a * h.neutralVec q.2.2.1 q.2.2.2.1 q.2.2.2.2
  | Sum.inr (Sum.inr q) =>
      fun a => h.neutralVec q.2.2.1 q.2.2.2.1 q.2.2.2.2 * h.gluonField ![] q.1 q.2.1 a

/-- Each of those families is an `su(3)` adjoint family: the colour factor moves the gluon
  index and fixes the neutral factor. -/
lemma isSU3Adjoint_colourFamily (i : ColourIdx) :
    IsSU3Adjoint B repGauge (h.colourFamily i) := by
  rcases i with p | (q | q)
  · exact h.isSU3Adjoint_gluonField p.1 p.2.1 p.2.2
  · refine ⟨fun U c => ?_⟩
    show repGauge (U, 1, 1) (h.gluonField ![] q.1 q.2.1 c
      * h.neutralVec q.2.2.1 q.2.2.2.1 q.2.2.2.2) = _
    rw [hrepGauge_mul, h.repGauge_gluonField (U, 1, 1), h.repGauge_su3_neutralVec,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc]; rfl
  · refine ⟨fun U c => ?_⟩
    show repGauge (U, 1, 1) (h.neutralVec q.2.2.1 q.2.2.2.1 q.2.2.2.2
      * h.gluonField ![] q.1 q.2.1 c) = _
    rw [hrepGauge_mul, h.repGauge_gluonField (U, 1, 1), h.repGauge_su3_neutralVec,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_smul_comm]; rfl

/-- The index of a family carrying one unpaired `su(2)` adjoint index at mass weight
  eight: a twice-derived `W`-boson tower, or an underived `W`-boson field strength against
  an underived hypercharge field strength on either side. -/
abbrev IsospinIdx : Type := DerivIdx ⊕ (EightIdx ⊕ EightIdx)

/-- The families carrying one unpaired `su(2)` adjoint index. -/
noncomputable def isospinFamily : IsospinIdx → Fin 3 → B
  | Sum.inl p => fun i => h.wField p.1 p.2.1 p.2.2 i
  | Sum.inr (Sum.inl q) =>
      fun i => h.wField ![] (q 0) (q 1) i * h.hyperchargeField ![] (q 2) (q 3)
  | Sum.inr (Sum.inr q) =>
      fun i => h.hyperchargeField ![] (q 2) (q 3) * h.wField ![] (q 0) (q 1) i

/-- Each of those families is an `su(2)` adjoint family: the isospin factor moves the
  `W`-boson index and fixes hypercharge. -/
lemma isSU2Adjoint_isospinFamily (i : IsospinIdx) :
    IsSU2Adjoint B repGauge (h.isospinFamily i) := by
  rcases i with p | (q | q)
  · exact h.isSU2Adjoint_wField p.1 p.2.1 p.2.2
  · refine ⟨fun U c => ?_⟩
    show repGauge (1, U, 1) (h.wField ![] (q 0) (q 1) c
      * h.hyperchargeField ![] (q 2) (q 3)) = _
    rw [hrepGauge_mul, h.repGauge_wField (1, U, 1), h.repGauge_hyperchargeField,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc]; rfl
  · refine ⟨fun U c => ?_⟩
    show repGauge (1, U, 1) (h.hyperchargeField ![] (q 2) (q 3)
      * h.wField ![] (q 0) (q 1) c) = _
    rw [hrepGauge_mul, h.repGauge_wField (1, U, 1), h.repGauge_hyperchargeField,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_smul_comm]; rfl

/-- The `su(2)` adjoint families of mass weight eight are fixed by the colour factor,
  every one of their factors being. -/
lemma repGauge_su3_isospinFamily (U : specialUnitaryGroup (Fin 3) ℂ) (i : IsospinIdx)
    (a : Fin 3) : repGauge (U, 1, 1) (h.isospinFamily i a) = h.isospinFamily i a := by
  rcases i with p | (q | q)
  · exact h.repGauge_su3_wField U p.1 p.2.1 p.2.2 a
  · show repGauge (U, 1, 1) (h.wField ![] (q 0) (q 1) a
      * h.hyperchargeField ![] (q 2) (q 3)) = _
    rw [hrepGauge_mul, h.repGauge_su3_wField, h.repGauge_hyperchargeField]
    rfl
  · show repGauge (U, 1, 1) (h.hyperchargeField ![] (q 2) (q 3)
      * h.wField ![] (q 0) (q 1) a) = _
    rw [hrepGauge_mul, h.repGauge_su3_wField, h.repGauge_hyperchargeField]
    rfl

/-- The join of the `su(2)` adjoint spans is fixed pointwise by the colour factor. -/
lemma repGauge_su3_of_mem_isospinJoin (U : specialUnitaryGroup (Fin 3) ℂ) {y : B}
    (hy : y ∈ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span) :
    repGauge (U, 1, 1) y = y := by
  refine Submodule.iSup_induction (motive := fun v => repGauge (U, 1, 1) v = v) _ hy
    (fun i v hv => ?_) (map_zero _) fun v w hv hw => by rw [map_add, hv, hw]
  obtain ⟨c, rfl⟩ := ((h.isSU2Adjoint_isospinFamily i).mem_span_iff v).1 hv
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => by
    rw [map_smul, h.repGauge_su3_isospinFamily U i d]

/-- A gauge invariant of the join of all the unpaired non-abelian adjoint spans together
  with a gauge-stable submodule lies in the submodule: the colour families are killed
  first, with the isospin ones held in the colour-stable tail, and the isospin families
  after that. -/
lemma mem_of_invariant_nonAbelianUnpaired_sup (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) {x : B}
    (hx : x ∈ ((⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span) ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ S := by
  classical
  rw [sup_assoc] at hx
  have hSI : ∀ U : specialUnitaryGroup (Fin 3) ℂ,
      ∀ y ∈ (⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span) ⊔ S,
      repGauge (U, 1, 1) y
        ∈ (⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span) ⊔ S := by
    intro U y hy
    have key : ((⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span) ⊔ S)
        ≤ Submodule.comap (repGauge (U, 1, 1))
          ((⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span) ⊔ S) :=
      sup_le (fun z hz => show repGauge (U, 1, 1) z
            ∈ (⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span) ⊔ S from by
          rw [h.repGauge_su3_of_mem_isospinJoin U hz]
          exact Submodule.mem_sup_left hz)
        fun z hz => Submodule.mem_sup_right (hS (U, 1, 1) z hz)
    exact key hy
  have hx₁ : x ∈ (⨆ i ∈ (Finset.univ : Finset ColourIdx),
      (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ((⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span) ⊔ S) := by
    rw [biSup_univ]
    exact hx
  have hx₂ := mem_of_su3_invariant_biSup_isSU3Adjoint_span
    (fun i : ColourIdx => h.isSU3Adjoint_colourFamily i) _ hSI Finset.univ hx₁
    fun U => hinv (U, 1, 1)
  have hx₃ : x ∈ (⨆ i ∈ (Finset.univ : Finset IsospinIdx),
      (h.isSU2Adjoint_isospinFamily i).span) ⊔ S := by
    rw [biSup_univ]
    exact hx₂
  exact mem_of_su2_invariant_biSup_isSU2Adjoint_span
    (fun i : IsospinIdx => h.isSU2Adjoint_isospinFamily i) S
    (fun U y hy => hS (1, U, 1) y hy) Finset.univ hx₃ fun U => hinv (1, U, 1)

/-- The twice-derived symbols on the colour and isospin Cartan directions lie in the joins
  of the single-adjoint spans. -/
lemma derivCartanNonAbelianPart_le :
    h.derivCartanNonAbelianPart
      ≤ (⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span := by
  rw [derivCartanNonAbelianPart]
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun c => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  have hglu : ∀ a : Fin 8, h.gluonField l μ ν a
      ∈ (⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span := fun a =>
    Submodule.mem_sup_left (Submodule.mem_iSup_of_mem (Sum.inl (l, μ, ν))
      (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)))
  have hw : ∀ i : Fin 3, h.wField l μ ν i
      ∈ (⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span := fun i =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (Sum.inl (l, μ, ν))
      (Submodule.mem_iSup_of_mem i (Submodule.mem_span_singleton_self _)))
  fin_cases c
  · exact hglu (GaugeAlgebra.su3CartanId 0)
  · exact hglu (GaugeAlgebra.su3CartanId 1)
  · exact hw GaugeAlgebra.su2CartanId

/-- A colour Cartan weight vector is the gluon field strength on the matching Cartan
  direction of `su(3)`. -/
lemma adjVec_colourCartan {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (c : Fin 2) :
    h.adjVec l μ ν (Sum.inr (Sum.inr c.castSucc.castSucc))
      = h.gluonField l μ ν (GaugeAlgebra.su3CartanId c) := by
  show F l μ ν (GaugeAlgebra.stdBasis.coord
    (GaugeAlgebra.cartanIdx c.castSucc.castSucc)) = _
  rw [IsSU3BiAdjoint.cartanIdx_castSucc]
  rfl

/-- The mixed neutral products lie in the joins of the single-adjoint spans: each of them
  pairs a weight-zero direction of one factor with a weight-zero direction of another, so
  one non-abelian adjoint index is left unpaired. -/
lemma mixedCartanPart_le :
    h.mixedCartanPart
      ≤ (⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span := by
  have hcol : ∀ (q : MixIdx) (a : Fin 8), h.colourFamily (Sum.inr (Sum.inl q)) a
      ∈ (⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span := fun q a =>
    Submodule.mem_sup_left (Submodule.mem_iSup_of_mem (Sum.inr (Sum.inl q))
      (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)))
  have hcol' : ∀ (q : MixIdx) (a : Fin 8), h.colourFamily (Sum.inr (Sum.inr q)) a
      ∈ (⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span := fun q a =>
    Submodule.mem_sup_left (Submodule.mem_iSup_of_mem (Sum.inr (Sum.inr q))
      (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)))
  have hiso : ∀ (q : EightIdx) (a : Fin 3), h.isospinFamily (Sum.inr (Sum.inl q)) a
      ∈ (⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span := fun q a =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (Sum.inr (Sum.inl q))
      (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)))
  have hiso' : ∀ (q : EightIdx) (a : Fin 3), h.isospinFamily (Sum.inr (Sum.inr q)) a
      ∈ (⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
        ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span := fun q a =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (Sum.inr (Sum.inr q))
      (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)))
  rw [mixedCartanPart, Submodule.mul_sup, Submodule.sup_mul]
  refine sup_le (sup_le ?_ ?_) (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_))
  · rw [colourCartanSpan, isospinCartanSpan]
    simp only [Submodule.iSup_mul, Submodule.mul_iSup]
    refine iSup_le fun μ => iSup_le fun ν => iSup_le fun μ' => iSup_le fun ν' =>
      iSup_le fun c => ?_
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
      Submodule.span_singleton_le_iff_mem, h.adjVec_colourCartan]
    exact hcol (μ', ν', μ, ν, 0) (GaugeAlgebra.su3CartanId c)
  · rw [colourCartanSpan, hyperchargeCartanSpan]
    simp only [Submodule.iSup_mul, Submodule.mul_iSup]
    refine iSup_le fun μ => iSup_le fun ν => iSup_le fun μ' => iSup_le fun ν' =>
      iSup_le fun c => ?_
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
      Submodule.span_singleton_le_iff_mem, h.adjVec_colourCartan]
    exact hcol (μ', ν', μ, ν, 1) (GaugeAlgebra.su3CartanId c)
  · rw [colourCartanSpan, isospinCartanSpan]
    simp only [Submodule.iSup_mul, Submodule.mul_iSup]
    refine iSup_le fun μ => iSup_le fun ν => iSup_le fun c => iSup_le fun μ' =>
      iSup_le fun ν' => ?_
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
      Submodule.span_singleton_le_iff_mem, h.adjVec_colourCartan]
    exact hcol' (μ, ν, μ', ν', 0) (GaugeAlgebra.su3CartanId c)
  · rw [colourCartanSpan, hyperchargeCartanSpan]
    simp only [Submodule.iSup_mul, Submodule.mul_iSup]
    refine iSup_le fun μ => iSup_le fun ν => iSup_le fun c => iSup_le fun μ' =>
      iSup_le fun ν' => ?_
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
      Submodule.span_singleton_le_iff_mem, h.adjVec_colourCartan]
    exact hcol' (μ, ν, μ', ν', 1) (GaugeAlgebra.su3CartanId c)
  · rw [isospinCartanSpan, hyperchargeCartanSpan]
    simp only [Submodule.iSup_mul, Submodule.mul_iSup]
    refine iSup_le fun μ => iSup_le fun ν => iSup_le fun μ' => iSup_le fun ν' => ?_
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
      Submodule.span_singleton_le_iff_mem]
    exact hiso ![μ', ν', μ, ν] GaugeAlgebra.su2CartanId
  · rw [isospinCartanSpan, hyperchargeCartanSpan]
    simp only [Submodule.iSup_mul, Submodule.mul_iSup]
    refine iSup_le fun μ => iSup_le fun ν => iSup_le fun μ' => iSup_le fun ν' => ?_
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
      Submodule.span_singleton_le_iff_mem]
    exact hiso' ![μ, ν, μ', ν'] GaugeAlgebra.su2CartanId

/-!

## G.4. The sup form of the zero-weight step

`GaugeWeightDecomposition.mem_zero_of_invariant` places an invariant of `V` in the
zero-weight piece, but an element of `V ⊔ S` need not have its `V`-part invariant, so it
does not apply. Dividing by the gauge-stable `S` repairs that, at the cost of a target
that is only a module: the decomposition carries `IsMulRep` as a field and the quotient of
a ring by a submodule is no ring. Section F.4 of `IsSU3BiAdjoint` closes exactly that gap.
The trivial square-zero extension of a module is an algebra built from the module
structure alone, a representation extends to it acting trivially on the scalar part, and
the extension is multiplicative for free. Transporting the decomposition along the
composite of the quotient map with the injection of the module therefore gives a
decomposition to which `mem_zero_of_invariant` applies, and the injectivity of the two
maps carries the conclusion back.

-/

/-- Transport of a gauge weight decomposition along an equivariant linear map into an
  algebra: the pieces of the image are the images of the pieces, the eigenvector
  equations being carried along by equivariance. -/
@[implicit_reducible]
noncomputable def mapGaugeWeightDecomposition {N : Type} [Ring N] [Algebra ℂ N]
    {rep' : Representation ℂ GaugeGroupI N} {V : Submodule ℂ B}
    (d : GaugeWeightDecomposition repGauge V) (f : B →ₗ[ℂ] N)
    (hf : ∀ (g : GaugeGroupI) (b : B), f (repGauge g b) = rep' g (f b))
    (hmul : IsMulRep rep') : GaugeWeightDecomposition rep' (V.map f) where
  piece w := (d.piece w).map f
  supp := d.supp
  rep_mul := hmul
  piece_le w x hx i := by
    obtain ⟨b, hb, rfl⟩ := hx
    rw [← hf, d.piece_le w b hb i, map_smul]
  piece_eq_bot w hw := by rw [d.piece_eq_bot w hw, Submodule.map_bot]
  iSup_piece := by rw [← Submodule.map_iSup, d.iSup_piece]

section SquareZero

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- The opposite scalar action on a complex vector space, which the square-zero extension
  needs to be a ring. Since `ℂ` is commutative it is the given action read through `unop`,
  and it is given a low priority so that the action of `ℂ` on itself is unaffected. -/
noncomputable local instance (priority := 100) opModule : Module ℂᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id ℂ).fromOpposite fun x y => mul_comm x y)

/-- The two scalar actions of `ℂ` on a complex vector space commute. -/
local instance (priority := 100) smulCommClassOpModule : SMulCommClass ℂ ℂᵐᵒᵖ M :=
  ⟨fun a b m => smul_comm a b.unop m⟩

/-- The opposite scalar action agrees with the given one, `ℂ` being commutative. -/
local instance (priority := 100) isCentralScalarOpModule : IsCentralScalar ℂ M :=
  ⟨fun _ _ => rfl⟩

/-- A gauge invariant of `V ⊔ S`, for a gauge-stable `S`, lies in the zero-weight piece of
  `V` joined with `S`. Nothing is asked of `S` beyond stability: the argument runs in the
  square-zero extension of the quotient by `S`, where the transported decomposition still
  makes sense. -/
lemma mem_piece_zero_sup_of_invariant {V : Submodule ℂ B}
    (d : GaugeWeightDecomposition repGauge V) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) {x : B} (hx : x ∈ V ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ d.piece 0 ⊔ S := by
  set ρ := IsSU3BiAdjoint.quotRep repGauge S hS with hρ
  set f : B →ₗ[ℂ] TrivSqZeroExt ℂ (B ⧸ S) :=
    (TrivSqZeroExt.inrHom ℂ (B ⧸ S)).comp S.mkQ with hfdef
  have hfapply : ∀ b : B, f b = TrivSqZeroExt.inr (S.mkQ b) := fun b => rfl
  have hf : ∀ (g : GaugeGroupI) (b : B),
      f (repGauge g b) = IsSU3BiAdjoint.sqZeroRep ρ g (f b) := by
    intro g b
    rw [hfapply, hfapply, IsSU3BiAdjoint.sqZeroRep_inr, hρ,
      IsSU3BiAdjoint.quotRep_mkQ]
  obtain ⟨u, hu, s, hs, hus⟩ := Submodule.mem_sup.1 hx
  have hfs : f s = 0 := by
    rw [hfapply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).2 hs]
    simp
  have hfx : f x ∈ V.map f := by
    rw [← hus, map_add, hfs, add_zero]
    exact Submodule.mem_map_of_mem hu
  have hfinv : ∀ g : GaugeGroupI, IsSU3BiAdjoint.sqZeroRep ρ g (f x) = f x := by
    intro g
    rw [← hf, hinv g]
  obtain ⟨v, hv, hvx⟩ := GaugeWeightDecomposition.mem_zero_of_invariant
    (mapGaugeWeightDecomposition d f hf (IsSU3BiAdjoint.isMulRep_sqZeroRep ρ)) hfx hfinv
  have hxv : x - v ∈ S := by
    have hq : S.mkQ (x - v) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact (TrivSqZeroExt.inr_injective (R := ℂ) (by rw [← hfapply, ← hfapply, hvx])).symm
    rwa [← Submodule.ker_mkQ S, LinearMap.mem_ker]
  rw [show x = v + (x - v) from by abel]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hv) (Submodule.mem_sup_right hxv)

end SquareZero

/-!

## G.3. The invariants of mass weight eight

-/

/-- The span of the three underived trace contractions, over all pairs of covector
  indices: the gauge invariants of mass weight eight that the bi-adjoint classification
  produces. -/
noncomputable def traceContractionEightSpan : Submodule ℂ B :=
  (⨆ p : EightIdx, ℂ ∙ (h.isSU3BiAdjoint_gluonField_mul ![] (p 0) (p 1) ![] (p 2)
      (p 3)).traceContraction)
    ⊔ ((⨆ p : EightIdx, ℂ ∙ (h.isSU2BiAdjoint_wField_mul ![] (p 0) (p 1) ![] (p 2)
        (p 3)).traceContraction)
      ⊔ ⨆ p : EightIdx, ℂ ∙ (h.isU1BiAdjoint_hyperchargeField_mul ![] (p 0) (p 1) ![]
        (p 2) (p 3)).traceContraction)

/-- The join of the gluon bi-adjoint subspaces is stable under the gauge group: each
  family obeys the transformation law at every gauge element. -/
lemma gluonPairSpan_stable (g : GaugeGroupI) {y : B} (hy : y ∈ h.gluonPairSpan) :
    repGauge g y ∈ h.gluonPairSpan := by
  have key : h.gluonPairSpan ≤ Submodule.comap (repGauge g) h.gluonPairSpan := by
    rw [gluonPairSpan]
    exact iSup_le fun p z hz => Submodule.mem_iSup_of_mem p
      (isSU3BiAdjoint_span_stable _
        (h.isSU3BiAdjointMat_gluonField_mul ![] (p 0) (p 1) ![] (p 2) (p 3) g) hz)
  exact key hy

/-- The join of the `W`-boson bi-adjoint subspaces is stable under the gauge group. -/
lemma wPairSpan_stable (g : GaugeGroupI) {y : B} (hy : y ∈ h.wPairSpan) :
    repGauge g y ∈ h.wPairSpan := by
  have key : h.wPairSpan ≤ Submodule.comap (repGauge g) h.wPairSpan := by
    rw [wPairSpan]
    exact iSup_le fun p z hz => Submodule.mem_iSup_of_mem p
      (isSU2BiAdjoint_span_stable _
        (h.isSU2BiAdjointMat_wField_mul ![] (p 0) (p 1) ![] (p 2) (p 3) g) hz)
  exact key hy

/-- The join of the hypercharge bi-adjoint subspaces is fixed pointwise by the gauge
  group: each hypercharge field strength is, and so is every product of two of them. -/
lemma repGauge_of_mem_hyperchargePairSpan (g : GaugeGroupI) {y : B}
    (hy : y ∈ h.hyperchargePairSpan) : repGauge g y = y := by
  rw [hyperchargePairSpan] at hy
  refine Submodule.iSup_induction (motive := fun v => repGauge g v = v) _ hy
    (fun p v hv => IsU1BiAdjoint.map_of_mem_span _
      (h.isU1BiAdjointMat_hyperchargeField_mul ![] (p 0) (p 1) ![] (p 2) (p 3) g) hv)
    (map_zero _) fun v w hv hw => by rw [map_add, hv, hw]

/-- The join of the hypercharge bi-adjoint subspaces is stable under the gauge group. -/
lemma hyperchargePairSpan_stable (g : GaugeGroupI) {y : B}
    (hy : y ∈ h.hyperchargePairSpan) : repGauge g y ∈ h.hyperchargePairSpan := by
  rw [h.repGauge_of_mem_hyperchargePairSpan g hy]
  exact hy

/-- The gauge invariants of mass weight eight modulo any gauge-stable submodule: such an
  invariant is a combination of the three underived trace contractions and the
  twice-derived hypercharge field strengths, plus a gauge-invariant remainder in `S`.
  Everything carrying an unpaired non-abelian adjoint index is killed first, contributing
  nothing at all; the three bi-adjoint joins are then peeled off one at a time, each time
  with the remaining ones joined to `S`, which stays gauge stable because each join is;
  and the twice-derived hypercharge span is split off last, being fixed pointwise by the
  gauge group. -/
theorem exists_mem_of_invariant_piece_zero_sup (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) {x : B}
    (hx : x ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ x - y ∈ h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan := by
  have hS₃ : ∀ g : GaugeGroupI, ∀ y ∈ h.hyperchargeDerivSpan ⊔ S,
      repGauge g y ∈ h.hyperchargeDerivSpan ⊔ S := by
    intro g y hy
    have key : (h.hyperchargeDerivSpan ⊔ S)
        ≤ Submodule.comap (repGauge g) (h.hyperchargeDerivSpan ⊔ S) :=
      sup_le (fun z hz => Submodule.mem_sup_left (h.hyperchargeDerivSpan_stable g hz))
        fun z hz => Submodule.mem_sup_right (hS g z hz)
    exact key hy
  have hS₂ : ∀ g : GaugeGroupI, ∀ y ∈ h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S),
      repGauge g y ∈ h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S) := by
    intro g y hy
    have key : (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S))
        ≤ Submodule.comap (repGauge g)
          (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S)) :=
      sup_le (fun z hz => Submodule.mem_sup_left (h.hyperchargePairSpan_stable g hz))
        fun z hz => Submodule.mem_sup_right (hS₃ g z hz)
    exact key hy
  have hS₁ : ∀ g : GaugeGroupI, ∀ y ∈ h.wPairSpan
        ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S)),
      repGauge g y ∈ h.wPairSpan
        ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S)) := by
    intro g y hy
    have key : (h.wPairSpan ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S)))
        ≤ Submodule.comap (repGauge g) (h.wPairSpan
          ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S))) :=
      sup_le (fun z hz => Submodule.mem_sup_left (h.wPairSpan_stable g hz))
        fun z hz => Submodule.mem_sup_right (hS₂ g z hz)
    exact key hy
  have hS₀ : ∀ g : GaugeGroupI, ∀ y ∈ h.gluonPairSpan ⊔ (h.wPairSpan
        ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S))),
      repGauge g y ∈ h.gluonPairSpan ⊔ (h.wPairSpan
        ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S))) := by
    intro g y hy
    have key : (h.gluonPairSpan ⊔ (h.wPairSpan
          ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S))))
        ≤ Submodule.comap (repGauge g) (h.gluonPairSpan ⊔ (h.wPairSpan
          ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S)))) :=
      sup_le (fun z hz => Submodule.mem_sup_left (h.gluonPairSpan_stable g hz))
        fun z hz => Submodule.mem_sup_right (hS₁ g z hz)
    exact key hy
  have hle : (h.massWeightSubmoduleGaugeWeightEight).piece 0 ⊔ S
      ≤ ((⨆ i : ColourIdx, (h.isSU3Adjoint_colourFamily i).span)
          ⊔ ⨆ i : IsospinIdx, (h.isSU2Adjoint_isospinFamily i).span)
        ⊔ (h.gluonPairSpan ⊔ (h.wPairSpan
          ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S)))) := by
    refine sup_le (h.massWeightSubmoduleGaugeWeightEight_piece_zero_le.trans
      (sup_le ?_ ?_)) ?_
    · exact (sup_le h.derivCartanNonAbelianPart_le h.mixedCartanPart_le).trans le_sup_left
    · exact sup_le (le_sup_of_le_right le_sup_left)
        (sup_le (le_sup_of_le_right (le_sup_of_le_right le_sup_left))
          (sup_le (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_left)))
            (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right
              (le_sup_of_le_right le_sup_left))))))
    · exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right
        (le_sup_of_le_right le_sup_right)))
  have hxT := h.mem_of_invariant_nonAbelianUnpaired_sup _ hS₀ (hle hx) hinv
  have hxG : x ∈ (⨆ p ∈ (Finset.univ : Finset EightIdx),
      (h.isSU3BiAdjoint_gluonField_mul ![] (p 0) (p 1) ![] (p 2) (p 3)).span)
        ⊔ (h.wPairSpan ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S))) := by
    rw [biSup_univ]
    exact hxT
  obtain ⟨y₁, hy₁, hy₁inv, hxy₁⟩ :=
    exists_mem_of_invariant_biSup_isSU3BiAdjoint_span
      (fun p : EightIdx =>
        h.isSU3BiAdjoint_gluonField_mul ![] (p 0) (p 1) ![] (p 2) (p 3))
      (fun p g => h.isSU3BiAdjointMat_gluonField_mul ![] (p 0) (p 1) ![] (p 2) (p 3) g)
      hrepGauge_mul _ hS₁ Finset.univ hxG hinv
  rw [biSup_univ] at hxy₁
  have hyW : y₁ ∈ (⨆ p ∈ (Finset.univ : Finset EightIdx),
      (h.isSU2BiAdjoint_wField_mul ![] (p 0) (p 1) ![] (p 2) (p 3)).span)
        ⊔ (h.hyperchargePairSpan ⊔ (h.hyperchargeDerivSpan ⊔ S)) := by
    rw [biSup_univ]
    exact hy₁
  obtain ⟨y₂, hy₂, hy₂inv, hy₁y₂⟩ :=
    exists_mem_of_invariant_biSup_isSU2BiAdjoint_span
      (fun p : EightIdx => h.isSU2BiAdjoint_wField_mul ![] (p 0) (p 1) ![] (p 2) (p 3))
      (fun p g => h.isSU2BiAdjointMat_wField_mul ![] (p 0) (p 1) ![] (p 2) (p 3) g)
      hrepGauge_mul _ hS₂ Finset.univ hyW hy₁inv
  rw [biSup_univ] at hy₁y₂
  obtain ⟨y₃, hy₃, hy₃inv, hy₂y₃⟩ :=
    exists_mem_of_invariant_iSup_isU1BiAdjoint_span
      (fun p : EightIdx =>
        h.isU1BiAdjoint_hyperchargeField_mul ![] (p 0) (p 1) ![] (p 2) (p 3))
      (fun p g =>
        h.isU1BiAdjointMat_hyperchargeField_mul ![] (p 0) (p 1) ![] (p 2) (p 3) g)
      (h.hyperchargeDerivSpan ⊔ S) hy₂ hy₂inv
  obtain ⟨y₄, hy₄, hy₄inv, hy₃y₄⟩ :=
    exists_mem_of_invariant_sup_fixed h.hyperchargeDerivSpan S
      (fun g v hv => h.repGauge_of_mem_hyperchargeDerivSpan g hv) hy₃ hy₃inv
  refine ⟨y₄, hy₄, hy₄inv, ?_⟩
  rw [show x - y₄ = x - y₁ + (y₁ - y₂ + (y₂ - y₃ + (y₃ - y₄))) from by abel,
    traceContractionEightSpan]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left hxy₁))
    (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.mem_sup_left hy₁y₂)))
      (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.mem_sup_right hy₂y₃)))
        (Submodule.mem_sup_right hy₃y₄)))

/-- The sup form at the mass-weight submodule: a gauge invariant of
  `massWeightSubmodule 8 ⊔ S`, for `S` gauge stable and absorbing the parts that carry an
  unpaired non-abelian adjoint index, is a combination of the three underived trace
  contractions and the twice-derived hypercharge field strengths plus a gauge-invariant
  remainder in `S`. The weight-eight part of such an element need not itself be invariant,
  and `mem_piece_zero_sup_of_invariant` is what places the element in the zero-weight
  piece all the same. -/
theorem exists_mem_of_invariant_massWeightSubmodule_eight_sup (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 8 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ x - y ∈ h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan :=
  h.exists_mem_of_invariant_piece_zero_sup S hS
    (mem_piece_zero_sup_of_invariant h.massWeightSubmoduleGaugeWeightEight S hS hx hinv)
    hinv

/-- The gauge invariants of the mass-weight eight submodule itself, the case `x ∈ V` of
  the sup form. -/
theorem exists_mem_of_invariant_massWeightSubmodule_eight (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 8) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ x - y ∈ h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan :=
  h.exists_mem_of_invariant_massWeightSubmodule_eight_sup S hS
    (Submodule.mem_sup_left hx) hinv

/-- An element of a finite join of lines is a linear combination of the vectors spanning
  them. -/
lemma exists_sum_of_mem_iSup_span_singleton {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → B) {x : B} (hx : x ∈ ⨆ i, ℂ ∙ v i) : ∃ c : ι → ℂ, x = ∑ i, c i • v i := by
  refine Submodule.iSup_induction (motive := fun z => ∃ c : ι → ℂ, z = ∑ i, c i • v i)
    (fun i => ℂ ∙ v i) hx (fun i z hz => ?_) ⟨0, by simp⟩ ?_
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨fun j => if j = i then a else 0, by
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]⟩
  · rintro z w ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
    exact ⟨c₁ + c₂, by simp [add_smul, Finset.sum_add_distrib]⟩

/-- The explicit form of `exists_mem_of_invariant_massWeightSubmodule_eight`: a gauge
  invariant of mass weight eight is a combination of the three underived trace
  contractions and the twice-derived hypercharge field strengths, one coefficient for each
  family of four covector indices, plus a gauge-invariant remainder in `S`. -/
theorem exists_sum_smul_traceContraction_of_invariant (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 8 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ cG cW cB cD : EightIdx → ℂ, ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ x = ∑ p, cG p • (h.isSU3BiAdjoint_gluonField_mul ![] (p 0) (p 1) ![] (p 2)
              (p 3)).traceContraction
          + (∑ p, cW p • (h.isSU2BiAdjoint_wField_mul ![] (p 0) (p 1) ![] (p 2)
              (p 3)).traceContraction
            + (∑ p, cB p • (h.isU1BiAdjoint_hyperchargeField_mul ![] (p 0) (p 1) ![]
                (p 2) (p 3)).traceContraction
              + (∑ p, cD p • h.hyperchargeField ![p 0, p 1] (p 2) (p 3) + y))) := by
  obtain ⟨y, hyS, hyinv, hxy⟩ :=
    h.exists_mem_of_invariant_massWeightSubmodule_eight_sup S hS hx hinv
  rw [traceContractionEightSpan, hyperchargeDerivSpan] at hxy
  obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.1 hxy
  obtain ⟨a, ha, v, hv, hav⟩ := Submodule.mem_sup.1 hu
  obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.1 hv
  obtain ⟨cG, rfl⟩ := exists_sum_of_mem_iSup_span_singleton _ ha
  obtain ⟨cW, rfl⟩ := exists_sum_of_mem_iSup_span_singleton _ hw
  obtain ⟨cB, rfl⟩ := exists_sum_of_mem_iSup_span_singleton _ hz
  obtain ⟨cD, rfl⟩ := exists_sum_of_mem_iSup_span_singleton _ ht
  refine ⟨cG, cW, cB, cD, y, hyS, hyinv, ?_⟩
  rw [← hav, ← hwz] at hut
  rw [sub_eq_iff_eq_add.mp hut.symm]
  abel

/-!

## H. The Lorentz classification of the mass-weight eight invariants

A product of two underived field-strength symbols carries four covector indices and
nothing else, so as a family indexed by those four it is a quadruple Lorentz tensor in the
sense of `IsQuadLorentz`. The transformation law is the Lorentz mirror of section B:
`repLorentz_F` at no covariant derivatives moves each covector index by the Lorentz matrix
of the `SL(2,ℂ)` element, and `hrepLorentz_mul` carries that through the product.

The three trace contractions of section D are sums of such products over a gauge index,
and a finite sum of quadruple Lorentz tensors is one again, so each of the three is a
quadruple Lorentz tensor in its own right. So is the twice-derived hypercharge field
strength, whose two derivative slots and two covector indices are four four-vector indices
as well. Each of the four spans is exactly the join of the lines that section G produces,
which is what lets the two classifications be composed: the gauge classification puts an
invariant of mass weight eight into the join of the four spans together with `S`, and the
Lorentz sup lemma peels those spans off one at a time, exactly as the bi-adjoint sup
lemmas did for the gauge group. The remainder stays gauge invariant at each step because
the components of the four families are, so everything in their spans is.

What is left is a combination of the four Lorentz contractions of each family: the outer,
inner and split metric contractions and the Levi-Civita contraction. The physical
expectation is that the first three collapse to one, the metric contraction of `F` with
itself, because `F` is antisymmetric in its two covector indices. That collapse is not
available here: `IsGaugeSector` does not assert the antisymmetry, its four fields being
the gauge law, the Lorentz law, the mass weight and commutativity, and none of them
relates `F l μ ν φ` to `F l ν μ φ`. All four contractions therefore survive.

-/

include h in
/-- The Lorentz transformation of an underived field-strength symbol: the general law of
  `IsGaugeSector` at no covariant derivatives, where the sum over the derivative slots is
  a single term, written with the two covector rotations gathered into one coefficient. -/
lemma repLorentz_F_underived (Λ : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repLorentz Λ (F ![] μ ν φ)
      = ∑ a : Fin 1 ⊕ Fin 3, ∑ b : Fin 1 ⊕ Fin 3,
        ((((SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) *
          (((SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ)) • F ![] a b φ := by
  rw [h.repLorentz_F Λ 0 ![] μ ν φ,
    Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
      (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
      (fun hb => absurd (Finset.mem_univ _) hb), Fin.prod_univ_zero, one_smul]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [smul_smul]

include h in
/-- A product of two underived field-strength symbols, viewed as a family indexed by the
  four covector indices it carries, is a quadruple Lorentz tensor. -/
lemma isQuadLorentz_F_mul (φ ψ : Module.Dual ℝ GaugeAlgebra) :
    IsQuadLorentz B repLorentz
      (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => F ![] (d 0) (d 1) φ * F ![] (d 2) (d 3) ψ) where
  repLorentz_T g l := by
    rw [hrepLorentz_mul, h.repLorentz_F_underived g (l 0) (l 1) φ,
      h.repLorentz_F_underived g (l 2) (l 3) ψ, IsQuadLorentz.sum_pi_four,
      Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (∑ x : Fin 1 ⊕ Fin 3, (∑ b : Fin 1 ⊕ Fin 3,
        ((((SL2C.toLorentzGroup g).1 a (l 0) : ℝ) : ℂ) *
          (((SL2C.toLorentzGroup g).1 b (l 1) : ℝ) : ℂ)) • F ![] a b φ) *
        ∑ y : Fin 1 ⊕ Fin 3, ((((SL2C.toLorentzGroup g).1 x (l 2) : ℝ) : ℂ) *
          (((SL2C.toLorentzGroup g).1 y (l 3) : ℝ) : ℂ)) • F ![] x y ψ)
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ b : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3,
        (((((SL2C.toLorentzGroup g).1 a (l 0) : ℝ) : ℂ) *
          (((SL2C.toLorentzGroup g).1 b (l 1) : ℝ) : ℂ)) • F ![] a b φ) *
        (((((SL2C.toLorentzGroup g).1 x (l 2) : ℝ) : ℂ) *
          (((SL2C.toLorentzGroup g).1 y (l 3) : ℝ) : ℂ)) • F ![] x y ψ) from
      Finset.sum_congr rfl fun x _ => Fintype.sum_mul_sum _ _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm]
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring_nf

/-- A finite sum of quadruple Lorentz tensors is a quadruple Lorentz tensor: the
  transformation law is linear in the family. -/
lemma isQuadLorentz_sum {ι : Type} [Fintype ι] {T : ι → (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hT : ∀ i, IsQuadLorentz B repLorentz (T i)) :
    IsQuadLorentz B repLorentz (fun d => ∑ i, T i d) where
  repLorentz_T g l := by
    have hstep : ∀ i, repLorentz g (T i l) = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3,
        (∏ j : Fin 4, (((SL2C.toLorentzGroup g).1 (a j) (l j) : ℝ) : ℂ)) • T i a :=
      fun i => (hT i).repLorentz_T g l
    rw [map_sum]
    simp only [hstep]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-- The span of the components of a quadruple Lorentz tensor is stable under the Lorentz
  group: each component goes to a combination of components. -/
lemma isQuadLorentz_span_stable {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsQuadLorentz B repLorentz T) (g : SL(2,ℂ)) {y : B} (hy : y ∈ hT.span) :
    repLorentz g y ∈ hT.span := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [map_smul, hT.repLorentz_T g d]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)))

/-- A quadruple Lorentz tensor whose components are gauge invariant has a span of gauge
  invariants; in particular its four Lorentz contractions are gauge invariant. -/
lemma repGauge_of_mem_isQuadLorentz_span {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsQuadLorentz B repLorentz T)
    (hTinv : ∀ (g : GaugeGroupI) (d : Fin 4 → Fin 1 ⊕ Fin 3), repGauge g (T d) = T d)
    (g : GaugeGroupI) {y : B} (hy : y ∈ hT.span) : repGauge g y = y := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff y).1 hy
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [map_smul, hTinv g d]

/-- The gluon trace contraction of two underived field strengths, read as a family of
  four four-vector indices, is a quadruple Lorentz tensor: it is a sum over the colour
  index of products of two underived field-strength symbols. -/
lemma isQuadLorentz_gluonTrace : IsQuadLorentz B repLorentz (fun d : EightIdx =>
    (h.isSU3BiAdjoint_gluonField_mul ![] (d 0) (d 1) ![] (d 2) (d 3)).traceContraction) := by
  rw [show (fun d : EightIdx =>
      (h.isSU3BiAdjoint_gluonField_mul ![] (d 0) (d 1) ![] (d 2) (d 3)).traceContraction)
      = fun d : EightIdx => ∑ a : Fin 8,
        F ![] (d 0) (d 1) (GaugeAlgebra.stdBasis.coord (Sum.inl a))
          * F ![] (d 2) (d 3) (GaugeAlgebra.stdBasis.coord (Sum.inl a)) from
    funext fun d => h.traceContraction_gluonField_mul ![] (d 0) (d 1) ![] (d 2) (d 3)]
  exact isQuadLorentz_sum fun a => h.isQuadLorentz_F_mul _ _

/-- The `W`-boson trace contraction of two underived field strengths, read as a family of
  four four-vector indices, is a quadruple Lorentz tensor. -/
lemma isQuadLorentz_wTrace : IsQuadLorentz B repLorentz (fun d : EightIdx =>
    (h.isSU2BiAdjoint_wField_mul ![] (d 0) (d 1) ![] (d 2) (d 3)).traceContraction) := by
  rw [show (fun d : EightIdx =>
      (h.isSU2BiAdjoint_wField_mul ![] (d 0) (d 1) ![] (d 2) (d 3)).traceContraction)
      = fun d : EightIdx => ∑ i : Fin 3,
        F ![] (d 0) (d 1) (GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inl i)))
          * F ![] (d 2) (d 3) (GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inl i))) from
    funext fun d => h.traceContraction_wField_mul ![] (d 0) (d 1) ![] (d 2) (d 3)]
  exact isQuadLorentz_sum fun i => h.isQuadLorentz_F_mul _ _

/-- The hypercharge trace contraction of two underived field strengths, read as a family
  of four four-vector indices, is a quadruple Lorentz tensor. -/
lemma isQuadLorentz_hyperchargeTrace : IsQuadLorentz B repLorentz (fun d : EightIdx =>
    (h.isU1BiAdjoint_hyperchargeField_mul ![] (d 0) (d 1) ![] (d 2)
      (d 3)).traceContraction) := by
  rw [show (fun d : EightIdx =>
      (h.isU1BiAdjoint_hyperchargeField_mul ![] (d 0) (d 1) ![] (d 2)
        (d 3)).traceContraction)
      = fun d : EightIdx =>
        F ![] (d 0) (d 1) (GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inr 0)))
          * F ![] (d 2) (d 3) (GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inr 0))) from
    funext fun d => h.traceContraction_hyperchargeField_mul ![] (d 0) (d 1) ![] (d 2) (d 3)]
  exact h.isQuadLorentz_F_mul _ _

/-- A sum over families of two covector indices is a double sum. -/
lemma sum_pi_two_cov {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, f ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3), f ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 1 ⊕ Fin 3) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

include h in
/-- The Lorentz transformation of a twice-derived field-strength symbol, with the four
  covector rotations gathered into one coefficient: the two derivative slots and the two
  covector indices all rotate. -/
lemma repLorentz_F_twice (Λ : SL(2,ℂ)) (l : Fin 2 → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    repLorentz Λ (F l μ ν φ)
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3,
        ∑ w : Fin 1 ⊕ Fin 3,
          ((((SL2C.toLorentzGroup Λ).1 x (l 0) : ℝ) : ℂ) *
            (((SL2C.toLorentzGroup Λ).1 y (l 1) : ℝ) : ℂ) *
            (((SL2C.toLorentzGroup Λ).1 z μ : ℝ) : ℂ) *
            (((SL2C.toLorentzGroup Λ).1 w ν : ℝ) : ℂ)) • F ![x, y] z w φ := by
  rw [h.repLorentz_F Λ 2 l μ ν φ, sum_pi_two_cov]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [smul_smul]
  congr 1
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

include h in
/-- A twice-derived field-strength symbol, viewed as a family indexed by its two
  derivative slots and its two covector indices, is a quadruple Lorentz tensor. -/
lemma isQuadLorentz_F_deriv_two (φ : Module.Dual ℝ GaugeAlgebra) :
    IsQuadLorentz B repLorentz
      (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => F ![d 0, d 1] (d 2) (d 3) φ) where
  repLorentz_T g l := by
    rw [h.repLorentz_F_twice g ![l 0, l 1] (l 2) (l 3) φ, IsQuadLorentz.sum_pi_four]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]

/-- The twice-derived hypercharge field strengths, read as a family of four four-vector
  indices, form a quadruple Lorentz tensor. This is the second shape of mass weight
  eight: a single field-strength symbol carrying two covariant derivatives. -/
lemma isQuadLorentz_hyperchargeDeriv : IsQuadLorentz B repLorentz
    (fun d : EightIdx => h.hyperchargeField ![d 0, d 1] (d 2) (d 3)) :=
  h.isQuadLorentz_F_deriv_two _

/-- The span of the four Lorentz contractions of a quadruple Lorentz tensor: the outer,
  inner and split metric contractions and the Levi-Civita contraction. -/
noncomputable def quadContractionSpan (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : Submodule ℂ B :=
  ℂ ∙ IsQuadLorentz.outerContraction (T := T)
    ⊔ (ℂ ∙ IsQuadLorentz.innerContraction (T := T)
      ⊔ (ℂ ∙ IsQuadLorentz.splitContraction (T := T)
        ⊔ ℂ ∙ IsQuadLorentz.epsilonContraction (T := T)))

/-- Peeling the span of a quadruple Lorentz tensor off a Lorentz-stable submodule. The
  remainder is Lorentz invariant by the sup lemma of `IsQuadLorentz`, and gauge invariant
  as well whenever the components of the family are, the four contractions then being
  gauge invariant along with everything else in the span. -/
lemma exists_mem_of_invariant_isQuadLorentz_span_sup {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsQuadLorentz B repLorentz T)
    (hTinv : ∀ (g : GaugeGroupI) (d : Fin 4 → Fin 1 ⊕ Fin 3), repGauge g (T d) = T d)
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ hT.span ⊔ S) (hLinv : ∀ g : SL(2,ℂ), repLorentz g x = x)
    (hGinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ y ∈ S, (∀ g : SL(2,ℂ), repLorentz g y = y)
      ∧ (∀ g : GaugeGroupI, repGauge g y = y) ∧ x - y ∈ quadContractionSpan T := by
  obtain ⟨a₁, a₂, a₃, a₄, y, hyS, hxy, hyinv⟩ :=
    (hT.mem_span_sup_invariant_iff x S hS).1 ⟨hx, hLinv⟩
  have hz : ∀ g : GaugeGroupI,
      repGauge g (a₁ • IsQuadLorentz.outerContraction (T := T)
          + a₂ • IsQuadLorentz.innerContraction (T := T)
          + a₃ • IsQuadLorentz.splitContraction (T := T)
          + a₄ • IsQuadLorentz.epsilonContraction (T := T))
        = a₁ • IsQuadLorentz.outerContraction (T := T)
          + a₂ • IsQuadLorentz.innerContraction (T := T)
          + a₃ • IsQuadLorentz.splitContraction (T := T)
          + a₄ • IsQuadLorentz.epsilonContraction (T := T) :=
    fun g => repGauge_of_mem_isQuadLorentz_span hT hTinv g
      (hT.smul_contraction_mem_span a₁ a₂ a₃ a₄)
  refine ⟨y, hyS, hyinv, fun g => ?_, ?_⟩
  · have hg := hGinv g
    rw [hxy, map_add, hz g, add_right_inj] at hg
    exact hg
  · rw [hxy, add_sub_cancel_right, quadContractionSpan]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.smul_mem _ _
          (Submodule.mem_span_singleton_self _)))
        (Submodule.mem_sup_right (Submodule.mem_sup_left (Submodule.smul_mem _ _
          (Submodule.mem_span_singleton_self _)))))
      (Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))))))
      (Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))))

/-- The span of the three underived trace contractions is the join of the spans of the
  three quadruple Lorentz families they form. -/
lemma traceContractionEightSpan_eq :
    h.traceContractionEightSpan = (h.isQuadLorentz_gluonTrace).span
      ⊔ ((h.isQuadLorentz_wTrace).span ⊔ (h.isQuadLorentz_hyperchargeTrace).span) := rfl

/-- The span of the four Lorentz contractions of each of the three underived
  trace-contraction families: the gauge and Lorentz invariants of mass weight eight that
  the two classifications together produce. -/
noncomputable def lorentzContractionEightSpan : Submodule ℂ B :=
  quadContractionSpan (fun d : EightIdx =>
      (h.isSU3BiAdjoint_gluonField_mul ![] (d 0) (d 1) ![] (d 2) (d 3)).traceContraction)
    ⊔ (quadContractionSpan (fun d : EightIdx =>
        (h.isSU2BiAdjoint_wField_mul ![] (d 0) (d 1) ![] (d 2) (d 3)).traceContraction)
      ⊔ (quadContractionSpan (fun d : EightIdx =>
          (h.isU1BiAdjoint_hyperchargeField_mul ![] (d 0) (d 1) ![] (d 2)
            (d 3)).traceContraction)
        ⊔ quadContractionSpan (fun d : EightIdx =>
          h.hyperchargeField ![d 0, d 1] (d 2) (d 3))))

/-- The gauge and Lorentz invariants of mass weight eight, modulo a submodule `S` stable
  under both groups and absorbing the parts that carry an unpaired non-abelian adjoint
  index. The gauge classification of section G puts such an invariant in the join of the
  three trace-contraction spans and the twice-derived hypercharge span together with `S`;
  each of those four is the span of a quadruple Lorentz tensor, so the Lorentz sup lemma
  peels them off one at a time, leaving a combination of the four Lorentz contractions of
  each family. The remainders stay gauge invariant because the components of the four
  families are. -/
theorem exists_mem_of_gauge_and_lorentz_invariant (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 8 ⊔ S)
    (hGinv : ∀ g : GaugeGroupI, repGauge g x = x)
    (hLinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
      ∧ x - y ∈ h.lorentzContractionEightSpan := by
  obtain ⟨y₀, hy₀S, hy₀G, hxy₀⟩ :=
    h.exists_mem_of_invariant_massWeightSubmodule_eight_sup S hS hx hGinv
  rw [h.traceContractionEightSpan_eq] at hxy₀
  have hS₃ : ∀ g : SL(2,ℂ), ∀ y ∈ (h.isQuadLorentz_hyperchargeDeriv).span ⊔ S,
      repLorentz g y ∈ (h.isQuadLorentz_hyperchargeDeriv).span ⊔ S := by
    intro g y hy
    have key : ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S)
        ≤ Submodule.comap (repLorentz g)
          ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S) :=
      sup_le (fun z hz => Submodule.mem_sup_left (isQuadLorentz_span_stable _ g hz))
        fun z hz => Submodule.mem_sup_right (hSL g z hz)
    exact key hy
  have hS₂ : ∀ g : SL(2,ℂ), ∀ y ∈ (h.isQuadLorentz_hyperchargeTrace).span
        ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S),
      repLorentz g y ∈ (h.isQuadLorentz_hyperchargeTrace).span
        ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S) := by
    intro g y hy
    have key : ((h.isQuadLorentz_hyperchargeTrace).span
          ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S))
        ≤ Submodule.comap (repLorentz g) ((h.isQuadLorentz_hyperchargeTrace).span
          ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S)) :=
      sup_le (fun z hz => Submodule.mem_sup_left (isQuadLorentz_span_stable _ g hz))
        fun z hz => Submodule.mem_sup_right (hS₃ g z hz)
    exact key hy
  have hS₁ : ∀ g : SL(2,ℂ), ∀ y ∈ (h.isQuadLorentz_wTrace).span
        ⊔ ((h.isQuadLorentz_hyperchargeTrace).span
          ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S)),
      repLorentz g y ∈ (h.isQuadLorentz_wTrace).span
        ⊔ ((h.isQuadLorentz_hyperchargeTrace).span
          ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S)) := by
    intro g y hy
    have key : ((h.isQuadLorentz_wTrace).span ⊔ ((h.isQuadLorentz_hyperchargeTrace).span
          ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S)))
        ≤ Submodule.comap (repLorentz g) ((h.isQuadLorentz_wTrace).span
          ⊔ ((h.isQuadLorentz_hyperchargeTrace).span
            ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S))) :=
      sup_le (fun z hz => Submodule.mem_sup_left (isQuadLorentz_span_stable _ g hz))
        fun z hz => Submodule.mem_sup_right (hS₂ g z hz)
    exact key hy
  have hx₁ : x ∈ (h.isQuadLorentz_gluonTrace).span ⊔ ((h.isQuadLorentz_wTrace).span
      ⊔ ((h.isQuadLorentz_hyperchargeTrace).span
        ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S))) := by
    rw [show x = x - y₀ + y₀ from by abel]
    refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (Submodule.mem_sup_right
      (Submodule.mem_sup_right (Submodule.mem_sup_right hy₀S))))
    have hle : ((h.isQuadLorentz_gluonTrace).span ⊔ ((h.isQuadLorentz_wTrace).span
          ⊔ (h.isQuadLorentz_hyperchargeTrace).span))
          ⊔ (h.isQuadLorentz_hyperchargeDeriv).span
        ≤ (h.isQuadLorentz_gluonTrace).span ⊔ ((h.isQuadLorentz_wTrace).span
          ⊔ ((h.isQuadLorentz_hyperchargeTrace).span
            ⊔ ((h.isQuadLorentz_hyperchargeDeriv).span ⊔ S))) :=
      sup_le (sup_le le_sup_left (sup_le (le_sup_of_le_right le_sup_left)
          (le_sup_of_le_right (le_sup_of_le_right le_sup_left))))
        (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_left)))
    exact hle hxy₀
  obtain ⟨y₁, hy₁, hy₁L, hy₁G, hxy₁⟩ :=
    exists_mem_of_invariant_isQuadLorentz_span_sup h.isQuadLorentz_gluonTrace
      (fun g d => IsSU3BiAdjoint.map_traceContraction _
        (h.isSU3BiAdjointMat_gluonField_mul ![] (d 0) (d 1) ![] (d 2) (d 3) g))
      _ hS₁ hx₁ hLinv hGinv
  obtain ⟨y₂, hy₂, hy₂L, hy₂G, hxy₂⟩ :=
    exists_mem_of_invariant_isQuadLorentz_span_sup h.isQuadLorentz_wTrace
      (fun g d => IsSU2BiAdjoint.map_traceContraction _
        (h.isSU2BiAdjointMat_wField_mul ![] (d 0) (d 1) ![] (d 2) (d 3) g))
      _ hS₂ hy₁ hy₁L hy₁G
  obtain ⟨y₃, hy₃, hy₃L, hy₃G, hxy₃⟩ :=
    exists_mem_of_invariant_isQuadLorentz_span_sup h.isQuadLorentz_hyperchargeTrace
      (fun g d => IsU1BiAdjoint.map_traceContraction _
        (h.isU1BiAdjointMat_hyperchargeField_mul ![] (d 0) (d 1) ![] (d 2) (d 3) g))
      _ hS₃ hy₂ hy₂L hy₂G
  obtain ⟨y₄, hy₄, hy₄L, hy₄G, hxy₄⟩ :=
    exists_mem_of_invariant_isQuadLorentz_span_sup h.isQuadLorentz_hyperchargeDeriv
      (fun g d => h.repGauge_hyperchargeField g ![d 0, d 1] (d 2) (d 3))
      S hSL hy₃ hy₃L hy₃G
  refine ⟨y₄, hy₄, hy₄G, hy₄L, ?_⟩
  rw [show x - y₄ = x - y₁ + (y₁ - y₂ + (y₂ - y₃ + (y₃ - y₄))) from by abel,
    lorentzContractionEightSpan]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hxy₁)
    (Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_sup_left hxy₂))
      (Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_sup_right
          (Submodule.mem_sup_left hxy₃)))
        (Submodule.mem_sup_right (Submodule.mem_sup_right
          (Submodule.mem_sup_right hxy₄)))))

/-- A family of four four-vector indices written as a fourfold sum, with the four indices
  read off the tuple. -/
lemma sum_quad {M : Type*} [AddCommMonoid M]
    (f : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → M) :
    (∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3,
        ∑ w : Fin 1 ⊕ Fin 3, f x y z w)
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3,
        ∑ w : Fin 1 ⊕ Fin 3, f y x z w := by
  rw [Finset.sum_comm]

/-- The outer contraction of a quadruple Lorentz tensor antisymmetric in its first two
  indices vanishes: the metric is symmetric in the pair the outer contraction ties
  together, so exchanging the two indices carries the sum to minus itself. -/
lemma outerContraction_eq_zero_of_swap {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hswap : ∀ x y z w : Fin 1 ⊕ Fin 3, T ![y, x, z, w] = - T ![x, y, z, w]) :
    IsQuadLorentz.outerContraction (T := T) = 0 := by
  have h1 : IsQuadLorentz.outerContraction (T := T)
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3,
        ∑ w : Fin 1 ⊕ Fin 3,
          ((minkowskiMatrixZ x y * minkowskiMatrixZ z w : ℤ) : ℂ) • T ![x, y, z, w] := by
    rw [IsQuadLorentz.outerContraction, IsQuadLorentz.sum_pi_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  have h3 : ∀ x y z w : Fin 1 ⊕ Fin 3,
      ((minkowskiMatrixZ y x * minkowskiMatrixZ z w : ℤ) : ℂ) • T ![y, x, z, w]
        = -(((minkowskiMatrixZ x y * minkowskiMatrixZ z w : ℤ) : ℂ) •
          T ![x, y, z, w]) := by
    intro x y z w
    rw [hswap x y z w, smul_neg, minkowskiMatrixZ.comm y x]
  have h4 : IsQuadLorentz.outerContraction (T := T)
      = - IsQuadLorentz.outerContraction (T := T) := by
    conv_lhs => rw [h1, sum_quad fun x y z w =>
      ((minkowskiMatrixZ x y * minkowskiMatrixZ z w : ℤ) : ℂ) • T ![x, y, z, w]]
    rw [h1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun w _ => h3 x y z w
  have h5 : (2 : ℂ) • IsQuadLorentz.outerContraction (T := T) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h4]
    exact neg_add_cancel _
  calc IsQuadLorentz.outerContraction (T := T)
      = ((2 : ℂ)⁻¹ * 2) • IsQuadLorentz.outerContraction (T := T) := by
        rw [inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
    _ = (2 : ℂ)⁻¹ • ((2 : ℂ) • IsQuadLorentz.outerContraction (T := T)) := by rw [mul_smul]
    _ = 0 := by rw [h5, smul_zero]

/-- The split contraction of a quadruple Lorentz tensor antisymmetric in its first two
  indices is minus the inner one: exchanging the first two indices exchanges the two
  metric pairings and changes the sign of the tensor. -/
lemma splitContraction_eq_neg_innerContraction_of_swap
    {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hswap : ∀ x y z w : Fin 1 ⊕ Fin 3, T ![y, x, z, w] = - T ![x, y, z, w]) :
    IsQuadLorentz.splitContraction (T := T)
      = - IsQuadLorentz.innerContraction (T := T) := by
  have h1 : IsQuadLorentz.splitContraction (T := T)
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3,
        ∑ w : Fin 1 ⊕ Fin 3,
          ((minkowskiMatrixZ x w * minkowskiMatrixZ y z : ℤ) : ℂ) • T ![x, y, z, w] := by
    rw [IsQuadLorentz.splitContraction, IsQuadLorentz.sum_pi_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  have h2 : IsQuadLorentz.innerContraction (T := T)
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3,
        ∑ w : Fin 1 ⊕ Fin 3,
          ((minkowskiMatrixZ x z * minkowskiMatrixZ y w : ℤ) : ℂ) • T ![x, y, z, w] := by
    rw [IsQuadLorentz.innerContraction, IsQuadLorentz.sum_pi_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  have h3 : ∀ x y z w : Fin 1 ⊕ Fin 3,
      ((minkowskiMatrixZ y w * minkowskiMatrixZ x z : ℤ) : ℂ) • T ![y, x, z, w]
        = -(((minkowskiMatrixZ x z * minkowskiMatrixZ y w : ℤ) : ℂ) •
          T ![x, y, z, w]) := by
    intro x y z w
    rw [hswap x y z w, smul_neg, mul_comm (minkowskiMatrixZ y w)]
  conv_lhs => rw [h1, sum_quad fun x y z w =>
    ((minkowskiMatrixZ x w * minkowskiMatrixZ y z : ℤ) : ℂ) • T ![x, y, z, w]]
  rw [h2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun w _ => h3 x y z w


/-!

## I. The spans as invariants of mass weight eight

Sections G and H run one way: a gauge invariant, or a gauge and Lorentz invariant, of mass
weight eight is a combination of the generators of a span, up to a remainder in `S`. The
converse is that the span is made of such invariants to begin with, and it is what turns
each classification into an equivalence.

Nothing new is needed for it. The generators of the trace-contraction span are gauge
invariant by the three bi-adjoint transformation laws of section B, and those of the
twice-derived hypercharge span by `repGauge_hyperchargeField`, which fixes the hypercharge
field strength at every derivative order; their mass weights are those of section E and of
`derivSubmodule`. The Lorentz contraction span is smaller still, each of its four blocks
being spanned by the four contractions of a quadruple Lorentz family, and a contraction is
a combination of the components of its family with the constant coefficients `minkowskiMatrixZ` and
`epsilonSignZ`, so it lies in the span of those components. Gauge invariance and mass
weight therefore pass to it from the gauge spans, and Lorentz invariance comes from
`IsQuadLorentz` directly.

## I.1. The contractions inside the span of the components

-/

/-- A quadruple Lorentz family whose components all lie in a submodule has its whole span
  of components there. -/
lemma isQuadLorentz_span_le {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsQuadLorentz B repLorentz T) (V : Submodule ℂ B) (hV : ∀ d, T d ∈ V) :
    hT.span ≤ V :=
  iSup_le fun d => (Submodule.span_singleton_le_iff_mem _ _).2 (hV d)

/-- The span of the four Lorentz contractions of a quadruple Lorentz family lies in the
  span of its components: each contraction is a combination of components with constant
  coefficients. -/
lemma quadContractionSpan_le_span {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsQuadLorentz B repLorentz T) : quadContractionSpan T ≤ hT.span :=
  sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hT.outerContraction_mem_span)
    (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hT.innerContraction_mem_span)
      (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hT.splitContraction_mem_span)
        ((Submodule.span_singleton_le_iff_mem _ _).2 hT.epsilonContraction_mem_span)))

/-- The span of the four Lorentz contractions of a quadruple Lorentz family is a space of
  Lorentz invariants, the four contractions being invariant by section I.6 of
  `IsQuadLorentz`. -/
lemma quadContractionSpan_le_lorentzInvariants {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsQuadLorentz B repLorentz T) :
    quadContractionSpan T ≤ repLorentz.invariants := by
  refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_))
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2 hT.repLorentz_outerContraction)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2 hT.repLorentz_innerContraction)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2 hT.repLorentz_splitContraction)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2 hT.repLorentz_epsilonContraction)

/-!

## I.2. The gauge spans are gauge invariants of mass weight eight

-/

/-- The span of the three underived trace contractions is a space of gauge invariants:
  each generator is fixed by the gauge group, by the bi-adjoint law of its family. -/
lemma traceContractionEightSpan_le_invariants :
    h.traceContractionEightSpan ≤ repGauge.invariants := by
  rw [traceContractionEightSpan]
  refine sup_le (iSup_le fun p => ?_) (sup_le (iSup_le fun p => ?_) (iSup_le fun p => ?_))
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2 fun g => IsSU3BiAdjoint.map_traceContraction _
        (h.isSU3BiAdjointMat_gluonField_mul ![] (p 0) (p 1) ![] (p 2) (p 3) g))
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2 fun g => IsSU2BiAdjoint.map_traceContraction _
        (h.isSU2BiAdjointMat_wField_mul ![] (p 0) (p 1) ![] (p 2) (p 3) g))
  · exact (Submodule.span_singleton_le_iff_mem _ _).2
      ((Representation.mem_invariants _ _).2 fun g => IsU1BiAdjoint.map_traceContraction _
        (h.isU1BiAdjointMat_hyperchargeField_mul ![] (p 0) (p 1) ![] (p 2) (p 3) g))

/-- The twice-derived hypercharge span is a space of gauge invariants, its generators
  being fixed pointwise by the whole gauge group. -/
lemma hyperchargeDerivSpan_le_invariants :
    h.hyperchargeDerivSpan ≤ repGauge.invariants :=
  fun _ hy => (Representation.mem_invariants _ _).2 fun g =>
    h.repGauge_of_mem_hyperchargeDerivSpan g hy

/-- The span of the three underived trace contractions lies in the mass-weight eight
  submodule: each generator does, by section E. -/
lemma traceContractionEightSpan_le_massWeightSubmodule :
    h.traceContractionEightSpan ≤ h.massWeightSubmodule 8 := by
  rw [traceContractionEightSpan]
  refine sup_le (iSup_le fun p => ?_) (sup_le (iSup_le fun p => ?_) (iSup_le fun p => ?_))
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_inf.1
      (h.traceContraction_gluonField_mul_mem_eight (p 0) (p 1) (p 2) (p 3))).1
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_inf.1
      (h.traceContraction_wField_mul_mem_eight (p 0) (p 1) (p 2) (p 3))).1
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_inf.1
      (h.traceContraction_hyperchargeField_mul_mem_eight (p 0) (p 1) (p 2) (p 3))).1

/-- The twice-derived hypercharge span lies in the mass-weight eight submodule: a
  field-strength symbol with two covariant derivatives has mass weight `2 * (2 + 2)`. -/
lemma hyperchargeDerivSpan_le_massWeightSubmodule :
    h.hyperchargeDerivSpan ≤ h.massWeightSubmodule 8 := by
  rw [hyperchargeDerivSpan]
  refine iSup_le fun d => (Submodule.span_singleton_le_iff_mem _ _).2 ?_
  have hmem := h.derivSubmodule_le_massWeightSubmodule 2
    (h.hyperchargeField_mem_derivSubmodule ![d 0, d 1] (d 2) (d 3))
  rwa [show 2 * (2 + 2) = 8 from by norm_num] at hmem

/-- The span the gauge classification of section G produces is a space of gauge invariants
  of mass weight eight: the converse of that classification. -/
lemma traceContractionEightSpan_sup_hyperchargeDerivSpan_le :
    h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan
      ≤ h.massWeightSubmodule 8 ⊓ repGauge.invariants :=
  sup_le (le_inf h.traceContractionEightSpan_le_massWeightSubmodule
      h.traceContractionEightSpan_le_invariants)
    (le_inf h.hyperchargeDerivSpan_le_massWeightSubmodule
      h.hyperchargeDerivSpan_le_invariants)

/-!

## I.3. The Lorentz contraction span

-/

/-- The twice-derived hypercharge span is the span of the components of the twice-derived
  quadruple Lorentz family. -/
lemma hyperchargeDerivSpan_eq :
    h.hyperchargeDerivSpan = (h.isQuadLorentz_hyperchargeDeriv).span := rfl

/-- The Lorentz contraction span sits inside the span the gauge classification produces:
  each of its four blocks is spanned by the four contractions of a quadruple Lorentz
  family whose components generate the matching block of the gauge span. -/
lemma lorentzContractionEightSpan_le_traceContractionEightSpan_sup :
    h.lorentzContractionEightSpan
      ≤ h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan := by
  rw [lorentzContractionEightSpan, h.traceContractionEightSpan_eq,
    h.hyperchargeDerivSpan_eq]
  refine sup_le ((quadContractionSpan_le_span h.isQuadLorentz_gluonTrace).trans ?_)
    (sup_le ((quadContractionSpan_le_span h.isQuadLorentz_wTrace).trans ?_)
      (sup_le ((quadContractionSpan_le_span h.isQuadLorentz_hyperchargeTrace).trans ?_)
        ((quadContractionSpan_le_span h.isQuadLorentz_hyperchargeDeriv).trans ?_)))
  · exact le_sup_of_le_left le_sup_left
  · exact le_sup_of_le_left (le_sup_of_le_right le_sup_left)
  · exact le_sup_of_le_left (le_sup_of_le_right le_sup_right)
  · exact le_sup_right

/-- The Lorentz contraction span is a space of gauge invariants: it lies in the gauge
  span, whose generators the gauge group fixes. -/
lemma lorentzContractionEightSpan_le_invariants :
    h.lorentzContractionEightSpan ≤ repGauge.invariants :=
  h.lorentzContractionEightSpan_le_traceContractionEightSpan_sup.trans
    (sup_le h.traceContractionEightSpan_le_invariants
      h.hyperchargeDerivSpan_le_invariants)

/-- The Lorentz contraction span lies in the mass-weight eight submodule, for the same
  reason. -/
lemma lorentzContractionEightSpan_le_massWeightSubmodule :
    h.lorentzContractionEightSpan ≤ h.massWeightSubmodule 8 :=
  h.lorentzContractionEightSpan_le_traceContractionEightSpan_sup.trans
    (sup_le h.traceContractionEightSpan_le_massWeightSubmodule
      h.hyperchargeDerivSpan_le_massWeightSubmodule)

/-- The Lorentz contraction span is a space of Lorentz invariants: each of its four blocks
  is spanned by the four contractions of a quadruple Lorentz family, and those are fixed
  by the Lorentz group. -/
lemma lorentzContractionEightSpan_le_lorentzInvariants :
    h.lorentzContractionEightSpan ≤ repLorentz.invariants := by
  rw [lorentzContractionEightSpan]
  exact sup_le (quadContractionSpan_le_lorentzInvariants h.isQuadLorentz_gluonTrace)
    (sup_le (quadContractionSpan_le_lorentzInvariants h.isQuadLorentz_wTrace)
      (sup_le (quadContractionSpan_le_lorentzInvariants h.isQuadLorentz_hyperchargeTrace)
        (quadContractionSpan_le_lorentzInvariants h.isQuadLorentz_hyperchargeDeriv)))

/-!

## J. The classifications as equivalences

The two directions meet. Forwards, sections G and H put an invariant of mass weight eight
in the span up to a remainder in `S`; backwards, section I says the span is made of such
invariants, so the remainder plus the span element is one again. Splitting `x` as
`(x - y) + y` is all the backward direction takes.

-/

/-- The gauge classification of mass weight eight as an equivalence: an element of
  `massWeightSubmodule 8 ⊔ S` is gauge invariant exactly when it is a combination of the
  three underived trace contractions and the twice-derived hypercharge field strengths up
  to a gauge-invariant remainder in `S`. Forwards this is
  `exists_mem_of_invariant_massWeightSubmodule_eight_sup`; backwards it splits `x` as
  `(x - y) + y`, both summands gauge invariant and both of mass weight eight or in `S`. -/
theorem mem_massWeightSubmodule_eight_sup_and_invariant_iff (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule 8 ⊔ S ∧ ∀ g : GaugeGroupI, repGauge g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ x - y ∈ h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan := by
  refine ⟨fun hx =>
    h.exists_mem_of_invariant_massWeightSubmodule_eight_sup S hS hx.1 hx.2, ?_⟩
  rintro ⟨y, hyS, hyinv, hxy⟩
  obtain ⟨hmem, hinv⟩ := Submodule.mem_inf.1
    (h.traceContractionEightSpan_sup_hyperchargeDerivSpan_le hxy)
  refine ⟨?_, fun g => ?_⟩
  · have hsum : x - y + y ∈ h.massWeightSubmodule 8 ⊔ S :=
      Submodule.add_mem _ (Submodule.mem_sup_left hmem) (Submodule.mem_sup_right hyS)
    simpa using hsum
  · have hstep : repGauge g (x - y + y) = x - y + y := by
      rw [map_add, (Representation.mem_invariants _ _).1 hinv g, hyinv g]
    simpa using hstep

/-- The gauge and Lorentz classification of mass weight eight as an equivalence: an
  element of `massWeightSubmodule 8 ⊔ S` is fixed by both groups exactly when it is a
  combination of the four Lorentz contractions of the four families of section H up to a
  remainder in `S` fixed by both groups. Forwards this is
  `exists_mem_of_gauge_and_lorentz_invariant`; backwards it splits `x` as `(x - y) + y`,
  the first summand invariant and of mass weight eight by section I. -/
theorem mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.lorentzContractionEightSpan := by
  refine ⟨fun hx =>
    h.exists_mem_of_gauge_and_lorentz_invariant S hS hSL hx.1 hx.2.1 hx.2.2, ?_⟩
  rintro ⟨y, hyS, hyG, hyL, hxy⟩
  have hmem := h.lorentzContractionEightSpan_le_massWeightSubmodule hxy
  have hG := (Representation.mem_invariants _ _).1
    (h.lorentzContractionEightSpan_le_invariants hxy)
  have hL := (Representation.mem_invariants _ _).1
    (h.lorentzContractionEightSpan_le_lorentzInvariants hxy)
  refine ⟨?_, fun g => ?_, fun g => ?_⟩
  · have hsum : x - y + y ∈ h.massWeightSubmodule 8 ⊔ S :=
      Submodule.add_mem _ (Submodule.mem_sup_left hmem) (Submodule.mem_sup_right hyS)
    simpa using hsum
  · have hstep : repGauge g (x - y + y) = x - y + y := by rw [map_add, hG g, hyG g]
    simpa using hstep
  · have hstep : repLorentz g (x - y + y) = x - y + y := by rw [map_add, hL g, hyL g]
    simpa using hstep

end IsGaugeSector

end StandardModel
