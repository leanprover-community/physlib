/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.InvariantReduction
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Adjoint
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsU1BiAdjoint
public import Physlib.Relativity.LorentzGroup.Invariants.RankFour
public import Mathlib.RepresentationTheory.Invariants
/-!
# Products of two field strengths as bi-adjoint gauge tensors

A single field-strength symbol of the gauge sector carries one adjoint index of the gauge
algebra, so a product of two of them carries two. Restricting the value index to one
factor of the gauge group turns such a product into a family indexed by two adjoint
indices of that factor, and the gauge transformation law of the sector says exactly that
these families are bi-adjoint in the sense of `IsSU3BiAdjoint`, `IsSU2BiAdjoint` and
`IsU1BiAdjoint`. The gauge invariant those propositions supply is the trace contraction,
the Kronecker contraction of the two adjoint indices, the familiar kinetic pairing of two
field strengths; it has mass weight eight and is fixed by the whole gauge group.

Conversely the colour and isospin generators of the zero-weight piece of mass weight eight
lie inside the spans of the underived gluon and `W`-boson families, and what does not is
either a hypercharge invariant or carries an unpaired adjoint index of a non-abelian
factor, which contributes nothing by `IsSU3Adjoint` and `IsSU2Adjoint`. Putting the two
directions together classifies the gauge invariants of mass weight eight modulo any
gauge-stable submodule: such an invariant is a combination of the three underived trace
contractions and the twice-derived hypercharge field strengths. Both shapes carry four
covector indices and no others, so both are quadruple Lorentz tensors, and the Lorentz
classification cuts the combinations down further, to the four Lorentz contractions of
each of the four families.

- A. Spans and stability
- B. The gauge transformation of the gauge-factor field strengths
- C. Products of two underived field strengths as bi-adjoint families
- D. The weight vectors of mass weight eight inside the bi-adjoint spans
- E. The zero-weight piece of mass weight eight
- F. The unpaired non-abelian adjoint indices
- G. The gauge invariants of mass weight eight
- H. The Lorentz classification of the mass-weight eight invariants
- I. The Lorentz contraction span as invariants of mass weight eight
- J. The classifications as equivalences

Both classifications are reductions in the sense of `ReducesInvariantsTo`, stated modulo
any stable submodule. The converse is that each span consists of invariants of mass weight
eight already, the gauge one because its generators are fixed by the gauge group and carry
the right mass weight, and the Lorentz one because it sits inside the gauge span and is
spanned by contractions that `RankFour` shows to be Lorentz invariant. Section J composes
the two reductions and puts the two directions together as the equivalences
`mem_massWeightSubmodule_eight_sup_and_invariant_iff` and
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

## A. Spans and stability

Every subspace in this file is spanned by a finite family. Where a classifier supplies or
consumes it, it is written `Submodule.span ℂ (Set.range T)`; where a family of lines is
collected, it is the join `⨆ i, ℂ ∙ T i`, and `Submodule.span_range_eq_iSup` passes between
the two. A join of lines lies in a submodule as soon as its generators do, and a linear map
fixing each generator fixes it pointwise; a linear map moving each generator to a
combination of the generators carries the span into itself.

The classification runs through `ReducesInvariantsTo`. Each bi-adjoint family's span
reduces, for its factor of the gauge group, to the line through its trace contraction, and
each adjoint family's span to `⊥`; `ReducesInvariantsTo.iSup` joins the families of one
kind, and `ReducesInvariantsTo.sup` joins the kinds.

-/

/-- A span lies in a submodule as soon as its generators do. -/
lemma iSup_span_singleton_le {ι : Sort*} (T : ι → B) {V : Submodule ℂ B}
    (hV : ∀ i, T i ∈ V) : (⨆ i, ℂ ∙ T i) ≤ V :=
  iSup_le fun i => (Submodule.span_singleton_le_iff_mem _ _).2 (hV i)

/-- A generator of a family with three indices lies in its span. -/
lemma mem_iSup_span₃ {α β γ : Sort*} (T : α → β → γ → B) (a : α) (b : β) (c : γ) :
    T a b c ∈ ⨆ (a) (b) (c), ℂ ∙ T a b c :=
  Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem c (Submodule.mem_span_singleton_self _)))

/-- A linear map moving each generator to a combination of the generators carries the span
  into itself; the transformation laws of this file all have this shape. -/
lemma span_stable_of_map_eq_sum {ι : Type} [Fintype ι] (T : ι → B) (f : B →ₗ[ℂ] B)
    {c : ι → ι → ℂ} (hf : ∀ l, f (T l) = ∑ a, c a l • T a) :
    ∀ y ∈ Submodule.span ℂ (Set.range T), f y ∈ Submodule.span ℂ (Set.range T) :=
  isStableUnder_span_range_of_sum (σ := fun _ : Unit => f) (fun _ l => ⟨_, hf l⟩) ()

/-- A linear map fixing each generator fixes the span pointwise. -/
lemma map_eq_self_of_mem_iSup_span {ι : Sort*} (T : ι → B) (f : B →ₗ[ℂ] B)
    (hf : ∀ i, f (T i) = T i) : ∀ y ∈ ⨆ i, ℂ ∙ T i, f y = y := fun _ hy =>
  LinearMap.mem_eqLocus.1 (iSup_span_singleton_le T (V := LinearMap.eqLocus f LinearMap.id)
    (fun i => LinearMap.mem_eqLocus.2 (hf i)) hy)

/-- The product of two lines lies in a submodule as soon as the product of the two
  generators does. -/
lemma span_singleton_mul_span_singleton_le {a b : B} {V : Submodule ℂ B} (hab : a * b ∈ V) :
    (ℂ ∙ a) * (ℂ ∙ b) ≤ V := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
  exact (Submodule.span_singleton_le_iff_mem _ _).2 hab

/-- The product of two spans lies in a submodule as soon as the products of their
  generators do. -/
lemma iSup_span_mul_iSup_span_le {α β γ α' β' γ' : Sort*} (T : α → β → γ → B)
    (T' : α' → β' → γ' → B) {V : Submodule ℂ B} (hV : ∀ a b c a' b' c', T a b c * T' a' b' c' ∈ V) :
    (⨆ (a) (b) (c), ℂ ∙ T a b c) * (⨆ (a) (b) (c), ℂ ∙ T' a b c) ≤ V := by
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    iSup_le fun _ => ?_
  exact span_singleton_mul_span_singleton_le (hV _ _ _ _ _ _)

/-- A product of two combinations is a combination indexed by pairs. -/
lemma sum_mul_sum_eq_sum_pi_two {k : ℕ} (c₀ c₁ : Fin k → ℂ) (X Y : Fin k → B) :
    (∑ a, c₀ a • X a) * ∑ b, c₁ b • Y b
      = ∑ d : Fin 2 → Fin k, (c₀ (d 0) * c₁ (d 1)) • (X (d 0) * Y (d 1)) := by
  rw [Fintype.sum_mul_sum, Family.sum_pi_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp

/-- A multiplicative map moving a family by a matrix and fixing a vector moves the
  products of the family with that vector by the same matrix. -/
lemma map_mul_fixed_eq_sum {k : ℕ} {f : B →ₗ[ℂ] B} (hf : ∀ x y, f (x * y) = f x * f y)
    {c : Fin k → Fin k → ℂ} {T : Fin k → B} (hT : ∀ l, f (T l) = ∑ a, c a l • T a) {v : B}
    (hv : f v = v) (l : Fin k) : f (T l * v) = ∑ a, c a l • (T a * v) := by
  rw [hf, hT, hv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => smul_mul_assoc _ _ _

/-- The mirror of `map_mul_fixed_eq_sum` with the fixed vector on the left. -/
lemma map_fixed_mul_eq_sum {k : ℕ} {f : B →ₗ[ℂ] B} (hf : ∀ x y, f (x * y) = f x * f y)
    {c : Fin k → Fin k → ℂ} {T : Fin k → B} (hT : ∀ l, f (T l) = ∑ a, c a l • T a) {v : B}
    (hv : f v = v) (l : Fin k) : f (v * T l) = ∑ a, c a l • (v * T a) := by
  rw [hf, hT, hv, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_smul_comm _ _ _

/-!

## B. The gauge transformation of the gauge-factor field strengths

The gauge law of `IsGaugeSector` moves the field-strength symbol by the coadjoint action of
the gauge group on its argument, which on the standard basis coordinates is the adjoint
matrix. That matrix is block diagonal, so the gluon field strengths transform among
themselves by the `su(3)` adjoint matrix of the colour factor, the `W`-boson field
strengths by the `su(2)` adjoint matrix of the isospin factor, and the hypercharge field
strength is fixed. The colour factor alone fixes the `W`-boson field strengths as well.

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
      = ∑ a : Fin 8, ((su3AdjointMatrix (GaugeGroupI.toSU3 g) a c : ℝ) : ℂ) •
          h.gluonField l μ ν a := by
  rw [gluonField, h.repGauge_F_coord g l μ ν (Sum.inl c), Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp [gluonField]

/-- The `W`-boson field strength transforms in the adjoint representation of the `su(2)`
  factor of the gauge group. -/
lemma repGauge_wField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 3) :
    repGauge g (h.wField l μ ν c)
      = ∑ i : Fin 3, ((su2AdjointMatrix (GaugeGroupI.toSU2 g) i c : ℝ) : ℂ) •
          h.wField l μ ν i := by
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

/-- The `W`-boson field strengths are fixed by the colour factor of the gauge group: the
  `su(2)` block of the adjoint matrix reads the isospin factor alone. -/
lemma repGauge_su3_wField (U : specialUnitaryGroup (Fin 3) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (i : Fin 3) :
    repGauge (U, 1, 1) (h.wField l μ ν i) = h.wField l μ ν i := by
  rw [h.repGauge_wField (U, 1, 1) l μ ν i]
  have hM : ∀ j : Fin 3, su2AdjointMatrix (GaugeGroupI.toSU2 ((U, 1, 1) : GaugeGroupI)) j i
      = if j = i then 1 else 0 := by
    intro j
    rw [show su2AdjointMatrix (GaugeGroupI.toSU2 ((U, 1, 1) : GaugeGroupI)) j i
        = GaugeAlgebra.adjointMatrix (1 : GaugeGroupI) (Sum.inr (Sum.inl j))
          (Sum.inr (Sum.inl i)) from rfl, GaugeAlgebra.adjointMatrix_one, Matrix.one_apply]
    simp
  simp only [hM]
  simp

/-- The gluon field strengths at fixed derivative slots and covector indices form a family
  of one `su(3)` adjoint index. -/
lemma isSU3Adjoint_gluonField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    IsSU3Adjoint B repGauge (h.gluonField l μ ν) :=
  IsSU3Adjoint.of_law fun U c => h.repGauge_gluonField (U, 1, 1) l μ ν c

/-- The `W`-boson field strengths at fixed derivative slots and covector indices form a
  family of one `su(2)` adjoint index. -/
lemma isSU2Adjoint_wField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    IsSU2Adjoint B repGauge (h.wField l μ ν) :=
  IsSU2Adjoint.of_law fun U c => h.repGauge_wField (1, U, 1) l μ ν c

/-!

## C. Products of two underived field strengths as bi-adjoint families

A product of two underived field strengths of one gauge factor, at the four covector
indices `p`, is a family indexed by the two adjoint indices of that factor, and by section
B and the multiplicativity of the gauge action it is a bi-adjoint family in the sense of
`IsSU3BiAdjoint`, `IsSU2BiAdjoint` and `IsU1BiAdjoint`, with the transformation law
holding at every gauge element and not only at those of its own factor. Its trace
contraction, the Kronecker contraction of the two adjoint indices, is fixed by the whole
gauge group and has mass weight eight, the sum of the mass weights of its two factors; so
is the twice-derived hypercharge field strength, the other shape of mass weight eight.

-/

/-- The index of a product of two underived field strengths: the two covector indices of
  the first factor followed by the two of the second, read as one family of four
  four-vector indices so that the Lorentz classification applies to it. -/
abbrev EightIdx : Type := Fin 4 → Fin 1 ⊕ Fin 3

/-- The product of two underived gluon field strengths at the covector indices `p`, indexed
  by the two `su(3)` adjoint indices it carries. -/
noncomputable def gluonPair (p : EightIdx) (a : Fin 2 → Fin 8) : B :=
  h.gluonField ![] (p 0) (p 1) (a 0) * h.gluonField ![] (p 2) (p 3) (a 1)

/-- The product of two underived `W`-boson field strengths at the covector indices `p`,
  indexed by the two `su(2)` adjoint indices it carries. -/
noncomputable def wPair (p : EightIdx) (a : Fin 2 → Fin 3) : B :=
  h.wField ![] (p 0) (p 1) (a 0) * h.wField ![] (p 2) (p 3) (a 1)

/-- The product of two underived hypercharge field strengths at the covector indices `p`,
  indexed by the two `u(1)` adjoint indices it carries. -/
noncomputable def hyperchargePair (p : EightIdx) (_ : Fin 2 → Fin 1) : B :=
  h.hyperchargeField ![] (p 0) (p 1) * h.hyperchargeField ![] (p 2) (p 3)

/-- The twice-derived hypercharge field strength at the derivative slots `d 0`, `d 1` and
  the covector indices `d 2`, `d 3`. -/
noncomputable def hyperchargeDeriv (d : EightIdx) : B :=
  h.hyperchargeField ![d 0, d 1] (d 2) (d 3)

/-- A gauge transformation moves a gluon pair as the `SU(3)` factor of that gauge group
  element moves a tensor with two `su(3)` adjoint indices. -/
lemma isSU3BiAdjointMat_gluonPair (p : EightIdx) (g : GaugeGroupI) :
    IsSU3BiAdjointMat (GaugeGroupI.toSU3 g) (repGauge g) (h.gluonPair p) := fun _ => by
  simp only [gluonPair, hrepGauge_mul, h.repGauge_gluonField, sum_mul_sum_eq_sum_pi_two,
    Fin.prod_univ_two]

/-- A gluon pair is a bi-adjoint `su(3)` tensor. -/
lemma isSU3BiAdjoint_gluonPair (p : EightIdx) : IsSU3BiAdjoint B repGauge (h.gluonPair p) :=
  IsSU3BiAdjoint.of_law fun U => h.isSU3BiAdjointMat_gluonPair p (U, 1, 1)

/-- A gauge transformation moves a `W`-boson pair as the `SU(2)` factor of that gauge group
  element moves a tensor with two `su(2)` adjoint indices. -/
lemma isSU2BiAdjointMat_wPair (p : EightIdx) (g : GaugeGroupI) :
    IsSU2BiAdjointMat (GaugeGroupI.toSU2 g) (repGauge g) (h.wPair p) := fun _ => by
  simp only [wPair, hrepGauge_mul, h.repGauge_wField, sum_mul_sum_eq_sum_pi_two,
    Fin.prod_univ_two]

/-- A `W`-boson pair is a bi-adjoint `su(2)` tensor. -/
lemma isSU2BiAdjoint_wPair (p : EightIdx) : IsSU2BiAdjoint B repGauge (h.wPair p) :=
  IsSU2BiAdjoint.of_law fun U => h.isSU2BiAdjointMat_wPair p (1, U, 1)

/-- A gauge transformation fixes a hypercharge pair, which is the `u(1)` bi-adjoint law. -/
lemma isU1BiAdjointMat_hyperchargePair (p : EightIdx) (g : GaugeGroupI) :
    IsU1BiAdjointMat (GaugeGroupI.toU1 g) (repGauge g) (h.hyperchargePair p) :=
  (isU1BiAdjointMat_iff _ _ _).2 fun _ => by
    simp only [hyperchargePair, hrepGauge_mul, h.repGauge_hyperchargeField]

/-- A hypercharge pair is a bi-adjoint `u(1)` tensor. -/
lemma isU1BiAdjoint_hyperchargePair (p : EightIdx) :
    IsU1BiAdjoint B repGauge (h.hyperchargePair p) :=
  ⟨fun u => h.isU1BiAdjointMat_hyperchargePair p (1, 1, u)⟩

/-- The gluon trace contraction at the covector indices `p`: the Kronecker contraction of
  the two colour indices of the gluon pair. -/
noncomputable def gluonTrace (p : EightIdx) : B := IsSU3BiAdjoint.traceContraction (h.gluonPair p)

/-- The `W`-boson trace contraction at the covector indices `p`. -/
noncomputable def wTrace (p : EightIdx) : B := IsSU2BiAdjoint.traceContraction (h.wPair p)

/-- The hypercharge trace contraction at the covector indices `p`. -/
noncomputable def hyperchargeTrace (p : EightIdx) : B :=
  IsU1BiAdjoint.traceContraction (h.hyperchargePair p)

/-- The gluon trace contraction is the kinetic pairing of two gluon field strengths. -/
lemma gluonTrace_eq (p : EightIdx) :
    h.gluonTrace p
      = ∑ a : Fin 8, h.gluonField ![] (p 0) (p 1) a * h.gluonField ![] (p 2) (p 3) a := by
  simp [gluonTrace, IsSU3BiAdjoint.traceContraction, gluonPair]

/-- The `W`-boson trace contraction is the kinetic pairing of two `W`-boson field
  strengths. -/
lemma wTrace_eq (p : EightIdx) :
    h.wTrace p = ∑ i : Fin 3, h.wField ![] (p 0) (p 1) i * h.wField ![] (p 2) (p 3) i := by
  simp [wTrace, IsSU2BiAdjoint.traceContraction, wPair]

/-- The hypercharge trace contraction is the product of the two hypercharge field
  strengths, the `u(1)` factor being one dimensional. -/
lemma hyperchargeTrace_eq (p : EightIdx) :
    h.hyperchargeTrace p
      = h.hyperchargeField ![] (p 0) (p 1) * h.hyperchargeField ![] (p 2) (p 3) := by
  simp [hyperchargeTrace, IsU1BiAdjoint.traceContraction, hyperchargePair]

/-- The gluon trace contraction is fixed by the whole gauge group. -/
lemma repGauge_gluonTrace (g : GaugeGroupI) (p : EightIdx) :
    repGauge g (h.gluonTrace p) = h.gluonTrace p :=
  IsSU3BiAdjoint.map_traceContraction (h.isSU3BiAdjointMat_gluonPair p g)

/-- The `W`-boson trace contraction is fixed by the whole gauge group. -/
lemma repGauge_wTrace (g : GaugeGroupI) (p : EightIdx) :
    repGauge g (h.wTrace p) = h.wTrace p :=
  IsSU2BiAdjoint.map_traceContraction (h.isSU2BiAdjointMat_wPair p g)

/-- The hypercharge trace contraction is fixed by the whole gauge group. -/
lemma repGauge_hyperchargeTrace (g : GaugeGroupI) (p : EightIdx) :
    repGauge g (h.hyperchargeTrace p) = h.hyperchargeTrace p :=
  IsU1BiAdjoint.map_traceContraction (h.isU1BiAdjointMat_hyperchargePair p g)

/-- The twice-derived hypercharge field strength is fixed by the whole gauge group. -/
lemma repGauge_hyperchargeDeriv (g : GaugeGroupI) (d : EightIdx) :
    repGauge g (h.hyperchargeDeriv d) = h.hyperchargeDeriv d :=
  h.repGauge_hyperchargeField g _ _ _

/-- Every field-strength symbol lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma F_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : F l μ ν φ ∈ h.derivSubmodule n := by
  rw [derivSubmodule]
  exact Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ
    (Submodule.mem_iSup_of_mem ν (Submodule.subset_span ⟨φ, rfl⟩)))

/-- A field-strength symbol with `n` covariant derivatives has mass weight `2 * (2 + n)`. -/
lemma F_mem_massWeightSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : F l μ ν φ ∈ h.massWeightSubmodule (2 * (2 + n)) :=
  h.derivSubmodule_le_massWeightSubmodule n (h.F_mem_derivSubmodule l μ ν φ)

/-- A product of two underived field-strength symbols has mass weight eight. -/
lemma F_mul_F_mem_massWeightSubmodule_eight (μ ν μ' ν' : Fin 1 ⊕ Fin 3)
    (φ φ' : Module.Dual ℝ GaugeAlgebra) :
    F ![] μ ν φ * F ![] μ' ν' φ' ∈ h.massWeightSubmodule 8 := by
  simpa using h.massWeightSubmodule_mul_le _ _ (Submodule.mul_mem_mul
    (h.F_mem_massWeightSubmodule ![] μ ν φ) (h.F_mem_massWeightSubmodule ![] μ' ν' φ'))

/-- The gluon trace contraction has mass weight eight. -/
lemma gluonTrace_mem_massWeightSubmodule (p : EightIdx) :
    h.gluonTrace p ∈ h.massWeightSubmodule 8 := by
  rw [gluonTrace_eq]
  exact Submodule.sum_mem _ fun a _ => h.F_mul_F_mem_massWeightSubmodule_eight _ _ _ _ _ _

/-- The `W`-boson trace contraction has mass weight eight. -/
lemma wTrace_mem_massWeightSubmodule (p : EightIdx) : h.wTrace p ∈ h.massWeightSubmodule 8 := by
  rw [wTrace_eq]
  exact Submodule.sum_mem _ fun i _ => h.F_mul_F_mem_massWeightSubmodule_eight _ _ _ _ _ _

/-- The hypercharge trace contraction has mass weight eight. -/
lemma hyperchargeTrace_mem_massWeightSubmodule (p : EightIdx) :
    h.hyperchargeTrace p ∈ h.massWeightSubmodule 8 := by
  rw [hyperchargeTrace_eq]
  exact h.F_mul_F_mem_massWeightSubmodule_eight _ _ _ _ _ _

/-- The twice-derived hypercharge field strength has mass weight `2 * (2 + 2)`, eight. -/
lemma hyperchargeDeriv_mem_massWeightSubmodule (d : EightIdx) :
    h.hyperchargeDeriv d ∈ h.massWeightSubmodule 8 := by
  simpa [hyperchargeDeriv, hyperchargeField] using
    h.F_mem_massWeightSubmodule ![d 0, d 1] (d 2) (d 3) (GaugeAlgebra.stdBasis.coord _)

/-!

## D. The weight vectors of mass weight eight inside the bi-adjoint spans

The gauge weight decomposition of the underived tower is built from the weight vectors
`adjVec` of one adjoint index. On a colour direction such a vector is a combination of
gluon field strengths, on the isospin directions a combination of `W`-boson field
strengths, and on the hypercharge direction the hypercharge field strength itself, the
combinations being the weight coordinates `GaugeAlgebra.su3WeightCoeff` and
`GaugeAlgebra.su2WeightCoeff`. A product of two of them is then a combination of the
components of the matching pair family, so it lies in the span of that family. At mass weight
eight this covers the gluon root part and the isospin root part of the zero-weight piece
computed by `massWeightSubmoduleGaugeWeightEight_piece_zero`.

-/

/-- The `su(3)` adjoint weight indices read as weight indices of the whole gauge
  algebra: the three colour roots and the two colour Cartan directions. -/
def su3AdjIdx : GaugeAlgebra.su3WeightIdx → Fin 4 ⊕ Fin 4 ⊕ Fin 4
  | Sum.inl r => Sum.inl r.castSucc
  | Sum.inr (Sum.inl r) => Sum.inr (Sum.inl r.castSucc)
  | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c.castSucc.castSucc)

/-- The `su(2)` adjoint weight indices read as weight indices of the whole gauge
  algebra: the isospin root and the isospin Cartan direction. -/
def su2AdjIdx : GaugeAlgebra.su2WeightIdx → Fin 4 ⊕ Fin 4 ⊕ Fin 4
  | Sum.inl _ => Sum.inl 3
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl 3)
  | Sum.inr (Sum.inr _) => Sum.inr (Sum.inr 2)

/-- A weight vector of the colour part of the adjoint is the matching combination of
  gluon field strengths. -/
lemma sum_su3WeightCoeff_smul_gluonField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (k : GaugeAlgebra.su3WeightIdx) :
    ∑ a : Fin 8, GaugeAlgebra.su3WeightCoeff k a • h.gluonField l μ ν a
      = h.adjVec l μ ν (su3AdjIdx k) := by
  rcases k with r | r | c <;>
    simp [GaugeAlgebra.su3WeightCoeff, su3AdjIdx, adjVec, GaugeAlgebra.rootIdx_castSucc,
      GaugeAlgebra.cartanIdx_castSucc, gluonField, add_smul, sub_smul, ite_smul, mul_ite,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- A weight vector of the isospin part of the adjoint is the matching combination of
  `W`-boson field strengths. -/
lemma sum_su2WeightCoeff_smul_wField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (k : GaugeAlgebra.su2WeightIdx) :
    ∑ i : Fin 3, GaugeAlgebra.su2WeightCoeff k i • h.wField l μ ν i
      = h.adjVec l μ ν (su2AdjIdx k) := by
  rcases k with r | r | c <;>
    simp [GaugeAlgebra.su2WeightCoeff, su2AdjIdx, adjVec, GaugeAlgebra.rootIdx_three,
      GaugeAlgebra.cartanIdx_two, wField, add_smul, sub_smul, ite_smul, mul_ite,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- A product of two colour weight vectors of the adjoint lies in the span of the matching
  gluon pair family. -/
lemma adjVec_mul_adjVec_mem_gluonPair_span (p : EightIdx)
    (k₀ k₁ : GaugeAlgebra.su3WeightIdx) :
    h.adjVec ![] (p 0) (p 1) (su3AdjIdx k₀) * h.adjVec ![] (p 2) (p 3) (su3AdjIdx k₁)
      ∈ Submodule.span ℂ (Set.range (h.gluonPair p)) := by
  rw [← h.sum_su3WeightCoeff_smul_gluonField, ← h.sum_su3WeightCoeff_smul_gluonField,
    sum_mul_sum_eq_sum_pi_two]
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨_, rfl⟩

/-- A product of two isospin weight vectors of the adjoint lies in the span of the matching
  `W`-boson pair family. -/
lemma adjVec_mul_adjVec_mem_wPair_span (p : EightIdx) (k₀ k₁ : GaugeAlgebra.su2WeightIdx) :
    h.adjVec ![] (p 0) (p 1) (su2AdjIdx k₀) * h.adjVec ![] (p 2) (p 3) (su2AdjIdx k₁)
      ∈ Submodule.span ℂ (Set.range (h.wPair p)) := by
  rw [← h.sum_su2WeightCoeff_smul_wField, ← h.sum_su2WeightCoeff_smul_wField,
    sum_mul_sum_eq_sum_pi_two]
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨_, rfl⟩

/-- The join, over all covector indices, of the spans of the gluon pair families. -/
noncomputable def gluonPairSpan : Submodule ℂ B := ⨆ p, Submodule.span ℂ (Set.range (h.gluonPair p))

/-- The join, over all covector indices, of the spans of the `W`-boson pair families. -/
noncomputable def wPairSpan : Submodule ℂ B := ⨆ p, Submodule.span ℂ (Set.range (h.wPair p))

/-- The gluon root part of the zero-weight piece, the three products of a colour raising
  vector against the matching lowering vector, lies in the gluon pair spans. -/
lemma gluonRootPart_le_gluonPairSpan : h.gluonRootPart ≤ h.gluonPairSpan := by
  have key : ∀ r : Fin 3,
      h.rootRaisingSpan r.castSucc * h.rootLoweringSpan r.castSucc ≤ h.gluonPairSpan :=
    fun r => iSup_span_mul_iSup_span_le _ _ fun l μ ν l' μ' ν' => by
      rw [Subsingleton.elim l ![], Subsingleton.elim l' ![]]
      exact Submodule.mem_iSup_of_mem ![μ, ν, μ', ν'] (h.adjVec_mul_adjVec_mem_gluonPair_span
        ![μ, ν, μ', ν'] (Sum.inl r) (Sum.inr (Sum.inl r)))
  exact sup_le (key 0) (sup_le (key 1) (key 2))

/-- The isospin root part of the zero-weight piece, the product of the isospin raising
  vector against the lowering vector, lies in the `W`-boson pair spans. -/
lemma isospinRootPart_le_wPairSpan : h.isospinRootPart ≤ h.wPairSpan :=
  iSup_span_mul_iSup_span_le _ _ fun l μ ν l' μ' ν' => by
    rw [Subsingleton.elim l ![], Subsingleton.elim l' ![]]
    exact Submodule.mem_iSup_of_mem ![μ, ν, μ', ν'] (h.adjVec_mul_adjVec_mem_wPair_span
      ![μ, ν, μ', ν'] (Sum.inl 0) (Sum.inr (Sum.inl 0)))

/-!

## E. The zero-weight piece of mass weight eight

`massWeightSubmoduleGaugeWeightEight_piece_zero` splits the zero-weight piece into the
twice-derived symbols on the four weight-zero directions of the adjoint, the gluon root
part, the isospin root part and the neutral part, the products of two weight-zero
directions. Section D puts the two root parts inside the pair spans. The neutral part
splits by gauge group factor: a colour Cartan direction against a colour Cartan direction
is a component of a gluon pair family, the isospin Cartan direction against itself of a
`W`-boson pair family, and hypercharge against itself is a hypercharge trace contraction.
What is left pairs a weight-zero direction of one factor with one of another and carries
an unpaired adjoint index of a non-abelian factor; so does a twice-derived symbol on a
colour or isospin Cartan direction, while the twice-derived hypercharge field strengths
are fixed by the whole gauge group.

The families with an unpaired index are collected in `colourFamily` and `isospinFamily`,
adjoint families in the sense of `IsSU3Adjoint` and `IsSU2Adjoint`: the colour factor moves
the gluon index of a mixed product and fixes the neutral factor. The piece is then bounded
by the joins of these families together with the four spans of gauge invariants.

-/

/-- The span of the hypercharge trace contractions. -/
noncomputable def hyperchargeTraceSpan : Submodule ℂ B := ⨆ p, ℂ ∙ h.hyperchargeTrace p

/-- The span of the twice-derived hypercharge field strengths. -/
noncomputable def hyperchargeDerivSpan : Submodule ℂ B := ⨆ d, ℂ ∙ h.hyperchargeDeriv d

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
  | Sum.inl p => h.gluonField p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inl q) =>
      fun a => h.gluonField ![] q.1 q.2.1 a * h.neutralVec q.2.2.1 q.2.2.2.1 q.2.2.2.2
  | Sum.inr (Sum.inr q) =>
      fun a => h.neutralVec q.2.2.1 q.2.2.2.1 q.2.2.2.2 * h.gluonField ![] q.1 q.2.1 a

/-- Each colour family is an `su(3)` adjoint family: the colour factor moves the gluon
  index and fixes the neutral factor. -/
lemma isSU3Adjoint_colourFamily : ∀ i : ColourIdx, IsSU3Adjoint B repGauge (h.colourFamily i)
  | Sum.inl p => h.isSU3Adjoint_gluonField p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inl q) => IsSU3Adjoint.of_law fun U => map_mul_fixed_eq_sum (hrepGauge_mul _)
      (h.repGauge_gluonField (U, 1, 1) ![] q.1 q.2.1) (h.repGauge_su3_neutralVec U _ _ _)
  | Sum.inr (Sum.inr q) => IsSU3Adjoint.of_law fun U => map_fixed_mul_eq_sum (hrepGauge_mul _)
      (h.repGauge_gluonField (U, 1, 1) ![] q.1 q.2.1) (h.repGauge_su3_neutralVec U _ _ _)

/-- The index of a family carrying one unpaired `su(2)` adjoint index at mass weight
  eight: a twice-derived `W`-boson tower, or an underived `W`-boson field strength against
  an underived hypercharge field strength on either side. -/
abbrev IsospinIdx : Type := DerivIdx ⊕ (EightIdx ⊕ EightIdx)

/-- The families carrying one unpaired `su(2)` adjoint index. -/
noncomputable def isospinFamily : IsospinIdx → Fin 3 → B
  | Sum.inl p => h.wField p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inl q) => fun i => h.wField ![] (q 0) (q 1) i * h.hyperchargeField ![] (q 2) (q 3)
  | Sum.inr (Sum.inr q) => fun i => h.hyperchargeField ![] (q 2) (q 3) * h.wField ![] (q 0) (q 1) i

/-- Each isospin family is an `su(2)` adjoint family: the isospin factor moves the
  `W`-boson index and fixes hypercharge. -/
lemma isSU2Adjoint_isospinFamily : ∀ i : IsospinIdx, IsSU2Adjoint B repGauge (h.isospinFamily i)
  | Sum.inl p => h.isSU2Adjoint_wField p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inl q) => IsSU2Adjoint.of_law fun U => map_mul_fixed_eq_sum (hrepGauge_mul _)
      (h.repGauge_wField (1, U, 1) ![] (q 0) (q 1)) (h.repGauge_hyperchargeField _ _ _ _)
  | Sum.inr (Sum.inr q) => IsSU2Adjoint.of_law fun U => map_fixed_mul_eq_sum (hrepGauge_mul _)
      (h.repGauge_wField (1, U, 1) ![] (q 0) (q 1)) (h.repGauge_hyperchargeField _ _ _ _)

/-- The isospin families are fixed by the colour factor, every one of their factors
  being. -/
lemma repGauge_su3_isospinFamily (U : specialUnitaryGroup (Fin 3) ℂ) :
    ∀ (i : IsospinIdx) (a : Fin 3),
      repGauge (U, 1, 1) (h.isospinFamily i a) = h.isospinFamily i a
  | Sum.inl p, a => h.repGauge_su3_wField U p.1 p.2.1 p.2.2 a
  | Sum.inr (Sum.inl q), a => by
      simp only [isospinFamily, hrepGauge_mul, h.repGauge_su3_wField, h.repGauge_hyperchargeField]
  | Sum.inr (Sum.inr q), a => by
      simp only [isospinFamily, hrepGauge_mul, h.repGauge_su3_wField, h.repGauge_hyperchargeField]

/-- The join of the spans of the colour families. -/
noncomputable def unpairedColourSpan : Submodule ℂ B :=
  ⨆ i : ColourIdx, Submodule.span ℂ (Set.range (h.colourFamily i))

/-- The join of the spans of the isospin families. -/
noncomputable def unpairedIsospinSpan : Submodule ℂ B :=
  ⨆ i : IsospinIdx, Submodule.span ℂ (Set.range (h.isospinFamily i))

/-- A component of a colour family lies in the join of the colour spans. -/
lemma colourFamily_mem (i : ColourIdx) (a : Fin 8) : h.colourFamily i a ∈ h.unpairedColourSpan :=
  Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨a, rfl⟩)

/-- A component of an isospin family lies in the join of the isospin spans. -/
lemma isospinFamily_mem (i : IsospinIdx) (a : Fin 3) :
    h.isospinFamily i a ∈ h.unpairedIsospinSpan :=
  Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨a, rfl⟩)

/-- The join of the isospin families is fixed pointwise by the colour factor. -/
lemma repGauge_su3_of_mem_unpairedIsospinSpan (U : specialUnitaryGroup (Fin 3) ℂ) :
    ∀ y ∈ h.unpairedIsospinSpan, repGauge (U, 1, 1) y = y :=
  isFixedBy_iSup (σ := fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge (U, 1, 1))
    (fun i => isFixedBy_span_range fun a U => h.repGauge_su3_isospinFamily U i a) U

/-- The colour Cartan directions of the underived tower: the two weight-zero directions of
  the `su(3)` factor. -/
noncomputable def colourCartanSpan : Submodule ℂ B :=
  ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (c : Fin 2),
    ℂ ∙ h.adjVec ![] μ ν (Sum.inr (Sum.inr c.castSucc.castSucc))

/-- The neutral directions of the underived tower: the isospin Cartan direction and
  hypercharge. -/
noncomputable def neutralSpan : Submodule ℂ B :=
  ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (j : Fin 2), ℂ ∙ h.neutralVec μ ν j

/-- A colour Cartan weight vector is the gluon field strength on the matching Cartan
  direction of `su(3)`. -/
lemma adjVec_colourCartan {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (c : Fin 2) :
    h.adjVec l μ ν (Sum.inr (Sum.inr c.castSucc.castSucc))
      = h.gluonField l μ ν (GaugeAlgebra.su3CartanId c) := by
  simp only [adjVec, GaugeAlgebra.cartanIdx_castSucc]
  rfl

/-- The weight-zero directions of the adjoint are the colour Cartan directions and the
  neutral directions. -/
lemma cartanSpan_le : h.cartanSpan ≤ h.colourCartanSpan ⊔ h.neutralSpan := by
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun c => ?_
  rw [Subsingleton.elim l ![], Submodule.span_singleton_le_iff_mem]
  fin_cases c
  · exact Submodule.mem_sup_left (mem_iSup_span₃ _ μ ν (0 : Fin 2))
  · exact Submodule.mem_sup_left (mem_iSup_span₃ _ μ ν (1 : Fin 2))
  · exact Submodule.mem_sup_right (mem_iSup_span₃ _ μ ν (0 : Fin 2))
  · exact Submodule.mem_sup_right (mem_iSup_span₃ _ μ ν (1 : Fin 2))

/-- A product of two colour Cartan directions is a component of a gluon pair family. -/
lemma colourCartanSpan_mul_colourCartanSpan_le :
    h.colourCartanSpan * h.colourCartanSpan ≤ h.gluonPairSpan :=
  iSup_span_mul_iSup_span_le _ _ fun μ ν c μ' ν' c' =>
    Submodule.mem_iSup_of_mem ![μ, ν, μ', ν'] (h.adjVec_mul_adjVec_mem_gluonPair_span
      ![μ, ν, μ', ν'] (Sum.inr (Sum.inr c)) (Sum.inr (Sum.inr c')))

/-- A colour Cartan direction against a neutral direction is a component of a colour
  family. -/
lemma colourCartanSpan_mul_neutralSpan_le :
    h.colourCartanSpan * h.neutralSpan ≤ h.unpairedColourSpan :=
  iSup_span_mul_iSup_span_le _ _ fun μ ν c μ' ν' j => by
    rw [h.adjVec_colourCartan]
    exact h.colourFamily_mem (Sum.inr (Sum.inl (μ, ν, μ', ν', j))) (GaugeAlgebra.su3CartanId c)

/-- A neutral direction against a colour Cartan direction is a component of a colour
  family. -/
lemma neutralSpan_mul_colourCartanSpan_le :
    h.neutralSpan * h.colourCartanSpan ≤ h.unpairedColourSpan :=
  iSup_span_mul_iSup_span_le _ _ fun μ ν j μ' ν' c => by
    rw [h.adjVec_colourCartan]
    exact h.colourFamily_mem (Sum.inr (Sum.inr (μ', ν', μ, ν, j))) (GaugeAlgebra.su3CartanId c)

/-- A product of two neutral directions: isospin against isospin is a component of a
  `W`-boson pair family, hypercharge against hypercharge is a hypercharge trace
  contraction, and the two mixed products are components of isospin families. -/
lemma neutralSpan_mul_neutralSpan_le :
    h.neutralSpan * h.neutralSpan
      ≤ h.unpairedIsospinSpan ⊔ (h.wPairSpan ⊔ h.hyperchargeTraceSpan) :=
  iSup_span_mul_iSup_span_le _ _ fun μ ν j μ' ν' j' => by
    fin_cases j <;> fin_cases j'
    · exact Submodule.mem_sup_right (Submodule.mem_sup_left (Submodule.mem_iSup_of_mem
        ![μ, ν, μ', ν'] (h.adjVec_mul_adjVec_mem_wPair_span ![μ, ν, μ', ν']
          (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0)))))
    · exact Submodule.mem_sup_left
        (h.isospinFamily_mem (Sum.inr (Sum.inl ![μ, ν, μ', ν'])) GaugeAlgebra.su2CartanId)
    · exact Submodule.mem_sup_left
        (h.isospinFamily_mem (Sum.inr (Sum.inr ![μ', ν', μ, ν])) GaugeAlgebra.su2CartanId)
    · exact Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem
        ![μ, ν, μ', ν'] (Submodule.mem_span_singleton.2
          ⟨1, by rw [one_smul, hyperchargeTrace_eq]; rfl⟩)))

/-- The neutral part of the zero-weight piece: the products pairing a factor with itself
  are components of the pair families or hypercharge trace contractions, and the mixed
  products carry an unpaired non-abelian index. -/
lemma neutralCartanPart_le :
    h.neutralCartanPart ≤ (h.unpairedColourSpan ⊔ h.unpairedIsospinSpan)
      ⊔ (h.gluonPairSpan ⊔ (h.wPairSpan ⊔ h.hyperchargeTraceSpan)) := by
  refine (Submodule.mul_le.2 fun x hx y hy => Submodule.mul_mem_mul (h.cartanSpan_le hx)
    (h.cartanSpan_le hy)).trans ?_
  rw [Submodule.mul_sup, Submodule.sup_mul, Submodule.sup_mul]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · exact h.colourCartanSpan_mul_colourCartanSpan_le.trans (le_sup_of_le_right le_sup_left)
  · exact h.neutralSpan_mul_colourCartanSpan_le.trans (le_sup_of_le_left le_sup_left)
  · exact h.colourCartanSpan_mul_neutralSpan_le.trans (le_sup_of_le_left le_sup_left)
  · exact h.neutralSpan_mul_neutralSpan_le.trans
      (sup_le (le_sup_of_le_left le_sup_right) (le_sup_of_le_right le_sup_right))

/-- The twice-derived symbols on the weight-zero directions: on a colour or isospin Cartan
  direction a component of an adjoint family, on hypercharge a twice-derived hypercharge
  field strength. -/
lemma derivCartanSpan_le :
    (⨆ (l : Fin 2 → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (c : Fin 4),
        ℂ ∙ F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.cartanIdx c)))
      ≤ (h.unpairedColourSpan ⊔ h.unpairedIsospinSpan) ⊔ h.hyperchargeDerivSpan := by
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun c =>
    (Submodule.span_singleton_le_iff_mem _ _).2 ?_
  fin_cases c
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (h.colourFamily_mem (Sum.inl (l, μ, ν)) (GaugeAlgebra.su3CartanId 0)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (h.colourFamily_mem (Sum.inl (l, μ, ν)) (GaugeAlgebra.su3CartanId 1)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (h.isospinFamily_mem (Sum.inl (l, μ, ν)) GaugeAlgebra.su2CartanId))
  · rw [← show ![l 0, l 1] = l from FinVec.etaExpand_eq l]
    exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ![l 0, l 1, μ, ν]
      (Submodule.mem_span_singleton_self _))

/-- The zero-weight piece of mass weight eight is bounded by the joins of the unpaired
  families together with the pair spans, the hypercharge trace contractions and the
  twice-derived hypercharge field strengths. -/
lemma massWeightSubmoduleGaugeWeightEight_piece_zero_le :
    (h.massWeightSubmoduleGaugeWeightEight).piece 0
      ≤ (h.unpairedColourSpan ⊔ h.unpairedIsospinSpan)
        ⊔ (h.gluonPairSpan
          ⊔ (h.wPairSpan ⊔ (h.hyperchargeTraceSpan ⊔ h.hyperchargeDerivSpan))) := by
  rw [h.massWeightSubmoduleGaugeWeightEight_piece_zero]
  refine sup_le (h.derivCartanSpan_le.trans (sup_le le_sup_left (le_sup_of_le_right
    (le_sup_of_le_right (le_sup_of_le_right le_sup_right))))) (sup_le ?_ (sup_le ?_ ?_))
  · exact h.gluonRootPart_le_gluonPairSpan.trans (le_sup_of_le_right le_sup_left)
  · exact h.isospinRootPart_le_wPairSpan.trans
      (le_sup_of_le_right (le_sup_of_le_right le_sup_left))
  · exact h.neutralCartanPart_le.trans (sup_le le_sup_left (sup_le (le_sup_of_le_right le_sup_left)
      (sup_le (le_sup_of_le_right (le_sup_of_le_right le_sup_left))
        (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_left))))))

/-!

## F. The unpaired non-abelian adjoint indices

A family carrying one unpaired adjoint index of a non-abelian factor has no gauge invariant
in its span at all, the adjoint representations of `su(3)` and `su(2)` having no invariant
vector: `IsSU3Adjoint.reducesInvariantsTo_bot` and its `su(2)` twin reduce such a span to
`⊥` for that factor. The colour families are reduced first, with the isospin join carried
in the target, since the colour factor fixes every isospin family; the isospin families
are reduced after that.

-/

/-- The joins of the unpaired families reduce to `⊥` for the gauge group: the colour
  families for the colour factor, with the colour-fixed isospin join kept in the target, and
  then the isospin families for the isospin factor. -/
lemma reducesInvariantsTo_unpaired :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGauge g)
      (h.unpairedColourSpan ⊔ h.unpairedIsospinSpan) ⊥ := by
  classical
  have hfix : IsFixedBy (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge (U, 1, 1))
      h.unpairedIsospinSpan := h.repGauge_su3_of_mem_unpairedIsospinSpan
  have hcolour : ReducesInvariantsTo
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge (U, 1, 1))
      (h.unpairedColourSpan ⊔ h.unpairedIsospinSpan) h.unpairedIsospinSpan :=
    ((ReducesInvariantsTo.iSup
        (fun i => IsSU3Adjoint.reducesInvariantsTo_bot (h.isSU3Adjoint_colourFamily i))
      (fun i => IsSU3Adjoint.isStableUnder_span (h.isSU3Adjoint_colourFamily i))
      isStableUnder_bot).mono_right bot_le).sup (reducesInvariantsTo_of_le le_rfl)
      hfix.isStableUnder hfix.isStableUnder
  have hisospin : ReducesInvariantsTo
      (fun U : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, U, 1)) h.unpairedIsospinSpan ⊥ :=
    ReducesInvariantsTo.iSup
        (fun i => IsSU2Adjoint.reducesInvariantsTo_bot (h.isSU2Adjoint_isospinFamily i))
      (fun i => IsSU2Adjoint.isStableUnder_span (h.isSU2Adjoint_isospinFamily i))
      isStableUnder_bot
  exact (hcolour.comp (σ := fun g : GaugeGroupI => repGauge g) (fun U => (U, 1, 1))).trans
    (hisospin.comp (σ := fun g : GaugeGroupI => repGauge g) (fun U => (1, U, 1)))

/-!

## G. The gauge invariants of mass weight eight

A gauge invariant of mass weight eight lies, modulo any gauge-stable submodule, in the
zero-weight piece of the gauge weight decomposition
(`GaugeWeightDecomposition.reducesInvariantsTo_piece_zero`), which section E bounds by the
unpaired joins, the two non-abelian pair spans and the two hypercharge spans. Section F
reduces the unpaired joins to `⊥`. Each pair span reduces to its trace contractions by
`IsSU3BiAdjoint.reducesInvariantsTo_span_traceContraction` and its `su(2)` twin, and the two
hypercharge spans are fixed pointwise by the gauge group and reduce to themselves.
`ReducesInvariantsTo.sup` joins the parts, asking stability of every part but the first and
of the target; no independence of the parts is needed.

The section closes with the converse: the gauge span is made of gauge invariants of mass
weight eight already.

-/

/-- The span of the gluon trace contractions. -/
noncomputable def gluonTraceSpan : Submodule ℂ B := ⨆ p, ℂ ∙ h.gluonTrace p

/-- The span of the `W`-boson trace contractions. -/
noncomputable def wTraceSpan : Submodule ℂ B := ⨆ p, ℂ ∙ h.wTrace p

/-- The span of the three underived trace contractions, over all covector indices: the
  gauge invariants of mass weight eight that the bi-adjoint classification produces. -/
noncomputable def traceContractionEightSpan : Submodule ℂ B :=
  h.gluonTraceSpan ⊔ (h.wTraceSpan ⊔ h.hyperchargeTraceSpan)

/-- The gluon pair spans are stable under the gauge group. -/
lemma isStableUnder_gluonPairSpan :
    IsStableUnder (fun g : GaugeGroupI => repGauge g) h.gluonPairSpan :=
  isStableUnder_iSup fun p g =>
    span_stable_of_map_eq_sum (h.gluonPair p) _ (h.isSU3BiAdjointMat_gluonPair p g)

/-- The `W`-boson pair spans are stable under the gauge group. -/
lemma isStableUnder_wPairSpan :
    IsStableUnder (fun g : GaugeGroupI => repGauge g) h.wPairSpan :=
  isStableUnder_iSup fun p g =>
    span_stable_of_map_eq_sum (h.wPair p) _ (h.isSU2BiAdjointMat_wPair p g)

/-- The hypercharge trace contractions are fixed pointwise by the gauge group. -/
lemma repGauge_of_mem_hyperchargeTraceSpan (g : GaugeGroupI) :
    ∀ y ∈ h.hyperchargeTraceSpan, repGauge g y = y :=
  map_eq_self_of_mem_iSup_span _ _ (h.repGauge_hyperchargeTrace g)

/-- The twice-derived hypercharge field strengths are fixed pointwise by the gauge
  group. -/
lemma repGauge_of_mem_hyperchargeDerivSpan (g : GaugeGroupI) :
    ∀ y ∈ h.hyperchargeDerivSpan, repGauge g y = y :=
  map_eq_self_of_mem_iSup_span _ _ (h.repGauge_hyperchargeDeriv g)

/-- The gauge span is a space of gauge invariants of mass weight eight: each generator is
  fixed by the gauge group and has mass weight eight by section C. This is the converse of
  the classification. -/
lemma traceContractionEightSpan_sup_hyperchargeDerivSpan_le :
    h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan
      ≤ h.massWeightSubmodule 8 ⊓ repGauge.invariants :=
  sup_le (sup_le (iSup_span_singleton_le _ fun p => Submodule.mem_inf.2
      ⟨h.gluonTrace_mem_massWeightSubmodule p,
        (Representation.mem_invariants _ _).2 (h.repGauge_gluonTrace · p)⟩)
    (sup_le (iSup_span_singleton_le _ fun p => Submodule.mem_inf.2
        ⟨h.wTrace_mem_massWeightSubmodule p,
          (Representation.mem_invariants _ _).2 (h.repGauge_wTrace · p)⟩)
      (iSup_span_singleton_le _ fun p => Submodule.mem_inf.2
        ⟨h.hyperchargeTrace_mem_massWeightSubmodule p,
          (Representation.mem_invariants _ _).2 (h.repGauge_hyperchargeTrace · p)⟩)))
    (iSup_span_singleton_le _ fun d => Submodule.mem_inf.2
      ⟨h.hyperchargeDeriv_mem_massWeightSubmodule d,
        (Representation.mem_invariants _ _).2 (h.repGauge_hyperchargeDeriv · d)⟩)

/-- The gauge span is fixed pointwise by the gauge group. -/
lemma isFixedBy_traceContractionEightSpan_sup :
    IsFixedBy (fun g : GaugeGroupI => repGauge g)
      (h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan) := fun g _ hy =>
  (Representation.mem_invariants _ _).1
    (Submodule.mem_inf.1 (h.traceContractionEightSpan_sup_hyperchargeDerivSpan_le hy)).2 g

/-- The gluon pair spans reduce, for the gauge group, to the gluon trace contractions: each
  gluon pair family is bi-adjoint for the colour factor. -/
lemma reducesInvariantsTo_gluonPairSpan :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGauge g) h.gluonPairSpan h.gluonTraceSpan := by
  classical
  exact ReducesInvariantsTo.iSup
    (fun p => ((IsSU3BiAdjoint.reducesInvariantsTo_span_traceContraction
      (h.isSU3BiAdjoint_gluonPair p)).comp (σ := fun g : GaugeGroupI => repGauge g)
        (fun U => (U, 1, 1))).mono_right (le_iSup (fun p => ℂ ∙ h.gluonTrace p) p))
    (fun p g => span_stable_of_map_eq_sum (h.gluonPair p) _ (h.isSU3BiAdjointMat_gluonPair p g))
    (isFixedBy_iSup fun p => isFixedBy_span_singleton (h.repGauge_gluonTrace · p)).isStableUnder

/-- The `W`-boson pair spans reduce, for the gauge group, to the `W`-boson trace
  contractions: each `W`-boson pair family is bi-adjoint for the isospin factor. -/
lemma reducesInvariantsTo_wPairSpan :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGauge g) h.wPairSpan h.wTraceSpan := by
  classical
  exact ReducesInvariantsTo.iSup
    (fun p => ((IsSU2BiAdjoint.reducesInvariantsTo_span_traceContraction
      (h.isSU2BiAdjoint_wPair p)).comp (σ := fun g : GaugeGroupI => repGauge g)
        (fun U => (1, U, 1))).mono_right (le_iSup (fun p => ℂ ∙ h.wTrace p) p))
    (fun p g => span_stable_of_map_eq_sum (h.wPair p) _ (h.isSU2BiAdjointMat_wPair p g))
    (isFixedBy_iSup fun p => isFixedBy_span_singleton (h.repGauge_wTrace · p)).isStableUnder

/-- Mass weight eight reduces, for the gauge group, to the three underived trace
  contractions and the twice-derived hypercharge field strengths. The torus puts a gauge
  invariant in the zero-weight piece; of the parts bounding it, the unpaired joins reduce to
  `⊥`, the pair spans to their trace contractions, and the hypercharge spans are already
  fixed. -/
lemma reducesInvariantsTo_traceContractionEightSpan_sup :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGauge g) (h.massWeightSubmodule 8)
      (h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan) := by
  have hW := h.isFixedBy_traceContractionEightSpan_sup.isStableUnder
  have hH : IsFixedBy (fun g : GaugeGroupI => repGauge g)
      (h.hyperchargeTraceSpan ⊔ h.hyperchargeDerivSpan) :=
    IsFixedBy.sup (fun g => h.repGauge_of_mem_hyperchargeTraceSpan g)
      (fun g => h.repGauge_of_mem_hyperchargeDerivSpan g)
  -- the pair spans and the hypercharge spans, joined
  have hrest := (h.reducesInvariantsTo_gluonPairSpan.mono_right
      (le_sup_of_le_left le_sup_left)).sup ((h.reducesInvariantsTo_wPairSpan.mono_right
        (le_sup_of_le_left (le_sup_of_le_right le_sup_left))).sup
      (reducesInvariantsTo_of_le (sup_le (le_sup_of_le_left (le_sup_of_le_right le_sup_right))
        le_sup_right)) hH.isStableUnder hW)
    (h.isStableUnder_wPairSpan.sup hH.isStableUnder) hW
  refine (ReducesInvariantsTo.comp (σ := fun g : GaugeGroupI => repGauge g) gaugeTorusGen
    h.massWeightSubmoduleGaugeWeightEight.reducesInvariantsTo_piece_zero).trans
    (((h.reducesInvariantsTo_unpaired.mono_right bot_le).sup hrest
      (h.isStableUnder_gluonPairSpan.sup (h.isStableUnder_wPairSpan.sup hH.isStableUnder))
      hW).mono_left h.massWeightSubmoduleGaugeWeightEight_piece_zero_le)

/-!

## H. The Lorentz classification of the mass-weight eight invariants

A product of two underived field-strength symbols carries four covector indices and
nothing else, so as a family indexed by those four it is a quadruple Lorentz tensor in the
sense of `IsLorentzCovariant 4`: `repLorentz_F` at no covariant derivatives moves each covector
index by the Lorentz matrix of the `SL(2,ℂ)` element, and `hrepLorentz_mul` carries that
through the product. The three trace contractions are sums of such products over a gauge
index, and a finite sum of quadruple Lorentz tensors is one again. So is the twice-derived
hypercharge field strength, whose two derivative slots and two covector indices are four
four-vector indices as well. The four spans of section G are exactly the spans of these
four families, and `RankFour.reducesInvariantsTo_span_contractionTensor` reduces each, for the
Lorentz group, to the span of its four contractions.

What is left is spanned by the four Lorentz contractions of each family, the outer, inner
and split metric contractions and the Levi-Civita contraction: sixteen spanning vectors,
twelve quadratic in the underived field strengths and four linear in the twice-derived
hypercharge field strength. This is a spanning statement; no generator is shown to be
nonzero and none is removed as redundant. `IsGaugeSector` does assert antisymmetry of `F`
in its two covector indices (`F_antisymm`, used below mass weight eight), which is expected
to make the outer metric contraction of each `F·F` family vanish and the inner and split
ones agree up to sign; that reduction of the generators is not carried out here.

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

/-- A product of two double combinations is a combination indexed by quadruples. -/
lemma sum_mul_sum_eq_sum_pi_four (c c' : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℂ)
    (X Y : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → B) :
    (∑ a, ∑ b, c a b • X a b) * (∑ x, ∑ y, c' x y • Y x y)
      = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
        (c (d 0) (d 1) * c' (d 2) (d 3)) • (X (d 0) (d 1) * Y (d 2) (d 3)) := by
  rw [RankFour.sum_pi_four, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fintype.sum_mul_sum, smul_mul_smul_comm, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  exact Finset.sum_comm

include h in
/-- A product of two underived field-strength symbols, viewed as a family indexed by the
  four covector indices it carries, is a quadruple Lorentz tensor. -/
lemma isLorentzCovariant_F_mul (φ ψ : Module.Dual ℝ GaugeAlgebra) :
    IsLorentzCovariant 4 B repLorentz (ofComponents
      fun d : Fin 4 → Fin 1 ⊕ Fin 3 => F ![] (d 0) (d 1) φ * F ![] (d 2) (d 3) ψ) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  rw [hrepLorentz_mul, h.repLorentz_F_underived g (l 0) (l 1) φ,
    h.repLorentz_F_underived g (l 2) (l 3) ψ, sum_mul_sum_eq_sum_pi_four]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.prod_univ_four, mul_assoc]

/-- A finite sum of quadruple Lorentz tensors is a quadruple Lorentz tensor: the
  transformation law is linear in the family. -/
lemma isLorentzCovariant_sum {ι : Type} [Fintype ι] {T : ι → (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hT : ∀ i, IsLorentzCovariant 4 B repLorentz (ofComponents (T i))) :
    IsLorentzCovariant 4 B repLorentz (ofComponents fun d => ∑ i, T i d) := by
  rw [ofComponents_sum]
  exact TensorSpecies.IsEquivariant.sum _ fun i _ => hT i

include h in
/-- A family of four four-vector indices whose members are sums of products of two
  underived field-strength symbols is a quadruple Lorentz tensor. -/
lemma isLorentzCovariant_of_eq_sum {ι : Type} [Fintype ι] {T : EightIdx → B}
    (φ : ι → Module.Dual ℝ GaugeAlgebra)
    (hT : ∀ d, T d = ∑ i, F ![] (d 0) (d 1) (φ i) * F ![] (d 2) (d 3) (φ i)) :
    IsLorentzCovariant 4 B repLorentz (ofComponents T) := by
  rw [show T = fun d => ∑ i, F ![] (d 0) (d 1) (φ i) * F ![] (d 2) (d 3) (φ i) from funext hT]
  exact isLorentzCovariant_sum fun _ => h.isLorentzCovariant_F_mul _ _

/-- The gluon trace contractions, read as a family of four four-vector indices, form a
  quadruple Lorentz tensor: a sum over the colour index of products of two underived
  field-strength symbols. -/
lemma isLorentzCovariant_gluonTrace :
    IsLorentzCovariant 4 B repLorentz (ofComponents h.gluonTrace) :=
  h.isLorentzCovariant_of_eq_sum (fun a : Fin 8 => GaugeAlgebra.stdBasis.coord (Sum.inl a))
    h.gluonTrace_eq

/-- The `W`-boson trace contractions form a quadruple Lorentz tensor. -/
lemma isLorentzCovariant_wTrace : IsLorentzCovariant 4 B repLorentz (ofComponents h.wTrace) :=
  h.isLorentzCovariant_of_eq_sum
    (fun i : Fin 3 => GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inl i))) h.wTrace_eq

/-- The hypercharge trace contractions form a quadruple Lorentz tensor. -/
lemma isLorentzCovariant_hyperchargeTrace :
    IsLorentzCovariant 4 B repLorentz (ofComponents h.hyperchargeTrace) := by
  rw [show h.hyperchargeTrace = fun d =>
      F ![] (d 0) (d 1) (GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inr 0)))
        * F ![] (d 2) (d 3) (GaugeAlgebra.stdBasis.coord (Sum.inr (Sum.inr 0))) from
    funext h.hyperchargeTrace_eq]
  exact h.isLorentzCovariant_F_mul _ _

/-- The twice-derived hypercharge field strengths, read as a family of four four-vector
  indices, form a quadruple Lorentz tensor: the two derivative slots and the two covector
  indices all rotate. This is the second shape of mass weight eight. -/
lemma isLorentzCovariant_hyperchargeDeriv :
    IsLorentzCovariant 4 B repLorentz (ofComponents h.hyperchargeDeriv) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  simp only [hyperchargeDeriv, hyperchargeField]
  rw [h.repLorentz_F g 2 ![l 0, l 1] (l 2) (l 3), sum_pi_fin_two, RankFour.sum_pi_four]
  simp only [Finset.smul_sum, smul_smul, Fin.prod_univ_two, Fin.prod_univ_four, mul_assoc,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]

/-- The span of the four Lorentz contractions of a quadruple Lorentz tensor: the images of
  the three metric pairings and of the Levi-Civita symbol. -/
noncomputable def quadContractionSpan (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) : Submodule ℂ B :=
  Submodule.span ℂ (Set.range fun i => ofComponents T (RankFour.contractionTensor i))

/-- The span of the four Lorentz contractions of a quadruple Lorentz family lies in the
  span of its components: each contraction is a combination of components with constant
  coefficients. -/
lemma quadContractionSpan_le_span {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B} :
    quadContractionSpan T ≤ Submodule.span ℂ (Set.range T) :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 fun i => by
    rw [SetLike.mem_coe, ← range_ofComponents]
    exact LinearMap.mem_range_self _ _

/-- The span of the four Lorentz contractions of a quadruple Lorentz family is a space of
  Lorentz invariants, the four contractions being invariant by `RankFour`. -/
lemma quadContractionSpan_le_lorentzInvariants {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsLorentzCovariant 4 B repLorentz (ofComponents T)) :
    quadContractionSpan T ≤ repLorentz.invariants :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 fun i =>
    (Representation.mem_invariants _ _).2
      (hT.rep_map_of_invariant (RankFour.contractionTensor_invariant i))

/-- The span of the four Lorentz contractions of each of the three underived
  trace-contraction families and of the twice-derived hypercharge family: the gauge and
  Lorentz invariants of mass weight eight that the two classifications together produce. -/
noncomputable def lorentzContractionEightSpan : Submodule ℂ B :=
  quadContractionSpan h.gluonTrace
    ⊔ (quadContractionSpan h.wTrace
      ⊔ (quadContractionSpan h.hyperchargeTrace ⊔ quadContractionSpan h.hyperchargeDeriv))

/-- The Lorentz contraction span sits inside the gauge span: each of its four blocks is
  spanned by the four contractions of a quadruple Lorentz family whose components generate
  the matching block of the gauge span. -/
lemma lorentzContractionEightSpan_le_traceContractionEightSpan_sup :
    h.lorentzContractionEightSpan ≤ h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan :=
  sup_le ((quadContractionSpan_le_span (T := h.gluonTrace)).trans
      (Submodule.span_range_eq_iSup.trans_le (le_sup_of_le_left le_sup_left)))
    (sup_le ((quadContractionSpan_le_span (T := h.wTrace)).trans
        (Submodule.span_range_eq_iSup.trans_le
          (le_sup_of_le_left (le_sup_of_le_right le_sup_left))))
      (sup_le ((quadContractionSpan_le_span (T := h.hyperchargeTrace)).trans
          (Submodule.span_range_eq_iSup.trans_le
            (le_sup_of_le_left (le_sup_of_le_right le_sup_right))))
        ((quadContractionSpan_le_span (T := h.hyperchargeDeriv)).trans
          (Submodule.span_range_eq_iSup.trans_le le_sup_right))))

/-- The Lorentz contraction span is a space of gauge invariants: it lies in the gauge
  span, whose generators the gauge group fixes. -/
lemma lorentzContractionEightSpan_le_invariants :
    h.lorentzContractionEightSpan ≤ repGauge.invariants :=
  h.lorentzContractionEightSpan_le_traceContractionEightSpan_sup.trans
    (h.traceContractionEightSpan_sup_hyperchargeDerivSpan_le.trans inf_le_right)

/-!

## I. The Lorentz contraction span as invariants of mass weight eight

The converse of the Lorentz classification: the Lorentz contraction span is made of gauge
and Lorentz invariants of mass weight eight. Its gauge invariance and its mass weight pass
to it from the gauge span, which contains it; Lorentz invariance comes from `RankFour`
directly, each block being spanned by the four contractions of a quadruple Lorentz family.

-/

/-- The Lorentz contraction span lies in the mass-weight eight submodule. -/
lemma lorentzContractionEightSpan_le_massWeightSubmodule :
    h.lorentzContractionEightSpan ≤ h.massWeightSubmodule 8 :=
  h.lorentzContractionEightSpan_le_traceContractionEightSpan_sup.trans
    (h.traceContractionEightSpan_sup_hyperchargeDerivSpan_le.trans inf_le_left)

/-- The Lorentz contraction span is a space of Lorentz invariants. -/
lemma lorentzContractionEightSpan_le_lorentzInvariants :
    h.lorentzContractionEightSpan ≤ repLorentz.invariants :=
  sup_le (quadContractionSpan_le_lorentzInvariants h.isLorentzCovariant_gluonTrace)
    (sup_le (quadContractionSpan_le_lorentzInvariants h.isLorentzCovariant_wTrace)
      (sup_le (quadContractionSpan_le_lorentzInvariants h.isLorentzCovariant_hyperchargeTrace)
        (quadContractionSpan_le_lorentzInvariants h.isLorentzCovariant_hyperchargeDeriv)))

/-- The Lorentz contraction span is fixed pointwise by both groups. -/
lemma isFixedBy_lorentzContractionEightSpan :
    IsFixedBy (gaugeLorentzMaps repGauge repLorentz) h.lorentzContractionEightSpan :=
  isFixedBy_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => (Representation.mem_invariants _ _).1
      (h.lorentzContractionEightSpan_le_invariants hy) g,
      fun Λ _ hy => (Representation.mem_invariants _ _).1
        (h.lorentzContractionEightSpan_le_lorentzInvariants hy) Λ⟩

/-!

## J. The classifications as equivalences

The gauge reduction of section G and the Lorentz reduction of section H compose, and the
composite needs no stability or fixedness of the gauge span under the Lorentz group. The
converse, sections G and I, turns each reduction into an equivalence through
`ReducesInvariantsTo.mem_sup_and_forall_eq_self_iff`.

-/

/-- The gauge sector at mass weight eight reduces, for the gauge and Lorentz groups
  together, to the four Lorentz contractions of each of the four families. The gauge group
  leaves the trace contractions and the twice-derived hypercharge field strengths; each of
  the four spans is spanned by a quadruple Lorentz tensor and reduces, for the Lorentz
  group, to the span of its four contractions. -/
lemma reducesInvariantsTo_lorentzContractionEightSpan :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.massWeightSubmodule 8)
      h.lorentzContractionEightSpan := by
  have hW : IsStableUnder (fun g : SL(2,ℂ) => repLorentz g) h.lorentzContractionEightSpan :=
    fun g _ hy => by
      rw [(Representation.mem_invariants _ _).1
        (h.lorentzContractionEightSpan_le_lorentzInvariants hy) g]
      exact hy
  have hst : ∀ {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B},
      IsLorentzCovariant 4 B repLorentz (ofComponents T) →
      IsStableUnder (fun g : SL(2,ℂ) => repLorentz g) (Submodule.span ℂ (Set.range T)) :=
    fun hT => by
      rw [← range_ofComponents]
      exact hT.isStableUnder_range
  have hred : ∀ {T : (Fin 4 → Fin 1 ⊕ Fin 3) → B},
      IsLorentzCovariant 4 B repLorentz (ofComponents T) →
      quadContractionSpan T ≤ h.lorentzContractionEightSpan →
      ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (Submodule.span ℂ (Set.range T))
        h.lorentzContractionEightSpan :=
    fun hT hle => by
      rw [← range_ofComponents]
      exact (RankFour.reducesInvariantsTo_span_contractionTensor hT).mono_right hle
  -- the Lorentz stage, on the four spans the gauge stage leaves
  have hlorentz : ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g)
      (h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan) h.lorentzContractionEightSpan := by
    have hsrc : h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan
        = Submodule.span ℂ (Set.range h.gluonTrace) ⊔ (Submodule.span ℂ (Set.range h.wTrace)
          ⊔ (Submodule.span ℂ (Set.range h.hyperchargeTrace)
            ⊔ Submodule.span ℂ (Set.range h.hyperchargeDeriv))) := by
      simp only [traceContractionEightSpan, gluonTraceSpan, wTraceSpan, hyperchargeTraceSpan,
        hyperchargeDerivSpan, ← Submodule.span_range_eq_iSup, sup_assoc]
    rw [hsrc]
    exact (hred h.isLorentzCovariant_gluonTrace le_sup_left).sup
      ((hred h.isLorentzCovariant_wTrace (le_sup_of_le_right le_sup_left)).sup
        ((hred h.isLorentzCovariant_hyperchargeTrace
            (le_sup_of_le_right (le_sup_of_le_right le_sup_left))).sup
          (hred h.isLorentzCovariant_hyperchargeDeriv
            (le_sup_of_le_right (le_sup_of_le_right le_sup_right)))
          (hst h.isLorentzCovariant_hyperchargeDeriv) hW)
        ((hst h.isLorentzCovariant_hyperchargeTrace).sup
          (hst h.isLorentzCovariant_hyperchargeDeriv)) hW)
      ((hst h.isLorentzCovariant_wTrace).sup ((hst h.isLorentzCovariant_hyperchargeTrace).sup
        (hst h.isLorentzCovariant_hyperchargeDeriv))) hW
  exact (ReducesInvariantsTo.ofGauge h.reducesInvariantsTo_traceContractionEightSpan_sup).trans
    (ReducesInvariantsTo.ofLorentz hlorentz)

/-- The gauge classification of mass weight eight as an equivalence: an element of
  `massWeightSubmodule 8 ⊔ S` is gauge invariant exactly when it is a combination of the
  three underived trace contractions and the twice-derived hypercharge field strengths up
  to a gauge-invariant remainder in `S`. -/
theorem mem_massWeightSubmodule_eight_sup_and_invariant_iff (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule 8 ⊔ S ∧ ∀ g : GaugeGroupI, repGauge g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ x - y ∈ h.traceContractionEightSpan ⊔ h.hyperchargeDerivSpan :=
  h.reducesInvariantsTo_traceContractionEightSpan_sup.mem_sup_and_forall_eq_self_iff
    (h.traceContractionEightSpan_sup_hyperchargeDerivSpan_le.trans inf_le_left)
    h.isFixedBy_traceContractionEightSpan_sup hS x

/-- The gauge and Lorentz classification of mass weight eight as an equivalence: an
  element of `massWeightSubmodule 8 ⊔ S` is fixed by both groups exactly when it is a
  combination of the four Lorentz contractions of the four families of section H up to a
  remainder in `S` fixed by both groups. -/
theorem mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.lorentzContractionEightSpan :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    h.reducesInvariantsTo_lorentzContractionEightSpan
    h.lorentzContractionEightSpan_le_massWeightSubmodule h.isFixedBy_lorentzContractionEightSpan
    hS hSL x

end IsGaugeSector

end StandardModel
