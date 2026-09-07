/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.KineticFamilies
/-!
# The ten kinetic blocks

The five conjugate pairs of the fermion sector, each with the covariant derivative on one
factor or the other, give ten blocks at mass weight eight, and each is packaged here as a
`KineticBlock` of `KineticFamilies`. The package does the work; what a block has to supply
is its components, the three index laws they obey, and the cancellation of the two
hypercharges.

The blocks differ only in which indices their symbols carry. The four quark-singlet
pairings `d ∂ bard`, `bard ∂ d`, `u ∂ baru` and `baru ∂ u` run a genuine colour stage and a
trivial isospin one; the two quark-doublet pairings `Q ∂ barQ` and `barQ ∂ Q` run both; the
two lepton-doublet pairings run a trivial colour stage and a genuine isospin one; and the
two lepton-singlet pairings run neither, their two symbols carrying only hypercharge and a
spinor index between them. In every case the unbarred symbol is anti-fundamental and the
barred one fundamental, since a symbol eats a covector and so carries the contragredient of
its value space; that is what makes each conjugate pair a fundamental against an
anti-fundamental, and it is the same fact that makes the two spinor indices of a pair
opposite in chirality.

What comes out of each block is one kinetic term per pair of generations; the join of the
ten over the nine generation pairs is the kinetic span of the sector, assembled in
`MassDimEight`.

- A. The four quark-singlet pairings
- B. The two quark-doublet pairings
- C. The two lepton-doublet pairings
- D. The two lepton-singlet pairings

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups Lorentz ComplexConjugate

namespace IsFermionSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

/-!

## A. The four quark-singlet pairings

The down and up singlets carry colour and hypercharge and nothing else, so their four
pairings run a genuine colour stage and a trivial isospin one.

-/

/-- The components of the block `d ∂ bard`: an underived down-singlet symbol against a
  once-derived conjugate down-singlet symbol. -/
noncomputable def dbardBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l c c' _ _ => h.dComponent f ![] (l.2, c') * h.bardComponent f' ![q] (l.1, c)

/-- The two colour indices of the `d ∂ bard` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU3FunAntiFun_dbardBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 3 => h.dbardBlk f f' q l (n 0) (n 1) w w') :=
  isSU3FunAntiFun_mul_swap hrepGauge_mul (fun U c => h.repGauge_su3_d U f ![] l.2 c)
    (fun U c => h.repGauge_su3_bard U f' ![q] l.1 c)

/-- An isospin transformation fixes the `d ∂ bard` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_dbardBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.dbardBlk f f' q l c c' w w')
      = h.dbardBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su2_d V f ![] (l.2, c'))
    (h.repGauge_su2_bard V f' ![q] (l.1, c))

/-- A hypercharge transformation fixes the `d ∂ bard` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_dbardBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.dbardBlk f f' q l c c' w w')
      = h.dbardBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (by rw [← mul_pow, unitary_mul_star_coe, one_pow])
    (h.repGauge_u1_d t f ![] (l.2, c'))
    (h.repGauge_u1_bard t f' ![q] (l.1, c))

/-- The colour stage of the `d ∂ bard` block. -/
noncomputable def dbardColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.dbardBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofSU3FunAntiFun (h.isSU3FunAntiFun_dbardBlk f f' q l w w')

/-- The colour contraction of the `d ∂ bard` block, written out. -/
lemma dbardColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.dbardColourStep f f' q l w w').contraction
      = ∑ a : Fin 3, h.dbardBlk f f' q l a a w w' := rfl

/-- The isospin stage of the `d ∂ bard` block. -/
noncomputable def dbardIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.dbardColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofFixedFamily (h.dbardColourStep f f' q l 0 0).contraction (fun _ => rfl)
    (fun V => isFixedBy_iSup_span_singleton
      (fun n V' => h.repGauge_su2_dbardBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (IsSU3FunAntiFun.deltaContraction_mem_span _))

/-- The doubly contracted `d ∂ bard` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_dbard (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.dbardIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.dbardIsospinStep f f' p.1 p.2).contraction
        = ∑ a : Fin 3, h.dbardBlk f f' p.1 p.2 a a 0 0 := fun _ => rfl
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_sum fun a : Fin 3 => isVectorDualLeftRightWeyl_mul_swap
      hrepLorentz_mul (h.isDualRightWeyl_rightComp (.d f a))
      (h.isVectorDualLeftWeyl_leftComp (.bard f' a))

/-- The Lorentz stage of the `d ∂ bard` block. -/
noncomputable def dbardLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.dbardIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_dbard f f')

/-- The `d ∂ bard` block as a kinetic block. -/
noncomputable def dbardKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.dbardBlk f f'
  colourStep := h.dbardColourStep f f'
  colourStep_mem _ _ _ _ := IsSU3FunAntiFun.deltaContraction_mem_span _
  isospinStep := h.dbardIsospinStep f f'
  isospinStep_mem _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  lorentzStep := h.dbardLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_dbardBlk t f f' q l c c' w w'

/-- The components of the block `bard ∂ d`: an underived conjugate down-singlet symbol against a
  once-derived down-singlet symbol. -/
noncomputable def barddBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l c c' _ _ => h.bardComponent f ![] (l.1, c) * h.dComponent f' ![q] (l.2, c')

/-- The two colour indices of the `bard ∂ d` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU3FunAntiFun_barddBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 3 => h.barddBlk f f' q l (n 0) (n 1) w w') :=
  isSU3FunAntiFun_mul hrepGauge_mul (fun U c => h.repGauge_su3_bard U f ![] l.1 c)
    (fun U c => h.repGauge_su3_d U f' ![q] l.2 c)

/-- An isospin transformation fixes the `bard ∂ d` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_barddBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.barddBlk f f' q l c c' w w')
      = h.barddBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su2_bard V f ![] (l.1, c))
    (h.repGauge_su2_d V f' ![q] (l.2, c'))

/-- A hypercharge transformation fixes the `bard ∂ d` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_barddBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barddBlk f f' q l c c' w w')
      = h.barddBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (by rw [← mul_pow, unitary_star_mul_coe, one_pow])
    (h.repGauge_u1_bard t f ![] (l.1, c))
    (h.repGauge_u1_d t f' ![q] (l.2, c'))

/-- The colour stage of the `bard ∂ d` block. -/
noncomputable def barddColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.barddBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofSU3FunAntiFun (h.isSU3FunAntiFun_barddBlk f f' q l w w')

/-- The colour contraction of the `bard ∂ d` block, written out. -/
lemma barddColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.barddColourStep f f' q l w w').contraction
      = ∑ a : Fin 3, h.barddBlk f f' q l a a w w' := rfl

/-- The isospin stage of the `bard ∂ d` block. -/
noncomputable def barddIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.barddColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofFixedFamily (h.barddColourStep f f' q l 0 0).contraction (fun _ => rfl)
    (fun V => isFixedBy_iSup_span_singleton
      (fun n V' => h.repGauge_su2_barddBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (IsSU3FunAntiFun.deltaContraction_mem_span _))

/-- The doubly contracted `bard ∂ d` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_bardd (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.barddIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.barddIsospinStep f f' p.1 p.2).contraction
        = ∑ a : Fin 3, h.barddBlk f f' p.1 p.2 a a 0 0 := fun _ => rfl
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_sum fun a : Fin 3 => isVectorDualLeftRightWeyl_mul
      hrepLorentz_mul (h.isDualLeftWeyl_leftComp (.bard f a))
      (h.isVectorDualRightWeyl_rightComp (.d f' a))

/-- The Lorentz stage of the `bard ∂ d` block. -/
noncomputable def barddLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.barddIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_bardd f f')

/-- The `bard ∂ d` block as a kinetic block. -/
noncomputable def barddKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.barddBlk f f'
  colourStep := h.barddColourStep f f'
  colourStep_mem _ _ _ _ := IsSU3FunAntiFun.deltaContraction_mem_span _
  isospinStep := h.barddIsospinStep f f'
  isospinStep_mem _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  lorentzStep := h.barddLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_barddBlk t f f' q l c c' w w'

/-- The components of the block `u ∂ baru`: an underived up-singlet symbol against a
  once-derived conjugate up-singlet symbol. -/
noncomputable def ubaruBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l c c' _ _ => h.uComponent f ![] (l.2, c') * h.baruComponent f' ![q] (l.1, c)

/-- The two colour indices of the `u ∂ baru` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU3FunAntiFun_ubaruBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 3 => h.ubaruBlk f f' q l (n 0) (n 1) w w') :=
  isSU3FunAntiFun_mul_swap hrepGauge_mul (fun U c => h.repGauge_su3_u U f ![] l.2 c)
    (fun U c => h.repGauge_su3_baru U f' ![q] l.1 c)

/-- An isospin transformation fixes the `u ∂ baru` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_ubaruBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.ubaruBlk f f' q l c c' w w')
      = h.ubaruBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su2_u V f ![] (l.2, c'))
    (h.repGauge_su2_baru V f' ![q] (l.1, c))

/-- A hypercharge transformation fixes the `u ∂ baru` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_ubaruBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.ubaruBlk f f' q l c c' w w')
      = h.ubaruBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (by rw [← mul_pow, unitary_star_mul_coe, one_pow])
    (h.repGauge_u1_u t f ![] (l.2, c'))
    (h.repGauge_u1_baru t f' ![q] (l.1, c))

/-- The colour stage of the `u ∂ baru` block. -/
noncomputable def ubaruColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.ubaruBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofSU3FunAntiFun (h.isSU3FunAntiFun_ubaruBlk f f' q l w w')

/-- The colour contraction of the `u ∂ baru` block, written out. -/
lemma ubaruColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.ubaruColourStep f f' q l w w').contraction
      = ∑ a : Fin 3, h.ubaruBlk f f' q l a a w w' := rfl

/-- The isospin stage of the `u ∂ baru` block. -/
noncomputable def ubaruIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.ubaruColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofFixedFamily (h.ubaruColourStep f f' q l 0 0).contraction (fun _ => rfl)
    (fun V => isFixedBy_iSup_span_singleton
      (fun n V' => h.repGauge_su2_ubaruBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (IsSU3FunAntiFun.deltaContraction_mem_span _))

/-- The doubly contracted `u ∂ baru` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_ubaru (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.ubaruIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.ubaruIsospinStep f f' p.1 p.2).contraction
        = ∑ a : Fin 3, h.ubaruBlk f f' p.1 p.2 a a 0 0 := fun _ => rfl
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_sum fun a : Fin 3 => isVectorDualLeftRightWeyl_mul_swap
      hrepLorentz_mul (h.isDualRightWeyl_rightComp (.u f a))
      (h.isVectorDualLeftWeyl_leftComp (.baru f' a))

/-- The Lorentz stage of the `u ∂ baru` block. -/
noncomputable def ubaruLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.ubaruIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_ubaru f f')

/-- The `u ∂ baru` block as a kinetic block. -/
noncomputable def ubaruKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.ubaruBlk f f'
  colourStep := h.ubaruColourStep f f'
  colourStep_mem _ _ _ _ := IsSU3FunAntiFun.deltaContraction_mem_span _
  isospinStep := h.ubaruIsospinStep f f'
  isospinStep_mem _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  lorentzStep := h.ubaruLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_ubaruBlk t f f' q l c c' w w'

/-- The components of the block `baru ∂ u`: an underived conjugate up-singlet symbol against a
  once-derived up-singlet symbol. -/
noncomputable def baruuBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l c c' _ _ => h.baruComponent f ![] (l.1, c) * h.uComponent f' ![q] (l.2, c')

/-- The two colour indices of the `baru ∂ u` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU3FunAntiFun_baruuBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 3 => h.baruuBlk f f' q l (n 0) (n 1) w w') :=
  isSU3FunAntiFun_mul hrepGauge_mul (fun U c => h.repGauge_su3_baru U f ![] l.1 c)
    (fun U c => h.repGauge_su3_u U f' ![q] l.2 c)

/-- An isospin transformation fixes the `baru ∂ u` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_baruuBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.baruuBlk f f' q l c c' w w')
      = h.baruuBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su2_baru V f ![] (l.1, c))
    (h.repGauge_su2_u V f' ![q] (l.2, c'))

/-- A hypercharge transformation fixes the `baru ∂ u` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_baruuBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.baruuBlk f f' q l c c' w w')
      = h.baruuBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (by rw [← mul_pow, unitary_mul_star_coe, one_pow])
    (h.repGauge_u1_baru t f ![] (l.1, c))
    (h.repGauge_u1_u t f' ![q] (l.2, c'))

/-- The colour stage of the `baru ∂ u` block. -/
noncomputable def baruuColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.baruuBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofSU3FunAntiFun (h.isSU3FunAntiFun_baruuBlk f f' q l w w')

/-- The colour contraction of the `baru ∂ u` block, written out. -/
lemma baruuColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.baruuColourStep f f' q l w w').contraction
      = ∑ a : Fin 3, h.baruuBlk f f' q l a a w w' := rfl

/-- The isospin stage of the `baru ∂ u` block. -/
noncomputable def baruuIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.baruuColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofFixedFamily (h.baruuColourStep f f' q l 0 0).contraction (fun _ => rfl)
    (fun V => isFixedBy_iSup_span_singleton
      (fun n V' => h.repGauge_su2_baruuBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (IsSU3FunAntiFun.deltaContraction_mem_span _))

/-- The doubly contracted `baru ∂ u` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_baruu (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.baruuIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.baruuIsospinStep f f' p.1 p.2).contraction
        = ∑ a : Fin 3, h.baruuBlk f f' p.1 p.2 a a 0 0 := fun _ => rfl
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_sum fun a : Fin 3 => isVectorDualLeftRightWeyl_mul
      hrepLorentz_mul (h.isDualLeftWeyl_leftComp (.baru f a))
      (h.isVectorDualRightWeyl_rightComp (.u f' a))

/-- The Lorentz stage of the `baru ∂ u` block. -/
noncomputable def baruuLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.baruuIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_baruu f f')

/-- The `baru ∂ u` block as a kinetic block. -/
noncomputable def baruuKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.baruuBlk f f'
  colourStep := h.baruuColourStep f f'
  colourStep_mem _ _ _ _ := IsSU3FunAntiFun.deltaContraction_mem_span _
  isospinStep := h.baruuIsospinStep f f'
  isospinStep_mem _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  lorentzStep := h.baruuLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_baruuBlk t f f' q l c c' w w'

/-!

## B. The two quark-doublet pairings

The quark doublet carries colour, isospin and hypercharge, so its two pairings are the only
blocks that run both a colour and an isospin stage.

-/

/-- The components of the block `Q ∂ barQ`: an underived quark-doublet symbol against a
  once-derived conjugate quark-doublet symbol. -/
noncomputable def QbarQBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l c c' w w' => h.QComponent f ![] (l.1, c', w') * h.barQComponent f' ![q] (l.2, c, w)

/-- The two colour indices of the `Q ∂ barQ` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU3FunAntiFun_QbarQBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 3 => h.QbarQBlk f f' q l (n 0) (n 1) w w') :=
  isSU3FunAntiFun_mul_swap hrepGauge_mul (fun U c => h.repGauge_su3_Q U f ![] l.1 c w')
    (fun U c => h.repGauge_su3_barQ U f' ![q] l.2 c w)

/-- The two isospin indices of the `Q ∂ barQ` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU2FunAntiFun_QbarQBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (c c' : Fin 3) :
    IsSU2FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 2 => h.QbarQBlk f f' q l c c' (n 0) (n 1)) :=
  isSU2FunAntiFun_mul_swap hrepGauge_mul (fun V w => h.repGauge_su2_Q V f ![] l.1 c' w)
    (fun V w => h.repGauge_su2_barQ V f' ![q] l.2 c w)

/-- A hypercharge transformation fixes the `Q ∂ barQ` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_QbarQBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.QbarQBlk f f' q l c c' w w')
      = h.QbarQBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (unitary_star_mul_coe t)
    (h.repGauge_u1_Q t f ![] l.1 c' w')
    (h.repGauge_u1_barQ t f' ![q] l.2 c w)

/-- The colour stage of the `Q ∂ barQ` block. -/
noncomputable def QbarQColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.QbarQBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofSU3FunAntiFun (h.isSU3FunAntiFun_QbarQBlk f f' q l w w')

/-- The colour contraction of the `Q ∂ barQ` block, written out. -/
lemma QbarQColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.QbarQColourStep f f' q l w w').contraction
      = ∑ a : Fin 3, h.QbarQBlk f f' q l a a w w' := rfl

/-- The isospin stage of the `Q ∂ barQ` block. -/
noncomputable def QbarQIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.QbarQColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofSU2FunAntiFun (by
    simp only [QbarQColourStep_contraction]
    exact IsSU2FunAntiFun.sum fun a : Fin 3 => h.isSU2FunAntiFun_QbarQBlk f f' q l a a)

/-- The doubly contracted `Q ∂ barQ` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_QbarQ (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.QbarQIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.QbarQIsospinStep f f' p.1 p.2).contraction
        = ∑ i : Fin 2 × Fin 3, h.QbarQBlk f f' p.1 p.2 i.2 i.2 i.1 i.1 := by
    intro p
    show (∑ a : Fin 3, h.QbarQBlk f f' p.1 p.2 a a 0 0)
        + ∑ a : Fin 3, h.QbarQBlk f f' p.1 p.2 a a 1 1 = _
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_sum fun i : Fin 2 × Fin 3 => isVectorDualLeftRightWeyl_mul
      hrepLorentz_mul (h.isDualLeftWeyl_leftComp (.Q f i.2 i.1))
      (h.isVectorDualRightWeyl_rightComp (.barQ f' i.2 i.1))

/-- The Lorentz stage of the `Q ∂ barQ` block. -/
noncomputable def QbarQLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.QbarQIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_QbarQ f f')

/-- The `Q ∂ barQ` block as a kinetic block. -/
noncomputable def QbarQKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.QbarQBlk f f'
  colourStep := h.QbarQColourStep f f'
  colourStep_mem _ _ _ _ := IsSU3FunAntiFun.deltaContraction_mem_span _
  isospinStep := h.QbarQIsospinStep f f'
  isospinStep_mem _ _ := IsSU2FunAntiFun.deltaContraction_mem_span _
  lorentzStep := h.QbarQLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_QbarQBlk t f f' q l c c' w w'

/-- The components of the block `barQ ∂ Q`: an underived conjugate quark-doublet symbol against a
  once-derived quark-doublet symbol. -/
noncomputable def barQQBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l c c' w w' => h.barQComponent f ![] (l.2, c, w) * h.QComponent f' ![q] (l.1, c', w')

/-- The two colour indices of the `barQ ∂ Q` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU3FunAntiFun_barQQBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 3 => h.barQQBlk f f' q l (n 0) (n 1) w w') :=
  isSU3FunAntiFun_mul hrepGauge_mul (fun U c => h.repGauge_su3_barQ U f ![] l.2 c w)
    (fun U c => h.repGauge_su3_Q U f' ![q] l.1 c w')

/-- The two isospin indices of the `barQ ∂ Q` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU2FunAntiFun_barQQBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (c c' : Fin 3) :
    IsSU2FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 2 => h.barQQBlk f f' q l c c' (n 0) (n 1)) :=
  isSU2FunAntiFun_mul hrepGauge_mul (fun V w => h.repGauge_su2_barQ V f ![] l.2 c w)
    (fun V w => h.repGauge_su2_Q V f' ![q] l.1 c' w)

/-- A hypercharge transformation fixes the `barQ ∂ Q` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_barQQBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barQQBlk f f' q l c c' w w')
      = h.barQQBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (unitary_mul_star_coe t)
    (h.repGauge_u1_barQ t f ![] l.2 c w)
    (h.repGauge_u1_Q t f' ![q] l.1 c' w')

/-- The colour stage of the `barQ ∂ Q` block. -/
noncomputable def barQQColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.barQQBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofSU3FunAntiFun (h.isSU3FunAntiFun_barQQBlk f f' q l w w')

/-- The colour contraction of the `barQ ∂ Q` block, written out. -/
lemma barQQColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.barQQColourStep f f' q l w w').contraction
      = ∑ a : Fin 3, h.barQQBlk f f' q l a a w w' := rfl

/-- The isospin stage of the `barQ ∂ Q` block. -/
noncomputable def barQQIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.barQQColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofSU2FunAntiFun (by
    simp only [barQQColourStep_contraction]
    exact IsSU2FunAntiFun.sum fun a : Fin 3 => h.isSU2FunAntiFun_barQQBlk f f' q l a a)

/-- The doubly contracted `barQ ∂ Q` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_barQQ (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.barQQIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.barQQIsospinStep f f' p.1 p.2).contraction
        = ∑ i : Fin 2 × Fin 3, h.barQQBlk f f' p.1 p.2 i.2 i.2 i.1 i.1 := by
    intro p
    show (∑ a : Fin 3, h.barQQBlk f f' p.1 p.2 a a 0 0)
        + ∑ a : Fin 3, h.barQQBlk f f' p.1 p.2 a a 1 1 = _
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_sum fun i : Fin 2 × Fin 3 => isVectorDualLeftRightWeyl_mul_swap
      hrepLorentz_mul (h.isDualRightWeyl_rightComp (.barQ f i.2 i.1))
      (h.isVectorDualLeftWeyl_leftComp (.Q f' i.2 i.1))

/-- The Lorentz stage of the `barQ ∂ Q` block. -/
noncomputable def barQQLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.barQQIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_barQQ f f')

/-- The `barQ ∂ Q` block as a kinetic block. -/
noncomputable def barQQKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.barQQBlk f f'
  colourStep := h.barQQColourStep f f'
  colourStep_mem _ _ _ _ := IsSU3FunAntiFun.deltaContraction_mem_span _
  isospinStep := h.barQQIsospinStep f f'
  isospinStep_mem _ _ := IsSU2FunAntiFun.deltaContraction_mem_span _
  lorentzStep := h.barQQLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_barQQBlk t f f' q l c c' w w'

/-!

## C. The two lepton-doublet pairings

The lepton doublet carries isospin and hypercharge but no colour, so its colour stage is
the trivial one.

-/

/-- The components of the block `L ∂ barL`: an underived lepton-doublet symbol against a
  once-derived conjugate lepton-doublet symbol. -/
noncomputable def LbarLBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l _ _ w w' => h.LComponent f ![] (l.1, w') * h.barLComponent f' ![q] (l.2, w)

/-- A colour transformation fixes the `L ∂ barL` block, neither symbol carrying
  colour. -/
lemma repGauge_su3_LbarLBlk (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.LbarLBlk f f' q l c c' w w')
      = h.LbarLBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su3_L U f ![] (l.1, w'))
    (h.repGauge_su3_barL U f' ![q] (l.2, w))

/-- The two isospin indices of the `L ∂ barL` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU2FunAntiFun_LbarLBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (c c' : Fin 3) :
    IsSU2FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 2 => h.LbarLBlk f f' q l c c' (n 0) (n 1)) :=
  isSU2FunAntiFun_mul_swap hrepGauge_mul (fun V w => h.repGauge_su2_L V f ![] l.1 w)
    (fun V w => h.repGauge_su2_barL V f' ![q] l.2 w)

/-- A hypercharge transformation fixes the `L ∂ barL` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_LbarLBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.LbarLBlk f f' q l c c' w w')
      = h.LbarLBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (by rw [← mul_pow, unitary_mul_star_coe, one_pow])
    (h.repGauge_u1_L t f ![] (l.1, w'))
    (h.repGauge_u1_barL t f' ![q] l.2 w)

/-- The colour stage of the `L ∂ barL` block. -/
noncomputable def LbarLColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.LbarLBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofFixedFamily (h.LbarLBlk f f' q l 0 0 w w') (fun _ => rfl)
    (fun U => h.repGauge_su3_LbarLBlk U f f' q l 0 0 w w')

/-- The colour contraction of the `L ∂ barL` block, written out. -/
lemma LbarLColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.LbarLColourStep f f' q l w w').contraction
      = h.LbarLBlk f f' q l 0 0 w w' := rfl

/-- The isospin stage of the `L ∂ barL` block. -/
noncomputable def LbarLIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.LbarLColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofSU2FunAntiFun (by
    simp only [LbarLColourStep_contraction]
    exact h.isSU2FunAntiFun_LbarLBlk f f' q l 0 0)

/-- The doubly contracted `L ∂ barL` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_LbarL (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.LbarLIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.LbarLIsospinStep f f' p.1 p.2).contraction
        = ∑ i : Fin 2, h.LbarLBlk f f' p.1 p.2 0 0 i i := by
    intro p
    show h.LbarLBlk f f' p.1 p.2 0 0 0 0 + h.LbarLBlk f f' p.1 p.2 0 0 1 1 = _
    rw [Fin.sum_univ_two]
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_sum fun i : Fin 2 => isVectorDualLeftRightWeyl_mul
      hrepLorentz_mul (h.isDualLeftWeyl_leftComp (.L f i))
      (h.isVectorDualRightWeyl_rightComp (.barL f' i))

/-- The Lorentz stage of the `L ∂ barL` block. -/
noncomputable def LbarLLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.LbarLIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_LbarL f f')

/-- The `L ∂ barL` block as a kinetic block. -/
noncomputable def LbarLKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.LbarLBlk f f'
  colourStep := h.LbarLColourStep f f'
  colourStep_mem _ _ _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  isospinStep := h.LbarLIsospinStep f f'
  isospinStep_mem _ _ := IsSU2FunAntiFun.deltaContraction_mem_span _
  lorentzStep := h.LbarLLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_LbarLBlk t f f' q l c c' w w'

/-- The components of the block `barL ∂ L`: an underived conjugate lepton-doublet symbol against a
  once-derived lepton-doublet symbol. -/
noncomputable def barLLBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l _ _ w w' => h.barLComponent f ![] (l.2, w) * h.LComponent f' ![q] (l.1, w')

/-- A colour transformation fixes the `barL ∂ L` block, neither symbol carrying
  colour. -/
lemma repGauge_su3_barLLBlk (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.barLLBlk f f' q l c c' w w')
      = h.barLLBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su3_barL U f ![] (l.2, w))
    (h.repGauge_su3_L U f' ![q] (l.1, w'))

/-- The two isospin indices of the `barL ∂ L` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isSU2FunAntiFun_barLLBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (c c' : Fin 3) :
    IsSU2FunAntiFun B repGauge
      (fun n : Fin 2 → Fin 2 => h.barLLBlk f f' q l c c' (n 0) (n 1)) :=
  isSU2FunAntiFun_mul hrepGauge_mul (fun V w => h.repGauge_su2_barL V f ![] l.2 w)
    (fun V w => h.repGauge_su2_L V f' ![q] l.1 w)

/-- A hypercharge transformation fixes the `barL ∂ L` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_barLLBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barLLBlk f f' q l c c' w w')
      = h.barLLBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (by rw [← mul_pow, unitary_star_mul_coe, one_pow])
    (h.repGauge_u1_barL t f ![] l.2 w)
    (h.repGauge_u1_L t f' ![q] (l.1, w'))

/-- The colour stage of the `barL ∂ L` block. -/
noncomputable def barLLColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.barLLBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofFixedFamily (h.barLLBlk f f' q l 0 0 w w') (fun _ => rfl)
    (fun U => h.repGauge_su3_barLLBlk U f f' q l 0 0 w w')

/-- The colour contraction of the `barL ∂ L` block, written out. -/
lemma barLLColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.barLLColourStep f f' q l w w').contraction
      = h.barLLBlk f f' q l 0 0 w w' := rfl

/-- The isospin stage of the `barL ∂ L` block. -/
noncomputable def barLLIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.barLLColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofSU2FunAntiFun (by
    simp only [barLLColourStep_contraction]
    exact h.isSU2FunAntiFun_barLLBlk f f' q l 0 0)

/-- The doubly contracted `barL ∂ L` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_barLL (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.barLLIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.barLLIsospinStep f f' p.1 p.2).contraction
        = ∑ i : Fin 2, h.barLLBlk f f' p.1 p.2 0 0 i i := by
    intro p
    show h.barLLBlk f f' p.1 p.2 0 0 0 0 + h.barLLBlk f f' p.1 p.2 0 0 1 1 = _
    rw [Fin.sum_univ_two]
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_sum fun i : Fin 2 => isVectorDualLeftRightWeyl_mul_swap
      hrepLorentz_mul (h.isDualRightWeyl_rightComp (.barL f i))
      (h.isVectorDualLeftWeyl_leftComp (.L f' i))

/-- The Lorentz stage of the `barL ∂ L` block. -/
noncomputable def barLLLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.barLLIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_barLL f f')

/-- The `barL ∂ L` block as a kinetic block. -/
noncomputable def barLLKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.barLLBlk f f'
  colourStep := h.barLLColourStep f f'
  colourStep_mem _ _ _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  isospinStep := h.barLLIsospinStep f f'
  isospinStep_mem _ _ := IsSU2FunAntiFun.deltaContraction_mem_span _
  lorentzStep := h.barLLLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_barLLBlk t f f' q l c c' w w'

/-!

## D. The two lepton-singlet pairings

The lepton singlet carries only hypercharge and a spinor index, so both gauge stages are
trivial and the whole classification is the Lorentz one.

-/

/-- The components of the block `e ∂ bare`: an underived lepton-singlet symbol against a
  once-derived conjugate lepton-singlet symbol. -/
noncomputable def ebareBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l _ _ _ _ => h.eComponent f ![] l.2 * h.bareComponent f' ![q] l.1

/-- A colour transformation fixes the `e ∂ bare` block, neither symbol carrying
  colour. -/
lemma repGauge_su3_ebareBlk (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.ebareBlk f f' q l c c' w w')
      = h.ebareBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su3_e U f ![] l.2)
    (h.repGauge_su3_bare U f' ![q] l.1)

/-- An isospin transformation fixes the `e ∂ bare` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_ebareBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.ebareBlk f f' q l c c' w w')
      = h.ebareBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su2_e V f ![] l.2)
    (h.repGauge_su2_bare V f' ![q] l.1)

/-- A hypercharge transformation fixes the `e ∂ bare` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_ebareBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.ebareBlk f f' q l c c' w w')
      = h.ebareBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (by rw [← mul_pow, unitary_mul_star_coe, one_pow])
    (h.repGauge_u1_e t f ![] l.2)
    (h.repGauge_u1_bare t f' ![q] l.1)

/-- The colour stage of the `e ∂ bare` block. -/
noncomputable def ebareColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.ebareBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofFixedFamily (h.ebareBlk f f' q l 0 0 w w') (fun _ => rfl)
    (fun U => h.repGauge_su3_ebareBlk U f f' q l 0 0 w w')

/-- The colour contraction of the `e ∂ bare` block, written out. -/
lemma ebareColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.ebareColourStep f f' q l w w').contraction
      = h.ebareBlk f f' q l 0 0 w w' := rfl

/-- The isospin stage of the `e ∂ bare` block. -/
noncomputable def ebareIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.ebareColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofFixedFamily (h.ebareColourStep f f' q l 0 0).contraction (fun _ => rfl)
    (fun V => isFixedBy_iSup_span_singleton
      (fun n V' => h.repGauge_su2_ebareBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)))

/-- The doubly contracted `e ∂ bare` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_ebare (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.ebareIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.ebareIsospinStep f f' p.1 p.2).contraction
        = h.ebareBlk f f' p.1 p.2 0 0 0 0 := fun _ => rfl
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_mul_swap
      hrepLorentz_mul (h.isDualRightWeyl_rightComp (.e f))
      (h.isVectorDualLeftWeyl_leftComp (.bare f'))

/-- The Lorentz stage of the `e ∂ bare` block. -/
noncomputable def ebareLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.ebareIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_ebare f f')

/-- The `e ∂ bare` block as a kinetic block. -/
noncomputable def ebareKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.ebareBlk f f'
  colourStep := h.ebareColourStep f f'
  colourStep_mem _ _ _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  isospinStep := h.ebareIsospinStep f f'
  isospinStep_mem _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  lorentzStep := h.ebareLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_ebareBlk t f f' q l c c' w w'

/-- The components of the block `bare ∂ e`: an underived conjugate lepton-singlet symbol against a
  once-derived lepton-singlet symbol. -/
noncomputable def bareeBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 → B :=
  fun q l _ _ _ _ => h.bareComponent f ![] l.1 * h.eComponent f' ![q] l.2

/-- A colour transformation fixes the `bare ∂ e` block, neither symbol carrying
  colour. -/
lemma repGauge_su3_bareeBlk (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.bareeBlk f f' q l c c' w w')
      = h.bareeBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su3_bare U f ![] l.1)
    (h.repGauge_su3_e U f' ![q] l.2)

/-- An isospin transformation fixes the `bare ∂ e` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_bareeBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.bareeBlk f f' q l c c' w w')
      = h.bareeBlk f f' q l c c' w w' :=
  repGauge_mul_fixed hrepGauge_mul (h.repGauge_su2_bare V f ![] l.1)
    (h.repGauge_su2_e V f' ![q] l.2)

/-- A hypercharge transformation fixes the `bare ∂ e` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_bareeBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.bareeBlk f f' q l c c' w w')
      = h.bareeBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed hrepGauge_mul (by rw [← mul_pow, unitary_star_mul_coe, one_pow])
    (h.repGauge_u1_bare t f ![] l.1)
    (h.repGauge_u1_e t f' ![q] l.2)

/-- The colour stage of the `bare ∂ e` block. -/
noncomputable def bareeColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    Step (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 3, ℂ ∙ h.bareeBlk f f' q l (n 0) (n 1) w w') :=
  Step.ofFixedFamily (h.bareeBlk f f' q l 0 0 w w') (fun _ => rfl)
    (fun U => h.repGauge_su3_bareeBlk U f f' q l 0 0 w w')

/-- The colour contraction of the `bare ∂ e` block, written out. -/
lemma bareeColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (h.bareeColourStep f f' q l w w').contraction
      = h.bareeBlk f f' q l 0 0 w w' := rfl

/-- The isospin stage of the `bare ∂ e` block. -/
noncomputable def bareeIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    Step (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (⨆ n : Fin 2 → Fin 2, ℂ ∙ (h.bareeColourStep f f' q l (n 0) (n 1)).contraction) :=
  Step.ofFixedFamily (h.bareeColourStep f f' q l 0 0).contraction (fun _ => rfl)
    (fun V => isFixedBy_iSup_span_singleton
      (fun n V' => h.repGauge_su2_bareeBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)))

/-- The doubly contracted `bare ∂ e` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isVectorDualLeftRightWeyl_baree (f f' : Fin 3) :
    IsVectorDualLeftRightWeyl B repLorentz
      (fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (h.bareeIsospinStep f f' p.1 p.2).contraction) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (h.bareeIsospinStep f f' p.1 p.2).contraction
        = h.bareeBlk f f' p.1 p.2 0 0 0 0 := fun _ => rfl
  simp only [hsum]
  exact isVectorDualLeftRightWeyl_mul
      hrepLorentz_mul (h.isDualLeftWeyl_leftComp (.bare f))
      (h.isVectorDualRightWeyl_rightComp (.e f'))

/-- The Lorentz stage of the `bare ∂ e` block. -/
noncomputable def bareeLorentzStep (f f' : Fin 3) :
    Step (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (⨆ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
        ℂ ∙ (h.bareeIsospinStep f f' p.1 p.2).contraction) :=
  Step.ofVectorDualLeftRightWeyl (h.isVectorDualLeftRightWeyl_baree f f')

/-- The `bare ∂ e` block as a kinetic block. -/
noncomputable def bareeKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := h.bareeBlk f f'
  colourStep := h.bareeColourStep f f'
  colourStep_mem _ _ _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  isospinStep := h.bareeIsospinStep f f'
  isospinStep_mem _ _ := Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)
  lorentzStep := h.bareeLorentzStep f f'
  lorentzStep_mem := pauliBarContraction_mem_iSup_span _
  hyper t q l c c' w w' := h.repGauge_u1_bareeBlk t f f' q l c c' w w'

end IsFermionSector

end StandardModel
