/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.MassWeight.KineticFamilies
/-!
# The ten kinetic blocks

The ten kinetic blocks of the fermion sector, each a conjugate pair with one covariant
derivative, as instances of `KineticBlock`.

## i. Overview

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

What comes out of each block is one kinetic term per pair of generations. The join of the
ten over the nine generation pairs is the kinetic span of the sector, assembled in
`MassDimEight`.

## ii. Key results

- `dbardKineticBlock`, `barddKineticBlock`, `ubaruKineticBlock`, `baruuKineticBlock`,
  `QbarQKineticBlock`, `barQQKineticBlock`, `LbarLKineticBlock`, `barLLKineticBlock`,
  `ebareKineticBlock`, `bareeKineticBlock` : the ten kinetic blocks.
- `dbardBlk` and its nine companions : the components of each block, an underived symbol against
  a once-derived symbol of the conjugate species.

## iii. Table of contents

- A. The four quark-singlet pairings
- B. The two quark-doublet pairings
- C. The two lepton-doublet pairings
- D. The two lepton-singlet pairings

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies
open suTensor (fundAntiFundIdx)

namespace StandardModel

open Matrix MatrixGroups Lorentz ComplexConjugate

namespace FermionSector

/-!

## A. The four quark-singlet pairings

The down and up singlets carry colour and hypercharge and nothing else, so their four
pairings run a genuine colour stage and a trivial isospin one.

-/

/-- The components of the block `d ∂ bard`, an underived down-singlet symbol against a
  once-derived conjugate down-singlet symbol. -/
noncomputable def dbardBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l c c' _ _ => dComponent f ![] (l.2, c') * bardComponent f' ![q] (l.1, c)

/-- The two colour indices of the `d ∂ bard` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_colourFundAntiFund_dbardBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (w w' : Fin 2) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun n : Fin 2 → Fin 3 => dbardBlk f f' q l (n 0) (n 1) w w') ∘
          fundAntiFundIdx)) :=
  (isEquivariant_colourFundAntiFund_mul_swap
    (fun U c => repGauge_su3_d U f ![] l.2 c)
    (fun U c => repGauge_su3_bard U f' ![q] l.1 c) :)

/-- An isospin transformation fixes the `d ∂ bard` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_dbardBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (dbardBlk f f' q l c c' w w')
      = dbardBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su2_d V f ![] (l.2, c'))
    (repGauge_su2_bard V f' ![q] (l.1, c))

/-- A hypercharge transformation fixes the `d ∂ bard` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_dbardBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (dbardBlk f f' q l c c' w w')
      = dbardBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (by rw [← mul_pow, Unitary.mul_star_self_of_mem t.2, one_pow])
    (repGauge_u1_d t f ![] (l.2, c'))
    (repGauge_u1_bard t f' ![q] (l.1, c))

/-- The colour stage of the `d ∂ bard` block. -/
noncomputable def dbardColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => dbardBlk f f' q l (n 0) (n 1) w w')) :=
  ColourFundAntiFund.invariantReductionToSpan
    (isEquivariant_colourFundAntiFund_dbardBlk f f' q l w w')

/-- The isospin stage of the `d ∂ bard` block. -/
noncomputable def dbardIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (dbardColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  InvariantReductionToSpan.ofFixedFamily (dbardColourStep f f' q l 0 0).spanningVector
    (fun _ => rfl)
    (fun V => isFixedBy_span_range
      (fun n V' => repGauge_su2_dbardBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (ColourFundAntiFund.deltaContraction_mem_span _))

/-- The doubly contracted `d ∂ bard` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_dbard (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (dbardIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (dbardIsospinStep f f' p.1 p.2).spanningVector
        = ∑ a : Fin 3, dbardBlk f f' p.1 p.2 a a 0 0 := fun _ => rfl
  simp only [hsum]
  refine isEquivariant_upDownRDownL_sum fun a : Fin 3 => ?_
  convert isEquivariant_upDownRDownL_mul_swap repLorentz_mul
    (repLorentz_rightComp (.d f a)) (repLorentz_leftComp_deriv_one (.bard f' a)) using 2
  funext p
  rfl

/-- The Lorentz stage of the `d ∂ bard` block. -/
noncomputable def dbardLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (dbardIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_dbard f f')

/-- The `d ∂ bard` block as a kinetic block. -/
noncomputable def dbardKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := dbardBlk f f'
  colourStep := dbardColourStep f f'
  colourStep_mem _ _ _ _ := ColourFundAntiFund.deltaContraction_mem_span _
  isospinStep := dbardIsospinStep f f'
  isospinStep_mem _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  lorentzStep := dbardLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_dbardBlk t f f' q l c c' w w'

/-- The components of the block `bard ∂ d`, an underived conjugate down-singlet symbol against a
  once-derived down-singlet symbol. -/
noncomputable def barddBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l c c' _ _ => bardComponent f ![] (l.1, c) * dComponent f' ![q] (l.2, c')

/-- The two colour indices of the `bard ∂ d` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_colourFundAntiFund_barddBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (w w' : Fin 2) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun n : Fin 2 → Fin 3 => barddBlk f f' q l (n 0) (n 1) w w') ∘
          fundAntiFundIdx)) :=
  (isEquivariant_colourFundAntiFund_mul (fun U c => repGauge_su3_bard U f ![] l.1 c)
    (fun U c => repGauge_su3_d U f' ![q] l.2 c) :)

/-- An isospin transformation fixes the `bard ∂ d` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_barddBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (barddBlk f f' q l c c' w w')
      = barddBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su2_bard V f ![] (l.1, c))
    (repGauge_su2_d V f' ![q] (l.2, c'))

/-- A hypercharge transformation fixes the `bard ∂ d` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_barddBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (barddBlk f f' q l c c' w w')
      = barddBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (by rw [← mul_pow, Unitary.star_mul_self_of_mem t.2, one_pow])
    (repGauge_u1_bard t f ![] (l.1, c))
    (repGauge_u1_d t f' ![q] (l.2, c'))

/-- The colour stage of the `bard ∂ d` block. -/
noncomputable def barddColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => barddBlk f f' q l (n 0) (n 1) w w')) :=
  ColourFundAntiFund.invariantReductionToSpan
    (isEquivariant_colourFundAntiFund_barddBlk f f' q l w w')

/-- The isospin stage of the `bard ∂ d` block. -/
noncomputable def barddIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (barddColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  InvariantReductionToSpan.ofFixedFamily (barddColourStep f f' q l 0 0).spanningVector
    (fun _ => rfl)
    (fun V => isFixedBy_span_range
      (fun n V' => repGauge_su2_barddBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (ColourFundAntiFund.deltaContraction_mem_span _))

/-- The doubly contracted `bard ∂ d` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_bardd (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (barddIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (barddIsospinStep f f' p.1 p.2).spanningVector
        = ∑ a : Fin 3, barddBlk f f' p.1 p.2 a a 0 0 := fun _ => rfl
  simp only [hsum]
  refine isEquivariant_upDownRDownL_sum fun a : Fin 3 => ?_
  convert isEquivariant_upDownRDownL_mul repLorentz_mul
    (repLorentz_leftComp (.bard f a))
    (repLorentz_rightComp_deriv_one (.d f' a)) using 2
  funext p
  rfl

/-- The Lorentz stage of the `bard ∂ d` block. -/
noncomputable def barddLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (barddIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_bardd f f')

/-- The `bard ∂ d` block as a kinetic block. -/
noncomputable def barddKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := barddBlk f f'
  colourStep := barddColourStep f f'
  colourStep_mem _ _ _ _ := ColourFundAntiFund.deltaContraction_mem_span _
  isospinStep := barddIsospinStep f f'
  isospinStep_mem _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  lorentzStep := barddLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_barddBlk t f f' q l c c' w w'

/-- The components of the block `u ∂ baru`, an underived up-singlet symbol against a
  once-derived conjugate up-singlet symbol. -/
noncomputable def ubaruBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l c c' _ _ => uComponent f ![] (l.2, c') * baruComponent f' ![q] (l.1, c)

/-- The two colour indices of the `u ∂ baru` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_colourFundAntiFund_ubaruBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (w w' : Fin 2) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun n : Fin 2 → Fin 3 => ubaruBlk f f' q l (n 0) (n 1) w w') ∘
          fundAntiFundIdx)) :=
  (isEquivariant_colourFundAntiFund_mul_swap
    (fun U c => repGauge_su3_u U f ![] l.2 c)
    (fun U c => repGauge_su3_baru U f' ![q] l.1 c) :)

/-- An isospin transformation fixes the `u ∂ baru` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_ubaruBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (ubaruBlk f f' q l c c' w w')
      = ubaruBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su2_u V f ![] (l.2, c'))
    (repGauge_su2_baru V f' ![q] (l.1, c))

/-- A hypercharge transformation fixes the `u ∂ baru` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_ubaruBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (ubaruBlk f f' q l c c' w w')
      = ubaruBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (by rw [← mul_pow, Unitary.star_mul_self_of_mem t.2, one_pow])
    (repGauge_u1_u t f ![] (l.2, c'))
    (repGauge_u1_baru t f' ![q] (l.1, c))

/-- The colour stage of the `u ∂ baru` block. -/
noncomputable def ubaruColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => ubaruBlk f f' q l (n 0) (n 1) w w')) :=
  ColourFundAntiFund.invariantReductionToSpan
    (isEquivariant_colourFundAntiFund_ubaruBlk f f' q l w w')

/-- The isospin stage of the `u ∂ baru` block. -/
noncomputable def ubaruIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (ubaruColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  InvariantReductionToSpan.ofFixedFamily (ubaruColourStep f f' q l 0 0).spanningVector
    (fun _ => rfl)
    (fun V => isFixedBy_span_range
      (fun n V' => repGauge_su2_ubaruBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (ColourFundAntiFund.deltaContraction_mem_span _))

/-- The doubly contracted `u ∂ baru` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_ubaru (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (ubaruIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (ubaruIsospinStep f f' p.1 p.2).spanningVector
        = ∑ a : Fin 3, ubaruBlk f f' p.1 p.2 a a 0 0 := fun _ => rfl
  simp only [hsum]
  refine isEquivariant_upDownRDownL_sum fun a : Fin 3 => ?_
  convert isEquivariant_upDownRDownL_mul_swap repLorentz_mul
    (repLorentz_rightComp (.u f a))
    (repLorentz_leftComp_deriv_one (.baru f' a)) using 2
  funext p
  rfl

/-- The Lorentz stage of the `u ∂ baru` block. -/
noncomputable def ubaruLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (ubaruIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_ubaru f f')

/-- The `u ∂ baru` block as a kinetic block. -/
noncomputable def ubaruKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := ubaruBlk f f'
  colourStep := ubaruColourStep f f'
  colourStep_mem _ _ _ _ := ColourFundAntiFund.deltaContraction_mem_span _
  isospinStep := ubaruIsospinStep f f'
  isospinStep_mem _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  lorentzStep := ubaruLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_ubaruBlk t f f' q l c c' w w'

/-- The components of the block `baru ∂ u`, an underived conjugate up-singlet symbol against a
  once-derived up-singlet symbol. -/
noncomputable def baruuBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l c c' _ _ => baruComponent f ![] (l.1, c) * uComponent f' ![q] (l.2, c')

/-- The two colour indices of the `baru ∂ u` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_colourFundAntiFund_baruuBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (w w' : Fin 2) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun n : Fin 2 → Fin 3 => baruuBlk f f' q l (n 0) (n 1) w w') ∘
          fundAntiFundIdx)) :=
  (isEquivariant_colourFundAntiFund_mul (fun U c => repGauge_su3_baru U f ![] l.1 c)
    (fun U c => repGauge_su3_u U f' ![q] l.2 c) :)

/-- An isospin transformation fixes the `baru ∂ u` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_baruuBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (baruuBlk f f' q l c c' w w')
      = baruuBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su2_baru V f ![] (l.1, c))
    (repGauge_su2_u V f' ![q] (l.2, c'))

/-- A hypercharge transformation fixes the `baru ∂ u` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_baruuBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (baruuBlk f f' q l c c' w w')
      = baruuBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (by rw [← mul_pow, Unitary.mul_star_self_of_mem t.2, one_pow])
    (repGauge_u1_baru t f ![] (l.1, c))
    (repGauge_u1_u t f' ![q] (l.2, c'))

/-- The colour stage of the `baru ∂ u` block. -/
noncomputable def baruuColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => baruuBlk f f' q l (n 0) (n 1) w w')) :=
  ColourFundAntiFund.invariantReductionToSpan
    (isEquivariant_colourFundAntiFund_baruuBlk f f' q l w w')

/-- The isospin stage of the `baru ∂ u` block. -/
noncomputable def baruuIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (baruuColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  InvariantReductionToSpan.ofFixedFamily (baruuColourStep f f' q l 0 0).spanningVector
    (fun _ => rfl)
    (fun V => isFixedBy_span_range
      (fun n V' => repGauge_su2_baruuBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (ColourFundAntiFund.deltaContraction_mem_span _))

/-- The doubly contracted `baru ∂ u` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_baruu (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (baruuIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (baruuIsospinStep f f' p.1 p.2).spanningVector
        = ∑ a : Fin 3, baruuBlk f f' p.1 p.2 a a 0 0 := fun _ => rfl
  simp only [hsum]
  refine isEquivariant_upDownRDownL_sum fun a : Fin 3 => ?_
  convert isEquivariant_upDownRDownL_mul repLorentz_mul
    (repLorentz_leftComp (.baru f a))
    (repLorentz_rightComp_deriv_one (.u f' a)) using 2
  funext p
  rfl

/-- The Lorentz stage of the `baru ∂ u` block. -/
noncomputable def baruuLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (baruuIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_baruu f f')

/-- The `baru ∂ u` block as a kinetic block. -/
noncomputable def baruuKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := baruuBlk f f'
  colourStep := baruuColourStep f f'
  colourStep_mem _ _ _ _ := ColourFundAntiFund.deltaContraction_mem_span _
  isospinStep := baruuIsospinStep f f'
  isospinStep_mem _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  lorentzStep := baruuLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_baruuBlk t f f' q l c c' w w'

/-!

## B. The two quark-doublet pairings

The quark doublet carries colour, isospin and hypercharge, so its two pairings are the only
blocks that run both a colour and an isospin stage.

-/

/-- The components of the block `Q ∂ barQ`, an underived quark-doublet symbol against a
  once-derived conjugate quark-doublet symbol. -/
noncomputable def QbarQBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l c c' w w' => QComponent f ![] (l.1, c', w') * barQComponent f' ![q] (l.2, c, w)

/-- The two colour indices of the `Q ∂ barQ` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_colourFundAntiFund_QbarQBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (w w' : Fin 2) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun n : Fin 2 → Fin 3 => QbarQBlk f f' q l (n 0) (n 1) w w') ∘
          fundAntiFundIdx)) :=
  (isEquivariant_colourFundAntiFund_mul_swap
    (fun U c => repGauge_su3_Q U f ![] l.1 c w')
    (fun U c => repGauge_su3_barQ U f' ![q] l.2 c w) :)

/-- The two isospin indices of the `Q ∂ barQ` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_isospinFundAntiFund_QbarQBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' : Fin 3) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun n : Fin 2 → Fin 2 => QbarQBlk f f' q l c c' (n 0) (n 1)) ∘
          fundAntiFundIdx)) :=
  (isEquivariant_isospinFundAntiFund_mul_swap
    (fun V w => repGauge_su2_Q V f ![] l.1 c' w)
    (fun V w => repGauge_su2_barQ V f' ![q] l.2 c w) :)

/-- A hypercharge transformation fixes the `Q ∂ barQ` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_QbarQBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (QbarQBlk f f' q l c c' w w')
      = QbarQBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (Unitary.star_mul_self_of_mem t.2)
    (repGauge_u1_Q t f ![] l.1 c' w')
    (repGauge_u1_barQ t f' ![q] l.2 c w)

/-- The colour stage of the `Q ∂ barQ` block. -/
noncomputable def QbarQColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => QbarQBlk f f' q l (n 0) (n 1) w w')) :=
  ColourFundAntiFund.invariantReductionToSpan
    (isEquivariant_colourFundAntiFund_QbarQBlk f f' q l w w')

/-- The colour contraction of the `Q ∂ barQ` block, written out. -/
lemma QbarQColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (QbarQColourStep f f' q l w w').spanningVector
      = ∑ a : Fin 3, QbarQBlk f f' q l a a w w' := rfl

/-- The isospin stage of the `Q ∂ barQ` block. -/
noncomputable def QbarQIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (QbarQColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  IsospinFundAntiFund.invariantReductionToSpan (by
    simp only [QbarQColourStep_contraction]
    exact IsospinFundAntiFund.sum fun a : Fin 3 =>
      isEquivariant_isospinFundAntiFund_QbarQBlk f f' q l a a)

/-- The doubly contracted `Q ∂ barQ` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_QbarQ (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (QbarQIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (QbarQIsospinStep f f' p.1 p.2).spanningVector
        = ∑ i : Fin 2 × Fin 3, QbarQBlk f f' p.1 p.2 i.2 i.2 i.1 i.1 := by
    intro p
    show (∑ a : Fin 3, QbarQBlk f f' p.1 p.2 a a 0 0)
        + ∑ a : Fin 3, QbarQBlk f f' p.1 p.2 a a 1 1 = _
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [hsum]
  refine isEquivariant_upDownRDownL_sum fun i : Fin 2 × Fin 3 => ?_
  convert isEquivariant_upDownRDownL_mul repLorentz_mul
    (repLorentz_leftComp (.Q f i.2 i.1))
    (repLorentz_rightComp_deriv_one (.barQ f' i.2 i.1)) using 2
  funext p
  rfl

/-- The Lorentz stage of the `Q ∂ barQ` block. -/
noncomputable def QbarQLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (QbarQIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_QbarQ f f')

/-- The `Q ∂ barQ` block as a kinetic block. -/
noncomputable def QbarQKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := QbarQBlk f f'
  colourStep := QbarQColourStep f f'
  colourStep_mem _ _ _ _ := ColourFundAntiFund.deltaContraction_mem_span _
  isospinStep := QbarQIsospinStep f f'
  isospinStep_mem _ _ := IsospinFundAntiFund.deltaContraction_mem_span _
  lorentzStep := QbarQLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_QbarQBlk t f f' q l c c' w w'

/-- The components of the block `barQ ∂ Q`, an underived conjugate quark-doublet symbol against a
  once-derived quark-doublet symbol. -/
noncomputable def barQQBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l c c' w w' => barQComponent f ![] (l.2, c, w) * QComponent f' ![q] (l.1, c', w')

/-- The two colour indices of the `barQ ∂ Q` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_colourFundAntiFund_barQQBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (w w' : Fin 2) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun n : Fin 2 → Fin 3 => barQQBlk f f' q l (n 0) (n 1) w w') ∘
          fundAntiFundIdx)) :=
  (isEquivariant_colourFundAntiFund_mul
    (fun U c => repGauge_su3_barQ U f ![] l.2 c w)
    (fun U c => repGauge_su3_Q U f' ![q] l.1 c w') :)

/-- The two isospin indices of the `barQ ∂ Q` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_isospinFundAntiFund_barQQBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' : Fin 3) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun n : Fin 2 → Fin 2 => barQQBlk f f' q l c c' (n 0) (n 1)) ∘
          fundAntiFundIdx)) :=
  (isEquivariant_isospinFundAntiFund_mul
    (fun V w => repGauge_su2_barQ V f ![] l.2 c w)
    (fun V w => repGauge_su2_Q V f' ![q] l.1 c' w) :)

/-- A hypercharge transformation fixes the `barQ ∂ Q` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_barQQBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (barQQBlk f f' q l c c' w w')
      = barQQBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (Unitary.mul_star_self_of_mem t.2)
    (repGauge_u1_barQ t f ![] l.2 c w)
    (repGauge_u1_Q t f' ![q] l.1 c' w')

/-- The colour stage of the `barQ ∂ Q` block. -/
noncomputable def barQQColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => barQQBlk f f' q l (n 0) (n 1) w w')) :=
  ColourFundAntiFund.invariantReductionToSpan
    (isEquivariant_colourFundAntiFund_barQQBlk f f' q l w w')

/-- The colour contraction of the `barQ ∂ Q` block, written out. -/
lemma barQQColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (barQQColourStep f f' q l w w').spanningVector
      = ∑ a : Fin 3, barQQBlk f f' q l a a w w' := rfl

/-- The isospin stage of the `barQ ∂ Q` block. -/
noncomputable def barQQIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (barQQColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  IsospinFundAntiFund.invariantReductionToSpan (by
    simp only [barQQColourStep_contraction]
    exact IsospinFundAntiFund.sum fun a : Fin 3 =>
      isEquivariant_isospinFundAntiFund_barQQBlk f f' q l a a)

/-- The doubly contracted `barQ ∂ Q` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_barQQ (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (barQQIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (barQQIsospinStep f f' p.1 p.2).spanningVector
        = ∑ i : Fin 2 × Fin 3, barQQBlk f f' p.1 p.2 i.2 i.2 i.1 i.1 := by
    intro p
    show (∑ a : Fin 3, barQQBlk f f' p.1 p.2 a a 0 0)
        + ∑ a : Fin 3, barQQBlk f f' p.1 p.2 a a 1 1 = _
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [hsum]
  refine isEquivariant_upDownRDownL_sum fun i : Fin 2 × Fin 3 => ?_
  convert isEquivariant_upDownRDownL_mul_swap repLorentz_mul
    (repLorentz_rightComp (.barQ f i.2 i.1))
    (repLorentz_leftComp_deriv_one (.Q f' i.2 i.1)) using 2
  funext p
  rfl

/-- The Lorentz stage of the `barQ ∂ Q` block. -/
noncomputable def barQQLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (barQQIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_barQQ f f')

/-- The `barQ ∂ Q` block as a kinetic block. -/
noncomputable def barQQKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := barQQBlk f f'
  colourStep := barQQColourStep f f'
  colourStep_mem _ _ _ _ := ColourFundAntiFund.deltaContraction_mem_span _
  isospinStep := barQQIsospinStep f f'
  isospinStep_mem _ _ := IsospinFundAntiFund.deltaContraction_mem_span _
  lorentzStep := barQQLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_barQQBlk t f f' q l c c' w w'

/-!

## C. The two lepton-doublet pairings

The lepton doublet carries isospin and hypercharge but no colour, so its colour stage is
the trivial one.

-/

/-- The components of the block `L ∂ barL`, an underived lepton-doublet symbol against a
  once-derived conjugate lepton-doublet symbol. -/
noncomputable def LbarLBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l _ _ w w' => LComponent f ![] (l.1, w') * barLComponent f' ![q] (l.2, w)

/-- A colour transformation fixes the `L ∂ barL` block, neither symbol carrying
  colour. -/
lemma repGauge_su3_LbarLBlk (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((U, 1, 1) : GaugeGroupI) (LbarLBlk f f' q l c c' w w')
      = LbarLBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su3_L U f ![] (l.1, w'))
    (repGauge_su3_barL U f' ![q] (l.2, w))

/-- The two isospin indices of the `L ∂ barL` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_isospinFundAntiFund_LbarLBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' : Fin 3) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun n : Fin 2 → Fin 2 => LbarLBlk f f' q l c c' (n 0) (n 1)) ∘
          fundAntiFundIdx)) :=
  (isEquivariant_isospinFundAntiFund_mul_swap
    (fun V w => repGauge_su2_L V f ![] l.1 w)
    (fun V w => repGauge_su2_barL V f' ![q] l.2 w) :)

/-- A hypercharge transformation fixes the `L ∂ barL` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_LbarLBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (LbarLBlk f f' q l c c' w w')
      = LbarLBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (by rw [← mul_pow, Unitary.mul_star_self_of_mem t.2, one_pow])
    (repGauge_u1_L t f ![] (l.1, w'))
    (repGauge_u1_barL t f' ![q] l.2 w)

/-- The colour stage of the `L ∂ barL` block. -/
noncomputable def LbarLColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => LbarLBlk f f' q l (n 0) (n 1) w w')) :=
  InvariantReductionToSpan.ofFixedFamily (LbarLBlk f f' q l 0 0 w w') (fun _ => rfl)
    (fun U => repGauge_su3_LbarLBlk U f f' q l 0 0 w w')

/-- The colour contraction of the `L ∂ barL` block, written out. -/
lemma LbarLColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (LbarLColourStep f f' q l w w').spanningVector
      = LbarLBlk f f' q l 0 0 w w' := rfl

/-- The isospin stage of the `L ∂ barL` block. -/
noncomputable def LbarLIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (LbarLColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  IsospinFundAntiFund.invariantReductionToSpan (by
    simp only [LbarLColourStep_contraction]
    exact isEquivariant_isospinFundAntiFund_LbarLBlk f f' q l 0 0)

/-- The doubly contracted `L ∂ barL` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_LbarL (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (LbarLIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (LbarLIsospinStep f f' p.1 p.2).spanningVector
        = ∑ i : Fin 2, LbarLBlk f f' p.1 p.2 0 0 i i := by
    intro p
    show LbarLBlk f f' p.1 p.2 0 0 0 0 + LbarLBlk f f' p.1 p.2 0 0 1 1 = _
    rw [Fin.sum_univ_two]
  simp only [hsum]
  refine isEquivariant_upDownRDownL_sum fun i : Fin 2 => ?_
  convert isEquivariant_upDownRDownL_mul repLorentz_mul
    (repLorentz_leftComp (.L f i))
    (repLorentz_rightComp_deriv_one (.barL f' i)) using 2
  funext p
  rfl

/-- The Lorentz stage of the `L ∂ barL` block. -/
noncomputable def LbarLLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (LbarLIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_LbarL f f')

/-- The `L ∂ barL` block as a kinetic block. -/
noncomputable def LbarLKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := LbarLBlk f f'
  colourStep := LbarLColourStep f f'
  colourStep_mem _ _ _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  isospinStep := LbarLIsospinStep f f'
  isospinStep_mem _ _ := IsospinFundAntiFund.deltaContraction_mem_span _
  lorentzStep := LbarLLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_LbarLBlk t f f' q l c c' w w'

/-- The components of the block `barL ∂ L`, an underived conjugate lepton-doublet symbol against a
  once-derived lepton-doublet symbol. -/
noncomputable def barLLBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l _ _ w w' => barLComponent f ![] (l.2, w) * LComponent f' ![q] (l.1, w')

/-- A colour transformation fixes the `barL ∂ L` block, neither symbol carrying
  colour. -/
lemma repGauge_su3_barLLBlk (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((U, 1, 1) : GaugeGroupI) (barLLBlk f f' q l c c' w w')
      = barLLBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su3_barL U f ![] (l.2, w))
    (repGauge_su3_L U f' ![q] (l.1, w'))

/-- The two isospin indices of the `barL ∂ L` block are one fundamental and one
  anti-fundamental, the barred symbol supplying the fundamental one. -/
lemma isEquivariant_isospinFundAntiFund_barLLBlk (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' : Fin 3) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGauge.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun n : Fin 2 → Fin 2 => barLLBlk f f' q l c c' (n 0) (n 1)) ∘
          fundAntiFundIdx)) :=
  (isEquivariant_isospinFundAntiFund_mul (fun V w => repGauge_su2_barL V f ![] l.2 w)
    (fun V w => repGauge_su2_L V f' ![q] l.1 w) :)

/-- A hypercharge transformation fixes the `barL ∂ L` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_barLLBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (barLLBlk f f' q l c c' w w')
      = barLLBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (by rw [← mul_pow, Unitary.star_mul_self_of_mem t.2, one_pow])
    (repGauge_u1_barL t f ![] l.2 w)
    (repGauge_u1_L t f' ![q] (l.1, w'))

/-- The colour stage of the `barL ∂ L` block. -/
noncomputable def barLLColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => barLLBlk f f' q l (n 0) (n 1) w w')) :=
  InvariantReductionToSpan.ofFixedFamily (barLLBlk f f' q l 0 0 w w') (fun _ => rfl)
    (fun U => repGauge_su3_barLLBlk U f f' q l 0 0 w w')

/-- The colour contraction of the `barL ∂ L` block, written out. -/
lemma barLLColourStep_contraction (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    (barLLColourStep f f' q l w w').spanningVector
      = barLLBlk f f' q l 0 0 w w' := rfl

/-- The isospin stage of the `barL ∂ L` block. -/
noncomputable def barLLIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (barLLColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  IsospinFundAntiFund.invariantReductionToSpan (by
    simp only [barLLColourStep_contraction]
    exact isEquivariant_isospinFundAntiFund_barLLBlk f f' q l 0 0)

/-- The doubly contracted `barL ∂ L` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_barLL (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (barLLIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (barLLIsospinStep f f' p.1 p.2).spanningVector
        = ∑ i : Fin 2, barLLBlk f f' p.1 p.2 0 0 i i := by
    intro p
    show barLLBlk f f' p.1 p.2 0 0 0 0 + barLLBlk f f' p.1 p.2 0 0 1 1 = _
    rw [Fin.sum_univ_two]
  simp only [hsum]
  refine isEquivariant_upDownRDownL_sum fun i : Fin 2 => ?_
  convert isEquivariant_upDownRDownL_mul_swap repLorentz_mul
    (repLorentz_rightComp (.barL f i))
    (repLorentz_leftComp_deriv_one (.L f' i)) using 2
  funext p
  rfl

/-- The Lorentz stage of the `barL ∂ L` block. -/
noncomputable def barLLLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (barLLIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_barLL f f')

/-- The `barL ∂ L` block as a kinetic block. -/
noncomputable def barLLKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := barLLBlk f f'
  colourStep := barLLColourStep f f'
  colourStep_mem _ _ _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  isospinStep := barLLIsospinStep f f'
  isospinStep_mem _ _ := IsospinFundAntiFund.deltaContraction_mem_span _
  lorentzStep := barLLLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_barLLBlk t f f' q l c c' w w'

/-!

## D. The two lepton-singlet pairings

The lepton singlet carries only hypercharge and a spinor index, so both gauge stages are
trivial and the whole classification is the Lorentz one.

-/

/-- The components of the block `e ∂ bare`, an underived lepton-singlet symbol against a
  once-derived conjugate lepton-singlet symbol. -/
noncomputable def ebareBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l _ _ _ _ => eComponent f ![] l.2 * bareComponent f' ![q] l.1

/-- A colour transformation fixes the `e ∂ bare` block, neither symbol carrying
  colour. -/
lemma repGauge_su3_ebareBlk (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((U, 1, 1) : GaugeGroupI) (ebareBlk f f' q l c c' w w')
      = ebareBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su3_e U f ![] l.2)
    (repGauge_su3_bare U f' ![q] l.1)

/-- An isospin transformation fixes the `e ∂ bare` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_ebareBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (ebareBlk f f' q l c c' w w')
      = ebareBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su2_e V f ![] l.2)
    (repGauge_su2_bare V f' ![q] l.1)

/-- A hypercharge transformation fixes the `e ∂ bare` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_ebareBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (ebareBlk f f' q l c c' w w')
      = ebareBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (by rw [← mul_pow, Unitary.mul_star_self_of_mem t.2, one_pow])
    (repGauge_u1_e t f ![] l.2)
    (repGauge_u1_bare t f' ![q] l.1)

/-- The colour stage of the `e ∂ bare` block. -/
noncomputable def ebareColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => ebareBlk f f' q l (n 0) (n 1) w w')) :=
  InvariantReductionToSpan.ofFixedFamily (ebareBlk f f' q l 0 0 w w') (fun _ => rfl)
    (fun U => repGauge_su3_ebareBlk U f f' q l 0 0 w w')

/-- The isospin stage of the `e ∂ bare` block. -/
noncomputable def ebareIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (ebareColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  InvariantReductionToSpan.ofFixedFamily (ebareColourStep f f' q l 0 0).spanningVector
    (fun _ => rfl)
    (fun V => isFixedBy_span_range
      (fun n V' => repGauge_su2_ebareBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (Submodule.subset_span ⟨![0, 0], rfl⟩))

/-- The doubly contracted `e ∂ bare` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_ebare (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (ebareIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (ebareIsospinStep f f' p.1 p.2).spanningVector
        = ebareBlk f f' p.1 p.2 0 0 0 0 := fun _ => rfl
  simp only [hsum]
  convert isEquivariant_upDownRDownL_mul_swap repLorentz_mul
    (repLorentz_rightComp (.e f))
    (repLorentz_leftComp_deriv_one (.bare f')) using 2
  funext p
  rfl

/-- The Lorentz stage of the `e ∂ bare` block. -/
noncomputable def ebareLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (ebareIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_ebare f f')

/-- The `e ∂ bare` block as a kinetic block. -/
noncomputable def ebareKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := ebareBlk f f'
  colourStep := ebareColourStep f f'
  colourStep_mem _ _ _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  isospinStep := ebareIsospinStep f f'
  isospinStep_mem _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  lorentzStep := ebareLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_ebareBlk t f f' q l c c' w w'

/-- The components of the block `bare ∂ e`, an underived conjugate lepton-singlet symbol against a
  once-derived lepton-singlet symbol. -/
noncomputable def bareeBlk (f f' : Fin 3) :
    (Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Fin 3 → Fin 3 → Fin 2 → Fin 2 →
    fieldData.LocalCovFieldAlgebra :=
  fun q l _ _ _ _ => bareComponent f ![] l.1 * eComponent f' ![q] l.2

/-- A colour transformation fixes the `bare ∂ e` block, neither symbol carrying
  colour. -/
lemma repGauge_su3_bareeBlk (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((U, 1, 1) : GaugeGroupI) (bareeBlk f f' q l c c' w w')
      = bareeBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su3_bare U f ![] l.1)
    (repGauge_su3_e U f' ![q] l.2)

/-- An isospin transformation fixes the `bare ∂ e` block, neither symbol carrying
  isospin. -/
lemma repGauge_su2_bareeBlk (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, V, 1) : GaugeGroupI) (bareeBlk f f' q l c c' w w')
      = bareeBlk f f' q l c c' w w' :=
  repGauge_mul_fixed (repGauge_su2_bare V f ![] l.1)
    (repGauge_su2_e V f' ![q] l.2)

/-- A hypercharge transformation fixes the `bare ∂ e` block, the hypercharges of a
  species and its conjugate cancelling. -/
lemma repGauge_u1_bareeBlk (t : unitary ℂ) (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) (c c' w w' : _) :
    repGauge ((1, 1, t) : GaugeGroupI) (bareeBlk f f' q l c c' w w')
      = bareeBlk f f' q l c c' w w' :=
  repGauge_mul_smul_fixed (by rw [← mul_pow, Unitary.star_mul_self_of_mem t.2, one_pow])
    (repGauge_u1_bare t f ![] l.1)
    (repGauge_u1_e t f' ![q] l.2)

/-- The colour stage of the `bare ∂ e` block. -/
noncomputable def bareeColourStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3) (l : Fin 2 × Fin 2)
    (w w' : Fin 2) :
    InvariantReductionToSpan
      (fun U : specialUnitaryGroup (Fin 3) ℂ => repGauge ((U, 1, 1) : GaugeGroupI))
      (Submodule.span ℂ
        (Set.range fun n : Fin 2 → Fin 3 => bareeBlk f f' q l (n 0) (n 1) w w')) :=
  InvariantReductionToSpan.ofFixedFamily (bareeBlk f f' q l 0 0 w w') (fun _ => rfl)
    (fun U => repGauge_su3_bareeBlk U f f' q l 0 0 w w')

/-- The isospin stage of the `bare ∂ e` block. -/
noncomputable def bareeIsospinStep (f f' : Fin 3) (q : Fin 1 ⊕ Fin 3)
    (l : Fin 2 × Fin 2) :
    InvariantReductionToSpan
      (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge ((1, V, 1) : GaugeGroupI))
      (Submodule.span ℂ (Set.range fun n : Fin 2 → Fin 2 =>
        (bareeColourStep f f' q l (n 0) (n 1)).spanningVector)) :=
  InvariantReductionToSpan.ofFixedFamily (bareeColourStep f f' q l 0 0).spanningVector
    (fun _ => rfl)
    (fun V => isFixedBy_span_range
      (fun n V' => repGauge_su2_bareeBlk V' f f' q l (n 0) (n 1) 0 0) V _
      (Submodule.subset_span ⟨![0, 0], rfl⟩))

/-- The doubly contracted `bare ∂ e` block carries one four-vector index and a pair of
  dual opposite-chirality Weyl indices. -/
lemma isEquivariant_upDownRDownL_baree (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.up, .downR, .downL] repLorentz
      (liftComponents ((fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (bareeIsospinStep f f' p.1 p.2).spanningVector) ∘ dualIndexEquiv)) := by
  have hsum : ∀ p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
      (bareeIsospinStep f f' p.1 p.2).spanningVector
        = bareeBlk f f' p.1 p.2 0 0 0 0 := fun _ => rfl
  simp only [hsum]
  convert isEquivariant_upDownRDownL_mul repLorentz_mul
    (repLorentz_leftComp (.bare f))
    (repLorentz_rightComp_deriv_one (.e f')) using 2
  funext p
  rfl

/-- The Lorentz stage of the `bare ∂ e` block. -/
noncomputable def bareeLorentzStep (f f' : Fin 3) :
    InvariantReductionToSpan (fun Λ : SL(2,ℂ) => repLorentz Λ)
      (Submodule.span ℂ (Set.range fun p : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 =>
        (bareeIsospinStep f f' p.1 p.2).spanningVector)) :=
  invariantReductionToPauliValDualWeylOfComponents
    (isEquivariant_upDownRDownL_baree f f')

/-- The `bare ∂ e` block as a kinetic block. -/
noncomputable def bareeKineticBlock (f f' : Fin 3) : KineticBlock repGauge repLorentz where
  blk := bareeBlk f f'
  colourStep := bareeColourStep f f'
  colourStep_mem _ _ _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  isospinStep := bareeIsospinStep f f'
  isospinStep_mem _ _ := Submodule.subset_span ⟨![0, 0], rfl⟩
  lorentzStep := bareeLorentzStep f f'
  lorentzStep_mem := liftComponents_comp_mem_span dualIndexEquiv _ _
  hyper t q l c c' w w' := repGauge_u1_bareeBlk t f f' q l c c' w w'

end FermionSector

end StandardModel
