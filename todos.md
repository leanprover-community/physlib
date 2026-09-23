# TODOs introduced by this branch

20 open &middot; as of 2026-08-25

> Regenerate with `python scripts/todos.py --md todos.md` after adding or
> resolving a TODO, and commit it in the same commit.

**Format.** Use the `TODO "…"` command

### `Particles/PureFermionic`

- Move the diagonal `SL(2, ℂ)` material `diagSL`, `diagSL_inv`, `diagSL_neg_one` and `twoI` to `Physlib.Relativity.SL2C.Basic`, their canonical home, when the effective-potential development is split up. &nbsp;[`EFTLagrangianExclDeriv.lean:162`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/PureFermionic/EFTLagrangianExclDeriv.lean#L162)

### `Particles/QED`

- Prove the composition law of the Lorentz action. Being a pullback on coordinates it is a right action, `lorentzAction M ∘ lorentzAction N = lorentzAction (N * M)`; the proof needs permutation-invariance and functoriality of `derivSum` over sorted lists. &nbsp;[`Basic.lean:1431`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Basic.lean#L1431)
- Define an antilinear star on the QED jet algebra with `star ψ = ψ̄`, `star A = A`, and prove hermiticity of the Lagrangian up to the total derivative of the kinetic term. &nbsp;[`Basic.lean:1434`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Basic.lean#L1434)
- Connect the QED matter content to `Physlib.QFT.QED.AnomalyCancellation`: the electron spectrum is vector-like (charges `±1`), so it satisfies the gravitational and cubic anomaly cancellation conditions. &nbsp;[`CurrentCoupling.lean:56`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/CurrentCoupling.lean#L56)
- Classify the gauge- and Lorentz-invariant elements of mass dimension at most four of the full QED jet algebra: the analogue for the Dirac electron of the classification `LeptonGaugeSector.JetAlgebra.MassDimFour.Classification`, showing the QED Lagrangian is the most general renormalizable choice. &nbsp;[`JetCompleteness.lean:57`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/JetCompleteness.lean#L57)
- Derive `diracEquation`, `diracAdjEquation` and `qedMaxwellEquation` variationally: define the Euler–Lagrange operator on the jet algebra (the variational derivative with respect to each jet coordinate) and prove they are the EL equations of `lagrangian`, following `Physlib.Electromagnetism.Dynamics.IsExtrema` concretely. &nbsp;[`Lagrangian.lean:119`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Lagrangian.lean#L119)
- Define the theta term `θ ε^{μνρσ} F_{μν} F_{ρσ}` and prove it is gauge invariant and a total derivative for `jetDeriv`, as in the lepton–gauge sector's theta term. &nbsp;[`Lagrangian.lean:123`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Lagrangian.lean#L123)
- Quantize: instantiate the field species of `Physlib.QFT.PerturbationTheory` with the photon and electron of this file, towards the Feynman rules of QED. &nbsp;[`Lagrangian.lean:125`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Lagrangian.lean#L125)
- Upgrade the mass-weight scaling to a genuine filtration by submodules, following `LeptonGaugeSector.JetAlgebra.MassDim` (`MassWeightLESubmodule`), together with the derivative-order and fermion-parity gradings needed for classification arguments. &nbsp;[`MassDimension.lean:61`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/MassDimension.lean#L61)

### `Particles/StandardModel/Fermions/JetAlgebra`

- Move FermionSpace to a seperate file by itself. &nbsp;[`Basic.lean:89`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/Fermions/JetAlgebra/Basic.lean#L89)
- For FermionSpace define the infinitismal action. &nbsp;[`Basic.lean:91`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/Fermions/JetAlgebra/Basic.lean#L91)

### `Particles/StandardModel/GaugeAlgebra`

- Make the API here match what is in the doc-string. &nbsp;[`JetGaugeAlgebra.lean:62`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeAlgebra/JetGaugeAlgebra.lean#L62)
- Add discussion about the basis. &nbsp;[`JetGaugeAlgebra.lean:63`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeAlgebra/JetGaugeAlgebra.lean#L63)
- Define the basis of the jet gauge algebra. &nbsp;[`JetGaugeAlgebra.lean:727`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeAlgebra/JetGaugeAlgebra.lean#L727)

### `Particles/StandardModel/GaugeBosons/BBoson`

- Show invariance of the mass weights with repsect to the Lorentz group. &nbsp;[`MassDim.lean:310`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeBosons/BBoson/MassDim.lean#L310)

### `Particles/StandardModel/GaugeGroup`

- Define the symmetrized maurerCartan forms. &nbsp;[`MaurerCartan.lean:59`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeGroup/MaurerCartan.lean#L59)

### `Particles/StandardModel/GaugeGroup/MaurerCartan`

- The below code needs cleaning up and moving to the correct place. &nbsp;[`Truncation.lean:135`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeGroup/MaurerCartan/Truncation.lean#L135)

### `Particles/StandardModel/JetAlgebra`

- Define the iterated derivative, and show that the iterated derivatives span the adjoin to give the whole algebra. &nbsp;[`JetDeriv.lean:279`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/JetAlgebra/JetDeriv.lean#L279)

### `Particles/WessZumino/EFTLagrangianExclDeriv`

- Define ComplexScalarEFTExclDeriv.rep &nbsp;[`Basic.lean:280`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/WessZumino/EFTLagrangianExclDeriv/Basic.lean#L280)

### `Relativity/Fermions/Weyl`

- Relate `DualLeftHandedWeyl` to `LeftHandedWeyl` via `Module.dual`. &nbsp;[`DualLeftHanded.lean:35`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean#L35)
