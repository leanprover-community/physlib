/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem, Adam Bornemann
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.EssentialSpectrum.Defs

/-!

# Discreteness theorem (not ported — recorded as a gap)

`adambornemann-glitch/Spectra`'s `SpectralTheory/Essential/Discrete.lean` proves the hard half of
the Weyl theory:

> A spectral point of a self-adjoint operator that is **not** in the essential spectrum is an
> eigenvalue of finite type — `∃ ψ ∈ A.domain, ψ ≠ 0 ∧ A ψ = λ • ψ`.

This is deliberately **not** ported here (not even as a `sorry`'d restatement against this repo's
own `LinearPMap`/`IsSelfAdjoint` types), for a specific reason:

## Why this one is skipped

Spectra's proof (`mem_essSpectrum_of_proj_singleton_eq_zero`) is not self-contained within
`SpectralTheory/Essential/` — it is built entirely on top of Spectra's own bespoke
projection-valued-measure infrastructure: `Spectra.ProjValMeasure`, `PVM.spectralPVM hA` (the
spectral measure of a self-adjoint operator, with its diagonal measures `P.diag`), the
Stone-generator correspondence `genToGroup`/`generator_genToGroup`, and the localization bound
`generator_sub_smul_norm_le_Icc` from Spectra's `Measure/GeneratorLink.lean` and `Eigenspace.lean`.

`EXTERNAL_INTEGRATION_PLAN.md` §4 explicitly rules out reusing Spectra's `ProjValMeasure`/POVM
wrapper types (this repo's own architecture decision forbids a second Hilbert-space PVM hierarchy),
and this port deliberately excludes pulling in unrelated Spectra subtrees beyond
`SpectralTheory/Essential/` and `SpectralTheory/` itself. Reproving this theorem against this
repo's *own* spectral-measure apparatus (`HilbertSpace/Unbounded/WOTSpectralMeasure`,
`SpectralIntegral/{Construction,SpecTheorem}.lean`) is real, substantial work — identifying the
right "spectral projection at a point/interval" primitives in this repo's own construction and
re-deriving the localization estimate — not a mechanical restatement, and out of scope for this
port.

## What the theorem would give, if ported

Restated against this repo's types, the target statement is:

```
theorem mem_pointSpectrum_of_mem_spectrum_notMem_essSpectrum {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {lam : ℝ} (hspec : (lam : ℂ) ∈ LinearPMap.spectrum A)
    (hne : lam ∉ essSpectrum hA) :
    ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ A ψ = (lam : ℂ) • (ψ : H)
```

## The connection to `JordanOrderUnit/SpectralDecomposition.lean`'s `discreteSpectrum` gap

Per `EXTERNAL_INTEGRATION_PLAN.md` §3.4, this theorem combined with `Weyl.lean`'s invariance
theorem and `HilbertSpace/TraceClass/Basic.lean`'s `HasFiniteMultiplicity` is exactly the tool that
gap needs: "discrete spectrum" done honestly is "spectrum outside `essSpectrum`", and each such
point is then an eigenvalue (this theorem) whose eigenspace projection is shown separately to be
trace class (`HasFiniteMultiplicity`) — giving Murray–von Neumann finite multiplicity without ever
invoking a purely topological/isolated-point notion of "discrete".

**Caveat found during this port**: no file named `JordanOrderUnit/SpectralDecomposition.lean`, and
no occurrence of `discreteSpectrum`, currently exists anywhere in this checkout
(`physlib-agent/pr-1602-reconcile`) — only `EXTERNAL_INTEGRATION_PLAN.md`'s own prose mentions it.
So this file records the intended bridge for when that file is written, rather than connecting to
an existing declaration.

**The exact remaining bridge**, once both pieces above are available:

1. Build the `H →L[ℂ] H`-bundling of `𝑅 A z` noted in `Weyl.lean`'s docstring (or otherwise supply
   an `IsResolventAt` witness), so `essSpectrum` invariance is usable on concrete operators.
2. Port (or re-derive against this repo's own spectral-measure machinery) the theorem stated above.
3. Define `discreteSpectrum hA := (LinearPMap.spectrum A ∩ Set.range ((↑) : ℝ → ℂ)) \ (essSpectrum
   hA image)` (or however `SpectralDecomposition.lean` ends up phrasing it) and show each of its
   points is an eigenvalue (step 2) with `HasFiniteMultiplicity` eigenprojection — the latter needs
   a separate, model-dependent finiteness argument (e.g. from a trace-class resolvent), not supplied
   by Weyl's theorem itself.

-/
