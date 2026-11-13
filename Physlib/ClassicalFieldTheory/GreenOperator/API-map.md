# Green operators and the causal propagator

## Abstract (Alpha)

Retarded and advanced Green operators solve a linear field equation with
support in the causal future or past of the source. Their difference produces
homogeneous solutions. This API describes the support assumptions for
extending the retarded inverse, identifying the homogeneous solution space,
and deriving the causal Green sequence, with the Klein–Gordon equation on
Minkowski spacetime as an example.

## Content (Alpha)

### Compact sources and causal support

Let $P$ be a linear operator on a space of admissible fields. Locality means
that $P$ cannot enlarge a field's closed support, so it acts on compactly
supported fields as well. [1] A retarded Green operator sends a compactly
supported source $f$ to a solution of $Pu=f$ supported in the causal future
of the closed support of $f$. The advanced operator uses the causal past.
Both are linear and recover a compactly supported field $v$ when applied to
$Pv$. A Green pair bundles these two inverses for the same $P$ and causal
relation. [2] Bär uses the opposite naming convention for the two time
directions. {1}

### The causal propagator

The sign convention is $E=G_{\mathrm{ret}}-G_{\mathrm{adv}}$. Applying $P$
to either response gives the same source, so $PEf=0$. The response is
supported in the union of the source's causal future and causal past. A
field is spacelike compact when its closed support lies in such a union
for some compact set. Thus $E$ maps compact sources to spacelike-compact
homogeneous solutions. [3][4][5]

The propagator annihilates every source of the form $Pv$ with $v$ compactly
supported. For the converse, assume that the intersection of the causal
future of one compact set with the causal past of another is always compact.
If $Ef=0$, the retarded and advanced responses agree. Their common support
lies in the intersection of the future and past of the source support, so
the common response is itself compactly supported and gives a compact
preimage under $P$. [3][6]

### Past-compact sources and the exact sequence

A source is past compact when its closed support has compact intersection
with the causal past of every compact set. [3][7] Given localization data,
the retarded response near an event can be computed from a compact
truncation of the source. The truncation agrees locally with the source
throughout the causal past of a compact observation set whose causal
past contains a neighborhood of the event. These responses agree on
overlaps and glue. With compact causal diamonds, the construction gives a
two-sided linear inverse for $P$ on past-compact fields and retains the
causal-future support bound. Time reversal supplies the corresponding
construction for advanced propagation. [8][9] For the smooth spacetime
setting in the literature, see {1}.

Assume compact causal diamonds and that every spacelike-compact field can
be written as the difference of a future-supported field and a past-supported
field, each supported to one side of a compact set. Assume also that $P$
is injective on fields supported in the future
of a compact set, and separately on fields supported in the past of a compact
set. Then every spacelike-compact homogeneous solution is $Ef$ for some compact
source $f$. The propagator identifies the compact source space modulo the image
of $P$ on compact fields with the spacelike-compact homogeneous solution
space. [10][11] Given both orientations of the
localization data, compact causal diamonds and causal cutoffs give the full
exact sequence
$0\to S_c\xrightarrow{P} S_c\xrightarrow{E} S_{sc}\xrightarrow{P} S_{sc}\to 0$,
where $S_c$ and $S_{sc}$ are the compactly supported and spacelike-compact
admissible fields. [12]

### Klein–Gordon on Minkowski spacetime

In any spatial dimension, the Klein–Gordon equation has a Green pair for
smooth fields valued in a complex Banach space, for any real mass parameter.
The construction uses a spatial Fourier response. A real scalar Green pair
is also available. [13] In the complex Banach-valued setting the API proves
uniqueness of the retarded solution with the causal-future support bound for
each compact source, as well as the exact sequence and the quotient
description above. [14]

## Lean References

1. PhyslibAlpha/Mathematics/Analysis/LocalOperator.lean — `LocalOperator`,
   `compactFields`, `compactOperator`
2. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/Basic.lean — `RetardedGreenOperator`,
   `AdvancedGreenOperator`, `GreenOperators`
3. PhyslibAlpha/Mathematics/Order/CausalRelation.lean — `causalHull`,
   `IsSpacelikeCompact`, `HasCompactCausalDiamonds`, `IsPastCompact`
4. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/Basic.lean — `spacelikeCompactSolution`
5. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/CausalPropagator.lean — `causalPropagator`,
   `causalPropagator_solves`, `causalPropagator_support`, `toSolutionSpace`
6. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/CausalPropagator.lean —
   `causalPropagator_comp_operator`, `retarded_compact_of_causalPropagator_eq_zero`,
   `causalPropagator_ker`
7. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/Basic.lean — `pastCompactFields`
8. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/Localization.lean — `PastLocalization`,
   `retardedValue_eq_on_past_bound`, `retardedSection`, `retardedExtension`,
   `retardedExtension_support`
9. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/Basic.lean — `reverse`
10. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/CausalPropagator.lean — `HasCausalCutoffs`
11. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/Uniqueness.lean — `toSolutionSpace_surjective`,
    `solutionSpaceEquivQuotient`, `solutionSpaceEquivQuotient_symm_mk`
12. PhyslibAlpha/ClassicalFieldTheory/GreenOperator/Uniqueness.lean — `causalGreen_exactSequence`
13. PhyslibAlpha/ClassicalFieldTheory/KleinGordon/GreenOperators.lean — `greenOperators`,
    `realGreenOperators`
14. PhyslibAlpha/ClassicalFieldTheory/KleinGordon/GreenOperators.lean —
    `existsUnique_retardedSolution`, `causalGreen_exactSequence`, `solutionSpaceEquivQuotient`

## References

1. Christian Bär, [Green-hyperbolic operators on globally hyperbolic spacetimes](https://arxiv.org/abs/1310.0738v2).
   Communications in Mathematical Physics 333, 1585–1615 (2015), Definition 3.1 and Theorems 3.8 and 3.22.
