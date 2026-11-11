# Poincaré transformations

## Abstract (Alpha)

Poincaré transformations combine Lorentz transformations with spacetime translations.
This API describes their action on spacetime, causal order, smooth fields, test
functions, and distributions.

## Content (Alpha)

### Group and spacetime action

In $d$ spatial dimensions, a Poincaré transformation is a pair $g=(a,\Lambda)$,
where $a$ is a spacetime translation and $\Lambda$ is a Lorentz transformation.
The product is $(a,\Lambda)(b,M)=(a+\Lambda b,\Lambda M)$, and the action
$g\cdot x=\Lambda x+a$ is a homeomorphism of spacetime. [1]
The Lorentz group is described in {1}.

### Smooth fields

A transformation acts on a field by inverse pullback,
$(g\cdot u)(x)=u(g^{-1}\cdot x)$; the field values have no additional internal
representation action. This is a left group action. [2]
For fields valued in a normed real vector space, pullback preserves smoothness
and compact support and defines real-linear maps on smooth and test fields.
The closed support of a transformed smooth field is the image of its original
closed support under $g$. [3]

### Causal order

A transformation is orthochronous when its Lorentz part preserves the direction
of time. [4] Orthochronous transformations preserve causal order and take causal
futures and pasts to those of the transformed sets. Transformations that are not
orthochronous reverse causal order and exchange causal futures and pasts. [5]

### Test functions and distributions

For each fixed transformation, pullback is a continuous linear map on real-valued
test functions. The induced action on real-valued distributions is $(g\cdot T)(\varphi)=T(g^{-1}\cdot\varphi)$
and obeys the left group action law. In particular, the delta distribution at
$p$ transforms to the delta distribution at $g\cdot p$. [6]

## Lean References

1. PhyslibAlpha/Relativity/Poincare/Basic.lean — `PoincareGroup`,
   `translation_mul`, `lorentz_mul`, `smul_def`, `toHomeomorph`
2. PhyslibAlpha/Relativity/Poincare/Basic.lean — `act`, `act_one`, `act_mul`
3. PhyslibAlpha/Relativity/Poincare/Fields.lean — `actSmooth`, `actTest`,
   `tsupport_actSmooth`
4. PhyslibAlpha/Relativity/Poincare/Basic.lean — `IsOrthochronous`
5. PhyslibAlpha/Relativity/Poincare/Causality.lean — `causallyFollows_smul_iff`,
   `causallyFollows_smul_iff_of_not`, `causalFuture_smul`, `causalPast_smul`,
   `causalFuture_smul_of_not`, `causalPast_smul_of_not`
6. PhyslibAlpha/Relativity/Poincare/Distributions.lean — `actTestFunction`,
   `actTestFunction_apply`, `actDist`, `actDist_apply`, `actDist_mul`, `actDist_delta`

## References

1. Physlib/Relativity/LorentzGroup/API-map.md — Lorentz group API map.
