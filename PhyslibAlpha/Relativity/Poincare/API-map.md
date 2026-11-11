# Poincaré transformations

## Abstract (Alpha)

Poincaré transformations combine Lorentz transformations with spacetime translations.
This API describes their group law, causal properties, and actions on smooth fields,
test functions, and distributions, including how these actions transport support.

## Content (Alpha)

### Group and spacetime action

In $d$ spatial dimensions, a Poincaré transformation is a pair $g=(a,\Lambda)$,
where $a$ is a spacetime translation and $\Lambda$ is a Lorentz transformation.
The product and inverse are
$(a,\Lambda)(b,M)=(a+\Lambda b,\Lambda M)$ and
$(a,\Lambda)^{-1}=(-\Lambda^{-1}a,\Lambda^{-1})$.
The action $g\cdot x=\Lambda x+a$ is a homeomorphism of spacetime. [1]
The Lorentz group is described in {1}.

### Smooth fields

A transformation acts on a field by inverse pullback,
$(g\cdot u)(x)=u(g^{-1}\cdot x)$; the field values have no additional internal
representation action. The identity acts trivially, composition gives a left
group action, and the action of the inverse undoes the transformation. [2]
For fields valued in a normed real vector space, pullback preserves smoothness
and compact support and defines real-linear maps on smooth fields and compactly
supported smooth test fields. The closed support of a transformed smooth field
is the image of its original closed support under $g$. [3]

### Causal order and reflections

A transformation is orthochronous when its Lorentz part preserves the direction
of time. The identity is orthochronous, as are products and inverses of
orthochronous transformations. [4] The point reflection with parameter $p$ acts
as $x\mapsto p-x$, so its centre is $p/2$. It reverses time orientation. [5]

Orthochronous transformations preserve causal order and take causal futures and
pasts to those of the transformed sets. Transformations that are not
orthochronous reverse causal order and exchange causal futures and pasts. [6]
Here the causal hull of a set means the union of its causal future and causal
past. [7] Every Poincaré transformation maps this hull to the causal hull of the
image, whether or not it preserves time orientation. [8]

### Test functions and distributions

Test functions are smooth, compactly supported functions on the whole spacetime,
with values in a normed real vector space. For each fixed transformation, the
pullback above is a continuous real-linear map on the test-function space and
obeys the left group action law. Its closed support is the image of the original
closed support under $g$. [9]

A distribution with values in a normed real vector space $V$ takes real-valued
test functions to $V$. Its transformed value is
$(g\cdot T)(\varphi)=T(g^{-1}\cdot\varphi)$. For fixed $g$, this defines a
continuous real-linear map on distributions; the identity and composition laws
again give a left group action. [10]

If $T$ vanishes on a set $U$, meaning it annihilates every test function whose
closed support lies in $U$, then $g\cdot T$ vanishes on $gU$. [11]
For real-valued distributions, the delta distribution at $p$ transforms to the
delta distribution at $g\cdot p$. [12]

## Lean References

1. PhyslibAlpha/Relativity/Poincare/Basic.lean — `PoincareGroup`,
   `translation_mul`, `lorentz_mul`, `translation_inv`, `lorentz_inv`,
   `smul_def`, `toHomeomorph`
2. PhyslibAlpha/Relativity/Poincare/Basic.lean — `act`, `act_apply`, `act_one`,
   `act_mul`, `act_inv_act`
3. PhyslibAlpha/Relativity/Poincare/Fields.lean — `contDiff_act`,
   `hasCompactSupport_act`, `actSmooth`, `actTest`, `tsupport_actSmooth`
4. PhyslibAlpha/Relativity/Poincare/Basic.lean — `IsOrthochronous`,
   `isOrthochronous_one`, `IsOrthochronous.mul`, `IsOrthochronous.inv`
5. PhyslibAlpha/Relativity/Poincare/Basic.lean — `pointReflection`,
   `pointReflection_smul`, `not_isOrthochronous_pointReflection`
6. PhyslibAlpha/Relativity/Poincare/Causality.lean — `causallyFollows_smul_iff`,
   `causallyFollows_smul_iff_of_not`, `causalFuture_smul`, `causalPast_smul`,
   `causalFuture_smul_of_not`, `causalPast_smul_of_not`
7. PhyslibAlpha/Mathematics/Order/CausalRelation.lean — `causalHull`
8. PhyslibAlpha/Relativity/Poincare/Causality.lean — `causalHull_smul`
9. PhyslibAlpha/Relativity/Poincare/Distributions.lean — `actTestFunction`,
   `actTestFunction_apply`, `actTestFunction_one`, `actTestFunction_mul`,
   `tsupport_actTestFunction`
10. PhyslibAlpha/Relativity/Poincare/Distributions.lean — `actDist`,
    `actDist_apply`, `actDist_one`, `actDist_mul`
11. PhyslibAlpha/Relativity/Poincare/Distributions.lean — `isVanishingOn_actDist`
12. PhyslibAlpha/Relativity/Poincare/Distributions.lean — `actDist_delta`

## References

1. Physlib/Relativity/LorentzGroup/API-map.md — Lorentz group API map.
