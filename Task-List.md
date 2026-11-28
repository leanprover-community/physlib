# Physlib `gravity` Branch — Handbook Alignment Task List

- **Branch / PR:** `gravity` / PR `#2132` (merge-base `7910f51f` on `master`, latest commit
  `f3c5362d`, `115` files changed, 30 419 insertions)
- **Audit date:** `2026-11-28` (re-run for `f3c5362d`; earlier full report for `3540573f` in
  `/home/alex/.gemini/antigravity/brain/d4b25eb5-a184-4c5d-a5b4-64448e95576f/scratch/handbook-2132-v5/report.md`,
  re-run against the pushed PR head in `/tmp/hb3/report.md`)
- **Prior baseline scores (`44e23ac2`):** Basic `2/5` | Documentation `3/5` | Organization `3/5` | Proofs `3/5` | References `4/5` | Scope `3/5`
- **Latest scores (`3540573f`, 2026-11-27):** Basic `2/5` *(11 suggestions)* | Documentation `3/5` *(10 suggestions)* | Organization `3/5` *(15 suggestions)* | Proofs `3/5` *(8 suggestions)* | References `3/5` *(9 suggestions)* | Scope `4/5` *(5 suggestions)* — **58 total suggestions**
- **Latest scores (`f3c5362d`, 2026-11-28, re-run over 115 files / 31 390 diff lines):** Basic `2/5` *(6)* | Documentation `3/5` *(6)* | Organization `3/5` *(6)* | Proofs `2/5` *(6)* | References `2/5` *(6)* | Scope `3/5` *(6)* — **30 suggestions**

---

## Session status

- **Commits this session (`gravity`, on top of `8e4011ba`):**
  - `8d406d94` — Task 18 (Basic #2, #5): general analysis moved to `Mathematics/`, `MondFieldTheory`
    structure, `STVGContent`/`TeVeSContent` structures.
  - `8f7a0485` — Task 21 (Proofs #4): `WaveSolutionOn.sub` / `WaveSolution3D.sub` extracted.
  - `963057c5` — Task 20 (Org #3): `Divergence3D.lean` renamed to `SpaceChart.lean`.
  - `41b1867e` — Task 21 (Proofs #4): `coordDeriv_ginv_eq` extracted from `inv_metric_compat`.
  - `5153a50b` — port ManifoldSobolev, CauchyInterfaces, LinearizedWaveGauge, ConformalDecomposition.
  - `5b43a6a4` — port ReducedCauchy (M3).
  - `710db324` — port MaximalDevelopment (M5), GaugeRecovery (M4), ExplicitDevelopments (M6);
    real references + API-map 107–114.
  - `e3760897` — Task 21 (Proofs #3, partial): add `coordDeriv_eq_of_slice_eq` and use it for the
    12 `unfold coordDeriv` steps in `SobolevInitialData`.
  - `bf0d8d7e` — add docstrings flagged by `docBlame` (`LinearizedBoxField`/`FLRWReducedSol` fields,
    `ConformalDecomposition.extrinsicCurvature`).
  - `bbcf03ff` — Task 21 (Proofs #3): rewrite `sobolevH1NormSq1D/3D`, `waveEnergy3DIntegrand`,
    `norm3Sq`, `spatialLaplacian3D` via equation lemmas; no `unfold` left in `SobolevInitialData`.
  - `1578d78a` — Task 21 (Proofs #4/#3): extract `coordDeriv_g_eq` (component metric compatibility).
  - `22abe72d` — Task 21 (Proofs #4/#3): extract `coordDeriv_g_eq_nhds` and
    `coordDeriv_coordDeriv_g` from `riemann_lower_skew_first`.
  Each commit verified with `lake build` of the touched modules, `module_doc_lint`, `theorem_lint`,
  and `alphaPythonLinters.sh` (only the pre-existing `Bianchi.lean` `ERR_NUM_LIN` remains). A full
  `lake build PhyslibAlpha` also succeeds across all three commits; the only warning in a touched
  file (`AqualVariation.lean:495` unused `<;>`) is pre-existing in HEAD.
- **Working-tree step (`2026-11-28`, uncommitted, on `gravity` at `8e4011ba`):** completed the
  in-progress Task 18 items (Basic #2, #5). `sum_link_mul_difference`/`secondDifference_tendsto`
  moved to `Mathematics/GraphDivergence.lean` and `Mathematics/Analysis/SecondDifference.lean`;
  `MondFieldTheory` structure added (Section C of `MondFieldTheory.lean`); `STVGContent`/`TeVeSContent`
  structures added to `DiracCounting.lean`; `PhyslibAlpha.lean` and API-map entries 92–94 updated.
  Verified: `lake build` of the five touched modules succeeds; `lake exe module_doc_lint`,
  `lake exe theorem_lint` clean; `alphaPythonLinters.sh` reports only the pre-existing
  `Bianchi.lean` `ERR_NUM_LIN` (tracked in Tasks 18/20). The `AqualVariation.lean:495` unused-`<;>`
  warning is pre-existing in HEAD, not introduced here. `.vscode/settings.json` carries an unrelated
  `CodeGPT.apiKey` edit that should not be committed.
- **Latest audit (`2026-11-27`, commit `3540573f`, matching `refs/pull/2132/head`):**
  - Followed recent commits `87458298`..`3540573f` (Friedmann derivation module rename, Kerr/FLRW/Lovelock/Kaluza-Klein proof speedups and deduplication, symmetric metric inverse helper, and mechanical reference metadata fixes).
  - **Score movement (`44e23ac2` → `3540573f`):** `Scope` improved `3/5 → 4/5`; `Basic`, `Documentation`, `Organization`, and `Proofs` held steady (`2/5`, `3/5`, `3/5`, `3/5`); `References` dropped `4/5 → 3/5` because `docs/references.bib` still contains a copied wrong DOI/journal on `ElingJacobsonMattingly2004`, an unused `Sciama1964` entry, `17` modules with only closed-access sources, and missing page/section pinpoints.
  - Note: `git diff 7910f51f` also included 5 unrelated minor file diffs (`Physlib/QFT/Euclidean/GlimmJaffe/{Axioms,FieldConfiguration}.lean`, `Physlib/SpaceAndTime/SpaceTime/TimeSlice.lean`, `Physlib/SpaceAndTime/TimeAndSpace/TestFunctions/Schwartz.lean`, `PhyslibAlpha/Particles/BeyondTheStandardModel/TwoHDM/Invariants.lean`). All five are now gone: `TwoHDM/Invariants.lean` was restored (`c3b44b7e`) and the four `Physlib/` files are back to their merge-base content (`10251800`), so the branch touches only `PhyslibAlpha` and `docs/references.bib`. Consequence: `lake exe lint_all` now reports those four restored `public import` lines as transitive imports (a pre-existing `Physlib` condition); fixing it would require editing `Physlib`, which is off limits.
- **Earlier `44e23ac2` session history (retained):**
  - **Task 6 `scope-renames` — complete** in `64176f69`: scope renames, `inertialDivergence`, and line wrapping.
  - **Task 7 `core-coordinate-metric-pipeline` — complete** across `3b20c5de`, `e1b37bae`, `dacd0fbc`, and `44e23ac2` (`Pipeline.lean` replaced by `Christoffel`/`Riemann`/`Ricci`/`Einstein`, `CoordinateMetric` aggregator, `CurvatureBridge.lean`, public chart curvature statements migrated).
  - **Task 1b `flrw-speed-of-light` — complete and verified** (`perfectFluidStressEnergy`, Friedmann bridge, and FLRW Einstein equations take `c : SpeedOfLight` and `G : GravitationalConstant`).
  - **Tasks 1, 2, 3, 4, 8 (`c7007f49`), 9, 10, 11 — complete and checked** for the `44e23ac2` batch; follow-up items surfaced in the `3540573f` audit are tracked below under **Tasks 14–17**.
  - **Task 5 — partially done** (`1447470e` applied mechanical metadata fixes; page/section locators and bibliography fixes remain open pending source verification).
  - **Task 12 — complete** (`3540573f`, `5daa23b8`, `d3fbef52`, and `253b8790` closed all `Proofs` items of the `3540573f` audit).

---

## Completed / In Progress

- [x] **1. `commit-modified-move`** *(Git/Build)* — Moved 24 files from `PhyslibAlpha/Relativity/General/Modified/*` to `PhyslibAlpha/Relativity/Modified/*` and updated `PhyslibAlpha.lean`, `API-map.md`, and module imports (`78aeab5a`).
- [x] **1b. `flrw-speed-of-light`** — `perfectFluidStressEnergy`, `einsteinTensor_00_iff_friedmann`, `einsteinTensor_spatial_iff_friedmann`, and `einsteinTensor_iff_friedmann` use `c : SpeedOfLight` and `G : GravitationalConstant`; `FriedmannBridge` and `FLRWTorsion` updated.
- [x] **2. `docs-physics-accuracy`** *(44e23ac2 batch)* — Ostrogradsky canonical pairs, `frameKretschmannScalar` Lorentzian qualification, Kottler metric-function wording, and `IncompressibleSphere` section intros updated *(remaining/new terminology & stale-header items tracked in Task 15)*.
- [x] **3. `docs-remove-review-notes-and-jargon`** *(44e23ac2 batch)* — Removed `thunder-detector` handles from docstrings, replaced pipeline jargon in the `44e23ac2` targets, standardized Ricci scalar prose (`R`), and deduplicated short module docs (`ff260da2` & related; remaining doc jargon tracked in Task 15).
- [x] **4. `docs-variable-names-and-boundaries`** *(44e23ac2 batch)* — Replaced listed bare one-letter names and stated postulated-vs-derived boundaries (`ff260da2`; remaining variable-name instances tracked in Task 15).
- [x] **6. `scope-renames`** *(Scope #1, #2 — 44e23ac2 batch)* — Done in `64176f69` *(5 remaining Scope polish items in Task 17)*.
- [x] **7. `core-coordinate-metric-pipeline`** *(Basic #2; Organization #1, #2)* — Done in `3b20c5de`, `e1b37bae`, `dacd0fbc`, `44e23ac2` *(follow-up namespace/placement cleanup tracked in Tasks 14 & 16)*.
- [x] **8. `foundations-and-bridges`** *(Basic #2, #3, #11)* — Done in `c7007f49`.
- [x] **9. `structures-and-invariants`** *(Basic #2, #5; Organization #1)* — Done in the `44e23ac2` batch *(remaining raw-vs-structure duplicates tracked in Task 14)*.
- [x] **10. `file-placement-and-namespaces`** *(Basic #6, #7, #8 — 44e23ac2 batch)* — Moved `perfectFluidStressEnergy`, `covariantDerivTensor2`, `FrameKretschmann`, `GeneralizedKronecker`, and `CoordDeriv` *(follow-up placement/namespace items tracked in Tasks 14 & 16)*.
- [x] **11. `file-organization-and-naming`** *(Organization #2, #3 — 44e23ac2 batch)* — Split FLRW curvature, `EinsteinCartan/`, and `Lovelock/`; renamed `FriedmannEquations.lean` *(15 remaining Organization items tracked in Task 16)*.

---

## Open Tasks

- [~] **5. `references-links-and-bib`** *(References #2, #4, #5 — 9 suggestions in `3540573f` audit)* — Mechanical fixes landed in `1447470e`; `3fa04081` repaired the bibliography record and added page-anchored open-access references. Remaining items need page numbers from sources not reachable offline:
  - [x] `docs/references.bib:1080` *(Ref #2)* — `ElingJacobsonMattingly2004` (`gr-qc/0410001`) is now a Deserfest proceedings chapter (World Scientific), so it no longer duplicates the *Physical Review D* 70, 024003 record of `JacobsonMattingly2004`.
  - [x] `docs/references.bib:1116` *(Ref #2)* — `[ref: Sciama1964]` is now cited in `PhyslibAlpha/Relativity/Modified/EinsteinCartan/Basic.lean`.
  - [x] `PhyslibAlpha/Relativity/Modified/Teleparallel/FTGravity.lean:42` *(Ref #5)* — `FerraroFiorini2007` now links to `https://arxiv.org/pdf/gr-qc/0610067#page=2` (Sec. II).
  - [~] `PhyslibAlpha/Relativity/General/GravitationalConstant.lean:58` *(Ref #5)* — `CODATA2022` now points at the Newtonian-constant entry (`https://physics.nist.gov/cgi-bin/cuu/Value?bg`); the BIPM `#page=` anchor is still missing because the brochure's printed and PDF page numbers differ by front matter.
  - [x] `PhyslibAlpha/Relativity/Modified/MOG.lean:59` *(Ref #5)* — `Harikumar2022MOG` now links to `https://www.mdpi.com/2218-1997/8/5/259/pdf#page=2` (Sec. 2–3).
  - [x] `PhyslibAlpha/Relativity/Modified/Lovelock/Contract5.lean:34` *(Ref #4)* — Open-access `[ref: PadmanabhanKothawala2013]` added with `https://arxiv.org/pdf/1302.2151#page=4`.
  - [x] `PhyslibAlpha/Relativity/General/FrameKretschmann.lean:29` *(Ref #4)* — `[ref: Carroll1997]` with per-topic `#page=` anchors added here and in all 7 closed-access-only siblings (`Mathematics/Calculus/CoordDeriv.lean`, `Metrics/{Christoffel,CoordDeriv,CovariantDerivTensor2,CurvatureBridge,Ricci}.lean`, `Tensors/PerfectFluidStressEnergy.lean`).
  - [~] `PhyslibAlpha/Relativity/Modified/KaluzaKlein/Basic.lean:42` *(Ref #4)* — `[ref: OverduinWesson1997]` (`gr-qc/9805018`, page-anchored) added to all four `KaluzaKlein` modules; `[ref: Shapiro2002torsion]` added to the three `EinsteinCartan` modules. `Nordstrom.lean` still lacks an open-access review because no suitable anchor could be verified.
  - [ ] `PhyslibAlpha/Relativity/Modified/Nordstrom.lean:57` *(Ref #2)* — Add section, equation, or page pinpoints to full-paper span citations: `Nordstrom1913`, `EinsteinFokker1914`, `Nordstrom1912`, `Ostrogradsky1850` (`Ostrogradsky.lean:53`), `Kaluza1921` (`KaluzaKlein/*.lean`), `Starobinsky1980` (`FRGravity.lean:72`), `BertottiIessTortora2003` (`BransDicke.lean:60`, `PPNParameters.lean:72`), and `Lanczos1938`/`Lovelock1972` (`Lovelock/*.lean`). These need the printed articles, which are not available offline.

- [x] **12. `proof-quality-and-speed`** *(Proofs #2, #3, #4, #5 — 8 suggestions in `3540573f` audit)* — All items closed: `3540573f` (Lovelock closed forms, Kerr fast zero-clearing, `sum_fin5_split`, `christoffel_diag`, FLRW derivative helpers, symmetric-inverse reuse, `simp_all` removal), `5daa23b8` (smul, chart restatements, helper extraction, `metricInv_offdiag`), `d3fbef52` (Reissner–Nordström component API, Kerr heartbeat split), and `253b8790` (FLRW/Nordström/FLRW-torsion case splits):
  - [x] `PhyslibAlpha/Relativity/General/ReissnerNordstrom/Basic.lean:313` *(Proofs #2)* — `metricTrace_smul` now takes `c • A` (the pointwise form became `metricTrace_smul_fun`), and `maxwellStressEnergy_trace_zero` is a single `rw` chain with no `change`.
  - [x] `PhyslibAlpha/Relativity/General/ReissnerNordstrom/Basic.lean:331` *(Proofs #3)* — `maxwellFieldInvariant_coulomb`, `maxwellStressEnergy_apply`, and `maxwellStressEnergyGaussian_apply` state the component forms, so `einsteinTensor_eq_maxwell_raw` rewrites through them instead of unfolding the stress-energy tensor.
  - [x] `PhyslibAlpha/Relativity/Metrics/StaticSphericalMetric/Christoffel.lean:212` *(Proofs #3)* — Both this lemma and `PhyslibAlpha/Relativity/Modified/Nordstrom.lean:177` now use `CoordinateMetric.christoffel_apply` with `toCoordinateMetric_g`/`toCoordinateMetric_ginv` instead of `rw [show ... from rfl]`.
  - [x] `PhyslibAlpha/Cosmology/FLRW/FriedmannEquations.lean:171` *(Proofs #4)* — The two rescaling equivalences are now `coordinateTime_firstOrder_iff` and `coordinateTime_secondOrder_iff`, and the main proof closes with `and_congr` of the two.
  - [x] `PhyslibAlpha/Cosmology/FLRW/PerfectFluid.lean:154` *(Proofs #4)* — The shared algebra is now the private lemma `spatial_coef_eq`, used by `einsteinTensor_spatial_iff_friedmann` and by the `hcoef` step of `einsteinTensor_iff_friedmann`.
  - [x] `PhyslibAlpha/Relativity/Modified/Lovelock/ConstantCurvature.lean:125` *(Proofs #4)* — The inner contraction is now the private lemma `rUp_inner_constantCurvature`, reused by `riemannSq_constantCurvature`.
  - [x] `PhyslibAlpha/Relativity/General/Kerr/Christoffel.lean:160` *(Proofs #5)* — `christoffel_eq_raw` is now four private lemmas `christoffel_eq_raw_k0…k3` (one per upper index) plus a dispatcher, and the `maxHeartbeats 1000000` override is gone.
  - [x] `PhyslibAlpha/Cosmology/FLRW/Christoffel.lean:310` *(Proofs #5)* — `simp_all [metricInv]` replaced by `@[simp] metricInv_offdiag` lemmas (`FLRW/Basic.lean`, `StaticSphericalMetric/Basic.lean`, `Nordstrom.lean`), and the 64-way `fin_cases` is split into one private lemma per upper index here, in `Nordstrom.lean:182`, and in `Teleparallel/FLRWTorsion.lean:204`.

- [ ] **14. `basic-foundations-mathlib-and-namespaces`** *(Basic #2, #4, #5, #6, #7, #8 — 9 suggestions)*:
  - [x] **Whole change** *(Basic #4)* — `PhyslibAlpha/Particles/BeyondTheStandardModel/TwoHDM/Invariants.lean` restored to its merge-base content, so the branch no longer carries that unrelated diff (`c3b44b7e`). *(The four `Physlib/` diffs are out of scope: `Physlib` is not modified on this branch.)*
  - [~] `PhyslibAlpha/Cosmology/FLRW/Basic.lean:282` *(Basic #2)* — `RegularPoint` threaded through every curvature lemma: the generic `StaticSphericalMetric.{riemann_eq_data,ricciTensor,ricciScalar,einsteinTensor}` and `FLRWSpacetime.{riemann_eq_data,ricciTensor,ricciScalar,einsteinTensor}` (`8fc26100`), then the SdS/Schwarzschild/RN wrappers (`59471724`); only the two differentiability hypotheses stay explicit, and the private `*_raw` lemmas keep the scalar form. Checked: the shared static-spherical boilerplate is already thin delegation — `SchwarzschildSpacetime`, `SchwarzschildDeSitterSpacetime`, and `ReissnerNordstromSpacetime` each define `metric`, `metricInv`, and `toCoordinateMetric` as one-line `S.toStaticSpherical.*` wrappers behind `rfl` simp lemmas, so no formula is duplicated and removing the wrappers would only push `S.toStaticSpherical.metric` into every call site.
  - [ ] `PhyslibAlpha/Relativity/Modified/KaluzaKlein/KaluzaMiracle.lean:80` *(Basic #2)* — Derive `ricci44` and `ricci5DHorizontal` from the 5D metric in `KaluzaKlein/Basic.lean` (and connect `FRGravity.lean` `box`/`d2` parameters to the derivative/d'Alembertian API) where feasible rather than hardcoding component formulas separately.
  - [ ] `PhyslibAlpha/Relativity/Modified/BransDicke.lean:92` *(Basic #5)* — Eliminate remaining raw-vs-structure duplicates (`gamma`/`coupling` vs `BransDickeTheory.*`; `KaluzaKlein/Basic.lean` `kkMetric`/`kkMetricInv`; `EinsteinCartan/Basic.lean` `torsion`; `EinsteinCartan/Contorsion.lean`; `Linearized/TraceReversed.lean`) and bundle bare parameters in `ChameleonScreening.lean:105-226`.
  - [x] `PhyslibAlpha/Relativity/General/ReissnerNordstrom/Basic.lean:423` *(Basic #6)* — `ricciTensor`, `ricciScalar`, and `einsteinTensor_eq_maxwell` moved from Section C into Section B, right after the private `*_raw` lemmas they restate (`c4b1366f`); `maxwellStressEnergyGaussian` and its `1 / (4π)`-scaling lemma moved to `Tensors/MaxwellStressEnergy.lean` as its Section B (`6314a14a`).
  - [x] `PhyslibAlpha/Relativity/Metrics/Einstein.lean:76` *(Basic #6)* — `christoffel_const`, `riemann_const`, `ricciTensor_const`, and `ricciScalar_const` moved next to their definitions in `Metrics/{Christoffel,Riemann,Ricci}.lean`; `Einstein.lean` keeps only `einsteinTensor_const` (`d7cc980e`).
  - [~] `PhyslibAlpha/Relativity/Modified/KaluzaKlein/Basic.lean:200` *(Basic #7)* — `sum_fin5_split` is now proved by `rw [Fin.sum_univ_castSucc]` instead of the `Fin.sum_univ_five` case split. The wrapper is kept because the callers' `h1` rewrites are stated at `⟨x.val, _⟩` indices and fail to match Mathlib's `Fin.castSucc`-indexed form.
  - [~] `PhyslibAlpha/Relativity/Metrics/Basic.lean:66` *(Basic #7)* — Attempted and reverted: `Matrix.mul_eq_one_comm` does not resolve for `Tensor2 n` here (no `IsDedekindFiniteMonoid` instance in scope), so the local lemma stays until that instance is available.
  - [x] `PhyslibAlpha/Relativity/Metrics/Christoffel.lean:52` *(Basic #8)* — The `CoordinateMetric.*` blocks are gone from `Metrics/{Christoffel,Riemann,Ricci,Einstein}.lean`, which now hold a single `namespace CoordinateCurvature` section each; the chart-level API lives in `Metrics/CoordinateMetric.lean`; paths aligned for `Metrics/SpaceTimeDerivBridge.lean` and `General/InitialData/CovariantDerivTensor2.lean` (`ad75aa1b`).

- [ ] **15. `docs-terminology-stale-headers-and-vars`** *(Documentation #1–#5; Basic #1, #10 — 12 suggestions)*:
  - [x] `PhyslibAlpha/Cosmology/FLRW/Christoffel.lean:555` *(Doc #2)* — Both docstrings now say "comoving coordinate time", matching `g_{00} = -1`.
  - [x] `PhyslibAlpha/Relativity/Modified/EinsteinCartan/ModifiedTorsion.lean:20` *(Doc #2)* — One notation throughout: `T^k_{ij}` for torsion, `T_i = T^m_{im}` for its trace, `S^k_{ij} = T^k_{ij} + δ^k_i T_j - δ^k_j T_i` for the modified torsion, and `S^k_{ij} = κ spin^k_{ij}` for Cartan's equation in the overview, Section A, and every docstring (`f3771c38`).
  - [x] `PhyslibAlpha/Relativity/General/Schwarzschild/Basic.lean:25` *(Doc #4)* — Overview and key results now claim only `Γ^t_{tr}` and `Γ^r_{rr}`, the two `*_from_metric` lemmas that actually exist in the file.
  - [x] `PhyslibAlpha/Cosmology/FLRW/Christoffel.lean:47` *(Doc #4)* — Both the overview step 3 and the key-results entry now name `FLRWSpacetime.riemann_eq_data_raw`.
  - [x] `PhyslibAlpha/Relativity/Modified/KaluzaKlein/KaluzaMiracle.lean:31,37` *(Basic #1; Doc #2)* — The prose now says `D.metric`, and the key-results entry names `Tensors/MaxwellStressEnergy.lean` as the home of the three Maxwell declarations.
  - [x] `PhyslibAlpha/Relativity/Modified/Lovelock/Basic.lean:27` *(Doc #3)* — Key results split into the structure, the contracted invariants (`ricciMixed`, `ricciScalar`, `ricciSq`, `riemannSq`), and the quadratic pair, with no duplicates.
  - [x] `PhyslibAlpha/Relativity/General/API-map.md:142,158` *(Doc #1)* — The 5D metric is now described as built from `g_{μν}`, and the dRGT potential from "elementary symmetric polynomials of trace powers".
  - [x] `PhyslibAlpha/Relativity/Metrics/Christoffel.lean:89` *(Doc #1)* — Lean-internal wording replaced: the "Unfolding lemma for ..." docstrings now say which tensor of the metric field the chart-level operator is, "bundled regular chart point" became "a point of the regular chart", "definitionally" was dropped, and the `ModifiedTorsion` "algebraic inverse helper" note now states the torsion formula it proves (`162ccf4f`).
  - [~] `PhyslibAlpha/Cosmology/FLRW/Basic.lean:29` *(Doc #3)* — The duplicated overview paragraph is trimmed; the `FLRW/Curvature.lean:63` Section A prose is still to differentiate.
  - [ ] `PhyslibAlpha/Relativity/Metrics/CoordinateMetric.lean:54` *(Doc #5)* — Close `/-! ... -/` after `## iv. References` (line 52) rather than embedding `## A.` inside the module header; add prose to empty section blocks in `Lovelock/ConstantCurvature.lean:52-56` and `Tensors/RiemannTensor.lean:79-83,123-127`.
  - [ ] `PhyslibAlpha/Relativity/Modified/KaluzaKlein/Basic.lean:332` *(Basic #10)* — Remove unexplained Lean binder variables from docstrings (`D`, `T`, `M`, `r`, `P`, `G`, `C`, `u`, `x`, `S.toCoordinateMetric`, etc.) across `KaluzaKlein/Basic:332`, `MOG:95`, `ChameleonScreening:92`, `Linearized/Basic:71`, `GeodesicSystem:93`, `PPNParameters:159`, `EinsteinAether:176`, `Metrics/Basic:175`, and `*_toCoordinateMetric_g/_ginv` lemmas.

- [ ] **16. `file-organization-and-naming-alignment`** *(Organization #1, #2, #3 — 15 suggestions)*:
  - [x] `PhyslibAlpha/Relativity/Metrics/CoordinateMetric.lean:8` & `Metrics/Basic.lean:66,150` *(Org #2, #3)* — `CoordinateMetric`, `CoordinateMetric.metricTensor` and the chart-level connection/geodesic/curvature operators live in `Metrics/CoordinateMetric.lean` (`ad75aa1b`); `Metrics/Basic.lean` keeps only `MetricTensor` and its contraction lemmas, with the structure opening the section and `mul_eq_one_of_isSymm_of_mul_eq_one` after them (`f3771c38`).
  - [x] `PhyslibAlpha/Relativity/Metrics/CoordDeriv.lean:51` *(Org #3)* — Renamed to `Metrics/SpaceTimeDerivBridge.lean`, since the file held only `coordDeriv_eq_spaceTime_deriv` while `coordDeriv` itself lives in `Mathematics/Calculus/CoordDeriv.lean`; `Metrics/CovariantDerivTensor2.lean` moved to `General/InitialData/` to match its namespace (`ad75aa1b`).
  - [ ] `PhyslibAlpha/Relativity/Metrics/Ricci.lean:61` *(Org #2)* — Separate `CoordinateCurvature.ricciScalar` and `CoordinateMetric.ricciScalar` (lines 61, 78) from `Ricci.lean` (or merge with `Metrics/RicciScalar.lean`).
  - [ ] `PhyslibAlpha/Cosmology/FLRW/Basic.lean:77` *(Org #1)* — Build FLRW coordinate metric and curvature API directly on `Physlib`'s `Cosmology.FLRW` structure (`FLRW.a` / `FLRW.geometry`) rather than duplicating `FLRWSpacetime`.
  - [x] `PhyslibAlpha/Cosmology/FLRW/PerfectFluid.lean:87` & `StaticSphericalMetric/RicciCurvature.lean` *(Org #2, #3)* — Merged: `FLRW/PerfectFluid.lean` is Section A of `FriedmannEquations.lean` and `StaticSphericalMetric/RicciCurvature.lean` is Section C of `StaticSphericalMetric/Christoffel.lean`; headers, imports and API-map entries merged and renumbered (`f3771c38`).
  - [x] `PhyslibAlpha/Cosmology/FLRW/Curvature.lean:1` *(Org #3)* — The merge of `FLRW/Curvature.lean` into `FLRW/Christoffel.lean` (`f3771c38`) was reversed on review: a module named after the tensors it defines is what Org #3 asks for, so `ricciTensor`/`ricciScalar`/`einsteinTensor`/`riemann_eq_data` are back in `FLRW/Curvature.lean`, with `FriedmannEquations` importing the curvature module and the API map entry split (`7de4c843`).
  - [~] `PhyslibAlpha/Relativity/General/Schwarzschild/CoordinateCurvature.lean:70` *(Org #3)* — The wrapper lemmas no longer shadow the component-level names: `SchwarzschildSpacetime.{ricciTensor_eq_zero,ricciScalar_eq_zero,einsteinTensor_eq_zero}`, `SchwarzschildDeSitterSpacetime.{ricciTensor_eq,ricciScalar_eq,einsteinTensor_eq}`, and `ReissnerNordstromSpacetime.{ricciTensor_eq,ricciScalar_eq_zero}` (`8046e2b0`). `SchwarzschildSpacetime.toDeSitter` and its `Λ = 0` reductions moved to `SchwarzschildDeSitter/Basic.lean`, beside the structure they produce and `metricFn_zero_lambda` (`2e271cc2`).
  - [ ] `PhyslibAlpha/Relativity/General/Schwarzschild/ElectricWeyl.lean:169` & `SchwarzschildDeSitter/DeSitterFrame.lean:86` *(Org #2)* — Group `tidalPart` and `frameRiemann` at top (or split) in `ElectricWeyl.lean`; regroup or split the 7 interleaved definitions in `DeSitterFrame.lean` (lines 86–347).
  - [x] `PhyslibAlpha/Relativity/General/ReissnerNordstrom/Basic.lean:110` *(Org #2)* — `maxwellStressEnergyGaussian` lives in `Tensors/MaxwellStressEnergy.lean` (`6314a14a`), and the chart operations (`metricFn`, `coulombFieldStrength`, `horizonPlus`/`horizonMinus`) are now grouped in Section A before the curvature lemmas, with Section B/C keeping only their consequences (`8046e2b0`).
  - [ ] `PhyslibAlpha/Relativity/Modified/Teleparallel/Basic.lean:75` & `Modified/ChameleonScreening.lean:105` *(Org #2)* — Move `superpotential` (line 136) and `torsionScalar` (line 159) before Weitzenböck lemmas or into named files; group the 6 helpers in `ChameleonScreening.lean` (lines 105–193) directly after `ChameleonModel` (or as methods).
  - [ ] `PhyslibAlpha/Relativity/Modified/MassiveGravity/VDVZ.lean:74` & `KaluzaKlein/KaluzaMiracle.lean:80` *(Org #3)* — Move or rename theorem-named files: put `grPropagatorCoupling`/`massivePropagatorCoupling`/`staticSource` into `MassiveGravity/Basic.lean` (or rename `VDVZ.lean`), and put `KaluzaKleinData.{ricci44,ricci5DHorizontal,scalar5D}` into `KaluzaKlein/Basic.lean` (or definition-named files).

- [ ] **17. `scope-naming-polish`** *(Scope #2 — 5 suggestions)*:
  - [x] `PhyslibAlpha/Relativity/Metrics/StaticSphericalMetric/Basic.lean:79` — Renamed `StaticSpherical.Metric` → `StaticSphericalMetric` (declaration, namespace `GeneralRelativity.StaticSpherical.StaticSphericalMetric`, and explicit references; dot notation unchanged) so it no longer collides with Mathlib's `Metric` namespace; `API-map.md` updated (`32b4555a`).
  - [x] `PhyslibAlpha/Relativity/General/FrameKretschmann.lean:54` — `RiemannTensor.frameKretschmannScalar` renamed `frameSumOfSquares` (with `electricWeyl_frameSumOfSquares_eq`, `SchwarzschildDeSitterSpacetime.frameSumOfSquares`), and the module prose now says the sum reproduces the Kretschmann scalar only when the gravitomagnetic components vanish (`8e70f8b5`).
  - [x] `PhyslibAlpha/Relativity/Modified/BransDicke.lean:169` — `BransDicke.coupling` / `BransDickeTheory.coupling` renamed `effectiveCouplingRatio` (with `effectiveCouplingRatio_eq_one_add`, `effectiveCouplingRatio_bounds`), matching the "effective gravitational coupling ratio" the docstrings already used; no call sites outside the file (`8e70f8b5`).
  - [x] `PhyslibAlpha/Relativity/Modified/KaluzaKlein/KaluzaMiracle.lean:80` — Section A now states that the dilaton is fixed to `φ = 1` throughout the file, so `ricci44`, `ricci5DHorizontal`, and `scalar5D` are the unit-dilaton components and the running-dilaton terms are out of scope; names kept (`8e70f8b5`).
  - [x] `PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/CoordinateCurvature.lean:365` — `frameScale`'s docstring now says it is not `S.metricInv`: the inverse metric carries `g^{00} = -(f)⁻¹`, while the frame components are compared with `η = diag(-1, 1, 1, 1)` and need the positive scale (`8e70f8b5`).

---

## Deferred

- [~] **13. `pr-splitting-strategy`** *(Basic #4 — deferred per user request)* — Split the PR into small coherent PRs (core foundations → `GravitationalConstant` → `StaticSphericalMetric`/black holes → `Kerr` → `FLRW` → `Linearized` → `GeodesicSystem`/`InitialData` → `Modified` gravity) and drop the unrelated diff outside gravity (`PhyslibAlpha/Particles/BeyondTheStandardModel/TwoHDM/Invariants.lean`); the four `Physlib/` diffs are out of scope.

---

## Handbook alignment re-run (branch vs `master` at `7910f51f`, 86 commits)

Six-pass `/handbook-alignment` report over the 90 Lean files of `PhyslibAlpha` in the branch diff
(raw outputs and generated report under `/tmp/hb/`): Basic 3, Documentation 4, Organization 4,
Proofs 4, Scope 4, References 3. Still diverging:

- [x] *Basic #7* — `14991fcd`: `mul_eq_one_of_isSymm_of_mul_eq_one` and `sum_fin5_split` moved to
  `PhyslibAlpha/Mathematics/MatrixInverse.lean` and `FinSum.lean`, with the five consuming files
  and `KaluzaKlein/Basic.lean` importing them directly. Followed by `416ee372`, which dropped the
  matrix wrapper in favour of Mathlib's `Matrix.mul_eq_one_comm` (it needs no symmetry hypothesis)
  and deleted `MatrixInverse.lean`; `FinSum.lean` stays.
- [x] *Basic #8* — `a15ea9b0`: the embedding moved to
  `SchwarzschildDeSitter/Embedding.lean`, so `Basic.lean` opens only its own namespaces; the
  Schwarzschild coordinate-curvature file imports the new module, and API-map entry 88 covers it.
- [x] *Basic #10 / Doc #3* — `61505fa6` removed the inventory-of-declarations sentence from the
  `Modified/MOG.lean` overview, and `bff75e60` replaced the variable `S.` in the
  `SchwarzschildDeSitter/CoordinateCurvature.lean` docstrings with the quantity each describes.
- [x] *Org #3* — `bed338be`: `FrameKretschmann.lean` renamed to `FrameSumOfSquares.lean`, with the
  root file, `DeSitterFrame`, `ElectricWeyl` and API-map entry 81 updated.
- [x] *Proofs #3* — `c2d66bd1`: `@[simp]` lemmas `rs_def`, `chia_def`, `cosChia_def`,
  `pressure_def`, `gttIn_def`, `grrIn_def`, `gttOut_def`, `grrOut_def` replace all 20 `unfold`
  calls; the four `gttGlue`/`grrGlue` coincidences now rewrite with `ite_eq_left le_rfl`.
- [x] *Results from `../physics`, Kretschmann* — `6ebc8b50` carries over
  `gravitation/Gravitation/KretschmannTotal.lean` as `kretschmann_scalar_total`
  (`Schwarzschild/ElectricWeyl.lean`) and `kretschmann_total`
  (`SchwarzschildDeSitter/DeSitterFrame.lean`), renamed to the branch's `frameSumOfSquares` API.
- [x] *Results from `../physics`, field theories* — `1514f856` adds the STVG and TeVeS action
  densities, residual field equations and solution structures of `MogFieldTheory.lean` and
  `TeVeSFieldTheory.lean` to the existing `Modified/MOG.lean` and `Modified/TeVeS.lean`.
- [x] *Results from `../physics`, charts* — `4be8ddb1` ports `ManifoldInterface.lean` to
  `Relativity/General/ManifoldInterface.lean` (`ChartSpacetime`, `PartialChartSpacetime`,
  `PartialChartTransition`, the causal classes, the chart isometries and the Mathlib bridge) and the
  ingoing Eddington–Finkelstein and Kruskal–Szekeres charts to
  `Relativity/General/Schwarzschild/`, rewritten to the branch's module-doc and `lemma`
  conventions. The EF exterior overlap stays out: it needs `SchwarzschildManifold.lean` (470) and
  hence the initial-data stack (import closure 6 856 lines); the tortoise coordinate is kept.
- [x] *Results from `../physics`, modified gravity* — `4391dfb8` adds `Modified/DiracCounting.lean`,
  `Modified/MondFieldTheory.lean` and `Modified/AqualVariation.lean` (API-map 92–94).
- [x] *Results from `../physics`, Bianchi* — `c419c3c1` ports `Bianchi.lean` to
  `Relativity/General/Bianchi.lean` (API-map 95).
- [x] *Results from `../physics`, FLRW perturbations* — `e13e6636` ports `Perturbation.lean` to
  `Cosmology/FLRW/Perturbation.lean` (API-map 96).
- [x] *Results from `../physics`, wave and initial-data stack* — `277cc874` ports `Divergence3D`,
  `WaveCauchy`, `ReducedWave3D`, `WaveEnergy`, `WaveEnergy3D`, `WaveEnergy3DConservation`,
  `WaveEnergy3DWave`, `WaveUniqueness`, `WaveUniqueness3D`, `InitialDataInterface` and
  `SobolevInitialData` to `Relativity/General/InitialData/` (API-map 97–107).
- [x] *Results from `../physics`, Schwarzschild manifold and EF overlap* — `768fbca3` ports
  `SchwarzschildManifold.lean` (API-map 108) and restores the EF overlap transition
  (`schwarzschildToEF`, `transitionJacobian`, `schwarzschild_eq_pullback`,
  `schwarzschildEFTransition`) that the earlier chart port had to drop.
- [x] *Results from `../physics`, remaining* — done across `5153a50b`, `5b43a6a4`, `710db324`: the
  development layer is ported — `ManifoldSobolev`, `CauchyInterfaces`, `LinearizedWaveGauge`,
  `ConformalDecomposition`, `ReducedCauchy`, `MaximalDevelopment`, `GaugeRecovery`,
  `ExplicitDevelopments` — with `Space3` adapted to `SpaceChart`, upstream `theorem`s converted to
  `lemma`, placeholder `None` references replaced by standard citations (Carroll, Wald, Evans,
  O'Neill), and API-map entries 107–114 added. Full `lake build PhyslibAlpha`, `module_doc_lint`,
  `theorem_lint` and `alphaPythonLinters.sh` pass (only the pre-existing `Bianchi.lean` length
  warning remains).
- [ ] *References #4/#5* — the unpinned sources listed under Task 5 (Nordström,
  Ostrogradsky, Starobinsky, Bertotti–Robinson, Lanczos, Lovelock) and the BIPM `#page=` numbering.

---

## Handbook alignment re-run (`2026-11-28`, PR head `f3c5362d`)

Addressed so far: `1a50922d`, `235fdd79`, `1820345c`, `ab2a30f9`, `1d0d6d35`, `1b0c2395`,
`80310d87`, `8faf7554`, `2a1a3d90`, `1a37efe7`, `e7403128`, `8a13c4b0`, `7885325c`, `546706d5`,
`8e4011ba` (Bianchi refactor note and `pd_*` docstrings, the
M2 shorthand, the Evans bib entry and keys, the two Kruskal proof comments, the wave-stack
key-results descriptions, the MOND/Dirac/Schwarzschild citations, the merge of the three
3D-energy modules, the sine-square slice derivative and Sobolev overview, the `SpaceChart` and
`ConstraintCount` naming, the Kruskal overview trim, the chart-level ADM wording in the
initial-data docstrings, the `pd_*` deduplication, the `contracted_bianchi` split, and the
branch-wide long-line pass).

Note: `./scripts/lint/required/alpha/alphaPythonLinters.sh` reported 162 `ERR_LIN` long lines on
this branch. These are now cleared: `546706d5` wrapped `Bianchi.lean` and `AqualVariation.lean`
(and fused the non-terminal `simp` there) and `8e4011ba` wrapped the remaining fourteen files, so
`lint-style.py` reports no `ERR_LIN` at all. Two `ERR_NUM_LIN` file-length reports remain
(`Bianchi.lean` 1617 lines, `AqualVariation.lean` 1638 lines, limit 1500); those need the planned
splits (Section E of `Bianchi` into its own module, and the AqualVariation analysis lemmas moved
to `Mathematics/`), not reformatting.

`/handbook-alignment` pass over PR #2132 at its pushed head: `refs/pull/2132/head` fetched
from GitHub is `f3c5362d`, identical to the local branch head, so this pass covers exactly
what the PR contains (base `master` merge-base `7910f51f`, 115 files, 30 419 insertions,
31 390 diff lines; six handbook files, 30 suggestions). Scores: Basic 2, Documentation 3, Organization 3,
Proofs 2, References 2, Scope 3. The previous audit's scores were Basic 2, Documentation 3,
Organization 3, Proofs 3, References 3, Scope 4; `Proofs`, `References` and `Scope` fell because
the new ports brought long proofs, uncited modules and invented names.

- [ ] **18. `handbook-basic-2026-11-28`** *(Basic 2/5)*
  - [x] `InitialData/SobolevInitialData.lean:76` *(Basic 7)* — done in `8faf7554`: the lemma is
    now `CoordinateCurvature.hasDerivAt_sin_sq` in `Mathematics/Calculus/CoordDeriv.lean`, beside
    `slice_differentiableAt`, so the physics file only calls it.
  - [x] `General/Bianchi.lean:77-167` *(Basic 7)* — done in `8a13c4b0`: the twelve `pd_*` lemmas
    are deleted, `coordDeriv_mul` and `coordDeriv_neg` were the only rules the shared API lacked
    and now live in `Mathematics/Calculus/CoordDeriv.lean`, and every `Bianchi` call site uses
    the `CoordinateCurvature` lemmas (with `slice_differentiableAt` where a pointwise hypothesis
    becomes a slice hypothesis).
  - [x] `Modified/AqualVariation.lean:278,1243` *(Basic 2)* — done (working tree, builds):
    `sum_link_mul_difference` and `secondDifference_tendsto` are general analysis; they now live
    without AQUAL parameters in `PhyslibAlpha/Mathematics/GraphDivergence.lean`
    (`GraphDivergence.discreteDivergence`, `GraphDivergence.sum_link_mul_difference`) and
    `PhyslibAlpha/Mathematics/Analysis/SecondDifference.lean` (`secondDifference`,
    `secondDifference_tendsto`, `secondDifference_tendsto_of_tendsto_site`), both imported into
    `PhyslibAlpha.lean`; `AqualVariation` only calls them.
  - [x] `Modified/MondFieldTheory.lean:60` *(Basic 5)* — done (working tree, builds): `a0`, `G`,
    `mu`, `F` are bundled in a `MondFieldTheory` structure (Section C), in the style of
    `BransDickeTheory`, with `MondFieldTheory.actionDensity` and `MondFieldTheory.fieldResidual`.
  - [x] `Modified/DiracCounting.lean:118` *(Basic 5)* — done (working tree, builds): the STVG and
    TeVeS field content is presented as `STVGContent` and `TeVeSContent` structures (with
    `VectorContent`) whose `count` projection reads off the degrees of freedom
    (`STVGContent.count_dof`, `TeVeSContent.count_dof`); API-map entry 92 updated.
  - [x] Whole change *(Basic 12)* — done (working tree): every ported header that carried
    `Copyright (c) 2026 The Gravitation formalisation contributors.` now reads
    `Copyright (c) 2026 Alex Vergara Gil.` (20 files: `General/Bianchi.lean`,
    `General/InitialData/*`, `General/Linearized/LinearizedWaveGauge.lean`, `General/ManifoldInterface.lean`,
    `General/Schwarzschild/{EddingtonFinkelstein,KruskalSzekeres,SchwarzschildManifold}.lean`); no
    file elsewhere in the repository names them.
  - [ ] Whole change *(Basic 4)* — split into coherent PRs (charts → Bianchi → wave stack →
    initial data → modified gravity).
- [ ] **19. `handbook-documentation-2026-11-28`** *(Documentation 3/5)*
  - [x] `InitialData/InitialDataInterface.lean:21,120` and `SobolevInitialData.lean:31`
    *(Doc 2)* — done in `235fdd79`: the "M2 layer" shorthand is gone from both overviews.
  - [x] `General/Bianchi.lean:69` *(Doc 4)* — done in `1a50922d`: the refactor note is removed and the
    eight `pd_*` lemmas now carry docstrings.
  - [x] `InitialData/SobolevInitialData.lean:5` *(Doc 4)* — done in `8faf7554`: the overview
    opens with the Cauchy problem and the need for Sobolev control before the inventory, and the
    key results say what each norm, embedding and estimate gives.
  - [x] `InitialData/WaveEnergy.lean:26` and the wave-stack siblings *(Doc 1)* — done in `1d0d6d35`:
    every key-results entry in the nine wave modules now states what the result is.
  - [x] `Schwarzschild/KruskalSzekeres.lean:21` *(Doc 3)* — done in `1a37efe7`: the overview keeps
    the coordinates and the horizon regularity and drops the explicit conformal factor and the
    singularity paragraph.
- [ ] **20. `handbook-organization-2026-11-28`** *(Organization 3/5)*
  - [x] `InitialData/WaveUniqueness{,3D}.lean` *(Org 3)* — folded into `WaveEnergy{,3D}`: the
    duplicate `WaveSolutionOn`/`WaveSolutionOn.sub`/`wave_unique_of_same_data` and
    `WaveSolution3D`/`WaveSolution3D.sub`/`wave_unique3D_of_same_data` content was removed from
    the standalone files; both files deleted, `LinearizedWaveGauge.lean` now imports
    `WaveEnergy3D`, `PhyslibAlpha.lean` imports trimmed, API-map entries 100–101 merged with
    102–103 and renumbered (working tree, uncommitted).
  - [x] `InitialData/WaveEnergy3DConservation.lean` and `WaveEnergy3DWave.lean` *(Org 3)* — done in
    `80310d87`: both are now sections B and C of `WaveEnergy3D.lean`, and API-map entries 101–103
    are one entry.
  - [x] `InitialData/InitialDataInterface.lean` *(Org 2)* — renamed to `ChartInitialData.lean`, moved
    first among InitialData imports in `PhyslibAlpha.lean`, API-map entry 102 updated (working tree,
    uncommitted).
  - [ ] `General/Bianchi.lean` *(Org 3)* — split by object or rename after an operator.
  - [x] `InitialData/Divergence3D.lean` *(Org 3)* — done in `963057c5`: renamed to
    `InitialData/SpaceChart.lean` after its key definition `SpaceChart`; importers
    (`WaveEnergy3D`, `ReducedWave3D`), `PhyslibAlpha.lean` and API-map entry 97 updated.
  - [x] `Modified/DiracCounting.lean:88` *(Org 2)* — already at the top: the counting structure
    and its `dof` are Section A before any application, and the applications follow in Section B
    (checked at `2a1a3d90`; no move was needed).
- [ ] **21. `handbook-proofs-2026-11-28`** *(Proofs 2/5)*
  - [x] `General/Bianchi.lean:964` *(Proofs 4)* — done in `7885325c`: the proof is six lemmas
    (`coordDeriv_ginv`, `sum_covDerivRiemann_second_bianchi`,
    `sum_ginv_covDerivRiemann_ricci`, `sum_ginv_covDerivRiemann_scalar`,
    `sum_ginv_riemann_ricci`, `sum_ginv_covDerivRiemann_ricci_div`) and `contracted_bianchi`
    is 26 lines of assembly. The largest extracted lemma is 223 lines and could be split again
    along its `hstep`/`hstep2` steps.
  - [x] `General/Bianchi.lean:454,321` *(Proofs 4)* — done in `1578d78a` + `22abe72d`:
    `inv_metric_compat` now uses `coordDeriv_g_eq` (component form of metric compatibility);
    `riemann_lower_skew_first` uses `coordDeriv_g_eq_nhds` and `coordDeriv_coordDeriv_g`
    (second coordinate derivative of the metric), replacing the inline `hmc_nhds`/`h2pd` haves.
  - [x] `General/Bianchi.lean` *(Proofs 3)* — done (working tree): added the component projection
    lemmas `covDeriv2_eq`, `covDeriv2Up_eq`, `covDerivRiemann_eq`, `covDiv2_eq` and
    `riemann_apply`, and replaced every `unfold riemann`/`unfold covDeriv2`/`unfold covDeriv2Up`
    in `Bianchi.lean` and `BianchiContracted.lean` by those rewrites (`riemann_skew_last`, the
    commutator lemma and `second_bianchi`'s inner step).  Only a `change` restating a notation
    remains; API-map 95 lists the new lemmas.
  - [x] `InitialData/SobolevInitialData.lean` *(Proofs 3)* — done in `e3760897` + `bbcf03ff`: the 12
    `unfold coordDeriv; rw [hfun]` steps use `coordDeriv_eq_of_slice_eq`, and the norm/energy
    operators (`sobolevH1NormSq1D/3D`, `waveEnergy3DIntegrand`, `norm3Sq`, `spatialLaplacian3D`) are
    rewritten via their equation lemmas; no `unfold` remains (only 6 irreducible `change`
    type-ascriptions after `fin_cases`/quadratic-form normalisation).
  - [x] `InitialData/WaveUniqueness{,3D}.lean` *(Proofs 4)* — done in `8f7a0485`: the inline
    difference-solution construction is extracted into `WaveSolutionOn.sub` and
    `WaveSolution3D.sub`, so each general-data uniqueness proof just applies the zero-data
    theorem to the extracted difference solution.
  - [x] `Schwarzschild/KruskalSzekeres.lean:230,269` *(Proofs 1)* — done in `1820345c`: the comments
    are gone; the `let` bindings and the bound hypotheses already name the witnesses.
  - [x] `Schwarzschild/EddingtonFinkelstein.lean:253,263,281` *(Proofs 5)* — done (working tree): the
    three `set_option maxHeartbeats` lines (two `in`-scoped at 2 000 000 and the file-wide 4 000 000)
    are all gone; the proofs already reduce each component through the `apply` lemmas
    `christoffel_eq_efGamma` and `coordDeriv_efGamma_eq`, and the module builds in 21 s (55 s CPU)
    under the default limit.
- [ ] **22. `handbook-references-2026-11-28`** *(References 2/5)*
  - [x] `InitialData/*` *(Ref 2)* — done in `235fdd79` (bib entry, `SobolevInitialData`) and
    `ab2a30f9` (the nine wave modules).
  - [x] `InitialData/WaveEnergy*.lean`, `WaveUniqueness*.lean` *(Ref 1)* — the Evans key added in
    `ab2a30f9` covers these modules.
  - [x] `Modified/AqualVariation.lean` *(Ref 1)* — done in `1b0c2395`: full titles plus
    `[ref: BekensteinMilgrom1984]` and `[ref: Milgrom1983a]`.
  - [~] `Schwarzschild/SchwarzschildManifold.lean` *(Ref 5)* — `1b0c2395` added
    `[ref: wald_1984_general_relativity, Ch. 6]`; the page number is still open because Wald is not
    reachable offline.
  - [x] `Modified/DiracCounting.lean` *(Ref 1)* — done in `1b0c2395`: `Dirac1964Lectures` and
    `HenneauxTeitelboim1992` bib entries, both cited by key.
  - [x] `InitialData/SobolevInitialData.lean` *(Ref 4)* — done (working tree): `BrillLindquist1963`
    (Phys. Rev. 131, 471) and `Gourgoulhon2012` (LNP 846, arXiv gr-qc/0703035, Ch. 4, page-anchored)
    added to `docs/references.bib` and cited in the overview, in the Brill–Lindquist, the
    Schwarzschild–de Sitter slice and the flat FLRW constraint docstrings.
  - [x] `Schwarzschild/EddingtonFinkelstein.lean`, `KruskalSzekeres.lean` *(Ref 3)* — done (working
    tree): both overviews now state the conventions (signature `(-, +, +, +)`, positive `g_{vr} = 1`,
    `G = c = 1`) and say they are those of the cited Carroll and Wald, and that the Kruskal
    conformal factor `F` is not the `f = 1 - 2M/r`.
- [ ] **23. `handbook-scope-2026-11-28`** *(Scope 3/5)*
  - [x] `InitialData/Divergence3D.lean:50` *(Scope 2)* — done in `2a1a3d90`: renamed to
    `SpaceChart`, the spatial analogue of `SpacetimeChart`, and the docstrings say so.
  - [x] `Modified/DiracCounting.lean:88` *(Scope 2)* — done in `2a1a3d90`: renamed to
    `ConstraintCount`, with the structure docstring naming the field content and the `dof`
    docstring explaining why first-class constraints remove two degrees of freedom and
    second-class constraints one.
  - [x] `InitialData/InitialDataInterface.lean` *(Scope 2)* — done in `e7403128`: the
    `ManifoldSpacetime` and `ManifoldInitialData` docstrings now call themselves chart-level ADM
    data read in a single global chart, and say the type is not a smooth manifold; the type names
    stay because renaming them is the separate Organization item.
  - [x] `General/ManifoldInterface.lean:78` *(Scope 2)* — already stated: the `ChartSpacetime`
    docstring says it is "not a smooth manifold" and the overview says the file "does not claim a
    smooth manifold"; checked at `2a1a3d90`, no change needed.
  - [ ] Whole change *(Scope 1)* — discuss the remaining development layer (`MaximalDevelopment`,
    `GaugeRecovery`, …) before porting it.
  - [ ] Whole change *(Scope 1)* — confirm with maintainers that modified gravity stays in scope
    as a group.
