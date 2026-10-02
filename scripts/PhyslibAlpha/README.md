# Meta programs for PhyslibAlpha

As well as passing a one-look review, code in PhyslibAlpha has to pass a number of linters
which we describe in this file.

## Lean-based linters

### runPhyslibAlphaLinters
```
lake exe runPhyslibAlphaLinters
```
This picks up things like lack of doc-strings on definitions, or incompatible `@[simp]` attributes.

### auxillary_script_test
```
lake exe auxillary_script_test
```
This runs the auxiliary scripts which generate the website data. One of them imports `Physlib`,
`QuantumInfo` and `PhyslibAlpha` together, so this fails if a declaration in PhyslibAlpha has the
same name as one in `Physlib` or `QuantumInfo`. See [../README.md](../README.md).

## Python-based linters

### alphaFileImports.py

```
./scripts/PhyslibAlpha/alphaFileImports.py
```
This checks that all PhyslibAlpha files are included in the file `PhyslibAlpha.lean`,
even if commented out based out with info of the commit where they broke.

### noAlphaImports.py

```
./scripts/PhyslibAlpha/noAlphaImports.py
```
This checks that no file in `./Physlib` or `./QuantumInfo` imports a file from `./PhyslibAlpha`.

### alphaPythonLinters.sh

```
./scripts/PhyslibAlpha/alphaPythonLinters.sh
```
Checks things like line length, `simp`s which are not `simp only` or final tactics.
