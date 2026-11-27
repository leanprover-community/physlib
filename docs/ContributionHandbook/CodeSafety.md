# Code safety

This page covers what kinds of code are allowed in the Physlib and PhyslibAlpha directories. Keeping the library purely mathematical keeps it focused, and it also guards against malware and other security risks.

<a id="mathematical-declarations"></a>

## 1. Definitions and lemmas should be mathematical

Everything in the Physlib and PhyslibAlpha directories should be mathematics: definitions, lemmas, theorems and the notation that goes with them. Code should not read or write files, access the network, start processes, or produce output such as HTML beyond the normal messages Lean gives. Notation is fine. Tactics run on top of IO, so whether code is allowed depends on what it does, not on its type.

<a id="human-checked-tactics"></a>

## 2. Tactics must be checked by a human

Tactics are allowed in both Physlib and PhyslibAlpha, but they are where the security risk lies, since a tactic can in principle do anything. In PhyslibAlpha, any new tactic must be read and understood by both its author and a maintainer before it is merged. Everything in Physlib is already reviewed, so this applies there by default.

<a id="proofwidgets"></a>

## 3. No ProofWidgets in PhyslibAlpha

`ProofWidgets` renders HTML and runs JavaScript in the reader's editor, so it is not allowed in PhyslibAlpha. In Physlib it is allowed after review.
