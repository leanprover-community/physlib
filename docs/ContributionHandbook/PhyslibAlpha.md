# PhyslibAlpha

This page sets out what PhyslibAlpha is for, what it accepts and what it doesn't.

## Contents

1. [PhyslibAlpha is a connected corpus of physics](#connected-corpus)
2. [Integrate with the library, don't move a project in](#integrate-dont-import)
3. [Expect a one-look review](#one-look-review)
4. [Run the handbook alignment skill on agent-written code](#handbook-alignment)
5. [Results are meant to move into Physlib](#move-into-physlib)

<a id="connected-corpus"></a>

## 1. PhyslibAlpha is a connected corpus of physics

PhyslibAlpha aims to build a connected corpus of physics formalizations that follows the best practices learned from Physlib. In doing so it acts as a guide to the new definitions and results that could be added to Physlib, and to the best approaches for formalizing them. It also adds new lemmas about Physlib's existing trusted definitions, giving others a larger pool of results to use in their own formalizations. Contributions are accepted when they fit with the existing library and clearly work towards this purpose.

<a id="integrate-dont-import"></a>

## 2. Integrate with the library, don't move a project in

PhyslibAlpha does not accept code dumps: standalone projects built elsewhere and then moved into PhyslibAlpha wholesale. Doing so loses one of the main benefits of PhyslibAlpha, a connected library where results are not reproduced by several people. Code written with the help of AI is fine, as long as it is integrated with the project. Other parts of this handbook describes what integration looks like in practice.

<a id="one-look-review"></a>

## 3. Expect a one-look review

PRs to PhyslibAlpha go through a one-look review. The reviewer asks whether the content will actually be useful for the purpose PhyslibAlpha is trying to deliver. If the answer is no, the PR is closed without an explicit reason.

<a id="handbook-alignment"></a>

## 4. Run the handbook alignment skill on agent-written code

If you use an agent to write code, you must run the `/handbook-alignment` skill on it afterwards. This checks the code against this handbook, so that it reaches the highest quality possible before review.

<a id="move-into-physlib"></a>

## 5. Results are meant to move into Physlib

Moving work from PhyslibAlpha into Physlib is one of the key parts of the project. This should help guide what you put into PhyslibAlpha, and how you structure it.
