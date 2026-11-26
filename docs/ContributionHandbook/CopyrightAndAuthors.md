# Copyright and authors

Every Lean file in Physlib starts with a copyright and author header. This page explains how to fill it in.

## Contents

1. [Use the standard copyright header](#copyright-header)
2. [Give the copyright to the person who first wrote the file](#copyright-holder)
3. [Use the year the file was first written](#copyright-year)
4. [List the people who can answer questions about the file](#who-is-an-author)
5. [Write real names, ordered by surname](#author-names)
6. [Attribute AI-generated content to the person running the agent](#ai-generated-content)

<a id="copyright-header"></a>

## 1. Use the standard copyright header

The copyright and author statement goes at the very top of the file. Use the following format:

```lean
/-
Copyright (c) 2026 Ada Example. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ada Example, Bob Placeholder, Cy Sample
-/
```

<a id="copyright-holder"></a>

## 2. Give the copyright to the person who first wrote the file

Ideally the copyright is given to one named person: the person who first wrote the file. The copyright has to be assigned to somebody, and it makes clear who holds the rights to the original work, so it makes sense to give it to the person who created the file. In practice this does not matter that much, because the file is released under the Apache 2.0 license. The only exception is when a well-known company or organization first contributed the file and has an agreement that allows it to put its copyright on that file.

<a id="copyright-year"></a>

## 3. Use the year the file was first written

The year in the copyright line should be the year the file was first written. Don't change it when the file is edited later.

<a id="who-is-an-author"></a>

## 4. List the people who can answer questions about the file

An author is somebody who has contributed to the file enough that they could reasonably answer design and implementation questions about it. The author list tells others who to contact about the content of that specific Lean file. See also section 12, Author lists, in [Basic.md](Basic.md).

<a id="author-names"></a>

## 5. Write real names, ordered by surname

Write each author's name as it would appear in an academic publication, and order the authors by surname, as is the convention in many fields of physics. Don't use pseudonyms, GitHub handles or anything similar. In addition something like 'Physlib contributors" is not acceptable.

<a id="ai-generated-content"></a>

## 6. Attribute AI-generated content to the person running the agent

If the content of a file is produced by an AI agent, the copyright and authorship go to the person responsible for running that agent. This is for accountability: someone has to answer for the content. The AI tool itself is never listed as an author.
