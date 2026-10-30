#!/usr/bin/env python3
"""
Turn the results of a handbook-alignment check into a Markdown report.

Each review writes one JSON file, `<name>.json`, in the format given in `protocol.md`. This
script reads every such file in a folder and prints a report: a table of scores and summaries,
followed by the suggested improvements for each handbook file.

Usage:

    python3 report.py <results-folder> > report.md
"""

from __future__ import annotations

import json
import os
import sys
from typing import TypedDict

# One suggested improvement, as in `protocol.md`. The class syntax cannot be used here because
# the key `handbook-line` contains a hyphen.
Improvement = TypedDict("Improvement", {
    "file": str,           # the path, or "" if about the whole change
    "line": int,           # 0 if not line-specific
    "handbook-line": str,  # the line of the handbook it relates to
    "suggestion": str,
})


class Result(TypedDict, total=False):
    """One review's result, as in `protocol.md`, plus `tips`, the name of its handbook file.
    A review that failed has only `tips` and `error`."""
    tips: str
    score: int | None  # None if no part of the handbook file applies to the change
    summary: str
    improvements: list[Improvement]
    error: str


def readJsonOutput(folder: str) -> list[Result]:
    """The results in `folder`, with `Basic` first and the rest in alphabetical order. A file
    that is not valid JSON becomes a result with an `error`."""
    names = sorted(f[:-5] for f in os.listdir(folder) if f.endswith(".json"))
    names.sort(key=lambda n: n != "Basic")
    results: list[Result] = []
    for name in names:
        try:
            with open(os.path.join(folder, f"{name}.json"), encoding="utf-8") as fh:
                result: Result = json.load(fh)
        except json.JSONDecodeError as e:
            result = {"error": f"the result is not valid JSON ({e})"}
        result["tips"] = name
        results.append(result)
    return results


def makeReport(results: list[Result]) -> str:
    """The Markdown report: a table of scores and summaries, then the suggested improvements
    for each handbook file."""

    def oneLine(text: str) -> str:
        # Collapse new lines and escape `|`, so the text fits in a table cell.
        return " ".join(str(text).split()).replace("|", "\\|")

    lines = [
        "<!-- handbook-alignment-report -->",
        "## Handbook alignment check",
        "",
        "| Handbook file | Score | Summary |",
        "| --- | --- | --- |",
    ]
    for r in results:
        if r.get("error"):
            score, summary = "error", r["error"]
        else:
            score = "n/a" if r.get("score") is None else f"{r['score']}/5"
            summary = r.get("summary", "")
        lines.append(f"| {r['tips']} | {score} | {oneLine(summary)} |")

    for r in results:
        improvements = r.get("improvements") or []
        if r.get("error") or not improvements:
            continue
        lines += ["", f"### {r['tips']}", ""]
        for imp in improvements:
            path, line = imp.get("file") or "", imp.get("line") or 0
            where = f"`{path}:{line}`" if path and line else f"`{path}`" if path else "Whole change"
            lines.append(f"- {where}: {oneLine(imp.get('suggestion', ''))}")
            if imp.get("handbook-line"):
                lines.append(f"  <sub>Handbook: {oneLine(imp['handbook-line'])}</sub>")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: python3 report.py <results-folder>")
    print(makeReport(readJsonOutput(sys.argv[1])), end="")
