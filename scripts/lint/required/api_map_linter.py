#!/usr/bin/env python3
"""Check the structure and source references in Physlib API maps.

An `API-map.md` is a prose document: a title, an overview, the APIs it builds
on, one paragraph per requirement, further reading, and - last - a numbered
list of the Lean declarations the prose cites. This script checks that the
document has that shape, that every citation resolves, and that every cited
declaration really is in the file it is attributed to.

The declaration check is deliberately a source-presence check. It verifies
named declarations and notation anchors in the Lean file named by a cited
reference. Claims about anonymous instances are reported as requiring a
Lean-environment check, not treated as passes.

No third-party packages are needed; the format is parsed directly.
"""

import argparse
import re
import sys
from pathlib import Path

TITLE = re.compile(r"^#\s+(\S.*)$")
HEADING = re.compile(r"^##\s+(\S.*)$")
REFERENCE_ENTRY = re.compile(r"^(\d+)\.\s+(\S+\.lean)\s*(?:[—-]\s*(.*))?$")
CITATION = re.compile(r"\[(\d+(?:\s*,\s*\d+)*|planned)\]")
TRAILING_CITATIONS = re.compile(r"(?:\s*\[(?:\d+(?:\s*,\s*\d+)*|planned)\])+\s*$")
BACKTICKED = re.compile(r"`([^`]+)`")
IDENTIFIER = re.compile(r"^[A-Za-z_À-ɏͰ-Ͽ℀-⅏][\w'.À-ɏͰ-Ͽ℀-⅏]*$")

REQUIRED_SECTIONS = ["Requirements", "Lean declarations"]
KNOWN_SECTIONS = ["Built on", "Requirements", "Further reading", "Lean declarations"]
NO_DECLARATIONS = "*None yet.*"


def split_sections(text):
    """The title, the overview paragraphs, and the `##` sections in order."""
    title, overview, sections, current = None, [], [], None
    for line in text.split("\n"):
        heading = HEADING.match(line)
        if heading is not None:
            current = (heading.group(1).strip(), [])
            sections.append(current)
            continue
        if title is None:
            matched = TITLE.match(line)
            if matched is not None:
                title = matched.group(1).strip()
                continue
        if current is None:
            overview.append(line)
        else:
            current[1].append(line)
    return title, paragraphs(overview), sections


def paragraphs(lines):
    """Blank-line-separated paragraphs, each folded onto one line."""
    out, current = [], []
    for line in lines:
        if line.strip() == "":
            if current:
                out.append(" ".join(current))
                current = []
        else:
            current.append(line.strip())
    if current:
        out.append(" ".join(current))
    return out


def citations_of(paragraph):
    """The citation numbers closing a requirement paragraph, and whether it is
    marked `[planned]`. Returns `None` when the paragraph has no closing
    citation at all."""
    trailing = TRAILING_CITATIONS.search(paragraph)
    if trailing is None:
        return None
    numbers, planned = [], False
    for group in CITATION.findall(trailing.group(0)):
        if group == "planned":
            planned = True
        else:
            numbers.extend(int(part) for part in group.split(","))
    return numbers, planned


def logical_entries(lines):
    """The declaration lines, with wrapped continuations folded back on."""
    folded = []
    for line in lines:
        line = line.strip()
        if line == "" or line == NO_DECLARATIONS:
            continue
        if folded and not re.match(r"^\d+\.\s", line):
            folded[-1] = folded[-1] + " " + line
        else:
            folded.append(line)
    return folded


def parse_references(lines):
    """The numbered Lean-declaration entries, as (number, file, [claims])."""
    entries, problems = [], []
    for line in logical_entries(lines):
        matched = REFERENCE_ENTRY.match(line)
        if matched is None:
            problems.append(f"REFERENCES: unreadable entry: {line!r}")
            continue
        claims = BACKTICKED.findall(matched.group(3) or "")
        entries.append((int(matched.group(1)), matched.group(2), claims))
    return entries, problems


def classify_claim(claim):
    claim = claim.strip()
    if claim.startswith("notation "):
        return "notation", claim[len("notation "):].strip()
    if " : " in claim:
        return "name", claim.split(" : ", 1)[0].strip()
    if IDENTIFIER.match(claim):
        return "name", claim
    if " " not in claim:
        return "notation", claim
    return "instance", claim


def claim_is_present(source, kind, token):
    if kind == "notation":
        fragments = [part for part in re.split(r"[·⬝\s]", token) if part]
        return all(fragment in source for fragment in fragments)
    if token in source:
        return True
    return re.search(r"\b" + re.escape(token.split(".")[-1]) + r"\b", source) is not None


def lint_map(path, repository, verbose):
    problems = []
    counts = {
        "requirements": 0,
        "done": 0,
        "checked": 0,
        "names_ok": 0,
        "missing_file": 0,
        "missing_name": 0,
        "need_lean": 0,
        "planned": 0,
        "lean_in_prose": 0,
    }
    title, overview, sections = split_sections(path.read_text(encoding="utf-8"))
    if title is None:
        problems.append("STRUCTURE: no `# Title` heading")
    if not overview:
        problems.append("STRUCTURE: no overview prose between the title and the first section")
    names = [name for name, _ in sections]
    for required in REQUIRED_SECTIONS:
        if required not in names:
            problems.append(f"STRUCTURE: missing section `## {required}`")
    for name in names:
        if name not in KNOWN_SECTIONS:
            problems.append(f"STRUCTURE: unknown section `## {name}`")
    known = [name for name in names if name in KNOWN_SECTIONS]
    if known != sorted(known, key=KNOWN_SECTIONS.index):
        problems.append(
            "STRUCTURE: sections must come in the order "
            + ", ".join(f"`## {name}`" for name in KNOWN_SECTIONS))
    body = {name: content for name, content in sections}

    entries, reference_problems = parse_references(body.get("Lean declarations", []))
    problems.extend(reference_problems)
    by_number = {}
    for number, lean_file, claims in entries:
        if number in by_number:
            problems.append(f"REFERENCES: duplicate entry [{number}]")
        by_number[number] = (lean_file, claims)
    for position, (number, _, _) in enumerate(entries, start=1):
        if number != position:
            problems.append(f"REFERENCES: entry [{number}] is in position {position}")
            break

    cited = set()
    for index, paragraph in enumerate(paragraphs(body.get("Requirements", []))):
        counts["requirements"] += 1
        found = citations_of(paragraph)
        if found is None:
            problems.append(
                f"req[{index}] NO CITATION: a requirement must end in `[n]` "
                f"citations or `[planned]`: {paragraph[:60]!r}..."
            )
            continue
        numbers, planned = found
        if planned:
            counts["planned"] += 1
        else:
            counts["done"] += 1
        for number in numbers:
            if number not in by_number:
                problems.append(f"req[{index}] DANGLING CITATION: [{number}]")
            cited.add(number)
        prose = TRAILING_CITATIONS.sub("", paragraph)
        if BACKTICKED.search(prose):
            counts["lean_in_prose"] += 1
            if verbose:
                problems.append(
                    f"req[{index}] STYLE: Lean names belong in the references, not the prose"
                )
    for number, _, _ in entries:
        if number not in cited:
            problems.append(f"REFERENCES: entry [{number}] is never cited")

    for number, relative_file, claims in entries:
        source_path = repository / relative_file
        if not source_path.is_file():
            counts["missing_file"] += 1
            problems.append(f"ref[{number}] MISSING FILE: {relative_file}")
            continue
        counts["checked"] += 1
        source = source_path.read_text(encoding="utf-8", errors="replace")
        if not claims:
            problems.append(f"ref[{number}] NO DECLARATIONS listed for {relative_file}")
        for claim in claims:
            kind, token = classify_claim(claim)
            if kind == "instance":
                counts["need_lean"] += 1
                if verbose:
                    problems.append(
                        f"ref[{number}] NEEDS LEAN ENVIRONMENT: {claim!r} in {relative_file}"
                    )
            elif claim_is_present(source, kind, token):
                counts["names_ok"] += 1
            else:
                counts["missing_name"] += 1
                problems.append(
                    f"ref[{number}] MISSING {kind.upper()}: {token!r} in {relative_file}"
                )
    return problems, counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, type=Path, help="physlib repository root")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    maps = sorted(args.repo.rglob("API-map.md"))
    stale = sorted(args.repo.rglob("API-map.yaml"))
    if not maps:
        sys.exit(f"no API-map.md files under {args.repo}")
    total = dict.fromkeys(
        ["requirements", "done", "checked", "names_ok", "missing_file",
         "missing_name", "need_lean", "planned", "lean_in_prose"], 0)
    failed = False
    for path in maps:
        problems, counts = lint_map(path, args.repo, args.verbose)
        for key, value in counts.items():
            total[key] += value
        invalid = (
            counts["missing_file"] or counts["missing_name"] or
            any(not problem.startswith(("req[", "ref[")) or "STYLE" not in problem
                for problem in problems)
        )
        failed = failed or bool(invalid)
        print(
            f"[{'FAIL' if invalid else 'ok'}] {path.relative_to(args.repo)} "
            f"({counts['done']} done, {counts['planned']} planned, "
            f"{counts['names_ok']} names ok, {counts['need_lean']} need-Lean)"
        )
        for problem in problems:
            print(f"  {problem}")
    for path in stale:
        failed = True
        print(f"[FAIL] {path.relative_to(args.repo)}: API maps are now `API-map.md`")
    print("\n=== SUMMARY ===")
    print(
        f"files={len(maps)} requirements={total['requirements']} done={total['done']} "
        f"planned={total['planned']} files_checked={total['checked']} "
        f"names_ok={total['names_ok']} MISSING_FILE={total['missing_file']} "
        f"MISSING_NAME={total['missing_name']} need_Lean_env={total['need_lean']} "
        f"lean_names_in_prose={total['lean_in_prose']}"
    )
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
