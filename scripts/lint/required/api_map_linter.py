#!/usr/bin/env python3
"""Check the schema and source references in Physlib API maps.

This is deliberately a source-presence check. It verifies named declarations
and notation anchors in the Lean file named by a completed requirement. Claims
about anonymous instances are reported as requiring a Lean-environment check,
not treated as passes.
"""

import argparse
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("PyYAML is required; install it with python3 -m pip install PyYAML.")


TOP_LEVEL_KEYS = {"version", "Title", "Overview", "ParentAPIs", "References", "Requirements"}
REQUIREMENT_KEYS = {"description", "done", "location"}
IDENTIFIER = re.compile(r"^[A-Za-z_À-ɏͰ-Ͽ℀-⅏][\w'.À-ɏͰ-Ͽ℀-⅏]*$")


def split_top_level(value, separator):
    """Split on a separator that is not enclosed in parentheses."""
    result, current, depth = [], [], 0
    for char in value:
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        if char == separator and depth == 0:
            result.append("".join(current).strip())
            current = []
        else:
            current.append(char)
    if current:
        result.append("".join(current).strip())
    return result


def parse_location(location):
    """Parse File.lean (claim, claim); Other.lean (claim) locations."""
    groups = []
    for part in split_top_level(location, ";"):
        match = re.match(r"^(\S+\.lean)\s*\((.*)\)\s*$", part)
        if match is None:
            groups.append((part if part.endswith(".lean") else None, []))
        else:
            groups.append((match.group(1), split_top_level(match.group(2), ",")))
    return groups


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
        "checked": 0,
        "names_ok": 0,
        "missing_file": 0,
        "missing_name": 0,
        "need_lean": 0,
        "skipped": 0,
    }
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except yaml.YAMLError as error:
        return [f"YAML PARSE ERROR: {error}"], counts
    if not isinstance(data, dict):
        return ["SCHEMA: expected a mapping at the top level"], counts
    missing = TOP_LEVEL_KEYS - set(data)
    if missing:
        problems.append(f"SCHEMA: missing top-level keys: {sorted(missing)}")
    requirements = data.get("Requirements")
    if not isinstance(requirements, list):
        return problems + ["SCHEMA: Requirements is not a list"], counts

    for index, requirement in enumerate(requirements):
        counts["requirements"] += 1
        if not isinstance(requirement, dict) or REQUIREMENT_KEYS - set(requirement):
            problems.append(f"req[{index}] SCHEMA: expected {sorted(REQUIREMENT_KEYS)}")
            continue
        location = str(requirement["location"]).strip()
        if requirement["done"] is not True or location in {"", "N/A"}:
            counts["skipped"] += 1
            continue
        counts["checked"] += 1
        for relative_file, claims in parse_location(location):
            if relative_file is None:
                problems.append(f"req[{index}] UNPARSABLE location: {location!r}")
                continue
            source_path = repository / relative_file
            if not source_path.is_file():
                counts["missing_file"] += 1
                problems.append(f"req[{index}] MISSING FILE: {relative_file}")
                continue
            source = source_path.read_text(encoding="utf-8", errors="replace")
            for claim in claims:
                kind, token = classify_claim(claim)
                if kind == "instance":
                    counts["need_lean"] += 1
                    if verbose:
                        problems.append(
                            f"req[{index}] NEEDS LEAN ENVIRONMENT: {claim!r} in {relative_file}"
                        )
                elif claim_is_present(source, kind, token):
                    counts["names_ok"] += 1
                else:
                    counts["missing_name"] += 1
                    problems.append(
                        f"req[{index}] MISSING {kind.upper()}: {token!r} in {relative_file}"
                    )
    return problems, counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, type=Path, help="physlib repository root")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    maps = sorted(args.repo.rglob("API-map.yaml"))
    if not maps:
        sys.exit(f"no API-map.yaml files under {args.repo}")
    total = {
        "requirements": 0, "checked": 0, "names_ok": 0, "missing_file": 0,
        "missing_name": 0, "need_lean": 0, "skipped": 0,
    }
    failed = False
    for path in maps:
        problems, counts = lint_map(path, args.repo, args.verbose)
        for key, value in counts.items():
            total[key] += value
        invalid = (
            counts["missing_file"] or counts["missing_name"] or
            any("SCHEMA" in problem or "PARSE" in problem or "UNPARSABLE" in problem
                for problem in problems)
        )
        failed = failed or invalid
        print(
            f"[{'FAIL' if invalid else 'ok'}] {path.relative_to(args.repo)} "
            f"({counts['checked']} checked, {counts['names_ok']} names ok, "
            f"{counts['need_lean']} need-Lean, {counts['skipped']} skipped)"
        )
        for problem in problems:
            print(f"  {problem}")
    print("\n=== SUMMARY ===")
    print(
        f"files={len(maps)} requirements={total['requirements']} checked={total['checked']} "
        f"names_ok={total['names_ok']} MISSING_FILE={total['missing_file']} "
        f"MISSING_NAME={total['missing_name']} need_Lean_env={total['need_lean']} "
        f"skipped(N/A|undone)={total['skipped']}"
    )
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
