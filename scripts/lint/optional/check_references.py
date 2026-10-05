#!/usr/bin/env python3
"""Validates the '## References' sections of Physlib/QuantumInfo/PhyslibAlpha modules.

Checks, for every module docstring References section:
  * the body is not empty
  * every "[ref: <key>]" tag resolves to an entry in docs/references.bib
  * docs/references.bib contains no Zulip entries (Zulip links clutter the
    bibliography and aren't useful indexed as formal references -- they should
    be left as plain, untagged URLs in the docstring instead)

Usage: ./scripts/lint/optional/check_references.py
Exits non-zero (and prints one message per problem) if any check fails.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
HEAD_RE = re.compile(r'^#{1,4}\s*(?:(?:i{1,3}v?|\d+)\.\s*)?References?:?\s*$')
REF_TAG_RE = re.compile(r'\[ref:\s*([^\]]+?)\]')
BIB_ENTRY_RE = re.compile(r'^@(\w+)\{\s*([^,\s]+)\s*,(.*?)^\}', re.MULTILINE | re.DOTALL)


def load_registry():
    text = (ROOT / 'docs' / 'references.bib').read_text(encoding='utf-8')
    entries = {}
    for m in BIB_ENTRY_RE.finditer(text):
        entries[m.group(2)] = m.group(3)
    return entries


def find_blocks(lines):
    blocks = []
    i = 0
    while i < len(lines):
        if HEAD_RE.match(lines[i].strip()):
            j = i + 1
            while j < len(lines):
                s = lines[j].strip()
                if s.startswith('#') and 'References' not in s:
                    break
                if s == '-/' or s.startswith('-/'):
                    break
                j += 1
            blocks.append((i, j))
            i = j
        else:
            i += 1
    return blocks


def main():
    registry = load_registry()
    keys = set(registry)
    problems = []

    for key, fields in registry.items():
        if 'zulip' in key.lower() or 'zulipchat.com' in fields:
            problems.append(f"docs/references.bib: entry '{key}' is a Zulip link "
                             f"-- Zulip links should not be added to the bibliography")

    for path in sorted(ROOT.rglob('*.lean')):
        if '.lake' in path.parts:
            continue
        lines = path.read_text(encoding='utf-8', errors='replace').split('\n')
        for head_idx, end_idx in find_blocks(lines):
            body_lines = lines[head_idx + 1:end_idx]
            body = '\n'.join(body_lines).strip()
            rel = path.relative_to(ROOT)
            if not body:
                problems.append(f"{rel}:{head_idx + 1}: empty References section "
                                 f"(use '* None.' if there is genuinely no reference)")
                continue
            for line_no, line in enumerate(body_lines, start=head_idx + 2):
                for m in REF_TAG_RE.finditer(line):
                    key = m.group(1).strip()
                    if key not in keys:
                        problems.append(f"{rel}:{line_no}: unknown reference key "
                                         f"'{key}' (not in docs/references.bib)")

    if problems:
        for p in problems:
            print(p)
        print(f"\n{len(problems)} problem(s) found")
        sys.exit(1)
    print("References sections OK")


if __name__ == '__main__':
    main()
