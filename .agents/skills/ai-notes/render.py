#!/usr/bin/env python3
"""
Helpers for the `ai-notes` skill (see SKILL.md next to this file).

The rubric passes of an assessment are run by whatever AI agent the person running the
skill uses; this script does the deterministic parts, so that the PR comment has the same
format whatever the agent or model:

    extract   pull the JSON object that follows the one-time marker out of a rubric pass's
              raw output, validate it, and write it as <results-dir>/<rubric>.json
    render    turn <results-dir>/*.json into the Markdown of the PR comment
    meta      print the hidden meta record of an existing assessment comment, read from
              stdin, as JSON (or `null` if the text holds none)

Sample usage:

    $ python3 render.py extract <marker> raw/correctness.txt results/ --rubric correctness
    $ python3 render.py render results/ --pr 1206 --sha <head sha> --model "<model>" > comment.md
    $ gh api repos/leanprover-community/physlib/issues/comments/<id> --jq .body | python3 render.py meta

The comment starts with the `<!-- physlib-ai-notes -->` marker, by which the skill finds
it again to edit it in place, and holds a `<!-- physlib-ai-notes:meta {...} -->` record
of the head commit and the scores, by which the skill sees whether it is current. Only the
standard library is used.
"""

import argparse
import datetime
import json
import os
import re
import subprocess
import sys

REPO = "leanprover-community/physlib"
MARKER = "<!-- physlib-ai-notes -->"
META_PREFIX = "<!-- physlib-ai-notes:meta "
META_RE = re.compile(r"<!-- physlib-ai-notes:meta (\{.*?\}) -->", re.DOTALL)

# The rubrics, in the order they are shown.  Each is `rubrics/<name>.md`.
RUBRICS = [
    "correctness",
    "physical-relevance",
    "reuse",
    "scope",
    "attribution",
    "api-design",
    "generality",
    "placement",
    "naming",
    "documentation",
    "proof-quality",
]

FINDING_FIELDS = ("file", "line", "observation", "suggestion", "evidence")

# GitHub refuses comments longer than 65536 characters; leave room for the meta record.
MAX_COMMENT = 60000

DISCLAIMER = ("This assessment makes no decisions and is intended to improve your PR where "
              "possible. Scores are from 0 to 5 per rubric; humans make every decision "
              "about this PR.")


# ------------------------------------------------------------------------------------------
# Validation

def validate(obj, rubric):
    """Check a rubric result against the schema of `rubrics/_common.md`.

    Returns a normalised copy, or raises `ValueError` saying what is wrong."""
    if not isinstance(obj, dict):
        raise ValueError("the result is not a JSON object")
    if obj.get("rubric", rubric) != rubric:
        raise ValueError(f"the result is for rubric {obj.get('rubric')!r}, not {rubric!r}")
    score = obj.get("score")
    if score is not None and (isinstance(score, bool) or not isinstance(score, int)
                              or not 0 <= score <= 5):
        raise ValueError(f"score {score!r} is not an integer from 0 to 5 or null")
    summary = obj.get("summary")
    if not isinstance(summary, str) or not summary.strip():
        raise ValueError("summary is missing")
    findings = obj.get("findings", [])
    if not isinstance(findings, list):
        raise ValueError("findings is not a list")
    out = []
    for i, f in enumerate(findings):
        if not isinstance(f, dict):
            raise ValueError(f"finding {i} is not an object")
        g = {k: f.get(k, "") for k in FINDING_FIELDS}
        try:
            g["line"] = int(g["line"] or 0)
        except (TypeError, ValueError):
            raise ValueError(f"finding {i} has a non-integer line {g['line']!r}")
        for k in ("file", "observation", "suggestion", "evidence"):
            if not isinstance(g[k], str):
                raise ValueError(f"finding {i} has a non-string {k}")
        if not g["suggestion"].strip():
            raise ValueError(f"finding {i} has no suggestion")
        out.append(g)
    return {"rubric": rubric, "score": score, "summary": summary.strip(), "findings": out}


def extract(marker, text, rubric):
    """The validated JSON object following the last occurrence of `marker` in `text`."""
    pos = text.rfind(marker)
    if pos < 0:
        raise ValueError("the marker does not occur in the output")
    rest = text[pos + len(marker):]
    start = rest.find("{")
    if start < 0:
        raise ValueError("no JSON object follows the marker")
    obj, _ = json.JSONDecoder().raw_decode(rest[start:])
    return validate(obj, rubric)


# ------------------------------------------------------------------------------------------
# Rendering

def neutralise(text):
    """Agent text quotes the PR, which is untrusted: make sure it cannot open an HTML comment
    (and so forge our markers) or close the `<details>` blocks it is shown in."""
    text = text.replace("<!--", "&lt;!--").replace("-->", "--&gt;")
    return re.sub(r"</?\s*(details|summary)\b", lambda m: m.group(0).replace("<", "&lt;"),
                  text, flags=re.IGNORECASE)


def one_line(text):
    """Text for a table cell."""
    return neutralise(" ".join(text.split())).replace("|", "\\|")


def score_text(result):
    if result.get("error"):
        return "error"
    if result["score"] is None:
        return "n/a"
    return f"{result['score']}/5"


def location(f, sha):
    if not f["file"]:
        return "PR-wide"
    path = f["file"]
    url = f"https://github.com/{REPO}/blob/{sha}/{path}"
    label = path
    if f["line"] > 0:
        url += f"#L{f['line']}"
        label += f":{f['line']}"
    return f"[`{label}`]({url})"


def render_rubric(result, sha):
    name = result["rubric"]
    lines = [f"<details><summary><b>{name}</b> — {score_text(result)}</summary>", ""]
    if result.get("error"):
        lines.append(f"This rubric could not be assessed: {neutralise(result['error'])}")
    else:
        lines.append(neutralise(result["summary"]))
        for f in result["findings"]:
            lines.append("")
            obs = neutralise(" ".join(f["observation"].split()))
            sug = neutralise(" ".join(f["suggestion"].split()))
            lines.append(f"- {location(f, sha)}: {obs}" if obs else f"- {location(f, sha)}")
            lines.append(f"  **Suggestion:** {sug}")
            if f["evidence"].strip():
                ev = neutralise(" ".join(f["evidence"].split()))
                lines.append(f"  <sub>Evidence: {ev}</sub>")
    lines += ["", "</details>"]
    return "\n".join(lines)


def rubrics_revision():
    """The last commit of this repository that changed the skill, if git knows it."""
    here = os.path.dirname(os.path.abspath(__file__))
    try:
        rev = subprocess.run(["git", "log", "-1", "--format=%h", "--", here], cwd=here,
                             capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        rev = ""
    return rev or "unknown"


def load_results(results_dir):
    results = []
    for name in RUBRICS:
        path = os.path.join(results_dir, f"{name}.json")
        try:
            with open(path, encoding="utf-8") as fh:
                obj = json.load(fh)
            if isinstance(obj, dict) and obj.get("error"):
                results.append({"rubric": name, "score": None, "error": str(obj["error"])})
            else:
                results.append(validate(obj, name))
        except FileNotFoundError:
            results.append({"rubric": name, "score": None, "error": "no result was produced"})
        except (ValueError, json.JSONDecodeError) as e:
            results.append({"rubric": name, "score": None, "error": f"invalid result ({e})"})
    return results


def render(results, pr, sha, model, date=None, rubrics_rev=None):
    date = date or datetime.date.today().isoformat()
    model = neutralise(" ".join(model.split()))
    rubrics_rev = rubrics_rev or rubrics_revision()
    scores = [r["score"] for r in results if r["score"] is not None]
    mean = f"{sum(scores) / len(scores):.1f}/5" if scores else "n/a"

    head = [
        MARKER,
        f"## AI assessment (advisory) — `{sha[:7]}`",
        "",
        f"> {DISCLAIMER}",
        "",
        "| rubric | score | summary |",
        "| --- | --- | --- |",
    ]
    for r in results:
        summary = r["error"] if r.get("error") else r["summary"]
        head.append(f"| {r['rubric']} | {score_text(r)} | {one_line(summary)} |")
    head += [
        "",
        f"Mean of the scored rubrics: **{mean}** (an indication only; the rubrics are not "
        "weighted and the mean is not a threshold).",
        "",
        "### Suggestions by rubric",
        "",
    ]
    foot = [
        "",
        "---",
        f"<sub>Assessed with {model} on {date}, using the rubrics of "
        f"`.agents/skills/ai-notes/` at `{rubrics_rev}`. "
        "Comment `ai-notes` on its own line to request a new assessment after further "
        "changes.</sub>",
    ]
    meta = {
        "pr": pr,
        "sha": sha,
        "date": date,
        "model": model,
        "rubrics": rubrics_rev,
        "scores": {r["rubric"]: ("error" if r.get("error") else r["score"]) for r in results},
    }
    meta_line = META_PREFIX + json.dumps(meta, separators=(",", ":")) + " -->"

    body = []
    budget = MAX_COMMENT - sum(len(x) + 1 for x in head + foot) - len(meta_line)
    for i, r in enumerate(results):
        block = render_rubric(r, sha)
        if len(block) + 2 > budget:
            left = ", ".join(x["rubric"] for x in results[i:])
            body.append(f"*The suggestions for {left} are omitted: the comment would exceed "
                        "GitHub's size limit.*")
            break
        body += [block, ""]
        budget -= len(block) + 2
    return "\n".join(head + body + foot + [meta_line]) + "\n"


def read_meta(text):
    m = None
    for m in META_RE.finditer(text):
        pass
    if m is None:
        return None
    return json.loads(m.group(1))


# ------------------------------------------------------------------------------------------
# Command line

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("extract", help="extract and validate a rubric pass's JSON result")
    p.add_argument("marker")
    p.add_argument("raw", help="the raw output of the rubric pass")
    p.add_argument("results_dir")
    p.add_argument("--rubric", required=True, choices=RUBRICS)

    p = sub.add_parser("render", help="render the PR comment from the results")
    p.add_argument("results_dir")
    p.add_argument("--pr", type=int, required=True)
    p.add_argument("--sha", required=True, help="the full head commit of the PR")
    p.add_argument("--model", required=True, help="the model (and agent) that assessed")

    sub.add_parser("meta", help="print the meta record of a comment read from stdin")

    args = parser.parse_args(argv)
    if args.command == "extract":
        with open(args.raw, encoding="utf-8") as fh:
            text = fh.read()
        try:
            result = extract(args.marker, text, args.rubric)
        except (ValueError, json.JSONDecodeError) as e:
            print(f"{args.rubric}: {e}", file=sys.stderr)
            return 1
        os.makedirs(args.results_dir, exist_ok=True)
        with open(os.path.join(args.results_dir, f"{args.rubric}.json"), "w",
                  encoding="utf-8") as fh:
            json.dump(result, fh, indent=2, ensure_ascii=False)
            fh.write("\n")
        print(f"{args.rubric}: score {score_text(result)}, {len(result['findings'])} findings")
    elif args.command == "render":
        if not re.fullmatch(r"[0-9a-f]{40}", args.sha):
            parser.error("--sha must be a full 40-character commit hash")
        sys.stdout.write(render(load_results(args.results_dir), args.pr, args.sha, args.model))
    elif args.command == "meta":
        print(json.dumps(read_meta(sys.stdin.read())))
    return 0


if __name__ == "__main__":
    sys.exit(main())
