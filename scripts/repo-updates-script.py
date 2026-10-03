import os
import sys
import json
import datetime
import urllib.request
import urllib.error
import urllib.parse
import base64

# Constants
GITHUB_API = "https://api.github.com"

GITHUB_TOKEN = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
REPO = os.environ["GITHUB_REPOSITORY"]  # "owner/repo", set automatically in Actions
OWNER, REPO_NAME = REPO.split("/")

BUSY_THRESHOLD = int(os.environ.get("BUSY_THRESHOLD", "3"))
MAX_PRS_LISTED = int(os.environ.get("MAX_PRS_LISTED", "3"))

ZULIP_SITE = os.environ["ZULIP_SITE"].rstrip("/")
ZULIP_EMAIL = os.environ["ZULIP_BOT_EMAIL"]
ZULIP_API_KEY = os.environ["ZULIP_BOT_API_KEY"]
ZULIP_STREAM = os.environ["ZULIP_STREAM"]
ZULIP_TOPIC = os.environ.get("ZULIP_TOPIC", "Reviewer load report")


def gh_request(path, params=None):
    url = f"{GITHUB_API}{path}"
    if params:
        url += "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url)
    req.add_header("Accept", "application/vnd.github+json")
    req.add_header("X-GitHub-Api-Version", "2022-11-28")
    if GITHUB_TOKEN:
        req.add_header("Authorization", f"Bearer {GITHUB_TOKEN}")
    try:
        with urllib.request.urlopen(req) as resp:
            body = resp.read()
            link_header = resp.headers.get("Link", "")
            return json.loads(body), link_header
    except urllib.error.HTTPError as e:
        detail = e.read().decode(errors="replace")
        print(f"GitHub API error for {url}: {e.code} {detail}", file=sys.stderr)
        raise


# this function makes the results of multiple github pages into a single list
def gh_paginate(path, params=None):
    params = dict(params or {})
    params.setdefault("per_page", 100)
    page = 1
    results = []
    while True:
        params["page"] = page
        data, link_header = gh_request(path, params)
        if not data:
            break
        results.extend(data)
        if 'rel="next"' not in link_header:
            break
        page += 1
    return results

# get a list of open PRs
def fetch_open_prs_in_window():
    prs = gh_paginate(
        f"/repos/{OWNER}/{REPO_NAME}/pulls",
        {"state": "open", "sort": "created", "direction": "desc"},
    )
    result = []
    for pr in prs:
        result.append(pr)

    return result

# get the number of lines changed in the PR to estimate the size
def fetch_pr_lines_changed(number):
    data, _ = gh_request(f"/repos/{OWNER}/{REPO_NAME}/pulls/{number}")
    return data.get("additions", 0) + data.get("deletions", 0)


def fetch_recently_merged_prs():
    """Return PRs whose merged_at timestamp falls in the previous UTC calendar day."""
    now = datetime.datetime.now(datetime.timezone.utc)
    cutoff = now - datetime.timedelta(hours=24)

    prs = gh_paginate(
        f"/repos/{OWNER}/{REPO_NAME}/pulls",
        {"state": "closed", "sort": "updated", "direction": "desc"},
    )
    merged = []
    for pr in prs:
        if not pr.get("merged_at"):
            continue
        merged_at = datetime.datetime.strptime(
            pr["merged_at"], "%Y-%m-%dT%H:%M:%SZ"
        ).replace(tzinfo=datetime.timezone.utc)
        if merged_at < cutoff:
            continue
        merged.append(pr)
    return merged


def fetch_recently_opened_prs():
    """Return PRs created in the last 24 hours."""
    now = datetime.datetime.now(datetime.timezone.utc)
    cutoff = now - datetime.timedelta(hours=24)

    prs = gh_paginate(
        f"/repos/{OWNER}/{REPO_NAME}/pulls",
        {"state": "all", "sort": "created", "direction": "desc"},
    )
    opened = []
    for pr in prs:
        created_at = datetime.datetime.strptime(
            pr["created_at"], "%Y-%m-%dT%H:%M:%SZ"
        ).replace(tzinfo=datetime.timezone.utc)
        if created_at < cutoff:
            break
        opened.append(pr)
    return opened

# gets people who arent assigned as a reviewer, but have pushed to the repo in the past
# needed to find people currently assigned to 0 reviews
def fetch_collaborators():
    try:
        collabs = gh_paginate(
            f"/repos/{OWNER}/{REPO_NAME}/collaborators", {"affiliation": "all"}
        )
        return [c["login"] for c in collabs]
    except Exception:
        print(
            "Warning: could not list collaborators (needs push access on the "
            "repo). Roster will be built from requested reviewers only.",
            file=sys.stderr,
        )
        return []

# get all the important values needed for the message
def build_report():
    prs = fetch_open_prs_in_window()

    pending_counts = {}
    pending_prs = {}  # reviewer -> list of (number, title, url)
    unreviewed_prs = []  # open PRs with no reviewer assigned

    for pr in prs:
        reviewers = [r["login"] for r in pr.get("requested_reviewers", [])]

        if not reviewers:
            labels = [lbl["name"] for lbl in pr.get("labels", [])]
            lines_changed = fetch_pr_lines_changed(pr["number"])
            unreviewed_prs.append((pr["number"], pr["title"], pr["html_url"], labels, lines_changed))
        for login in reviewers:
            pending_counts[login] = pending_counts.get(login, 0) + 1
            pending_prs.setdefault(login, []).append(
                (pr["number"], pr["title"], pr["html_url"])
            )

    merged_recently = fetch_recently_merged_prs()
    opened_recently = fetch_recently_opened_prs()


    roster = set(fetch_collaborators()) | set(pending_counts.keys())
    roster = sorted(roster)

    # sort into 3 groups
    busy, moderate, quiet = [], [], []
    for login in roster:
        count = pending_counts.get(login, 0)
        if count >= BUSY_THRESHOLD:
            busy.append((login, count))
        elif count == 0:
            quiet.append((login, count))
        else:
            moderate.append((login, count))

    busy.sort(key=lambda x: -x[1])
    moderate.sort(key=lambda x: -x[1])
    quiet.sort(key=lambda x: x[0].lower())

    return {
        "busy_threshold": BUSY_THRESHOLD,
        "pr_count": len(prs),
        "busy": busy,
        "moderate": moderate,
        "quiet": quiet,
        "pending_prs": pending_prs,
        "unreviewed_prs": unreviewed_prs,
        "merged_recently": [
            (pr["number"], pr["title"], pr["html_url"], pr["user"]["login"])
            for pr in merged_recently
        ],
        "opened_recently": [
            (pr["number"], pr["title"], pr["html_url"], pr["user"]["login"])
            for pr in opened_recently
        ],
    }


# make the message string
def format_message(report):
    lines = []
    lines.append(
        "Summary of PRs that need attention and available reviewers"
    )
    lines.append("")

    def section(title, entries, show_prs=False):
        lines.append(f"**{title}** ({len(entries)})")
        if not entries:
            lines.append("- _none_")
        else:
            for login, count in entries:
                suffix = f" — {count} pending review(s)" if count else ""
                lines.append(f"- @**{login}**{suffix}")
                if show_prs:
                    for number, title_, url in report["pending_prs"].get(login, [])[
                        :MAX_PRS_LISTED
                    ]:
                        lines.append(f"    - [#{number} {title_}]({url})")
        lines.append("")

    # unreviewed open PRs
    unreviewed = report["unreviewed_prs"]
    lines.append(f"**⚪ Open PRs with no reviewer assigned** ({len(unreviewed)})")
    if not unreviewed:
        lines.append("- _none_")
    for number, title_, url, labels, lines_changed in unreviewed:
        tag_str = " " + " ".join(f"`{l}`" for l in labels) if labels else ""
        lines.append(f"- [#{number} {title_}]({url}){tag_str} — {lines_changed} lines changed")
    lines.append("")

    section(
        f"🔴 Busy (≥{report['busy_threshold']} pending reviews)",
        report["busy"],
        show_prs=True,
    )
    section("🟡 Moderate", report["moderate"])
    section("🟢 Quiet (0 pending reviews)", report["quiet"])

    # PRs opened in the last 24h
    opened = report["opened_recently"]
    lines.append(f"**🟤 Opened in the last 24h** ({len(opened)})")
    if not opened:
        lines.append("- _none_")
    for number, title_, url, author in opened:
        lines.append(f"- [#{number} {title_}]({url}) by @**{author}**")
    lines.append("")

    # PRs merged in the last 24h
    merged = report["merged_recently"]
    lines.append(f"**✅ Merged in the last 24h** ({len(merged)})")
    if not merged:
        lines.append("- _none_")
    for number, title_, url, author in merged:
        lines.append(f"- [#{number} {title_}]({url}) by @**{author}**")
    lines.append("")

    return "\n".join(lines)


def post_to_zulip(content):
    data = urllib.parse.urlencode(
        {
           "type": "stream",
          "to": ZULIP_STREAM,
         "topic": ZULIP_TOPIC,
            "content": content,
        }
    ).encode()
    # send a DM (Testing only)
    '''data = urllib.parse.urlencode(
        {
            "type": "private",
            "to": json.dumps([1175816]),
            "content": content,
        }
    ).encode()'''

    req = urllib.request.Request(f"{ZULIP_SITE}/api/v1/messages", data=data)
    credentials = f"{ZULIP_EMAIL}:{ZULIP_API_KEY}"

    req.add_header(
        "Authorization", "Basic " + base64.b64encode(credentials.encode()).decode()
    )
    try:
        with urllib.request.urlopen(req) as resp:
            print("Zulip response:", resp.read().decode())
    except urllib.error.HTTPError as e:
        print("Zulip API error:", e.code, e.read().decode(), file=sys.stderr)


def main():
    report = build_report()
    message = format_message(report)
    print(message)
    post_to_zulip(message)


if __name__ == "__main__":
    main()
