#!/usr/bin/env python3
"""
Review claims for pull requests.

To avoid two reviewers (human or AI) reviewing the same PR, a reviewer says what
they intend to review and claims it, by commenting on the PR:

    claim               claim this PR for review, for the default window
    claim 5 days        ... for a specific window (hours / days / weeks)
    claim 2026-08-01    ... until a specific date
    disclaim            release the claim early

The bot requests a review from the claimant, assigns them, applies the
`review-claimed` label and keeps a single status comment recording the deadline.
Claiming again extends the window; submitting a review completes the claim.
A claim that runs out without a review is released -- the claimant comes off the
PR as reviewer and assignee -- and announced on Zulip, so that somebody else
picks the PR up.

The whole state of a claim lives in that one status comment, in a hidden marker
holding a JSON record.  The comment is edited in place rather than reposted, so a
PR accumulates at most one of them however often the claim is extended, and there
is nothing to keep in sync anywhere else.

Sample usage, from the workflows in .github/workflows/review_claim*.yml:

    $ python scripts/github/review_claim.py comment   # handle an issue_comment event
    $ python scripts/github/review_claim.py review    # handle a pull_request_review event
    $ python scripts/github/review_claim.py expire    # remind about, and expire, claims

The first two read the event from GITHUB_EVENT_PATH.  All three need GITHUB_TOKEN
and GITHUB_REPOSITORY; the Zulip announcement additionally needs ZULIP_SITE,
ZULIP_BOT_EMAIL, ZULIP_BOT_API_KEY and ZULIP_STREAM, and is skipped with a
warning when they are not set.
"""

import base64
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone

CLAIM_LABEL = 'review-claimed'
MARKER_PREFIX = '<!-- review-claim '
MARKER_SUFFIX = ' -->'
CLAIM_FIELDS = ('state', 'claimant', 'claimed_at', 'until')
REMINDER_MARKER = '<!-- review-claim-reminder:{until}:{hours}h -->'

# A review claim is a short promise, so the windows are much tighter than the
# roadmap intentions this is modelled on.
DEFAULT_WINDOW = timedelta(days=2)
MAX_WINDOW = timedelta(days=14)
MIN_WINDOW = timedelta(hours=1)

# Reminders are @-mentions sent this many hours before the deadline.  A reminder
# is skipped when it is not shorter than the window itself, so a one day claim is
# never warned about a day in advance.  Ascending, so that the smallest
# applicable reminder wins if a scheduled run is skipped.
REMINDERS_HOURS = (24, 48)

UNITS = {
    'hour': timedelta(hours=1), 'hours': timedelta(hours=1),
    'day': timedelta(days=1), 'days': timedelta(days=1),
    'week': timedelta(weeks=1), 'weeks': timedelta(weeks=1),
}

API_ROOT = 'https://api.github.com'


class ClaimError(Exception):
    """A command we understood the shape of but cannot carry out."""


def warn(message):
    """Emit a GitHub Actions warning annotation."""
    print(f'::warning::{message}')


def now():
    return datetime.now(timezone.utc)


def to_iso(when):
    return when.astimezone(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def parse_iso(text):
    """Parse an ISO 8601 timestamp, tolerating the trailing `Z` GitHub sends."""
    return datetime.fromisoformat(text.replace('Z', '+00:00'))


def format_utc(when):
    """Format a timestamp the way the bot's comments always spell one out."""
    return when.astimezone(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')


def describe_window(window):
    """Spell a duration back to the claimant, so they can check what we understood."""
    seconds = window.total_seconds()

    def trim(value):
        return str(int(value)) if value == int(value) else str(round(value, 1))

    if seconds % 86400 == 0 and seconds >= 86400:
        days = seconds / 86400
        if days % 7 == 0:
            weeks = days / 7
            return f'{trim(weeks)} week' + ('' if weeks == 1 else 's')
        return f'{trim(days)} day' + ('' if days == 1 else 's')
    hours = seconds / 3600
    return f'{trim(hours)} hour' + ('' if hours == 1 else 's')


def parse_window(argument, at):
    """
    Parse the argument of a `claim` command into a deadline.

    Accepts an empty argument (the default window), `<n> hours|days|weeks`, or an
    absolute `YYYY-MM-DD` date, read as the end of that day UTC.  Over-long
    windows are clamped rather than rejected; the caller is told via `clamped`.
    Returns a `(until, clamped)` pair, or raises `ClaimError` with a message
    meant for the claimant.
    """
    trimmed = (argument or '').strip().lower()

    if trimmed == '':
        until = at + DEFAULT_WINDOW
    elif re.fullmatch(r'\d{4}-\d{2}-\d{2}', trimmed):
        try:
            until = parse_iso(f'{trimmed}T23:59:59Z')
        except ValueError:
            raise ClaimError(f'`{trimmed}` is not a real date.')
    else:
        match = re.fullmatch(r'(\d+)\s*(hour|hours|day|days|week|weeks)', trimmed)
        if not match:
            raise ClaimError(
                f'I could not read `{trimmed}` as a window. Use `claim`, '
                '`claim 5 days` (or hours/weeks), or `claim 2026-08-01`.')
        until = at + int(match.group(1)) * UNITS[match.group(2)]

    if until - at < MIN_WINDOW:
        raise ClaimError('That window is already over. Pick a deadline in the future.')
    clamped = until - at > MAX_WINDOW
    if clamped:
        until = at + MAX_WINDOW
    return until, clamped


def parse_command(body):
    """
    Read a command out of a comment body.

    As elsewhere in this repository, a command is a whole line: we react to a line
    whose entire content, up to whitespace, is the command, so that a comment
    merely discussing claims does not trigger one.  The last command in a comment
    wins.  Returns a `(name, argument)` pair, or None.
    """
    command = None
    for line in (body or '').replace('\r', '').split('\n'):
        trimmed = line.strip()
        match = re.match(r'claim\b(.*)$', trimmed, re.IGNORECASE)
        if match:
            command = ('claim', match.group(1))
        elif re.fullmatch(r'disclaim', trimmed, re.IGNORECASE):
            command = ('disclaim', None)
    return command


def read_claim(body):
    """
    The claim record carried by a comment body, or None if there is none.

    A marker that is unreadable or missing a field is treated as no claim at all,
    rather than trusted and crashed on: anyone can paste one of these into a
    comment, and the expiry run then clears the stale label as it would for any
    other PR labelled without a live claim.
    """
    if not body or MARKER_PREFIX not in body:
        return None
    start = body.index(MARKER_PREFIX) + len(MARKER_PREFIX)
    end = body.find(MARKER_SUFFIX, start)
    if end == -1:
        return None
    try:
        record = json.loads(body[start:end])
    except json.JSONDecodeError:
        return None
    if not isinstance(record, dict) or not all(
            isinstance(record.get(field), str) for field in CLAIM_FIELDS):
        return None
    return record


def pick_status_comment(comments):
    """The status comment among an already-fetched list, or None if there is none."""
    for comment in reversed(comments):
        if MARKER_PREFIX in (comment.get('body') or ''):
            return comment
    return None


def render_status(claim):
    """Render the status comment body for a claim record."""
    marker = MARKER_PREFIX + json.dumps(claim) + MARKER_SUFFIX
    claimant = claim['claimant']

    if claim['state'] == 'released':
        return f'{marker}\nReview claim by @{claimant} released. This PR is back in the review queue.'
    if claim['state'] == 'completed':
        return f'{marker}\nReview claim by @{claimant} completed — thanks for the review.'
    if claim['state'] == 'expired':
        return '\n'.join([
            marker,
            f'Review claim by @{claimant} expired on {format_utc(parse_iso(claim["until"]))} '
            'without a review.',
            'This PR is back in the review queue.',
        ])

    until = parse_iso(claim['until'])
    window = until - parse_iso(claim['claimed_at'])
    reminders = [hours for hours in REMINDERS_HOURS if timedelta(hours=hours) < window]
    reminders.sort(reverse=True)
    if reminders:
        promise = ('I will remind them here '
                   + ' and '.join(f'{hours}h' for hours in reminders)
                   + ' before that runs out.')
    else:
        promise = 'That window is too short for a reminder, so there will not be one.'

    return '\n'.join([
        marker,
        f'**@{claimant} has claimed this PR for review** until {format_utc(until)} '
        f'({describe_window(window)}).',
        '',
        promise,
        'If no review lands in time the claim is released automatically and this PR returns to',
        'the review queue.',
        '',
        'Comment `claim` to extend, `claim 5 days` / `claim 2026-08-01` for a specific window, or',
        '`disclaim` to release it early. A claim is cooperative, not a lock: it signals intent so',
        'that others can steer around it, and anyone is still free to review this PR.',
    ])


class GitHub:
    """The slice of the GitHub REST API these workflows need."""

    def __init__(self, token, repo):
        self.token = token
        self.repo = repo

    def request(self, method, path, data=None):
        url = path if path.startswith('http') else f'{API_ROOT}/repos/{self.repo}{path}'
        body = json.dumps(data).encode() if data is not None else None
        request = urllib.request.Request(url, data=body, method=method)
        request.add_header('Authorization', f'Bearer {self.token}')
        request.add_header('Accept', 'application/vnd.github+json')
        request.add_header('X-GitHub-Api-Version', '2022-11-28')
        if body is not None:
            request.add_header('Content-Type', 'application/json')
        with urllib.request.urlopen(request) as response:
            payload = response.read()
            link = response.headers.get('Link', '')
        return (json.loads(payload) if payload else None), link

    def get(self, path):
        return self.request('GET', path)[0]

    def post(self, path, data):
        return self.request('POST', path, data)[0]

    def patch(self, path, data):
        return self.request('PATCH', path, data)[0]

    def delete(self, path, data=None):
        return self.request('DELETE', path, data)[0]

    def paginate(self, path):
        """Follow `Link: rel="next"` until the collection is exhausted."""
        separator = '&' if '?' in path else '?'
        url = f'{path}{separator}per_page=100'
        items = []
        while url:
            page, link = self.request('GET', url)
            items.extend(page or [])
            match = re.search(r'<([^>]+)>;\s*rel="next"', link or '')
            url = match.group(1) if match else None
        return items

    def tolerate(self, description, method, path, data=None):
        """
        Make a call whose failure must not stop the workflow.

        Labels, assignees and review requests are all things GitHub may refuse --
        the label may be gone already, the claimant may not be a collaborator --
        and none of those are worth failing a run over.
        """
        try:
            self.request(method, path, data)
            return True
        except urllib.error.HTTPError as error:
            warn(f'{description}: {error.code} {error.reason}')
        except urllib.error.URLError as error:
            warn(f'{description}: {error.reason}')
        return False


def take_claim(github, number, claimant):
    """
    Put the claimant on the PR as both assignee and requested reviewer.

    Requesting a review is the half that shows up in everyone's review queue, but
    GitHub refuses it for a non-collaborator and for the PR's own author, and
    claiming deliberately needs no permissions -- so that half is best-effort.
    """
    github.tolerate(f'#{number}: could not label', 'POST',
                    f'/issues/{number}/labels', {'labels': [CLAIM_LABEL]})
    github.tolerate(f'#{number}: could not assign {claimant}', 'POST',
                    f'/issues/{number}/assignees', {'assignees': [claimant]})
    github.tolerate(f'#{number}: could not request review from {claimant}', 'POST',
                    f'/pulls/{number}/requested_reviewers', {'reviewers': [claimant]})


def release_claim(github, number, claimant=None):
    """
    Drop the claim label and, when a claimant is given, take them back off the PR
    as reviewer and assignee.  Every step tolerates its target being gone already.
    """
    github.tolerate(f'#{number}: could not remove {CLAIM_LABEL}', 'DELETE',
                    f'/issues/{number}/labels/{CLAIM_LABEL}')
    if not claimant:
        return
    github.tolerate(f'#{number}: could not unassign {claimant}', 'DELETE',
                    f'/issues/{number}/assignees', {'assignees': [claimant]})
    github.tolerate(f'#{number}: could not drop the review request for {claimant}', 'DELETE',
                    f'/pulls/{number}/requested_reviewers', {'reviewers': [claimant]})


def has_reviewed_since(github, number, claimant, since):
    """
    Has the claimant looked at the PR since claiming it?  A submitted review or an
    inline review comment both count; a plain issue comment deliberately does not.
    """
    for review in github.paginate(f'/pulls/{number}/reviews'):
        if review['user']['login'] == claimant and parse_iso(review['submitted_at']) >= since:
            return True
    for comment in github.paginate(f'/pulls/{number}/comments'):
        if comment['user']['login'] == claimant and parse_iso(comment['created_at']) >= since:
            return True
    return False


def write_status(github, number, claim, existing):
    """Create or edit the single status comment carrying the claim record."""
    body = {'body': render_status(claim)}
    if existing:
        return github.patch(f'/issues/comments/{existing["id"]}', body)
    return github.post(f'/issues/{number}/comments', body)


def notify_zulip(content):
    """
    Announce something on Zulip, using the same bot credentials and message API as
    the Physlib Zulip bots.

    A missing or broken Zulip setup must never take a workflow down with it: the
    GitHub side of an expiry has already happened by the time this is called, so a
    failure here is warned about and swallowed.
    """
    site = os.environ.get('ZULIP_SITE')
    email = os.environ.get('ZULIP_BOT_EMAIL')
    key = os.environ.get('ZULIP_BOT_API_KEY')
    stream = os.environ.get('ZULIP_STREAM')
    if not (site and email and key and stream):
        warn('Zulip is not configured (ZULIP_SITE / ZULIP_BOT_EMAIL / ZULIP_BOT_API_KEY / '
             'ZULIP_STREAM), skipping the announcement.')
        return False

    # `to` takes a stream name or a stream id, so ZULIP_STREAM can be either.
    body = urllib.parse.urlencode({
        'type': 'stream',
        'to': stream,
        'topic': os.environ.get('ZULIP_TOPIC') or 'PR reviews',
        'content': content,
    }).encode()
    credentials = base64.b64encode(f'{email}:{key}'.encode()).decode()

    request = urllib.request.Request(f'{site.rstrip("/")}/api/v1/messages', data=body,
                                     method='POST')
    request.add_header('Authorization', f'Basic {credentials}')
    request.add_header('Content-Type', 'application/x-www-form-urlencoded')
    try:
        with urllib.request.urlopen(request):
            return True
    except urllib.error.HTTPError as error:
        warn(f'Zulip API error: {error.code} {error.read().decode(errors="replace")}')
    except urllib.error.URLError as error:
        warn(f'Could not reach Zulip: {error.reason}')
    return False


def may_release(github, actor, claimant):
    """
    The claimant can always let go; a maintainer can release someone else's claim
    without waiting for it to time out.
    """
    if actor == claimant:
        return True
    try:
        access = github.get(f'/collaborators/{actor}/permission')
    except (urllib.error.HTTPError, urllib.error.URLError):
        return False
    return access.get('permission') in ('admin', 'maintain', 'write')


def handle_comment(github, event):
    """Handle an `issue_comment` event: the `claim` and `disclaim` commands."""
    command = parse_command(event['comment']['body'])
    if not command:
        print('No claim command in this comment.')
        return
    name, argument = command

    number = event['issue']['number']
    actor = event['comment']['user']['login']
    comment_id = event['comment']['id']
    at = now()

    def react(content):
        github.tolerate('Could not react', 'POST',
                        f'/issues/comments/{comment_id}/reactions', {'content': content})

    def reject(message):
        react('confused')
        github.post(f'/issues/{number}/comments', {'body': f'@{actor} {message}'})

    comments = github.paginate(f'/issues/{number}/comments')
    status_comment = pick_status_comment(comments)
    current = read_claim(status_comment.get('body') if status_comment else None)
    active = current if current and current['state'] == 'active' else None

    if name == 'disclaim':
        if not active:
            print(f'#{number}: nothing to disclaim.')
            react('confused')
            return
        if not may_release(github, actor, active['claimant']):
            reject(f'this PR is claimed by @{active["claimant"]} until '
                   f'{format_utc(parse_iso(active["until"]))}, and only they (or a maintainer) '
                   'can release it. It will be released automatically if no review arrives '
                   'by then.')
            return

        print(f'#{number}: {actor} released the claim held by {active["claimant"]}.')
        release_claim(github, number, active['claimant'])
        write_status(github, number,
                     dict(active, state='released', released_by=actor), status_comment)
        react('+1')
        return

    # Someone else's live claim is not silently overwritten: the point of the whole
    # mechanism is that a second reviewer finds out before duplicating the work.
    if active and active['claimant'] != actor:
        reject(f'this PR is already claimed by @{active["claimant"]} until '
               f'{format_utc(parse_iso(active["until"]))}. It will be released automatically '
               'if no review arrives by then, and you are still free to review it in the '
               'meantime — a claim signals intent rather than locking anyone out.')
        return

    try:
        until, clamped = parse_window(argument, at)
    except ClaimError as error:
        reject(str(error))
        return

    # Extending records a fresh claim time, so the status comment keeps describing
    # the window the claimant actually asked for.
    claim = {
        'state': 'active',
        'claimant': actor,
        'claimed_at': to_iso(at),
        'until': to_iso(until),
    }
    take_claim(github, number, actor)
    write_status(github, number, claim, status_comment)
    react('+1')

    if clamped:
        github.post(f'/issues/{number}/comments', {'body':
                    f'@{actor} that window was longer than the {describe_window(MAX_WINDOW)} '
                    f'maximum, so I shortened it to {format_utc(until)}. Comment `claim` again '
                    'to extend it later.'})
    print(f'#{number}: {actor} claimed until {to_iso(until)}.')


def handle_review(github, event):
    """Handle a `pull_request_review` event: a review completes its claim."""
    number = event['pull_request']['number']
    reviewer = event['review']['user']['login']

    comments = github.paginate(f'/issues/{number}/comments')
    status_comment = pick_status_comment(comments)
    current = read_claim(status_comment.get('body') if status_comment else None)
    if not current or current['state'] != 'active' or current['claimant'] != reviewer:
        print(f'#{number}: review by {reviewer} does not close an active claim.')
        return

    print(f'#{number}: {reviewer} reviewed, completing their claim.')
    # The label goes, but the assignee stays: they are engaged with this PR now,
    # which is the opposite of the case the expiry run handles.
    release_claim(github, number)
    write_status(github, number, dict(current, state='completed'), status_comment)


def expire(github):
    """
    Remind about, complete and release claims on every PR carrying the label.

    Reviews on fork PRs arrive with a read-only token, so the `review` handler cannot
    complete those claims; this hourly run does it instead.  Closed PRs are included
    so that a claim on a PR closed before the next run does not keep its label.
    """
    issues = (list(github.paginate(f'/issues?state=open&labels={CLAIM_LABEL}'))
              + list(github.paginate(f'/issues?state=closed&labels={CLAIM_LABEL}')))
    at = now()

    for issue in issues:
        # The issues endpoint returns issues and PRs alike; we only want PRs.
        if 'pull_request' not in issue:
            continue
        number = issue['number']

        # One fetch serves both the claim record and the reminder markers.
        comments = github.paginate(f'/issues/{number}/comments')
        status_comment = pick_status_comment(comments)
        claim = read_claim(status_comment.get('body') if status_comment else None)
        if not claim or claim['state'] != 'active':
            warn(f'#{number}: labelled {CLAIM_LABEL} with no active claim; clearing the label.')
            release_claim(github, number)
            continue

        claimant = claim['claimant']
        claimed_at = parse_iso(claim['claimed_at'])
        until = parse_iso(claim['until'])
        hours_left = (until - at).total_seconds() / 3600

        if has_reviewed_since(github, number, claimant, claimed_at):
            print(f'#{number}: {claimant} has reviewed; completing the claim.')
            # The label goes, but the assignee stays: they did the work.
            release_claim(github, number)
            write_status(github, number, dict(claim, state='completed'), status_comment)
            continue

        if issue['state'] == 'closed':
            print(f'#{number}: closed without a review from {claimant}; clearing the label.')
            release_claim(github, number)
            continue

        if at < until:
            # Smallest reminder that is both due and shorter than the window: if a
            # scheduled run is skipped and we come back with 20h left, that sends
            # the 24h reminder rather than a stale 48h one.
            due = next((hours for hours in REMINDERS_HOURS
                        if timedelta(hours=hours) < until - claimed_at and hours_left <= hours),
                       None)
            if due is None:
                print(f'#{number}: {claimant} has {hours_left:.1f}h left, no reminder due.')
                continue
            # Keyed to the deadline, so the hourly runs in between do not repeat a
            # reminder and an extension earns a fresh set.
            marker = REMINDER_MARKER.format(until=claim['until'], hours=due)
            if any(marker in (comment.get('body') or '') for comment in comments):
                print(f'#{number}: {due}h reminder for {claimant} already posted.')
                continue

            print(f'#{number}: posting the {due}h reminder for {claimant}.')
            github.post(f'/issues/{number}/comments', {'body': '\n'.join([
                marker,
                f'@{claimant} about {due} hours are left on your review claim for this PR, '
                f'which runs out at {format_utc(until)}.',
                '',
                'Reviewing it before then completes the claim. Comment `claim` to give yourself',
                'more time, or `disclaim` to hand it back to the review queue.',
            ])})
            continue

        print(f'#{number}: claim by {claimant} ran out without a review.')

        release_claim(github, number, claimant)
        write_status(github, number, dict(claim, state='expired'), status_comment)
        # The status comment is edited rather than reposted, which notifies nobody,
        # so the release itself gets its own @-mention.
        github.post(f'/issues/{number}/comments', {'body': '\n'.join([
            f'@{claimant} your review claim on this PR ran out at {format_utc(until)} '
            'without a review, so I have removed you as a reviewer and assignee.',
            '',
            'This PR is back in the general review queue. Comment `claim` if you would still',
            'like to take it.',
        ])})

        # Zulip only hears about the failures: a claim that was honoured is not
        # news, and the point of announcing this one is that the PR now needs
        # somebody else.  GitHub logins are not Zulip names, so the claimant is
        # named rather than @-mentioned.
        repo_name = github.repo.split('/')[-1]
        notify_zulip('\n'.join([
            f'**Review claim expired** on [{repo_name}#{number}]({issue["html_url"]}): '
            f'{issue["title"]}',
            '',
            f'`{claimant}` claimed this review until {format_utc(until)}, but no review '
            'arrived, so they have been removed as a reviewer and the PR is back in the',
            'review queue. It is open for anyone to `claim`.',
        ]))


def main(argv):
    if len(argv) != 2 or argv[1] not in ('comment', 'review', 'expire'):
        print(f'usage: {argv[0]} comment|review|expire', file=sys.stderr)
        return 2

    github = GitHub(os.environ['GITHUB_TOKEN'], os.environ['GITHUB_REPOSITORY'])
    if argv[1] == 'expire':
        expire(github)
        return 0

    with open(os.environ['GITHUB_EVENT_PATH'], encoding='utf-8') as handle:
        event = json.load(handle)
    if argv[1] == 'comment':
        handle_comment(github, event)
    else:
        handle_review(github, event)
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
