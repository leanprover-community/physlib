# Zulip DM relay

Cloudflare Worker that bridges Zulip to GitHub Actions: when the configured
Zulip bot receives a direct message, this relay fires a `repository_dispatch`
event (`zulip-dm`) against this repo, which the
[Repo Updates workflow](../.github/workflows/repo-updates.yml) listens for.

GitHub Actions has no native "Zulip DM" trigger, and Zulip's outgoing webhook
can't call the GitHub API directly (it can't attach the auth token GitHub
requires), so this small service sits in between.

## Deploy

1. Create a free Cloudflare account at https://dash.cloudflare.com/sign-up.
2. Create a GitHub fine-grained personal access token scoped to this repo
   only, with **Contents: Read and write** permission (required for
   `repository_dispatch`).
3. From this directory:
   ```bash
   npx wrangler login
   npx wrangler secret put GITHUB_TOKEN        # paste the token from step 2
   npx wrangler secret put ZULIP_WEBHOOK_TOKEN  # any random string, e.g. `openssl rand -hex 20`
   npx wrangler deploy
   ```
   This prints a `*.workers.dev` URL.
4. In Zulip, create an **Outgoing webhook** bot (Settings -> Personal
   settings -> Bots -> Add a new bot), interface "Generic", endpoint URL =
   the `workers.dev` URL from step 3, and set the bot's token to the same
   string used for `ZULIP_WEBHOOK_TOKEN` above.
5. DM the bot. It should trigger a "Repo Updates" run in the Actions tab
   within a few seconds.

Debug with `npx wrangler tail` while sending a test DM.
