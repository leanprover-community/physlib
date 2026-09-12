// Relay: Zulip outgoing webhook (bot got a DM) -> GitHub repository_dispatch.
//
// Zulip POSTs a JSON body here whenever the configured bot receives a
// message. We check it's really from Zulip (shared token) and that it's a
// DM (not a stream mention), then ask GitHub to fire the "zulip-dm"
// repository_dispatch event, which the repo-updates workflow listens for.

export default {
  async fetch(request, env) {
    if (request.method !== "POST") {
      return new Response("Method not allowed", { status: 405 });
    }

    let payload;
    try {
      payload = await request.json();
    } catch {
      return new Response("Bad request", { status: 400 });
    }

    // Zulip includes the token you set when creating the outgoing webhook
    // bot. This is how we know the request actually came from Zulip and not
    // some random caller who found this URL.
    if (payload.token !== env.ZULIP_WEBHOOK_TOKEN) {
      return new Response("Unauthorized", { status: 401 });
    }

    // Only trigger on direct messages, not @-mentions in a stream.
    if (payload.trigger !== "private_message") {
      return jsonResponse({});
    }

    const dispatchResp = await fetch(
      `https://api.github.com/repos/${env.GITHUB_OWNER}/${env.GITHUB_REPO}/dispatches`,
      {
        method: "POST",
        headers: {
          Authorization: `Bearer ${env.GITHUB_TOKEN}`,
          Accept: "application/vnd.github+json",
          "X-GitHub-Api-Version": "2022-11-28",
          "User-Agent": "zulip-dm-relay",
        },
        body: JSON.stringify({ event_type: "zulip-dm" }),
      }
    );

    if (!dispatchResp.ok) {
      const errText = await dispatchResp.text();
      console.error("GitHub dispatch failed", dispatchResp.status, errText);
      return jsonResponse({
        content: "Sorry, I couldn't trigger the report (GitHub API error).",
      });
    }

    return jsonResponse({ content: "Triggered the repo updates report." });
  },
};

function jsonResponse(body) {
  return new Response(JSON.stringify(body), {
    headers: { "Content-Type": "application/json" },
  });
}
