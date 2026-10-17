# Setting up the Physlib build cache bucket

Physlib publishes its compiled artifacts so contributors do not have to build
the library from source. This uses Lean's `lake cache`, which is used within get_cache.lean
to fetch the artifacts from a Cloudfare R2 bucket. R2 is the best choice for a small amount of
storage, with lots of people downloading it.

## 1. Create the bucket

Call it `physlib-cache`. Add its S3 API endpoint into `lake-cache.toml` as the write path.

## 2. Allow anonymous reads — done

Contributors fetch without credentials, so the bucket needs a public URL. You can use the public
development URL for testing, but it is better to deploy with a custom domain. We set up
`lake-cache.physlib.io` for this purpose.

Note the resulting hostname; it goes into `lake-cache.toml` at step 5.

Only reads become public. Writes stay behind the key from step 3.

## 3. Create an API token for CI

Create a token with write access, limited to
`physlib-cache`. Keep the Access Key ID and Secret Access Key.

Lake expects them as a single SigV4 credential, colon-separated:

```
<ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>
```

## 4. Add the GitHub secret

Add the keys as a GitHub secret called `LAKE_CACHE_KEY`, set to the colon-joined pair above.

## 5. Fill in the read endpoint — done

Both endpoints in `lake-cache.toml` are set. To move to a custom domain, edit
the `physlib-r2` service — hostname only, no scheme, no trailing slash. `physlib-r2` is the name
of the anonymous read service in cloudflare.

## 6. Verify

Test these commands work within the Physlib repo:

```bash
lake exe get_cache
lake build
```

## Notes

- Costs to watch as the project grows: storage past 10GB, and Class A
  (write) operations. Egress, the usual scaling problem, is free on R2.
- Each half publishes under its own scope, `physlib-master/<toolchain>/physlib`
  and `.../alpha`, so the two CI jobs do not overwrite each other's mappings.
  The workflow and `scripts/dev/get_cache.lean` must build the same strings.
