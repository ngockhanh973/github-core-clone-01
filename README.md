# github-core-clone-01

Standalone GitHub-compatible git forge in one process, Node 22 standard library only.

- Git smart HTTP: protocol v2 upload-pack (`ls-refs`, `fetch`, shallow/deepen), v0 receive-pack with `report-status` / `side-band-64k` / `delete-refs`, fast-forward enforcement per ref.
- REST v3 under `/api/v3`: repositories, branches, commits, contents, labels, issues + comments, pull requests + files + squash merge, pagination via `Link: rel="next"`.
- GraphQL v4 at `/api/graphql`: the documents `gh` and `github-mcp-server` send (viewer, repository, issues, pull requests, mutations, `__type` introspection, `node(id:)`, batched operations).
- MCP at `/mcp`: Streamable HTTP JSON-RPC 2.0, modern `server/discover` (revision 2026-07-28) plus the legacy `initialize` handshake; tools `create_repo`, `get_repo`, `create_issue`, `list_issues`, `create_pull_request`, `merge_pull_request`, `get_issue`.

Run: `node main.ts` (binds an ephemeral port; with `MAKEFUN_ENV_URL` set it registers with the suite and exits when the suite says done; without it, it serves on `$PORT` or an ephemeral port for local runs).

Auth: every API call needs `Authorization: Bearer $MAKEFUN_SHOP_TOKEN` (the token owner's login is the repository owner).
