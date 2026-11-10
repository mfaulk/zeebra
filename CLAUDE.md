# CLAUDE.md

Repo-specific guidance for coding agents working on Zeebra. The user-global
policies (Red-Green TDD, Conventional Commits, README upkeep, sparse source-file
doc comments, rust-analyzer/LSP for semantic Rust work) apply here unchanged;
this file adds only what is specific to this repository.

## Multi-agent coordination (claiming work)

Several agents share this repo and the single board
([Zeebra, project #7](https://github.com/users/mfaulk/projects/7)). GitHub issues
are the **coordination substrate**: an agent claims an issue before working it,
keeps the claim alive while active, and releases it when done or abandoning.
This is what stops two agents doing the same work, and it makes the project
state self-describing for whoever — human or agent — looks next.

Everything below is implemented by `scripts/agent/zb-claim.sh`. Prefer the
script over hand-rolled `gh` calls; its reads distinguish failure from emptiness
(see §0) and hand-rolled ones usually do not.

### 0. Three outcomes, never two

Every read in the claim tooling exits **0 = data, 1 = genuinely empty, 2 = the
read FAILED**. This matters more than it looks: a rate-limited or
unauthenticated `gh` prints nothing and exits 0, and through a `| jq` pipeline
that empty output is indistinguishable from "nothing is claimed" — which would
hand the same issue to every agent at once.

**Branch on the status, never on whether stdout was empty.**

```bash
rc=0; queue="$(./scripts/agent/zb-claim.sh orient)" || rc=$?
case $rc in
  0) echo "$queue" ;;
  1) echo "nothing open and unclaimed" ;;
  *) echo "BOARD READ FAILED — this is not an empty queue" >&2; exit 2 ;;
esac
```

### 1. Never run file-mutating agents on a shared checkout

`Agent(..., isolation: "worktree")` is not a reliable guarantee of file
isolation for concurrent writers. Rules:

- **One writer per checkout.** If you fan out, give each agent its own real
  `git worktree` on its own branch (`git worktree add ../zb-<slug> -b <branch>
  origin/main`) and have it operate only there.
- Prefer **sequential** implementation where the work touches overlapping files.
  In this repo the contention magnets are `src/grobner/f4/`, `src/linalg/`, and
  `src/fields/` — several open issues touch each.
- Read-only fan-out (search, audit) parallelizes safely; **writes do not**.
- After any parallel run, `git status` the orchestrator checkout and confirm no
  agent touched files outside its scope.
- Give each agent a **private `CARGO_TARGET_DIR`** — `target-<issue>` inside its
  own worktree, with `RUSTC_WRAPPER=""` — so concurrent builds neither clobber
  each other nor link against a stale rlib. `.gitignore` covers `/target-*`,
  but prefer an explicit file list to `git add -A` regardless.

`cargo test --doc` is the one suite that fails for reasons that are not the
diff. `/tmp` here is a 252 G tmpfs, its pages are RAM, and when it is near full
the linker dies on its mapped temporaries — dozens of doctests failing at
*varying* line numbers with `ld terminated with signal 7 [Bus error]`. A real
breakage fails the same test every time. Check `df -h /tmp` and `uptime`, then
re-run with `TMPDIR` off tmpfs; one session went from 32/70 failing to 67/67
passing on that alone. Do not retry in a loop, which only adds load.

All agents commit as the same git user, so the assignee cannot tell them apart.
The distinguishing identity is **worktree + branch**:

```bash
./scripts/agent/zb-claim.sh id      # e.g. zb-two-adicity@feat/two-adicity
```

That id is *derived*, so it can change under you — a branch rename, a rebase
onto a new base, a retargeted PR. Every claim therefore also carries a **claim
token**, minted once per checkout and kept in the worktree's own git directory:

```bash
./scripts/agent/zb-claim.sh token   # e.g. fa9315b49fb5720b
```

The token is what proves a claim is yours when the id no longer matches the one
you claimed under (§3).

### 2. Orient before picking up work (every session start)

```bash
git fetch --prune
./scripts/agent/zb-claim.sh orient
```

`orient` lists open issues that are **unclaimed** and **unblocked**, ranked
`High → Medium → Low → unset`. Priority is a board field rather than a label, so
the read joins each issue to its board row.

The read is **paginated**, because GraphQL caps `first:` at 100 and this repo has
more open issues than that. A pagination walk it cannot finish is status **2**
under §0, not a shorter queue — the fourth outcome §0 was not written against is
"succeeded, returned data, and was incomplete", which is how #448 hid the 12
newest issues behind a `rc=0` queue that looked complete. If `orient` reports
more than `ZB_ORIENT_MAX_PAGES` pages (default 20), raise it rather than reading
the failure as an empty tail.

Selection rule: take the highest-priority unclaimed, unblocked issue. Skip
anything labeled `agent:claimed` unless its lease is stale (§5), anything
labeled `blocked`, and anything a human has assigned to someone else. Respect
stated dependencies — several issues name a prerequisite in their body (for
instance #124 depends on #119, which depends on #122).

### 3. Claim it, before writing any code

A claim is a **structured comment + the `agent:claimed` label + self-assign +
board Status = In Progress**. The comment carries the identity and a **4-hour
lease**; the label alone cannot expire, because a label does not record when it
was applied.

```bash
./scripts/agent/zb-claim.sh claim 119 "implement two-adicity and the two-adic root of unity"
```

That writes a marker other agents parse — keep the shape exactly:

```
<!-- zb-claim agent="<id>" token="<token>" at="<iso8601>" until="<iso8601>" -->
```

`token=` is optional when *reading* — markers written before it existed parse
with no token and resolve by id alone — but every marker you write must carry
it, which `claim` and `heartbeat` do for you.

`claim` re-reads the issue afterwards and tells you whether you actually hold
it. **Among claims inside the current lease window, the earliest `at=` wins** —
two agents claiming in the same second both see their own comment land, so the
tiebreak has to be a property of the data, not of who looked last.

```bash
./scripts/agent/zb-claim.sh verify 119      # rc 0 = yours, rc 1 = back off
```

**If `verify` exits 1 you lost: `withdraw`, and do not `release`.**

```bash
./scripts/agent/zb-claim.sh withdraw 119    # retract your own claim only
```

The distinction is the whole of #544. The label, the assignee and the board row
are **one each and belong to the winner**; `release` removes them, so the loser
of a race — following the instruction this paragraph used to give — stripped the
winner's claim while their lease was still live and their work still in flight.
Nothing in the output said so, and `orient` reads the label, so the issue then
presented as available to the next agent along. `withdraw` writes a marker the
resolver reads and changes no shared state at all. `release` now refuses when
another agent holds the claim and names `--force` for the cases that genuinely
need it — a human cleaning up after a dead agent, mostly.

A withdrawal also means something to the tiebreak: a withdrawn claim stops
competing, so the next-earliest standing claim takes the issue. That is what
makes conceding a race a real act rather than a comment.

**A rename does not cost you the claim.** The tiebreak picks the earliest live
claim; the token then decides whether that claim is yours, by any of three
routes — the marker carries your token, its id is the id you have now, or its id
appears in another live marker bearing your token (which is how an issue claimed
before the token existed and heartbeaten after it is still recognized). Only you
can write a marker carrying your token, so none of this can take another agent's
claim, and the resolution rule itself is untouched. `verify` says which route
matched when the id has changed:

```
verified: #325 is held by this checkout, claimed as zb-325-claim@fix/325-claim-branch-rename
  (matched by alias; the id is now zb-325-claim@fix/325-rename-proof)
```

If you rename a branch on an issue claimed **before** the token existed, with no
heartbeat since, there is nothing to prove ownership with and `verify` will
report `LOST RACE` against you. Heartbeat once under the new script first, then
rename.

### 4. Keep the claim alive

The lease is 4 hours. A claim is **live** if **any** of these hold, else
**stale** and reclaimable:

- an open linked PR exists (`Closes #NNN` / `Fixes #NNN`) — always live; or
- the newest marker's `until=` is still in the future; or
- a commit landed on the claim branch inside the lease window.

The cleanest heartbeat is to **open a draft PR early** with `Closes #NNN` in the
body: it pins the issue to In Progress and signals liveness with no timer to
babysit. Working long without a PR, refresh before the lease expires:

```bash
./scripts/agent/zb-claim.sh heartbeat 119
./scripts/agent/zb-claim.sh state 119       # live | stale
```

A marker with an unparseable `until=` counts as **stale** by design — a corrupt
claim must not strand an issue behind something no one can disprove.

### 5. Reclaiming a stale claim

```bash
./scripts/agent/zb-claim.sh reap                 # every claimed issue whose lease expired
./scripts/agent/zb-claim.sh reclaim 119 "<intent>"
```

`reclaim` refuses if the lease is live, and announces the takeover in a comment
so the trail stays honest. Before reusing or discarding the previous agent's
branch, look at what is there (`git fetch && git log origin/<their-branch>`) and
salvage usable commits rather than silently dropping them.

### 6. Release

- **Finished** → open the PR with `Closes #NNN`. Merging closes the issue and
  moves the board to Done. Drop the working label:
  `./scripts/agent/zb-claim.sh release 119`. Leave the issue open until the PR
  merges; the PR keeps it In Progress — and `orient` reads the open PR, not the
  label, so dropping it does not put the work back in anyone's queue (#544).
- **Abandoning or handing off** → never leave a silent dangling claim. Comment
  what was and was not done and why, then:
  `./scripts/agent/zb-claim.sh release 119 --abandon`, which also removes the
  assignee and returns the board row to Todo.
- **Lost a race** → `withdraw`, never `release`. See §3.

Both `release` forms refuse if another agent holds the claim, because both touch
state there is only one of.

**A green check is not a green merge.** CI tests your branch merged into `main`
*as of when the run was queued*, and nothing re-runs when `main` moves — which is
how #311 and #324 were each green and the merge of both a panic, with no textual
conflict for git to refuse. The `merge-staleness` job warns when the gap since
your run touches files you also changed; that warning is **advisory and does not
block**, so acting on it is yours to do: rebase onto current `origin/main` and
let CI run again before merging. Branches are not gated on being current because
the cost is measured and unaffordable — see `docs/guide/development.md`,
"Testing the merged result". And if your change touches the external comparands or the corpus,
run the coverage assertion from that section before
merging: CI has no msolve, so those tests pass on the runner without being run.

### 7. Keep board state truthful

The next agent's orientation is only as good as the state you leave behind. File
issues for follow-ups, bugs, and scope creep you discover, add them to the board
explicitly, set Priority, and link parent ↔ sub-issue both ways.

## Board reference

| Thing | Value |
|---|---|
| Project | [#7 Zeebra](https://github.com/users/mfaulk/projects/7) (private) |
| Views | Open, Bugs, Polynomial System Solving, Blocked, Owner Actions, Opportunities |
| Status | `Todo` / `In Progress` / `Done` |
| Priority | `High` / `Medium` / `Low` — a board field, not a label |
| Coordination labels | `agent:claimed`, `blocked`, `owner-action`, `opportunity` |

Every view is grouped by Priority and carries Priority, Milestone, Linked pull
requests, Status, and Labels. Note that **group-by is not settable through the
GitHub API** — it is a UI-only setting, so a view created by script needs its
grouping set by hand (View → Group by → Priority → Save view, then confirm in
the modal).

## Tests for the agent tooling

`scripts/agent/zb-claim.sh` has unit tests over its pure half — marker parsing,
race resolution, and the lease arithmetic:

```bash
bash scripts/agent/test/zb-claim-test.sh
bash tools/test/rss-guard-test.sh
bash tools/test/check-measurement-provenance-test.sh
bash tools/check-measurement-provenance.sh
shellcheck -S warning scripts/agent/*.sh scripts/agent/test/*.sh \
  tools/*.sh tools/test/*.sh tools/external/*.sh tools/external/smoke/*.sh
```

`tools/rss-guard.sh` is the memory-ceiling guard for benchmark runs; its tests
cover the pure half against a synthetic `/proc`, because the failure it exists
to prevent is a guard watching the wrong pid. Never find a measured binary with
`pgrep -f`: a heredoc script's own text is in its wrapper's cmdline, so the
pattern matches the wrapper (#328).

`tools/check-measurement-provenance.sh` is the only one of these that reads the
repository's own documents rather than a script: a document publishing a timing
or memory figure must say in its header which commit it came from. A finding is a
document to fix, not a broken script. Writing a new figure means writing the
commit beside it — `docs/research/external-comparison-protocol.md` §10 is the
rule, and #335 is what it costs when nobody does.

All of the above run in CI (the `agent-scripts` job). The subcommands that call `gh` are
deliberately not unit-tested: they are thin wrappers whose failure modes are the
API's, and a test that mocked `gh` would pin the mock rather than the behaviour.
