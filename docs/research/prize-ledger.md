# Prize ledger: which programmes are claimable, stated separately from what is solved

**Measured at:** not measured here — no figure below is a measurement of this crate. The money is
the organizers' own, quoted; the three Zeebra results §5 assesses are quoted from the documents
that measured them, and are cited rather than restated
([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

Reference for #200 (A8), child of #65; related to #67, #71, #140.
`docs/research/ef-cryptanalysis.md` is the survey of **parameters and objectives** — what each
programme asks for. This document records only **claimability** — whether a reward can still be
collected — because that is a different fact, it moves on the organizers' calendar rather than on
the mathematics, and conflating the two is how a closed programme's dollar figures came to read as
a live opportunity in `poseidon.md` §5a.

Nothing here was submitted, registered, applied for, or raised with any organizer. This is
bookkeeping.

---

## 0. The distinction, in one case

Three rows in the registry — `poseidon256-cico-2025-rf6-rp11`, `poseidon256-cico-2025-rf6-rp16`,
`poseidon64-cico-2025-rf6-rp13` — are the only rows with **no public solution recorded**, which is
why they are the most interesting problems in it. They each carried a dollar figure and no window.

Both of these are true, and they are not the same fact:

- **unsolved**, re-verified 2026-11-08 — a durable statement about mathematics, and the registry's
  `ExternalStatus::NoneRecorded { as_of }` is the field for it;
- **unclaimable**, as of 2025-12-01 — a statement about a funding programme that closed by its own
  terms. `ExternalStatus` cannot say this and should not be taught to.

Solving one of them would still be a first public solution of a registered instance. That is the
research result, and it does not depend on the prize existing.

## 1. The vocabulary: five states

| state | means | what it licenses |
|---|---|---|
| **open** | the window is current and the organizer accepts submissions | may be described as claimable, with its deadline |
| **paused** | the organizer has suspended it; the window has not expired and it could resume | not claimable now; track, do not plan against |
| **finished** | the organizer declares the programme complete — typically every tier claimed | not claimable; the amounts are historical record |
| **expired** | the window ended by its own stated terms, with or without a closing announcement | not claimable; the amounts are historical record |
| **unverified** | no status statement was located — silence, or a source unreachable from here | **never read as open.** Record the failure with its date |

**The standing rule.** A reward figure is never written anywhere in this repository without all
three of: the programme **window**, the **read date**, and one of these five **states**. `expired`
and `finished` are kept apart on purpose: "finished" is an organizer's declaration and "expired" is
arithmetic on a date, and a reader who sees neither cannot tell which kind of claim is being made.

## 2. The ledger, read 2026-11-08

Status wording is the organizer's, verbatim, from <https://www.poseidon-initiative.info/> unless
another source is named. Read **2026-11-08**; HTTP 200.

| programme | status, verbatim | window | budget | state | bearing on Zeebra |
|---|---|---|---|---|---|
| **Attack Reward Program 2026** | "The paper should be made public (ePrint) by the end of 2026." | to **2026-12-31** | "The minimal prize is $5000, the entire award fund is $90000." | **open** | the only presently claimable item anywhere in this ledger. It rewards a **paper**, not a witness. §5 |
| Bounty Program 2026 (container) | "Bounty program runs till January 1st, 2027." | to 2027-01-01 | $150,000 | open as a container; all four of its problems are finished or paused | — |
| — 2026 CICO problem | "UPDATE: THE PROGRAM IS FINISHED" | within the above | $6,000 / $10,000 / $15,000, verified 2026-04-10, 2026-05-06, 2026-07-06 | **finished** | the three `poseidon31-cico-rf6-rp{6,8,10}` registry rows. Best available outcome is a reproduction |
| — 2026 Zero-test problem | "UPDATE: THE PROGRAM IS FINISHED" | within the above | $40,000; six records claimed 2026-06-03 … 2026-07-27 | **finished** | objective never modelled here |
| — 2026 Density problem | "UPD: PAUSED" | submission windows "Before August 1st 2026" and "August 1st–December 1st 2026" | $40,000 | **paused** | objective never modelled here |
| — Poseidon1 Collision Prize | "UPDATE: THE PROGRAM IS PAUSED STARTING 1 AUG 2026 AoE." | "Runs till January 1st, 2029" | $992,000; `q = 3` $32K "Claimed on April 6th 2026", `q = 4` $64K, `q = 5` $128K, `q = 6` $256K, `q = 7` $512K | **paused** | a partial-collision objective, not a solving target. §6 |
| **Bounty Program 2025** | "Bounty program runs till December 1st, 2025." | **ended 2025-12-01** | $130,000 | **expired** | the three unsolved registry rows. The instances remain open; **the rewards do not.** §0 |
| Short Term Grants 2026 | applications "by June 1st, 2026" | ended 2026-06-01 | $20,000–$40,000 | **expired** | names *Attack with resultants* explicitly (`ef-cryptanalysis.md` §3.5) |
| Gröbner Basis Exploratory grants | applications "by April 1st, 2025" | ended 2025-04-01 | — | **expired** | the programme that specifies this crate's pipeline (`ef-cryptanalysis.md` §3.5) |
| EF ZK Hash Cryptanalysis Bounties 2021–2022 | "Solutions should be sent to … before November 30th 2022."; the page carries **no** closing statement | ended 2022-11-30 | "Total Bounty Budget -- $200 000." | **expired** by its own terms | #71's scope. Source <https://www.zkhashbounties.info/>, read 2026-11-08 |
| MiMC hash challenge | **no status statement and no deadline on the page** | not stated | "$20,000" for "Collisions on the proposed 220 rounds, on either of the fields, targeting 128-bit security" | **unverified** | `ef-cryptanalysis.md` §5 rejects it as a solving target on objective grounds. Source <https://crypto.ethereum.org/bounties/mimc-hash-challenge>, read 2026-11-08 |
| LowMC cryptanalysis challenge | "A third round is now running until April 27 2021"; latest news entry 19 October 2021, reporting the third round's results | ended 2021-04-27 | "In total, EUR 22k may be earned in this current round", against original sponsorship of "USD 50k from Microsoft and EUR 50k from iov42" | **expired** | `additional-benchmarks.md` §5 already declines it: no challenge files, and scoring is on claimed complexity. Source <https://lowmcchallenge.github.io/>, read 2026-11-08 |
| Fukuoka MQ Challenge | no prize: "a hall of fame recognition system rather than cash prizes"; latest solved record 2026/09/28 | open-ended; "You are welcome to download and solve any challenge and submit the answer to us." | **none — no monetary award exists** | not applicable | the registry's Fukuoka rows. Nothing to classify, because there is no reward figure. Source <https://www.mqchallenge.org/>, read 2026-11-08 |

**The container row is not a loophole.** "Bounty program runs till January 1st, 2027" is true of the
2026 programme as a whole while each of its four problems is separately finished or paused. A
reader who quoted only the container would conclude there is $150,000 available; there is not.
State is per problem, and the container is recorded so that the discrepancy is visible rather than
discoverable.

## 3. What moved in the two days since #200's snapshot

#200's table was read 2026-11-06. Re-read 2026-11-08:

- **No status wording changed.** All six Poseidon-family statuses re-read identical, character for
  character where quoted.
- **Two details the earlier snapshot did not carry**, both recorded above: the Density problem's two
  explicit submission windows, and the Zero-test problem's six claimed records running to
  2026-07-27.
- **One quote tightened.** #200 recorded the collision prize as "listed through 2029-01-01"; the
  page's own words are "Runs till January 1st, 2029".
- **One correction to the record, and it matters for §5.** `ef-cryptanalysis.md` §11 records the
  *Survey of attacks on Poseidon and Poseidon2* as `https://eprint.iacr.org/2024/886.pdf`,
  unreachable here with a `403`. Two findings on 2026-11-08: the page's own "Survey of attacks"
  link is a Google Drive file, which **is** reachable and extractable here; and ePrint 2024/886 is
  a **different paper** — Yang, Zheng, Yang, Liu and Tang, *A New Security Evaluation Method Based
  on Resultant for Arithmetic-Oriented Algorithms* — so the old citation pointed at the wrong
  document. The survey is Grassi, Rechberger, Schofnegger and Khovratovich, **22 November 2024**.
  Which document the page linked before 2026-11-08 is not established here and is not inferred.

## 4. Second sources (research question 1)

Every status in §2 is the organizer's own page. Question 1 asks what a *second* primary source says.

| programme | second source | verdict |
|---|---|---|
| 2026 bounty problems | <https://github.com/khovratovich/poseidon-tools> — "plus verifiers and sample challengers for the Poseidon Initiative 2026 bounties", with `cico_verifier.py`, `zerotest_verifier.py`, `density_verifier.py`, `partial_collision_verifier.py` | **confirms the problems, silent on status.** The repository carries no open/closed/paused statement and no tier claims, so it can neither confirm nor contradict any row of §2. Recorded as silence, not as agreement |
| 2025 (Nov-2024) programme, and the three unsolved tiers | ePrint **2026/150**, Bak, Bariant, Boeuf, Hostettler, Jazeron, received 2026-01-30, revised 2026-02-11 — already read, and listed as read in `elimination-beyond-grobner.md`'s source table | **confirms.** "In november 2024, the Ethereum foundation (EF) issued a bounty program with challenges on Poseidon and Poseidon2." The authors report solving "the first 3 proposed instances of Poseidon2-31m and Poseidon2-31k, along with solutions for the first two Poseidon-256 instances", and that "These solutions have been confirmed to be correct and eligible for bounty by the Ethereum fundation". The *first two* Poseidon-256 tiers are `R_P = 8` and `R_P = 9`; `R_P = 11` and `R_P = 16` are not among them. So the registry's `NoneRecorded` on those rows is corroborated by a second primary source and not only by the organizer's table |
| the Attack Reward Program's eligibility reference | *Survey of attacks on Poseidon and Poseidon2*, Grassi, Rechberger, Schofnegger, Khovratovich, 22 November 2024, via the organizer's own link | **obtained and read 2026-11-08.** Its §3.3.3 surveys the Gröbner route ([BSGL20], [Mei22], [Ste24]) and §3.5 tabulates the concrete attacks ([BCD+20], [KR21], [ABM24]). This is the bar §5 measures against |
| the state of the art the resultant route competes with | ePrint **2026/1905**, Bak and Hostettler, received 2026-09-07 — already read in full, per `elimination-beyond-grobner.md`'s source table (§1, §2.2, §2.3, §4, §6.2, §6.3) | **a published improvement, post-dating the survey.** It treats CICO-2 as "a bivariate system `P(X, Y) = Q(X, Y) = 0` where the polynomials have total degree delta = d^(RF +RP)", proposes an adapted algorithm, and reports "a practical speedup compared to the previous approaches". It claims no prize. §5 has to clear this, not only the survey. Its abstract page was re-read here 2026-11-08 to confirm the citation; the analysis is the existing document's, not this one's |
| 2026 CICO, EF announcement | none located | **not found.** No EF announcement or blog post confirming the CICO programme's completion was located on 2026-11-08. Recorded as not found, which is not evidence either way |

**Reachability, corrected.** `eprint.iacr.org` **abstract landing pages** (`/2026/150`, `/2026/1905`,
`/2024/886`) answered normally here on 2026-11-08; it is the `/<id>.pdf` paths that return `403`, as
`minrank.md` §9 and `fukuoka-mq.md` §13 record. A citation can therefore be checked against its own
abstract page without the PDF. The one source **not** obtained as text in the normal way was the
survey, whose Drive viewer page carries no extractable text; the file itself downloads and
`pdftotext -layout` reads it.

**Rejected as a source, permanently.** Third-party prize aggregators. One
(`prizeproblems.org/problems/167/`) surfaced again in a search on 2026-11-08 with a Poseidon-31
entry. It is not the organizer. No figure, status or date in this repository may cite it, and it is
named here only so the rejection does not have to be re-derived.

## 5. Research question 2: the Attack Reward Program 2026 — an owner decision

**This section is an assessment of facts, not a recommendation to act, and nothing has been
submitted or applied for.** Whether to pursue an award is the repository owner's decision alone.
It is recorded here because it is the only item in this ledger with a clock on it, and tracked as
an `owner-action` issue so it cannot lapse silently.

### 5.1 The criteria, quoted

From <https://www.poseidon-initiative.info/>, read 2026-11-08:

> "Attack should be on a reduced-round version of one of three instances described above:
> Poseidon-256, Poseidon-64, or Poseidon-31."

> "Attack should be an improvement to the attacks presented in the survey"

> "The amount of the award is proportional to the paper merit and remains at discretion of Ethereum
> Foundation. The minimal prize is $5000, the entire award fund is $90000."

> "The paper should be made public (ePrint) by the end of 2026."

> "Poseidon authors can not be applicants to the grants nor to the award program."

The operative deadline is therefore **2026-12-31**, and the operative bar is "an improvement to the
attacks presented in **the survey**" — a narrower condition than "an improvement on published
attacks". The survey is §4's: Grassi, Rechberger, Schofnegger, Khovratovich, 22 November 2024.
Its §3.3.3 surveys the Gröbner-basis route through [BSGL20], [Mei22] and [Ste24]; its §3.5 table of
concrete attacks is six rows drawn from [BCD+20], [KR21] and [ABM24], every one of them a
complexity against a stated `(n, t, d, M)` at a stated round count — `2^61` and `2^125` zero-sum
distinguishers, `2^236` assuming a weak linear layer, and three algebraic rows from `2^351.56` to
`2^712.98` of which only the Gröbner step is below the security level. The table is not ranked here
because the rows target different instances at different security levels; what matters below is
that an eligible result has to move one of them.

### 5.2 The three candidate results, each traced to a committed record

Each is a real, verified, committed result. None is asserted here beyond what its own document
says, and each document's own disqualifying sentence is quoted rather than paraphrased.

| candidate | record | what the record itself says |
|---|---|---|
| a verified CICO witness at the official state width `t = 16` | `full-width-poseidon.md` §3.5; witness re-verified through the permutation in-crate | at `R_F = 2, R_P = 0` against the official `R_F = 6, R_P ∈ {6, 8, 10}`. "**It is not evidence about any official target.**" The registry records it as a witness for a faithful reduction and names what it reduced from |
| the resultant route reaching four rounds where F4 reaches two | `resultant-elimination.md` §6.1; witnesses at `research/witnesses/resultant-cico-t16.json` | "It is a frontier on *faithful reduced-round instances*, not on an official public problem", with the official targets still priced at `3.3 × 10^15` field operations and above. Credit "belongs to #162 and to the formulation, not to the subgroup interpolation", and the NTT route is "a **measured negative result**" |
| Graeffe root finding at degree `3^13` in 3.1 s | `graeffe-root-finding.md` §4.4, §8, §9 | "**A fast root finder is not the published attack.**" "**A successful Graeffe benchmark is not a successful attack.** No figure in this document may be quoted as progress on a registered challenge." The 57.1-hour comparand is "an extrapolation of `roots`, not a measurement of it", and `roots` is **this crate's own earlier code**, not a published attack |

### 5.3 The assessment

On the facts committed to this repository, **none of the three is an "improvement to the attacks
presented in the survey"**:

- None of them improves a complexity on any row of the survey's §3.5 table, and none of them is a
  complexity claim about a full or official instance at all. Two are results on faithful
  reductions; one is a stage benchmark.
- The baseline each one beats is internal. The Graeffe result's comparand is
  `src/poly/univariate/roots.rs`; the resultant result's is Zeebra's own F4. "An improvement to the
  attacks presented in the survey" is not satisfied by beating one's own previous implementation,
  and this repository has already written that down twice, independently of this issue:
  `MILESTONE-ALGORITHMIC-ELIMINATION.md` and `MILESTONE-COMPETITIVE-MQ-SOLVING.md` both record that
  "**a faster implementation of an established algorithm does not qualify**".
- For the resultant route specifically the bar has moved **above** the survey since the survey was
  written, and this repository has already read where it moved to. ePrint 2026/1905 (Bak and
  Hostettler, September 2026) is a published improvement to the bivariate-resultant CICO-2 attack,
  reporting "a practical speedup compared to the previous approaches".
  `elimination-beyond-grobner.md` §4 reads its measurements and records that for CICO-2 Gröbner is
  the *least* competitive of three methods, "by about 7 500x in time at the only instance all three
  reach", and §6.2 that "Zeebra has no Sylvester construction, no subresultants and no Poseidon2".
  An improvement claim over the current state of the art on this objective is therefore further
  away than the survey alone would suggest, not closer.

What this repository *does* hold that the programme's own framing values, stated without
overclaiming: the Gröbner Basis Exploratory call asks for per-stage cost and memory separated across
feasible `(R_F, R_P)`, extrapolated to a formula (`ef-cryptanalysis.md` §3.5), and that
stage-separated table is what M23/M24 produced. That is a *measurement* programme, not an attack
improvement, and the Attack Reward Program rewards the latter.

### 5.4 What the owner would have to decide

By **2026-12-31**, and only by the owner:

1. whether anything beyond §5.2's three candidates — in hand or reachable before the deadline — is
   an improvement to an attack in the survey. §5.3 answers only for those three, on the records
   that exist today; what else might qualify, and whether it is worth the writing, is the owner's
   judgement and not an assessment this document can make;
2. if so, whether to write and publish an ePrint paper inside the remaining window;
3. if not, to record the programme as declined, so that it lapses deliberately rather than silently.

Tracked at **#564**, labelled `owner-action`, with the deadline in its title. No contact with the
organizers has been made and none is proposed by this document.

## 6. Research question 3: the Poseidon1 collision prize, recorded once

`q = 4` is $64,000 and the fund is $992,000, which is why the question keeps being asked. The
answer is structural and has nothing to do with the amount, so it is recorded here once, with the
one condition for reopening it stated in the last paragraph.

The objective is a **partial collision**: find 15-element `X ≠ Y` with
`H(0xc09de4, X) = H(0xc09de4, Y)` agreeing on the first `q` output elements
(`ef-cryptanalysis.md` §3.1). That is birthday-type. The source's own generic bound is
`m(m-1)/(2 p^t)` for `m` hash calls, and its per-tier expected complexities — left inside a LaTeX
`\begin{comment}` block and therefore absent from the compiled PDF — run from `2^31.5` at the
smallest tabulated tier to `2^109` at the largest (`ef-cryptanalysis.md` §3.1, which records them as
read-from-source-and-deliberately-unpublished rather than as published figures).

#67's position is that a collision is "generally not what a Gröbner solver attacks", and that is the
whole of it: **no polynomial system whose solutions are `q`-element collisions is known to this
repository that could be solved below the birthday bound**, and every tool here is a
polynomial-system solver. The prize's size does not change the objective. It therefore stays in §2
as a claimability fact and appears nowhere else as a target.

Reopen only on a **new algebraic formulation of the collision objective** — not on a faster solver,
and not on a change in the prize's status.

## 7. Research question 4: why claimability is not a schema field

Answered **no**, as #200 proposed, and `ChallengeManifest` is unchanged.

- `ChallengeManifest::canonical` feeds the identity digest and covers the family, the parameters,
  the target values and the objective. A programme that pauses, expires or is reinstated would
  change a problem's **identity** if claimability were inside the digest, breaking every historical
  comparison keyed on it — the same argument `additional-benchmarks.md` §6.2 makes for programme
  metadata.
- `test_the_registry_is_frozen` would then fail every time an organizer edited a web page, which
  trains people to re-freeze rather than to look. It passed unchanged across the edit that produced
  this document, which is the demonstration rather than the assertion.
- `ExternalStatus` answers "has anyone solved this". That is a durable fact about mathematics.
  Claimability is a fact about a funding programme. §0 is what conflating them costs.

**Where claimability lives in the code instead.** In `ChallengeProgram`, which exists for the
programme's paperwork and is already outside the digest:

- `reward` stays the amount **as the program words it** — `"$10,000"`, unannotated;
- `version` carries the programme, its window, the read date and the claimability state — for the
  three 2025 rows, `"2025 bounty program, ran till 2025-12-01, read 2026-11-08; the reward is
  EXPIRED — the window closed and the tier is still listed as unclaimed"`;
- `external` keeps saying only `NoneRecorded { as_of: "2026-11-08" }`, re-verified for this issue.

`test_a_reward_is_never_recorded_without_its_claimability_and_a_read_date` holds the line: every
registry row carrying a reward must name one of §1's five states and an ISO read date. It fails
loudly on a row that records money with no claimability state or no read date, which is the
defect #200 was filed for.

## 8. The standing check

Every currency figure in this repository must be traceable to a quoted status, a window and a read
date. There is nothing to compute; the verification procedure is the deliverable:

```sh
grep -rn '\$[0-9]\|EUR\|USD' docs/ research/ src/ README.md
```

Each hit must either sit beside its window, state and read date, or point at §2 of this document.
A figure that satisfies neither is the finding.

## 9. Open

- **No EF announcement was located** for any Poseidon programme status (§4). If one exists it would
  be the natural second source, and its absence is why §2 rests on a single primary source for the
  five Poseidon rows.
- **The MiMC challenge is `unverified`, not closed** (§2). Its page states a reward and no window at
  all. Classifying it needs a statement from the organizer that does not exist on the page.
- **#71 should adopt §1's vocabulary** for the 2021–2022 programme rather than inventing another.
- **Whether the page linked a different survey before 2026-11-08** is not established (§3) and was
  not inferred from the `403`.
