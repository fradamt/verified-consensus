# The complete protocol (Section 7 of the paper), extracted for the Lean formalization

## Source and method

Measured SHA-256 of the source file (`shasum -a 256`):

```text
dc471b47a46896fe0a3df300c188fef1512f475615ce0fc0df18dbea6d2e5517
```

```text
┌──────────────────┬───────────────────────────────────────────────────────────────────┐
│ Source file      │ consensus.tex                                                     │
│ File length      │ 2 457 lines                                                       │
│ Section 7 range  │ lines 1459–2281 (§7 "Complete protocol")                          │
│ Assumptions      │ lines 2394–2457 (§9 "Participation and accountability")           │
│ Appendix sources │ §1 (85–114), §2 (115–333), §3 (484–608), §4 (685–848),            │
│                  │ §5 (850–1042), §6 (1158–1345, 1452–1458)                          │
└──────────────────┴───────────────────────────────────────────────────────────────────┘
```

Source: `consensus.tex` at commit `9f5ed717ffac` (not yet public).
This file is a faithful extraction. The pseudocode is reproduced verbatim in
structure: the paper's function names, argument names, statement order and
comments are kept, and no line of an algorithm is omitted. LaTeX macros are
rendered to plain Unicode math (`\Sigma` → Σ, `\preceq` → ⪯, `\bot` → ⊥,
`\gfPool` → `gf_votes`, and so on). The paper loads `algpseudocode` with the
`noend` option, so block ends are not printed; block structure is carried by
indentation alone here, exactly as it is in the typeset paper. Line numbers are
not reproduced, because the paper numbers lines continuously across all
functions of one figure and those numbers cannot be recovered without
compiling. Section cross-references `\S\ref{...}` are rendered as the section
number followed by its label. Symbols and definitions that Section 7 uses
without restating them (⪯, depth, the weights `w` and `W`, `T_r`, `η_SG`, the
resolution time, the grade cutoffs, and so on) are collected in the Appendix at
the end of this file, in the paper's order; read it first if a symbol is new.

Section numbers used throughout:

```text
┌──────┬───────────────────────────────────────┬────────────────────────────┐
│ §1   │ Common substrate                      │ sec:substrate              │
│ §2   │ Goldfish available chain              │ sec:goldfish               │
│ §2.1 │ Schedule and wire objects             │ sec:goldfish-schedule      │
│ §2.2 │ Store                                 │ sec:goldfish-store         │
│ §2.3 │ View merge                            │ sec:view-merge             │
│ §2.4 │ Goldfish fork-choice                  │ sec:one-slot-ghost         │
│ §2.5 │ Duties and handlers                   │ sec:goldfish-handlers      │
│ §2.6 │ Available confirmation                │ sec:available-confirmation │
│ §3   │ Relative-majority stabilization gadget│ sec:majority-sg            │
│ §3.1 │ Rounds and SG votes                   │ sec:sg-schedule            │
│ §3.2 │ Store                                 │ sec:sg-store               │
│ §3.3 │ Latest votes and relative majority    │ sec:sg-fork-choice         │
│ §3.4 │ Duty and handler                      │ sec:sg-handlers            │
│ §4   │ Finality-gadget state transition      │ sec:state-machine          │
│ §5   │ Finality gadget in the fork-choice    │ sec:fg-fork-choice         │
│ §6   │ Graded SG healing                     │ sec:healing                │
│ §6.1 │ Round schedule                        │ sec:healing-schedule       │
│ §6.2 │ Grades                                │ sec:grades                 │
│ §6.3 │ The SG root                           │ sec:fresh-anchor           │
│ §6.4 │ The round action                      │ sec:healing-action         │
│ §6.5 │ Nonjustifiable heights                │ sec:nonjustifiable         │
│ §7   │ Complete protocol                     │ sec:complete-protocol      │
│ §7.1 │ Cumulative node store                 │ sec:complete-store         │
│ §7.2 │ Duties and handlers                   │ sec:public-handlers        │
│ §8   │ Leak identification                   │ sec:leak                   │
│ §9   │ Participation and accountability      │ sec:assumptions            │
└──────┴───────────────────────────────────────┴────────────────────────────┘
```

---

# 1. The cumulative node store (§7.1, `sec:complete-store`)

The final store is one cumulative object:

```text
Σ = ( t, s, 𝒯, timestamp[·], σ[·],
      gf_votes[·], attestations[·], G2, G1, G0,
      F, J, h_j, h_max,
      live_confirmed, latest_confirmed, latest_stable ).
```

The local validator index is again `val_index`; the validator also keeps its
anti-slashing record

```text
Λ = ( target[·], timeout[·], lock[·], timeouts )
```

of §5 (`sec:fg-fork-choice`), one entry per height, initially (⊥, false, ⊥) and
the empty set. It belongs to the validator, not to the store, and
`record_attestation()` is its only writer.

## 1.1 Store Σ

```text
┌──────────────────────┬──────────────────────────────────────────────┬──────────────────┐
│ Field                │ Type / meaning                               │ Initial value    │
├──────────────────────┼──────────────────────────────────────────────┼──────────────────┤
│ t                    │ current time                                 │ 0                │
│ s                    │ current slot                                 │ 0                │
│ 𝒯                    │ tree of processed blocks, parent-closed,     │ {B_gen}          │
│                      │ rooted at B_gen                              │                  │
│ timestamp[·]         │ time at which object x is processed into the │ timestamp(B_gen) │
│                      │ store; an attestation is stamped by its SG   │ = −∞             │
│                      │ projection                                   │                  │
│ σ[·]                 │ block state map: the post-state of each      │ —                │
│                      │ processed block                              │                  │
│ gf_votes[·]          │ gf_votes[k] = processed slot-k Goldfish      │ empty            │
│                      │ votes; at most two distinct votes per        │                  │
│                      │ validator                                    │                  │
│ attestations[·]      │ attestations[r] = processed round-r combined │ empty            │
│                      │ attestations, in full; at most two           │                  │
│                      │ attestations with distinct safe blocks per   │                  │
│                      │ validator                                    │                  │
│ G2                   │ round's saved grade-2 block, or ⊥            │ ⊥                │
│ G1                   │ round's saved grade-1 block, or ⊥            │ ⊥                │
│ G0                   │ round's saved grade-0 block, or ⊥            │ ⊥                │
│ F                    │ finalized block                              │ B_gen            │
│ J                    │ lex-greatest justification compatible with F │ B_gen            │
│ h_j                  │ height of J                                  │ 0                │
│ h_max                │ maximum state height seen                    │ 1                │
│ live_confirmed       │ protocol-facing confirmation: the eligible   │ B_gen            │
│                      │ Goldfish confirmation, or the FG-root floor  │                  │
│                      │ when no such confirmation is available; only │                  │
│                      │ this value is used by the voting rules       │                  │
│ latest_confirmed     │ user-facing confirmation record              │ B_gen            │
│ latest_stable        │ user-facing stable record                    │ B_gen            │
└──────────────────────┴──────────────────────────────────────────────┴──────────────────┘
```

At initialization,

```text
Σ.t = Σ.s = 0,   Σ.𝒯 = {B_gen},   Σ.timestamp(B_gen) = −∞,   Σ.h_max = 1,
Σ.F = Σ.J = B_gen,   Σ.h_j = 0,
Σ.live_confirmed = Σ.latest_confirmed = Σ.latest_stable = B_gen,
```

every pool is empty and Σ.G2 = Σ.G1 = Σ.G0 = ⊥.

## 1.2 Validator record Λ

```text
┌────────────┬────────────────────────────────────────────────────┬────────────────┐
│ Field      │ Type / meaning                                     │ Initial value  │
├────────────┼────────────────────────────────────────────────────┼────────────────┤
│ target[h]  │ the validator's first target at height h           │ ⊥              │
│ timeout[h] │ whether it emitted a timeout at height h           │ false          │
│ lock[h]    │ the target of its first finality pair at height h  │ ⊥              │
│ timeouts   │ the set of (h, T) pairs its timeouts have named,   │ ∅              │
│            │ so that timeout[h] holds exactly when some (h, T)  │                │
│            │ is in it                                           │                │
└────────────┴────────────────────────────────────────────────────┴────────────────┘
```

One entry per height, initially (⊥, false, ⊥) and the empty set.

## 1.3 Chain state σ (§4, `sec:state-machine`; Definition "Chain state")

```text
σ = ( L, s, h, T_h, nj,
      target_participation, progress, finalize,
      J, h_j, F, h_F ).
```

```text
┌────────────────────────┬─────────────────────────────────────────────┬───────────────┐
│ Field                  │ Type / meaning                              │ Initial value │
├────────────────────────┼─────────────────────────────────────────────┼───────────────┤
│ L                      │ the latest block                            │ B_gen         │
│ s                      │ σ.s = σ.L.slot                              │ 0             │
│ h                      │ the current height                          │ 1             │
│ T_h                    │ the block that brought the transition into  │ B_gen         │
│                        │ height σ.h                                  │               │
│ nj                     │ Boolean, computed when the chain enters σ.h │ false         │
│                        │ and fixed until the height changes          │               │
│ target_participation   │ one Boolean per validator                   │ false^V       │
│ progress               │ one Boolean per validator                   │ false^V       │
│ finalize               │ one Boolean per validator                   │ false^V       │
│ J                      │ latest justification on the chain           │ B_gen         │
│ h_j                    │ its height                                  │ 0             │
│ F                      │ latest finalization on the chain            │ B_gen         │
│ h_F                    │ its height                                  │ 0             │
└────────────────────────┴─────────────────────────────────────────────┴───────────────┘
```

The quorum sets are derived when used:

```text
Q_target(σ)   = { i : σ.target_participation[i] }
Q_prog(σ)     = { i : σ.progress[i] }
Q_finality(σ) = { i : σ.finalize[i] }
```

## 1.4 Store prose (§7.1, verbatim)

Σ.attestations[r] holds the processed round-r combined attestations, in full.
An SG vote is an attestation's (val_index, round, safe) projection, and every
SG rule and grade reads only this projection; the pool keeps at most two
attestations with distinct safe blocks per validator, and attestations
differing only in their pair fields are one vote, so the second of them is
refused. Attestations reach the pool on the wire, through the node's own
`attest()`, and from the blocks the node accepts: an accepted block's
attestations pass through `on_sg_vote()` after the block's finality update,
under the same admission rule as a wire receipt. §3.2 (`sec:sg-store`)'s rule
that SG votes travel only on the wire is thus relaxed here, and blocks are the
only other way in. An attestation resolves as an SG vote does (§3.2,
`sec:sg-store`), at the later of its own and its safe block's timestamps — an
empty safe block resolves at receipt — and the pair fields never take part;
inclusion in a block supplies no resolution of its own. The state transition
reads a block's attestations directly, whether or not the pool admitted them.

Σ.G2, Σ.G1 and Σ.G0 are the current round's saved grades (§6.2, `sec:grades`),
each the deepest graded block or empty, written once per round at the grade's
completion time. They are the only quantities the store caches; a view, a
quorum set, a support score, an anchor, a viable tree or a filtered tree is
derived when used, from timestamps compared against past instants. A finality
advance cuts every saved block back to its deepest ancestor compatible with the
new Σ.F, and every reader projects a saved block onto the current filtered tree
through `active_prefix()`.

A block is accepted only when its parent is held and, beyond the guards of the
earlier layers, only when every attestation it includes has a round at most
round(B.slot): a block may not include attestations from its own future. There
is no lower bound; an old included attestation is read by the state transition
however old it is, and enters the pool only if the SG window admits it. The
proposer includes the attestations of the pool whose round lies in the
inclusive window [max(0, r − η_SG), r] of the current round r, together with the
attestations included in held blocks of a slot in that window, again those with
a round in the window, removing every attestation already on the parent's
chain. Unresolved attestations are included too: resolution is a fact of the
proposer's store, not of the attestation.

The complete protocol exposes three tips, nested by construction: the finalized
chain with tip Σ.F, the stable chain with tip `get_stable(Σ)`, and the
available chain with tip `get_confirmed(Σ)`. The protocol-facing value
Σ.live_confirmed is the eligible Goldfish confirmation, or the FG-root floor
when no such confirmation is available. Only this value is used by the voting
rules. The user-facing record Σ.latest_confirmed instead takes the confirmation
walk's result H when H is eligible. When it is not, the record takes the active
prefix of the round's saved grade-2 block if there is one, and is otherwise
left alone: the FG root and the anchor are never offered to it. Grade 2 is the
strongest of the three relative grades, the one that under graded delivery
holds grade 1 at every honest node whose filtered tree contains the block, so
it is the only value besides an eligible head that the record accepts. An
ancestor candidate leaves the record unchanged; an extension or a conflicting
candidate replaces it. This permits recovery from a conflicting record formed
in an unsafe period. Monotonicity of the user record is guaranteed from genesis
under its normal safety assumptions, and after the proved healing handoff for
arbitrary pre-healing history. At that handoff, the fresh honest proposal
replaces the old record. The finite healing construction supplies this
proposal; no later proposer is assumed merely to refresh the record.
Monotonicity is not claimed across an earlier unsafe reset.

At the same duty a second user-facing record, Σ.latest_stable, is written from
the round's stable root: the active prefix of the saved grade-2 block, and the
FG root itself when there is no grade-2 block or it has no active prefix
(`stable_root()`). The record advances by the confirmation record's rule — an
ancestor candidate leaves it unchanged, an extension or a conflicting candidate
replaces it — and the write is never empty. It backs the stable chain, one
layer above finality and one below the available chain.

The confirmation record's write is floored on the stable record, in the same
duty and after it. The candidate above is recorded when it extends the new
stable record; when it does not, the old record is kept while that still
extends the new stable record, so a confirmation head that has left the stable
branch is ignored rather than recorded; and only when the new stable record has
left the old record's chain does the confirmation record move to the stable
record itself. Two properties hold by these three cases alone, with no fault
bound: the records are ordered at every node and every time,
Σ.latest_stable ⪯ Σ.latest_confirmed, and the confirmation record is never
moved below a value it already held, so the floor cannot undo the record's own
progress.

`get_stable(Σ)` returns Σ.latest_stable when it extends Σ.F, and Σ.F otherwise;
the confirmed tip `get_confirmed(Σ)` is Σ.latest_confirmed when it extends the
stable tip, and the stable tip otherwise, so the available chain floors on the
stable chain rather than directly on finality. The three tips therefore nest at
every node and every time,

```text
Σ.F ⪯ get_stable(Σ) ⪯ get_confirmed(Σ),
```

by construction of the two accessors alone, with no fault bound or synchrony
hypothesis; each of the three chains has the ebb-and-flow prefix property. No
voting rule reads either user-facing record.

---

# 2. Duties and handlers (§7.2, `sec:public-handlers`)

The public times of the schedule, the view freeze included, are the only tick
times; the tick at a public time runs once, before the objects processed at
that time, so an object processed between two public times gets the earlier
one's stamp. A tick first completes the grades whose completion time it is,
from the store as it stands, and only then advances the clock and runs the
duties (§6.1, `sec:healing-schedule`). Figures `alg:store`–`alg:chain-full`
list the complete protocol: every function in final form — the store handlers,
the fork choice with its grades, the validator duties with their helpers, the
validator client, and the state transition — each marked with the section that
defined it, *unchanged* means verbatim, and *extended* or *redefined* marking
the functions this layer changes. The mathematical definitions they draw on —
resolution times, scores and supports, the relative majority and its grades,
and the trees — are those of §2 (`sec:goldfish`)–§6 (`sec:healing`), and at
slot 0 the head is genesis. Relative to the earlier layers, the proposer gains
the included attestations; block processing gains the state transition, the
finality update, which now also cuts back the saved grades, the included
attestations and a guard against reprocessing; and available confirmation runs
the composed fork choice — the filtered tree and the round's anchor — over the
confirmation window's votes and writes the two records. It advances the
protocol-facing value only when the result itself holds a window majority, and
otherwise returns the FG root: the confirmed value is always this evaluation's
output, either a genuine confirmation or the root, and the root sits below
every walk floor in `attest()`, so an unconfirmed slot lands on the grade-2 and
anchor fallbacks there.

---

## 2.1 Figure `alg:store` — Complete protocol: handlers

<a id="on_tick"></a>
### on_tick(Σ, Λ, t)

Algorithm block: `alg:store` ("Complete protocol: handlers").

```text
function on_tick(Σ, Λ, t)                        ▷ §5 (sec:fg-fork-choice), extended at this layer
    update_grades(Σ, t)                          ▷ §6.2 (sec:grades), before the clock advances
    s ← ⌊t / (4Δ)⌋; (Σ.t, Σ.s) ← (t, s)
    if s > 0 and t = t_s and val_index is the slot-s proposer then
        propose_block(Σ)
    if s > 0 and t = t_s + Δ then
        goldfish_vote(Σ)
    if s > 0 and t = t_s + 2Δ then
        update_confirmation(Σ, s − 1)
    r ← round(Σ.s)
    if t = a_r and val_index is awake in round r then
        attest(Σ, Λ)
```

<a id="update_confirmation"></a>
### update_confirmation(Σ, s)

Algorithm block: `alg:store`.

```text
function update_confirmation(Σ, s)               ▷ §2 (sec:goldfish), redefined at this layer
                                                 ▷ at t_s + 6Δ
    early_votes ← { vote ∈ Σ.gf_votes[s] : Σ.resolution_time(vote) < t_s + 2Δ }
    late_votes ← { vote ∈ Σ.gf_votes[s] : Σ.timestamp(vote) < t_s + 6Δ }
    support_votes ← { vote ∈ early_votes :
                      late_votes holds no second distinct vote by vote.val_index }
    voters_count ← |{ v : late_votes holds a vote by v }|
    define eligible(B) as
        2 · goldfish_score(support_votes, support_votes, s, B) > voters_count
    tree ← get_filtered_block_tree(Σ);   root ← get_fg_root(Σ)
    A ← get_sg_root(Σ)
    H ← ghost(A, tree, goldfish_score(support_votes, support_votes, s, ·), eligible)
    if eligible(H) then
        Σ.live_confirmed ← H;   C ← H
    else
        Σ.live_confirmed ← root
        C ← active_prefix(Σ, Σ.G2)               ▷ the saved grade-2 block stands in for the walk
    update_user_confirmation_records(Σ, C)
```

<a id="update_user_confirmation_records"></a>
### update_user_confirmation_records(Σ, C)

Algorithm block: `alg:store`.

```text
function update_user_confirmation_records(Σ, C)
    C′ ← advance(Σ.latest_confirmed, C)
    Σ.latest_stable ← advance(Σ.latest_stable, stable_root(Σ))
    if Σ.latest_stable ⪯ C′ then
        Σ.latest_confirmed ← C′                  ▷ the candidate extends the new stable record
    else if Σ.latest_stable ⋠ Σ.latest_confirmed then
        Σ.latest_confirmed ← Σ.latest_stable     ▷ the old record has left the stable chain
```

<a id="advance"></a>
### advance(old, C)

Algorithm block: `alg:store`.

```text
function advance(old, C)
    return old if C = ⊥ or C ⪯ old, else C       ▷ no candidate or an ancestor leaves the record unchanged
```

<a id="stable_root"></a>
### stable_root(Σ)

Algorithm block: `alg:store`.

```text
function stable_root(Σ)
    A ← active_prefix(Σ, Σ.G2)
    return A if A ≠ ⊥, else get_fg_root(Σ)
```

<a id="get_stable"></a>
### get_stable(Σ)

Algorithm block: `alg:store`.

```text
function get_stable(Σ)                           ▷ user-facing; no protocol rule reads it
    if Σ.F ⪯ Σ.latest_stable then
        return Σ.latest_stable
    return Σ.F
```

<a id="get_confirmed"></a>
### get_confirmed(Σ)

Algorithm block: `alg:store`.

```text
function get_confirmed(Σ)                        ▷ user-facing; no protocol rule reads it
    if get_stable(Σ) ⪯ Σ.latest_confirmed then
        return Σ.latest_confirmed
    return get_stable(Σ)
```

<a id="on_block"></a>
### on_block(Σ, B)

Algorithm block: `alg:store`.

```text
function on_block(Σ, B)                          ▷ §5 (sec:fg-fork-choice), extended at this layer
    if B.slot > Σ.s or B ∈ Σ.𝒯 or B.parent ∉ Σ.𝒯 then
        return
    if Σ.F ⋠ B then
        return
    if some a ∈ B.attestations has a.round > round(B.slot) then
        return
                                                 ▷ no attestation from the block's future
    Σ.σ[B] ← state_transition(Σ.σ[B.parent], B)
    add B to Σ.𝒯; Σ.timestamp(B) ← Σ.t
    for all vote ∈ B.votes do
        on_goldfish_vote(Σ, vote)
    update_finality(Σ, Σ.σ[B])
    for all a ∈ B.attestations do
        on_sg_vote(Σ, a)
```

<a id="on_goldfish_vote"></a>
### on_goldfish_vote(Σ, vote)

Algorithm block: `alg:store`.

```text
function on_goldfish_vote(Σ, vote)               ▷ §2 (sec:goldfish), unchanged
    if vote.slot < Σ.s − 1 or vote.slot > Σ.s or vote.val_index ∉ 𝒦_{vote.slot}
       or vote ∈ Σ.gf_votes[vote.slot] then
        return
    if Σ.gf_votes[vote.slot] holds two distinct votes by vote.val_index then
        return
    add vote to Σ.gf_votes[vote.slot]; Σ.timestamp(vote) ← Σ.t
```

<a id="on_sg_vote"></a>
### on_sg_vote(Σ, a)

Algorithm block: `alg:store`.

```text
function on_sg_vote(Σ, a)                        ▷ §3 (sec:majority-sg), redefined at this layer
    round_votes ← { b.safe : b ∈ Σ.attestations[a.round], b.val_index = a.val_index }
    if a.round < max{0, round(Σ.s) − η_SG} or
       a.round > round(Σ.s) or
       a.safe ∈ round_votes or |round_votes| = 2 then
        return
    add a to Σ.attestations[a.round]; Σ.timestamp(a) ← Σ.t
```

<a id="update_finality"></a>
### update_finality(Σ, σ)

Algorithm block: `alg:store`.

```text
function update_finality(Σ, σ)                   ▷ §5 (sec:fg-fork-choice), extended at this layer
    Σ.h_max ← max(Σ.h_max, σ.h)
    if Σ.F ⪯ σ.J and (σ.h_j, σ.J.root) > (Σ.h_j, Σ.J.root) then
                                                 ▷ lex order
        (Σ.J, Σ.h_j) ← (σ.J, σ.h_j)
    if Σ.F ≺ σ.F and σ.F ⪯ Σ.J and σ.F ∈ viable_tree(Σ) then
        Σ.F ← σ.F
        for all g ∈ {Σ.G2, Σ.G1, Σ.G0} with g ≠ ⊥ do
            replace g by its deepest ancestor compatible with Σ.F
                                                 ▷ §6.2 (sec:grades)
```

---

## 2.2 Figure `alg:fc-full` — Complete protocol: fork choice

<a id="resolution_time"></a>
### resolution_time(Σ, x)

Algorithm block: `alg:fc-full` ("Complete protocol: fork choice").

```text
function resolution_time(Σ, x)                   ▷ §2.2 (sec:goldfish-store) and §3.2 (sec:sg-store), unchanged
    C ← the head of x if x is a Goldfish vote, else the safe block of x
    if C = ⊥ then
        return Σ.timestamp(x)
    if C ∉ Σ.𝒯 then
        return +∞
    return max{ Σ.timestamp(x), Σ.timestamp(C) }
```

<a id="viable_tree_from"></a>
### viable_tree_from(Σ, blocks)

Algorithm block: `alg:fc-full`.

```text
function viable_tree_from(Σ, blocks)             ▷ §5 (sec:fg-fork-choice), unchanged
    return { B ∈ blocks : Σ.F ⪯ B, ∃ B′ ∈ blocks, B ⪯ B′, Σ.σ[B′].h ≥ Σ.h_max − 1 }
```

<a id="viable_tree"></a>
### viable_tree(Σ)

Algorithm block: `alg:fc-full`.

```text
function viable_tree(Σ)                          ▷ §5 (sec:fg-fork-choice), unchanged
    return viable_tree_from(Σ, Σ.𝒯)
```

<a id="goldfish_score"></a>
### goldfish_score(votes, support_votes, s, B)

Algorithm block: `alg:fc-full`.

```text
function goldfish_score(votes, support_votes, s, B)   ▷ §2 (sec:goldfish), unchanged
    equivocators ← { v : votes holds two distinct votes by v }
    supporters ← { v ∉ equivocators : (v, s, B′) ∈ support_votes with B ⪯ B′ }
    return |equivocators| + |supporters|          ▷ equivocators count for every block
```

<a id="ghost"></a>
### ghost(anchor, tree, score, eligible)

Algorithm block: `alg:fc-full`.

```text
function ghost(anchor, tree, score, eligible)    ▷ §2 (sec:goldfish), unchanged
    H ← anchor
    loop
        children ← { B : B is a child of H in tree, eligible(B) }
        if children = ∅ then
            return H
        H ← argmax_{B ∈ children} score(B), ties by root order
```

<a id="goldfish_eligible"></a>
### goldfish_eligible(Σ, votes, support_votes, s, B)

Algorithm block: `alg:fc-full`.

```text
function goldfish_eligible(Σ, votes, support_votes, s, B)   ▷ §5 (sec:fg-fork-choice), unchanged
    voters_count ← |{ v : votes holds a vote by v }|
    return Σ.σ[B.parent].h < Σ.h_max − 1
           or 2 · goldfish_score(votes, support_votes, s, B) > voters_count
           or B.slot = Σ.s
```

<a id="goldfish_fork_choice"></a>
### goldfish_fork_choice(Σ, anchor, tree, votes, support_votes, s)

Algorithm block: `alg:fc-full`.

```text
function goldfish_fork_choice(Σ, anchor, tree, votes, support_votes, s)   ▷ §2 (sec:goldfish), unchanged
    define score(B) as
        goldfish_score(votes, support_votes, s, B)
    define eligible(B) as
        goldfish_eligible(Σ, votes, support_votes, s, B)
    return ghost(anchor, tree, score, eligible)
```

<a id="get_fg_root"></a>
### get_fg_root(Σ)

Algorithm block: `alg:fc-full`.

```text
function get_fg_root(Σ)                          ▷ §5 (sec:fg-fork-choice), unchanged
    if Σ.h_max = Σ.h_j + 1 then
        return Σ.J
    return Σ.F
```

<a id="get_filtered_block_tree_from"></a>
### get_filtered_block_tree_from(Σ, blocks)

Algorithm block: `alg:fc-full`.

```text
function get_filtered_block_tree_from(Σ, blocks)  ▷ §5 (sec:fg-fork-choice), unchanged
    root ← get_fg_root(Σ)
    return { B ∈ viable_tree_from(Σ, blocks) : root ⪯ B }
```

<a id="get_filtered_block_tree"></a>
### get_filtered_block_tree(Σ)

Algorithm block: `alg:fc-full`.

```text
function get_filtered_block_tree(Σ)              ▷ §5 (sec:fg-fork-choice), unchanged
    return get_filtered_block_tree_from(Σ, Σ.𝒯)
```

<a id="equivocates"></a>
### equivocates(Σ, r, x, v, k₀)

Algorithm block: `alg:fc-full`.

```text
function equivocates(Σ, r, x, v, k₀)             ▷ §3 (sec:majority-sg), unchanged
    return Σ.attestations[k], for some k ∈ I_r with k ≥ k₀, holds two votes by v
           received before x with distinct safe values
```

<a id="supports"></a>
### supports(Σ, r, h, e, v, B)

Algorithm block: `alg:fc-full`.

```text
function supports(Σ, r, h, e, v, B)              ▷ §3 (sec:majority-sg), unchanged
    E_v ← resolved_votes(Σ, r, h, v);   L_v ← resolved_votes(Σ, r, e, v)
    if E_v = ∅ then
        return false
    u ← the vote of greatest round in E_v
    return u covers B and
           not equivocates(Σ, r, e, v, u.round) and
           every x ∈ L_v with x.round > u.round covers B
```

<a id="opposes"></a>
### opposes(Σ, r, h, e, v, B)

Algorithm block: `alg:fc-full`.

```text
function opposes(Σ, r, h, e, v, B)               ▷ §3 (sec:majority-sg), unchanged
    E_v ← resolved_votes(Σ, r, h, v);   L_v ← resolved_votes(Σ, r, e, v)
    k₀ ← max{ u.round : u ∈ E_v }, or 0 if E_v = ∅
    return some x ∈ L_v with x.round ≥ k₀ does not cover B
           or equivocates(Σ, r, e, v, k₀)
```

<a id="relative_majority"></a>
### relative_majority(Σ, r, h, e, B)

Algorithm block: `alg:fc-full`.

```text
function relative_majority(Σ, r, h, e, B)        ▷ §3 (sec:majority-sg), unchanged
    return w({ v : supports(Σ, r, h, e, v, B) }) > w({ v : opposes(Σ, r, h, e, v, B) })
```

<a id="resolved_votes"></a>
### resolved_votes(Σ, r, x, v)

Algorithm block: `alg:fc-full`.

```text
function resolved_votes(Σ, r, x, v)              ▷ §6 (sec:healing), unchanged
                                                 ▷ redefines the §3 (sec:majority-sg) body:
                                                 ▷ only votes for the finalized chain
    return { a ∈ Σ.attestations[k] : k ∈ I_r, a.val_index = v,
             Σ.resolution_time(a) < x, a.safe compatible with Σ.F }
```

<a id="grade"></a>
### grade(Σ, r, h, e, B)

Algorithm block: `alg:fc-full`.

```text
function grade(Σ, r, h, e, B)                    ▷ §6 (sec:healing), unchanged
    return relative_majority(Σ, r, h, e, B)
```

<a id="update_grades"></a>
### update_grades(Σ, t)

Algorithm block: `alg:fc-full`.

```text
function update_grades(Σ, t)                     ▷ §6 (sec:healing), unchanged
                                                 ▷ at every tick, before the clock advances
    r ← round(⌊t / (4Δ)⌋)
    if t = T_{r+1} − Δ then
        Σ.G2 ← graded_block(Σ, r + 1, T_{r+1} − 5Δ, T_{r+1} − Δ)
    else if t = T_r then
        Σ.G1 ← graded_block(Σ, r, T_r − 4Δ, T_r − 2Δ)
    else if t = T_r + Δ then
        Σ.G0 ← graded_block(Σ, r, T_r − 3Δ, T_r − 3Δ)
```

<a id="graded_block"></a>
### graded_block(Σ, r, h, e)

Algorithm block: `alg:fc-full`.

```text
function graded_block(Σ, r, h, e)                ▷ §6 (sec:healing), unchanged
    graded ← { B ∈ Σ.𝒯 : grade(Σ, r, h, e, B) }
    return the deepest B ∈ graded, or ⊥ if graded = ∅
```

<a id="active_prefix"></a>
### active_prefix(Σ, g)

Algorithm block: `alg:fc-full`.

```text
function active_prefix(Σ, g)                     ▷ §6 (sec:healing), unchanged
    tree ← get_filtered_block_tree(Σ)
    return the deepest B ∈ tree with B ⪯ g, or ⊥ if g = ⊥ or there is none
```

<a id="G0_compatible"></a>
### G0_compatible(Σ, B)

Algorithm block: `alg:fc-full`.

```text
function G0_compatible(Σ, B)                     ▷ §6 (sec:healing), unchanged
    return Σ.G0 = ⊥ or B is compatible with Σ.G0
```

<a id="get_sg_root"></a>
### get_sg_root(Σ)

Algorithm block: `alg:fc-full`.

```text
function get_sg_root(Σ)                          ▷ §6 (sec:healing), unchanged
                                                 ▷ redefines the §5 (sec:fg-fork-choice) body
    A ← active_prefix(Σ, Σ.G1)
    if A = ⊥ then
        return get_fg_root(Σ)                    ▷ no grade-1 block, or the root has passed it
    return A                                     ▷ the fresh SG root
```

<a id="get_head_in_tree"></a>
### get_head_in_tree(Σ, tree, votes, support_votes, k)

Algorithm block: `alg:fc-full`.

```text
function get_head_in_tree(Σ, tree, votes, support_votes, k)   ▷ §5 (sec:fg-fork-choice), unchanged
    A ← get_sg_root(Σ)
    return goldfish_fork_choice(Σ, A, tree, votes, support_votes, k)
```

<a id="get_head"></a>
### get_head(Σ, votes, support_votes, k)

Algorithm block: `alg:fc-full`.

```text
function get_head(Σ, votes, support_votes, k)    ▷ §5 (sec:fg-fork-choice), unchanged
    tree ← get_filtered_block_tree(Σ)
    return get_head_in_tree(Σ, tree, votes, support_votes, k)
```

---

## 2.3 Figure `alg:duties` — Complete protocol: validator duties

Interleaved prose of §7.2, between figures `alg:fc-full` and `alg:duties`:

> The vote duty uses a block-domain merge analogous to its vote merge. It first
> forms a processed-block view from blocks received before the previous-slot
> freeze and every ancestor of a current-slot proposal, then recomputes
> viability and the filtered block tree inside that view. In particular, it does
> not filter the current viable tree after the fact: a late witness cannot make
> an old pre-freeze child enter this vote's walk. The proposer and the other
> protocol duties keep the ordinary full-tree `get_head()`.

<a id="voter_processed_block_tree"></a>
### voter_processed_block_tree(Σ, s)

Algorithm block: `alg:duties` ("Complete protocol: validator duties").

```text
function voter_processed_block_tree(Σ, s)
    freeze ← t_{s−1} + 3Δ
    proposals ← { P ∈ Σ.𝒯 : P.slot = s }
    return { B ∈ Σ.𝒯 : Σ.timestamp(B) < freeze or ∃ P ∈ proposals, B ⪯ P }
```

<a id="voter_filtered_block_tree"></a>
### voter_filtered_block_tree(Σ, s)

Algorithm block: `alg:duties`.

```text
function voter_filtered_block_tree(Σ, s)
    blocks ← voter_processed_block_tree(Σ, s)
    return get_filtered_block_tree_from(Σ, blocks)
```

<a id="propose_block"></a>
### propose_block(Σ)

Algorithm block: `alg:duties`.

```text
function propose_block(Σ)                        ▷ §2 (sec:goldfish), extended at this layer
    s ← Σ.s                                      ▷ runs at t_s
    votes ← Σ.gf_votes[s − 1]                    ▷ every previous-slot vote held
    support_votes ← { vote ∈ votes : Σ.resolution_time(vote) < +∞ }
    H ← get_head(Σ, votes, support_votes, s − 1)
    B ← a block with B.parent = H, B.slot = s, B.proposer = val_index
    B.votes ← votes
    B.support_votes ← support_votes              ▷ the proposal-time support subset
    B.attestations ← proposal_attestations(Σ, H)
    broadcast B; on_block(Σ, B)
```

<a id="proposal_attestations"></a>
### proposal_attestations(Σ, H)

Algorithm block: `alg:duties`.

```text
function proposal_attestations(Σ, H)
    r ← round(Σ.s);   I ← [max{0, r − η_SG}, r]
    A ← ⋃_{r′ ∈ I} Σ.attestations[r′]
    for all B′ ∈ Σ.𝒯 with round(B′.slot) ∈ I do
        A ← A ∪ { a ∈ B′.attestations : a.round ∈ I }
                                                 ▷ included attestations are included again
    A ← A minus every attestation on H's chain
    return A with at most two attestations of each validator for each round
```

<a id="goldfish_vote"></a>
### goldfish_vote(Σ)

Algorithm block: `alg:duties`.

The source carries the layer comment twice on this function (consensus.tex
lines 2054–2055); both lines are reproduced.

```text
function goldfish_vote(Σ)                        ▷ §2 (sec:goldfish), unchanged
                                                 ▷ §2 (sec:goldfish), unchanged
    s ← Σ.s                                      ▷ runs at t_s + Δ
    votes ← { vote ∈ Σ.gf_votes[s − 1] : Σ.timestamp(vote) < t_{s−1} + 3Δ }
                                                 ▷ received before the freeze
    support_votes ← { vote ∈ votes : Σ.resolution_time(vote) < t_{s−1} + 3Δ }
    for all B ∈ Σ.𝒯 with B.slot = s do
        included_votes ← { vote ∈ B.votes : vote.slot = s − 1 }
        votes ← votes ∪ included_votes
        support_votes ← support_votes ∪ { (v, s − 1, H) ∈ B.support_votes : H ∈ Σ.𝒯 }
    tree ← voter_filtered_block_tree(Σ, s)
    H ← get_head_in_tree(Σ, tree, votes, support_votes, s − 1)
    if val_index ∈ 𝒦_s then
        vote ← (val_index, s, H); broadcast vote; on_goldfish_vote(Σ, vote)
```

<a id="attest"></a>
### attest(Σ, Λ)

Algorithm block: `alg:duties`.

```text
function attest(Σ, Λ)                            ▷ §6 (sec:healing), unchanged
    r ← round(Σ.s)                               ▷ runs at a_r; all three grades of round r are complete
    A_G2 ← active_prefix(Σ, Σ.G2)
    C_sg ← get_sg_vote(Σ, A_G2)
    (h_c, T_c, ν, h_j, J, h_F) ← get_fg_vote(Σ, A_G2)
    a ← create_attestation(Λ, r, C_sg, h_c, T_c, ν, h_j, J, h_F)
    broadcast a; on_sg_vote(Σ, a)
```

<a id="get_sg_vote"></a>
### get_sg_vote(Σ, A_G2)

Algorithm block: `alg:duties`.

```text
function get_sg_vote(Σ, A_G2)                    ▷ §6 (sec:healing), unchanged
    C ← Σ.live_confirmed;   A ← get_sg_root(Σ)
    if some B with A ⪯ B ⪯ C satisfies G0_compatible(Σ, B) then
        return the deepest such B
    if A_G2 ≠ ⊥ then
        return A_G2                              ▷ the grade-2 block stays canonical
    else if Σ.G2 ≠ ⊥ then
        return get_fg_root(Σ)                    ▷ grade 2 exists, but the root has passed it
    return A                                     ▷ the anchor fallback keeps voting total
```

<a id="get_fg_vote"></a>
### get_fg_vote(Σ, A_G2)

Algorithm block: `alg:duties`.

```text
function get_fg_vote(Σ, A_G2)                    ▷ §6 (sec:healing), unchanged
    votes ← Σ.gf_votes[Σ.s]
    support_votes ← { vote ∈ votes : Σ.resolution_time(vote) < +∞ }
    H ← get_head(Σ, votes, support_votes, Σ.s)
    (h_j, J, h_F) ← (Σ.σ[H].h_j, Σ.σ[H].J, Σ.σ[H].h_F)
    if A_G2 = ⊥ then
        return (⊥, ⊥, ⊥, h_j, J, h_F)            ▷ no fresh quorum: no height pair
    C ← Σ.live_confirmed
    C_fg ← the deepest B with A_G2 ⪯ B ⪯ C and G0_compatible(Σ, B), else A_G2
                                                 ▷ the deepest grade-0-compatible block,
                                                 ▷ or the grade-2 block
    return (Σ.σ[C_fg].h, Σ.σ[C_fg].T_h, Σ.σ[C_fg].nj, h_j, J, h_F)
```

---

## 2.4 Figure `alg:attn-full` — Complete protocol: validator client

<a id="finality_pair"></a>
### finality_pair(Λ, h_j, J, h_F)

Algorithm block: `alg:attn-full` ("Complete protocol: validator client").

```text
function finality_pair(Λ, h_j, J, h_F)           ▷ §5 (sec:fg-fork-choice), unchanged
    if h_j > h_F then                            ▷ a justification not yet finalized
        if Λ.target[h_j] ∈ {⊥, J} and not Λ.timeout[h_j] and Λ.lock[h_j] ∈ {⊥, J} then
                                                 ▷ the record allows it
            return (h_j, J)
    return (⊥, ⊥)
```

<a id="height_pair"></a>
### height_pair(Λ, h_c, T_c, ν, h_f, T_f)

Algorithm block: `alg:attn-full`.

```text
function height_pair(Λ, h_c, T_c, ν, h_f, T_f)   ▷ §5 (sec:fg-fork-choice), unchanged
    if h_c = ⊥ then
        return (⊥, ⊥, ⊥)
    lock ← Λ.lock[h_c];   if h_c = h_f then lock ← T_f
                                                 ▷ this attestation's own lock
    if Λ.timeout[h_c] then
        return (h_c, T_c, true)                  ▷ a timeout repeats, naming the current entry
    if lock ≠ ⊥ then                             ▷ a lock repeats
        if lock = T_c then
            return (h_c, T_c, false)
        return (⊥, ⊥, ⊥)                         ▷ locked elsewhere: wait out the height
    if Λ.target[h_c] ≠ ⊥ then                    ▷ a recorded target repeats
        if Λ.target[h_c] = T_c then
            return (h_c, T_c, false)
    else if not ν then
        return (h_c, T_c, false)                 ▷ no history: adopt the chain's target
    return (h_c, T_c, true)                      ▷ otherwise time out at h_c
```

<a id="create_attestation"></a>
### create_attestation(Λ, r, safe, h_c, T_c, ν, h_j, J, h_F)

Algorithm block: `alg:attn-full`.

```text
function create_attestation(Λ, r, safe, h_c, T_c, ν, h_j, J, h_F)   ▷ §5 (sec:fg-fork-choice), unchanged
                                                 ▷ validator-client side: no store access
    (h_f, T_f) ← finality_pair(Λ, h_j, J, h_F)
    (h, T, τ) ← height_pair(Λ, h_c, T_c, ν, h_f, T_f)
    a ← (val_index, r, safe, h, T, τ, h_f, T_f)
    record_attestation(Λ, a); return a           ▷ record, then release
```

<a id="record_attestation"></a>
### record_attestation(Λ, a)

Algorithm block: `alg:attn-full`.

```text
function record_attestation(Λ, a)                ▷ §5 (sec:fg-fork-choice), unchanged
                                                 ▷ the only writer of Λ
    (h, T, τ, h_f, T_f) ← a's height and finality pairs
    if T_f ≠ ⊥ then
        Λ.lock[h_f] ← T_f
    if h ≠ ⊥ then
        if not τ and Λ.target[h] = ⊥ then
            Λ.target[h] ← T
        if τ then
            Λ.timeout[h] ← true; add (h, T) to Λ.timeouts
```

---

## 2.5 Figure `alg:chain-full` — Complete protocol: state transition

<a id="state_transition"></a>
### state_transition(σ, B)

Algorithm block: `alg:chain-full` ("Complete protocol: state transition").

```text
function state_transition(σ, B)                  ▷ §4 (sec:state-machine), unchanged
    assert B.proposer = proposer(B.slot)
    assert B.parent.slot < B.slot
    σ.s ← B.slot
    for all a ∈ B.attestations do
        σ ← process_attestation(σ, a)
    σ.L ← B
    return process_height_events(σ)
```

<a id="process_attestation"></a>
### process_attestation(σ, a)

Algorithm block: `alg:chain-full`.

```text
function process_attestation(σ, a)               ▷ §4 (sec:state-machine), unchanged
    val_index ← a.val_index
    if σ.h_j > σ.h_F and a's finality pair = (σ.h_j, σ.J) then
        σ.finalize[val_index] ← true
    if a's height pair is (h, T, τ) with h = σ.h and T = σ.T_h then
                                                 ▷ names the chain's own entry
        σ.progress[val_index] ← true
        if not τ then
            σ.target_participation[val_index] ← true
    return σ
```

<a id="process_height_events"></a>
### process_height_events(σ)

Algorithm block: `alg:chain-full`.

```text
function process_height_events(σ)                ▷ §4 (sec:state-machine), unchanged
    if σ.h_j > σ.h_F and w(Q_finality(σ)) ≥ q then
        (σ.F, σ.h_F) ← (σ.J, σ.h_j)
    if w(Q_target(σ)) ≥ q then
        if ¬σ.nj then
            (σ.J, σ.h_j) ← (σ.T_h, σ.h)
            σ.finalize ← false^V
        return advance_height(σ)
    if w(Q_prog(σ)) ≥ q and σ.s ≥ σ.T_h.slot + δ_t then
                                                 ▷ timeouts count only after the delay
        return advance_height(σ)
    return σ
```

<a id="advance_height"></a>
### advance_height(σ)

Algorithm block: `alg:chain-full`.

```text
function advance_height(σ)                       ▷ §4 (sec:state-machine), unchanged
    σ.h ← σ.h + 1;   σ.T_h ← σ.L
    σ.nj ← (K | σ.h) ∧ (σ.h − σ.h_F > D)
    σ.target_participation, σ.progress ← false^V
    return σ
```

---

# 3. Participation and accountability (§9, `sec:assumptions`)

Whether a validator is awake in a round is an input to the node, like the
committee: an honest validator awake in round r runs its attestation at a_r,
and one asleep skips it and nothing else (§6.1, `sec:healing-schedule`). Let ℋ
be the run's honest set and 𝒜 = V \ ℋ. The grades rest on two participation
conditions over the vote window I_r of §3.3 (`sec:sg-fork-choice`), each
required of every round r > 0 whose action time or grade completion times fall
within the run — before, during and after an outage alike. In the
weak-participation results (weak genesis, weak continuation, vote safety) the
awake-window majority is required of every round r > 0 whose preceding action
time a_{r−1} falls within the run, which is one round of look-ahead at the end
of a finite run; the Lean statements are the reference for these guards.

## 3.1 Awake-window majority

The honest validators awake at least once in the window outweigh the
adversary,

```text
𝒲_r = { v ∈ ℋ : v is awake in some k ∈ I_r },        w(𝒜) < w(𝒲_r).
```

It counts a validator once, against the whole adversarial weight, including
validators that send nothing.

## 3.2 Grade-forming majority

Let H_k be the honest validators that attest in round k. Those whose latest
attestation in the window is older than round r − 1 are

```text
S_r = ⋃_{k ∈ I_r, k ≤ r−2} H_k \ H_{r−1},
```

and the condition is

```text
w(𝒜 ∪ S_r) < w(H_{r−1}).
```

A retained honest vote for an older head opposes every deeper block until it is
replaced or expires (§3.3, `sec:sg-fork-choice`), so the round r − 1 attesters
must outweigh the adversary together with the honest validators whose vote is
stale. This is stronger than the awake-window majority, which does not imply
it, and it is the condition under which the graded delivery of §6.2
(`sec:grades`) forms a grade.

## 3.3 Accountable bound

For any two blocks of the run, let X be the set of validators with E1 or E2
evidence (§4, `sec:state-machine`) between the two chains, an attestation on
each side by the same signer; the entry named by a timeout plays no part in the
evidence (a timeout conflicts with every finality pair at its height, whatever
entry it names; E2 never involves a timeout), and the two attestations may be
one and the same. The bound is

```text
W + w(X) < 2q.
```

It bounds the slashable evidence a run exposes, not the faulty weight: it
neither implies nor follows from a bound on w(𝒜), and it holds throughout the
run, healthy periods included.

## 3.4 Bounded outage

An outage is an interval [b₀, b₁) of the run. A message sent at t < b₀ is
received before t + Δ, and one sent during the outage before max(t, b₁) + Δ,
whenever that instant is within the run; a message sent before b₀ whose
deadline falls inside the outage has only the second bound. Synchrony resumes
at b₁. Receipt means the handler call, for an object included in a block too: a
relay recipient that processes the block's copy has received the object, and it
is never sent a duplicate.

---

# Appendix. Definitions from earlier sections used by §7

Every `\Function` that §7 calls is defined inside §7 itself. The items below
are the mathematical and notational definitions that §7's algorithms use
without restating them.

## A.1 §1 `sec:substrate` — Common substrate

A fixed validator set V is given. Slot s starts at t_s = 4Δs and has an
assigned proposer and a fixed committee 𝒦_s ⊆ V; in every committee, honest
members outnumber adversarial members. After t_GST, Δ is a strict delivery
bound. A scheduled action uses the store immediately before its public time.

Every block B has a root B.root, slot B.slot, parent B.parent, and proposer
index B.proposer. Processed blocks form a parent-closed tree rooted at B_gen.
Write B ⪯ C when B = C or B is an ancestor of C, and write B ≺ C for strict
ancestry. Two blocks are compatible when one is an ancestor of the other, and
they conflict otherwise. The depth of a block is the number of parent edges
from genesis. "Deepest" means maximum depth; ties use a fixed root order.

Σ.timestamp(x) is the time at which object x is processed into the store; an
attestation is stamped by its SG projection.

Opening prose of the paper (before §1): The node keeps a store Σ, the
validator's anti-slashing record Λ of §5 (`sec:fg-fork-choice`), and, from §6
(`sec:healing`) on, the three saved grades of the current round. A combined
attestation is kept in full; every SG rule and grade reads only its *SG
projection* (val_index, round, safe), and the finality gadget reads its height
and finality pairs. Blocks are kept in full, with their attestation lists.

## A.2 §2.1 `sec:goldfish-schedule` — Schedule and wire objects

Slot s has these public actions:

```text
t_s        proposal,
t_s + Δ    Goldfish vote,
t_s + 2Δ   support cutoff,
t_s + 3Δ   view freeze,
t_s + 6Δ   slot-s confirmation evaluation.
```

Because t_s + 6Δ = t_{s+1} + 2Δ, the last action is also the support action of
slot s + 1.

A Goldfish vote is a tuple (val_index, s, B) from validator val_index ∈ 𝒦_s
with head B, where B.slot ≤ s. A block B has B.parent, B.slot, B.proposer, a
set B.votes of slot-(B.slot − 1) Goldfish votes, and a subset
B.support_votes ⊆ B.votes. An honest proposer puts every previous-slot vote it
holds in B.votes and puts exactly the members resolved at proposal time in
B.support_votes. A slot-s block is valid only when B.proposer = proposer(s).
There is no proposal envelope: the block is the only wire object a proposer
emits, and B.votes is the channel by which a proposal forwards votes. The
support subset records the proposer's view; it is not a second set of votes to
process.

## A.3 §2.2 `sec:goldfish-store` — Goldfish store, resolution and equivocation

The store keeps messages and their timestamps, and nothing else. Every rule
below is a timestamp comparison on this one pool. A validator has equivocated
as of t when Σ.gf_votes[k] holds two of its votes both timestamped before t, so
its *equivocation-detection time* is the later of the two timestamps, and one
cutoff decides which votes are timely and which equivocations are.

`on_block(Σ, B)` and `on_goldfish_vote(Σ, vote)` accept each object at most
once. A call that returns before acceptance does not consume the object: a
later delivery may invoke the handler again after the guard condition changes.
A block is processed after its parent. A vote is processed on receipt, whether
or not the store holds its head; a vote is *resolved* when it does and the head
is a block of the vote's slot or earlier (H.slot ≤ s, §2.1,
`sec:goldfish-schedule`); a vote whose head is a later-slot block stays in the
pool as a cast vote but never resolves, so it is never counted as support for
its head. For a vote with head H, the *resolution time* is the derived
function

```text
Σ.resolution_time(vote) = max{ Σ.timestamp(vote), Σ.timestamp(H) },  H ∈ Σ.𝒯,
                        = +∞,                                        H ∉ Σ.𝒯.
```

An honest node forwards every block it admits and every accepted Goldfish vote
independently. The vote rule also applies when the node first accepts the vote
from an admitted block. The node ignores votes older than the previous slot or
from a future slot. A vote whose head is a block of a later slot than the vote
is kept in the pool like any other vote, so that every node counts the same
cast votes, but it never resolves and is never counted as support (§2.2,
`sec:goldfish-store`). It may discard expired pool entries.

## A.4 §2.3 `sec:view-merge` — View merge

To run the Goldfish fork choice in slot s, a voter at t_s + Δ forms two sets.
The set *votes* contains each slot-(s − 1) vote that the store received before
t_{s−1} + 3Δ, together with every slot-(s − 1) vote included in an admitted
slot-s proposal. The subset *support_votes* contains local votes resolved
before the freeze time t_{s−1} + 3Δ, together with each vote in the proposal's
B.support_votes whose head is in Σ.𝒯 by voting time. This proposal arm does not
require the vote to have entered Σ.gf_votes or to have a local receipt
timestamp. For a proposal B, a vote in B.votes \ B.support_votes remains
outside *support_votes* even if it resolves before the voter runs.
Participation and equivocation are determined by *votes*, regardless of
resolution, while *support_votes* determines direct subtree support.

The proposer does not apply the freeze. It uses all previous-slot votes it
holds when it builds the block as *votes* and their resolved subset as
*support_votes*, and includes both sets in the proposal. Voters do not derive
the proposal's support subset again from their later stores.

## A.5 §2.4 `sec:one-slot-ghost` — Goldfish score and walk (Definition `def:goldfish-walk`)

Fix a vote slot s, a set *votes* of slot-s votes, and a subset
*support_votes* ⊆ *votes*. Validator v ∈ 𝒦_s *equivocates* when *votes* holds
two of its distinct votes, and *participates* when it holds at least one.
`goldfish_score(votes, support_votes, s, B)` counts every equivocator plus
every non-equivocating participant for which *support_votes* holds a vote whose
head descends from B. An equivocator counts for every block and stays among the
participants: discovering an equivocation cannot make a majority-eligible block
ineligible, though it can make another block newly eligible. A non-equivocating
validator counts once, in one subtree.

Throughout this document, we use this as a building block:

```text
ghost(anchor, tree, score, eligible),
```

where *score* is a function on blocks and *eligible* a predicate on blocks. It
descends from *anchor* through eligible children in *tree*, taking the highest
score at each step, and stops where no child is eligible.

Goldfish instantiates the walk with
`goldfish_score(votes, support_votes, s, ·)` and the eligibility condition

```text
goldfish_eligible(Σ, votes, support_votes, s, B)
  ⟺ 2 · goldfish_score(votes, support_votes, s, B) > voters_count or B.slot = Σ.s,
```

with voters_count = |{ v : votes holds a vote by v }|. The majority condition
can be used to enforce timeliness and other fork-choice conditions, like FOCIL
inclusion. It only does not apply to proposals from the current slot, which
cannot yet have votes.

At slot 0 the vote set is empty, no child is eligible, and the head is genesis.

## A.6 §3.1 `sec:sg-schedule` — Rounds, weights and SG votes

Each validator v ∈ V has a fixed positive integer weight w(v). For S ⊆ V, write
w(S) = Σ_{v ∈ S} w(v) and W = w(V).

For a fixed integer R ≥ 1, round r consists of slots rR, …, rR + R − 1; slot rR
is its *opening slot*, T_r = t_{rR} is the opening slot's proposal time, and
round(s) = ⌊s / R⌋. Each round has one SG vote time a_r, a public parameter in
this intermediate protocol.

An SG vote is a tuple (val_index, r, C) from validator val_index ∈ V with safe
block C, a block or ⊥. At a_r, an honest validator votes its current
Σ.live_confirmed as safe, which is a block; the empty value appears only in
adversarial votes. A round-r vote is read from round r + 1 on.

## A.7 §3.2 `sec:sg-store` — SG store and expiry window

This layer adds one field: Σ.attestations[r], which at this layer holds the
processed round-r SG votes. Like Σ.gf_votes, it is timestamped and keeps at
most two distinct votes per validator, which is all any rule reads; two
distinct safe blocks from one validator in one round are an *equivocation*, and
it is detected on receipt, whether or not the blocks are known. For an SG vote
with safe block C, the derived function is

```text
Σ.resolution_time(vote) = Σ.timestamp(vote),                        C = ⊥,
                        = max{ Σ.timestamp(vote), Σ.timestamp(C) }, C ∈ Σ.𝒯,
                        = +∞,                                       C ≠ ⊥ and C ∉ Σ.𝒯.
```

Thus, an SG vote is resolved when the store holds its nonempty safe block, and
an empty safe block resolves at receipt. At this layer SG votes travel only on
the wire; §7 (`sec:complete-protocol`) lets blocks include them.

An honest node forwards every accepted SG vote while its round is in the η_SG
expiry window. The same rule later applies to combined attestations. Messages
outside this fixed round window need not be accepted or forwarded. Old finality
pairs need not remain available on the wire because validators can submit
target and timeout votes again. Expired pool entries may be discarded.

## A.8 §3.3 `sec:sg-fork-choice` — Window, resolved votes, support and opposition (Definition `def:majority-fork-choice`)

Fix an expiry window η_SG ≥ 1 in rounds. The votes read in round r are those of
the rounds

```text
I_r = { k : max{0, r − η_SG} ≤ k < r };
```

round 0 reads nothing. A test is taken at a pair of cutoffs h ≤ e, the *early*
and the *late* cutoff, both strict: an object received at a cutoff is later.
For validator v and a cutoff x, R_v(x) is the set of v's votes in
Σ.attestations[k], k ∈ I_r, received before x. A vote in R_v(x) is *resolved*
by x when Σ.resolution_time(vote) < x (§3.2, `sec:sg-store`): its safe value is
empty, or its safe block is in Σ.𝒯 and was processed before x; a vote whose
block is unknown is not resolved. A vote *covers* B when its safe block C
satisfies B ⪯ C; an empty safe value covers no block.

Let E_v be v's votes resolved by h, L_v its votes resolved by e, and
R_v = R_v(e). Validator v *supports* B when its latest vote in E_v covers B,
R_v holds no equivocation at or after that vote's round, and every vote in L_v
of a later round covers B too. Validator v *opposes* B when L_v holds a vote,
at or after every round in E_v, that does not cover B, or when R_v holds an
equivocation at or after every round in E_v. Pos(B) and Opp(B) are the
supporting and the opposing validators, each counted once, and B holds a
*relative majority* at (h, e) when

```text
w(Pos(B)) > w(Opp(B)).
```

A validator with no vote resolved by the early cutoff supports nothing, while
its later votes can still oppose. A head that is a proper ancestor of B does
not cover B and opposes it: a validator whose latest vote stands below B has
not endorsed B. Merely receiving a newer vote does not replace the resolved one
until its block is known; this keeps asynchrony from reducing honest support.
There is no absolute threshold: only the latest votes in the window are
weighed, the supporters of B against the validators that have moved away from
it or equivocated. Since support is inherited by ancestors and a supporter of B
opposes every block conflicting with B, two conflicting blocks cannot both hold
a relative majority at one store and one cutoff pair:
w(Pos(B)) > w(Opp(B)) ≥ w(Pos(C)) > w(Opp(C)) ≥ w(Pos(B)) is impossible. The
blocks holding a relative majority therefore lie on one chain, and the deepest
of them is well defined.

## A.9 §4 `sec:state-machine` — Quorum, combined attestations, evidence, height constants

The finality gadget extends each non-genesis block with a list of combined
attestations. It also defines the weighted quorum threshold

```text
q = ⌈2W / 3⌉.
```

A quorum is a set of validators whose total weight is at least q.

Height is a finality counter and is separate from slot. Genesis is justified
and finalized at height 0, and every chain starts at height 1. A justification
or a progress event increments height by one.

We extend the attestation to

```text
a = ( val_index, round, safe, height, target, τ, finalize_height, finalize_target ),
```

adding a height pair and a finality pair to the SG vote. The height pair is
empty, (⊥, ⊥, ⊥), or a vote (h, T, τ) at height h naming the block T that
brought the chain into height h on the validator's source, with τ = false for a
*target vote* and τ = true for a *timeout*: a timeout names the entry it times
out at. The finality pair is (h_f, T_f) with T_f ≠ ⊥, or the empty pair
(⊥, ⊥). Every SG rule reads only the projection (val_index, round, safe); the
anti-slashing record of §5 (`sec:fg-fork-choice`) reads the pairs with the flag
folded in, a timeout at h as (h, ⊥).

Two pair occurrences from one validator are slashable under either condition:

- **E1:** one finality pair is (h, T) with T ≠ ⊥, and one height pair at h is a
  timeout, or a target vote (h, T′, false) with T′ ≠ T;
- **E2:** two target votes are (h, T, false) and (h, T′, false) with T ≠ T′.

A timeout is never an E2 occurrence. The conflicting occurrences can be in one
attestation. An empty height pair triggers neither condition.

An honest validator emits at most one proposal per slot, one Goldfish vote per
slot, and one combined attestation per round.

Every block is evaluated from its parent's immutable post-state:

```text
σ[B] = state_transition(σ[B.parent], B).
```

(The chain state σ, its fields, its initial values and the quorum sets Q_target,
Q_prog, Q_finality are tabulated in §1.3 above, Definition `def:chain-state`.)

Fix constants K ≥ 4, D ≥ 2 and a timeout delay δ_t ≥ 0 in slots; K is meant
large, D minimal, and §6 (`sec:healing`) sets δ_t = 2R, two rounds. A height
pair counts only when it names the chain's own entry at the current height: a
target vote then records target participation and progress, a timeout records
progress alone, and a pair naming another entry records nothing, while its
finality pair is folded regardless. Timeouts are recorded in *progress* as soon
as they are folded, but a progress quorum that needs them is consumed only by a
block whose slot is at least σ.T_h.slot + δ_t, where σ.T_h is the block that
entered the height; an exact target quorum is consumed immediately:
attestations are synchronous at the scale of rounds, so a timeout may not be
used to leave a height before the target votes cast at that height have had
time to arrive. Without the delay, faulty timeouts released right after an
honest block that folded a partial honest target batch can cross the height
without justifying it.

The steady pipeline enters heights at debt σ.h − σ.h_F = 2, so D ≥ 2; K ≥ 3
avoids a skip cadence that regenerates itself at K = 2; K ≥ 4 is required
because finality liveness needs a proposer gap g ≥ 2 with g + 2 ≤ K, so K = 3
would admit no run with the liveness premises. On entry into a new height σ.h,
after the same transition has applied any finalization, set

```text
σ.nj ← (K | σ.h) ∧ (σ.h − σ.h_F > D).
```

## A.10 §5 `sec:fg-fork-choice` — Viability, derived views, anti-slashing record

The store adds a block state map Σ.σ[·] and finality state
(Σ.F, Σ.J, Σ.h_j, Σ.h_max). The block handler admits only descendants of the
finalized block, computes and stores the post-state, then folds it into the
finality caches with `update_finality(Σ, σ)`. The pair (Σ.J, Σ.h_j) tracks the
lex-greatest justification event compatible with the finalized block. Σ.F
advances only to a viable proper descendant of itself below Σ.J, so Σ.F ⪯ Σ.J
always holds and finalization never reverts. Σ.h_max only grows, and every
block that raises it descends the finalized block at that moment. When Σ.F
advances, an admitted block can stop descending it and its branch freezes: its
children now fail admission. The viability guard on the advance then keeps
Σ.h_max at most one above the largest state height among the finalized block's
descendants, so Σ.F itself is always viable.

**Definition (Viability, `def:fg-candidate-tree`).** A descendant of the
finalized block is viable when one of its descendants has state height at most
one below the current maximum. `viable_tree_from(Σ, blocks)` is defined over an
explicit processed-block view. The ordinary `viable_tree(Σ)` uses Σ.𝒯, and in
prose 𝒱(Σ) abbreviates it.

Fork choice uses two derived views: `get_fg_root(Σ)`, the FG root — the block
the walk starts from — and `get_filtered_block_tree_from(Σ, blocks)`, the
viable blocks below it in an explicit processed-block view.
`get_filtered_block_tree(Σ)` uses the full Σ.𝒯. Goldfish starts at the root
even if the root is not in the filtered tree.

At this layer `goldfish_eligible()` gains one clause: a child of a block whose
state height is below Σ.h_max − 1 is eligible without a majority. The majority
gate thus applies exactly while the walk stands inside the band
{Σ.h_max − 1, Σ.h_max}: every viable block below the band has a viable child,
so the walk always reaches height Σ.h_max − 1, and it never passes through the
band without a majority.

**Definition (Anti-slashing record, `def:antislashing`).** The record Λ holds,
for every height h, the validator's first target Λ.target[h], whether it
emitted a timeout Λ.timeout[h], and the target of its first finality pair
Λ.lock[h]; initially (⊥, false, ⊥). It also keeps the set Λ.timeouts of the
(h, T) pairs its timeouts have named, so that Λ.timeout[h] holds exactly when
some (h, T) is in it; a repeated timeout at h names the current entry, which
may differ from the one first named. It belongs to the validator, not to the
store, and `record_attestation()` is the only place that writes it. A validator
that never voted at height h_j may still emit a finality pair for (h_j, J): the
pair writes Λ.lock[h_j] ← J before release, so from then on its height pair at
h_j is either (h_j, J) or empty, never a timeout or another target; only a
recorded timeout or a different first target at h_j refuses the pair. A height
pair is refused, and left empty, when the record is locked elsewhere at its
height. Together, Σ and Λ determine the combined attestation. This is modeled
after the anti-slashing database of today's validators: a minimal, hardened
component of the validator client, separate from the beacon client that keeps
Σ. `create_attestation()` is its whole interface: it takes the record and the
vote information, produces the attestation, and updates the record before
releasing it; it never reads the store.

The height pair is built from a confirmed block's height fields: a target vote
can create a justification, and only confirmed blocks may be justified. The
finality pair is built from the head's finality fields: its subject is already
justified, so it may read an unconfirmed chain, and the head chain state holds
the freshest justification. Here C is Σ.live_confirmed, or the
relative-majority anchor when the anchor does not precede it: the vote never
falls behind or beside the represented chain. H is the fork-choice head; the
graded action passes its own safe block and head. `attest(Σ, Λ)` is the
beacon-client side: it derives the safe block, the head, and their chain-state
fields from the store, and broadcasts what `create_attestation()` releases. The
pair rules only read the record; `record_attestation(Λ, a)` folds the emitted
attestation into it before release, and `height_pair()` receives the same
attestation's finality pair as the lock at its height, so one attestation never
forms E1 evidence. `on_tick()` gains the record argument and, at a_r, runs
`attest()` in place of `sg_vote()`.

## A.11 §6.1 `sec:healing-schedule` — Round schedule, grade cutoffs, timeout delay

Assume R ≥ 3 slots per round, write T_r = t_{rR} for the opening slot's
proposal time, and set the timeout delay of §4 (`sec:state-machine`) to
δ_t = 2R: a timeout at a height is counted only from the second round after the
round in which the height was entered, because target votes of one round are
assumed to reach every honest store by the end of the next round. This is the
protocol's value. The Lean results are proved for every δ_t = (2 + e)R with
e ≥ 0 extra rounds; e enters the liveness constants only, through the
height-progress lag L = 7g + 22 + 4e for a proposer-recurrence gap of g rounds.
Each grade has an early cutoff h_r, a late cutoff e_r, and a completion time
d_r:

```text
┌───────┬──────────┬──────────┬──────────┐
│ grade │   h_r    │   e_r    │   d_r    │
├───────┼──────────┼──────────┼──────────┤
│ G2    │ T_r − 5Δ │ T_r − Δ  │ T_r − Δ  │
│ G1    │ T_r − 4Δ │ T_r − 2Δ │ T_r      │
│ G0    │ T_r − 3Δ │ T_r − 3Δ │ T_r + Δ  │
└───────┴──────────┴──────────┴──────────┘
```

Every cutoff is strict: an object received at the cutoff is later. A grade
completes from the store as it was before its completion tick; objects
processed at that time are excluded. The action time is a_r = T_r + 6Δ, the
opening slot's confirmation evaluation: `on_tick()` evaluates that confirmation
and then runs `attest()` in the same tick.

At a tick, the node first completes every grade whose completion time it is,
then advances its clock and runs the slot duties in their order: proposal,
Goldfish vote, confirmation, attestation. Grade 1 of round r is therefore
complete for the opening proposal, and grade 0 for the opening Goldfish vote. A
validator that is asleep for round r skips its attestation only; grade
completion and the slot duties run regardless.

The previous round's action is at T_r − 4RΔ + 6Δ; under synchrony its
attestation reaches every honest store before T_r − 4RΔ + 7Δ ≤ T_r − 5Δ, the
grade-2 early cutoff, with equality at R = 3. This is why R ≥ 3.

## A.12 §6.2 `sec:grades` — Grades, completion, active prefix

**Definition (Grades, `def:grades`).** The three grades of round r are the
relative majority of Definition `def:majority-fork-choice`, over the window
I_r, taken at the three cutoff pairs of the schedule: G2 at
(T_r − 5Δ, T_r − Δ), G1 at (T_r − 4Δ, T_r − 2Δ), and G0 at
(T_r − 3Δ, T_r − 3Δ), with one refinement: a vote is resolved by a cutoff only
if its safe block is also compatible with the finalized block Σ.F. A vote for a
block conflicting with the finalized chain therefore neither supports nor
covers; a resolved vote for a finalized ancestor keeps that ancestor as its
head. The window is fixed by the round label, not by the clock at which the
grade is computed; a round-k vote is read by the grades of rounds
k + 1, …, k + η_SG. In prose, G2(B) abbreviates the grade-2 test on B with the
store and round from context, and likewise grades 1 and 0.

The grade is the relative majority of §3 (`sec:majority-sg`) read at fixed
cutoffs rather than at the time of use: the early cutoff fixes whose latest
vote counts, the late cutoff lets later votes and equivocations oppose. By the
same argument as there, the blocks holding one grade in one store lie on one
chain, and the deepest of them is well defined.

**Definition (Completion and finality, `def:frame`).** At the completion time
of a grade, the node evaluates the grade over the processed tree Σ.𝒯, from the
store as it was before the tick, and saves the result in the store's field for
that grade, Σ.G2, Σ.G1 or Σ.G0: the deepest graded block, or ⊥ when no block
holds the grade. Each field is written once per round, at its completion time,
and never recomputed; the grade-2 write falls in the last Δ of the previous
round. Whenever the finalized block advances, every saved block is replaced by
its deepest ancestor compatible with the new finalized block; a field at ⊥
stays there. The three fields always hold the current round's grades when read:
grade 2 is written after the previous round's last read, and grades 1 and 0 are
written by the tick that runs their first readers, the opening proposal and the
attestation. A node that joins starts with empty fields and does not
reconstruct a missed grade; its first complete set of grades is the next
round's.

A saved block is *active* when it has an ancestor in the filtered block tree of
§5 (`sec:fg-fork-choice`), and its *active prefix* is the deepest such
ancestor: the fork choice can use it, and it descends the FG root. Grades 2
and 1 are used positively, through their active prefix. Grade 0 is used only
negatively, as a veto: a block is *grade-0 compatible* when it is compatible
with the saved grade-0 block, and every block is while that field is ⊥. The
veto is not restricted to the filtered tree, since a fresh majority against the
confirmed branch counts whatever the position of its own block.

Across validators, *graded delivery* is conditional on admission. Under
synchrony, a vote or block counted at one cutoff reaches every validator by the
next, and a vote is resolved at the receiver once the receiver admits its head,
that is, once that head is compatible with the receiver's finalized block. A
block at or above the receiving store's finalized block that holds grade 2 here
therefore holds grade 1 there, and grade 1 here gives grade 0 there; a store
that refuses the supporting heads has finalized a block they conflict with.
Under the same conditions the saved grade-2 blocks of honest stores lie on one
chain, and a saved grade-2 or grade-1 block is compatible with the saved
grade-0 block of every honest store: it is never vetoed.

## A.13 §6.3 `sec:fresh-anchor` — The SG root

The SG root of round r is the active prefix of the saved grade-1 block, and the
FG root when there is no grade-1 block or it has no active prefix. It replaces
the relative-majority walk of §3 (`sec:majority-sg`) in the complete protocol:
the walk's relative majority is now the grade, computed once at T_r over the
window's latest votes and saved, and the deepest graded block is where the walk
would end. The FG-root case covers a fresh finalization, when the root has
advanced past every grade-1 block and is itself canonical, as well as a round
without any grade-1 block. The selection is derived at every use, from the
saved grade and the current store; in walk position the SG root is the anchor,
and the prose calls it that. A fresh SG root in use at an honest validator is a
grade-1 block of its store; under the delivery conditions above it holds
grade 0 in every honest store that admits its supporting heads, and it is a
veto there whether or not that store's filtered tree contains it.

## A.14 §6.5 `sec:nonjustifiable` — Nonjustifiable heights

The flag σ.nj of §4 (`sec:state-machine`) disables justification at every K-th
height under finality debt, while exact and empty-target votes still advance
the height. Healing therefore never waits on a justification that the debt rule
forbids.
