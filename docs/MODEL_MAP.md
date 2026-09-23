# Complete-protocol Model map

This map compares Section 7 of `consensus.tex` with the retained
`DecoupledConsensusModel` declarations. It lists hand-written source
declarations only. Compiler-generated constructors, recursors, projections,
and derived instances stay grouped with their source type.

## Store and validator record

The paper has 17 cumulative-store components. `Protocol.Store` has 16 core
Lean fields: one paper timestamp component is three typed maps, and the three
paper grade fields are in the node cache. `NamedStore` carries full named block
and attestation payloads as runtime metadata.

```text
┌──────────────────────────────┬────────────────────────────────────────────────────────────────────┬─────────────────┐
│ Paper item                   │ Active Lean declaration                                             │ Divergence      │
├──────────────────────────────┼────────────────────────────────────────────────────────────────────┼─────────────────┤
│ Σ.t                          │ Protocol.Store.t; NamedStore.setClock                               │ none            │
│ Σ.s                          │ Protocol.Store.s; NamedStore.setClock                               │ none            │
│ Σ.T                          │ Protocol.Store.T                                                    │ none            │
│ Σ.timestamp[blocks]          │ Protocol.Store.timestamp_block                                      │ different shape │
│ Σ.timestamp[Goldfish votes]  │ Protocol.Store.timestamp_vote                                       │ different shape │
│ Σ.timestamp[attestations]    │ Protocol.Store.timestamp_sg_vote, keyed by Protocol.sgVote           │ different shape │
│ Σ.σ                          │ Protocol.Store.σ                                                    │ none            │
│ Σ.gfPool[k]                  │ Protocol.Store.gf_votes; Protocol.Store.pool                         │ renamed         │
│ Σ.attestations[r]            │ Protocol.Store.sg_votes; Protocol.NamedStore.sg_rows; Store.sg_pool           │ different shape │
│ Σ.Gtwo/Gone/Gzero            │ Execution.NamedNodeState.cache; Protocol.Cache.current/next              │ different shape │
│ Σ.F                          │ Protocol.Store.F                                                    │ none            │
│ Σ.J                          │ Protocol.Store.J                                                    │ none            │
│ Σ.h_j                        │ Protocol.Store.h_j                                                  │ none            │
│ Σ.hmax                       │ Protocol.Store.h_max                                                │ renamed         │
│ Σ.liveConfirmed              │ Protocol.Store.live_confirmed                                       │ renamed         │
│ Σ.latestConfirmed            │ Protocol.Store.latest_confirmed                                     │ renamed         │
│ Σ.latestStable               │ Protocol.Store.latest_stable                                        │ renamed         │
│ full block payloads          │ Protocol.NamedStore.bodies                                                   │ different shape │
│ full attestation payloads    │ Protocol.NamedStore.sg_rows                                                  │ different shape │
│ Λ.target[h]                  │ NamedRecord.legacy.target                                            │ different shape │
│ Λ.timeout[h]                 │ NamedRecord.legacy.timeout                                           │ different shape │
│ Λ.lock[h]                    │ NamedRecord.legacy.lock                                              │ different shape │
│ Λ.timeouts                   │ NamedRecord.timeoutHistory                                           │ renamed         │
└──────────────────────────────┴────────────────────────────────────────────────────────────────────┴─────────────────┘
```

`Λ.timeouts` is present and active. `Protocol.NamedRecord.rememberTimeout` records the
full `(h,T)` pair, and `NamedNodeState.record` carries it.

## Section 7 functions

```text
┌──────────────────────────────────┬────────────────────────────────────────────────────────────────────┬─────────────────┐
│ Paper function                   │ Active Lean implementation                                         │ Divergence      │
├──────────────────────────────────┼────────────────────────────────────────────────────────────────────┼─────────────────┤
│ on_tick                          │ NamedNode.tick; NamedTick.tick; TickScheduler.runWith               │ different shape │
│ update_confirmation              │ Protocol.update_confirmation_with; NamedDuties counterpart         │ different shape │
│ update_user_confirmation_records │ update_confirmation_with record-update expression                   │ inlined         │
│ advance                          │ Protocol.advance_confirmed; Option handled by caller                 │ different shape │
│ stable_root                      │ Protocol.frameStableRoot                                             │ renamed         │
│ get_stable                       │ Protocol.get_stable                                                  │ none            │
│ get_confirmed                    │ Protocol.get_confirmed                                               │ none            │
│ on_block                         │ NamedAdmission.on_block_with; NamedStore.process_block_core          │ different shape │
│ on_goldfish_vote                 │ on_goldfish_vote_checked plus on_goldfish_vote core                  │ different shape │
│ on_sg_vote                       │ Protocol.on_sg_vote; NamedAdmission.admit_row                         │ different shape │
│ update_finality                  │ Protocol.update_finality plus NamedNode cache clipping               │ different shape │
│ clip saved grade on F advance    │ Protocol.clipGrade; clipFrame; clipCache                            │ inlined         │
│ resolution_time                  │ Protocol.resolution_time; SG rawInputs/bodyReady split               │ different shape │
│ viable_tree_from                 │ Protocol.viable_tree with explicit blocks                            │ renamed         │
│ viable_tree                      │ callers pass Σ.T to Protocol.viable_tree                              │ inlined         │
│ goldfish_score                   │ Protocol.goldfish_score                                               │ none            │
│ ghost                            │ Protocol.ghost                                                        │ none            │
│ goldfish_eligible                │ Protocol.goldfish_eligible                                            │ none            │
│ goldfish_fork_choice             │ Protocol.goldfish_fork_choice                                         │ none            │
│ get_fg_root                      │ Protocol.get_fg_root                                                  │ none            │
│ get_filtered_block_tree_from     │ Protocol.get_filtered_block_tree_from                                 │ none            │
│ get_filtered_block_tree          │ Protocol.get_filtered_block_tree                                      │ none            │
│ equivocates (SG)                 │ Protocol.CleanFrom via Protocol.rawView                              │ different shape │
│ supports                         │ Protocol.Supports; Protocol.positive                                  │ different shape │
│ opposes                          │ Protocol.Opposes; Protocol.opposing                                   │ different shape │
│ relative_majority                │ Protocol.gradeBool                                                     │ renamed         │
│ resolved_votes                   │ Protocol.rawInputs/interpretedInputs/bodyReady                       │ different shape │
│ grade                            │ gradeBool call in freezeRoot                                          │ inlined         │
│ update_grades                    │ Protocol.onPhaseTick/completeFrame/completeOne                         │ different shape │
│ graded_block                     │ Protocol.freezeRoot                                                   │ renamed         │
│ active_prefix                    │ Protocol.activePrefix                                                 │ different shape │
│ G0_compatible                    │ Protocol.clear                                                        │ renamed         │
│ get_sg_root                      │ Protocol.get_sg_root_with over frameGradeRead.anchor                   │ different shape │
│ get_head_in_tree                 │ Protocol.get_head_in_tree_with                                         │ different shape │
│ get_head                         │ Protocol.get_head_with                                                 │ different shape │
│ voter_processed_block_tree       │ Protocol.voter_processed_block_tree                                    │ none            │
│ voter_filtered_block_tree        │ Protocol.voter_filtered_block_tree                                   │ none            │
│ propose_block                    │ NamedDuties.propose_block_with; NamedActions.proposal_with            │ protocol change │
│ proposal_attestations            │ NamedProposalRows.proposalRows                                        │ protocol change │
│ goldfish_vote                    │ NamedDuties.goldfish_vote_with; Protocol.goldfish_vote_with           │ different shape │
│ attest                           │ NamedDuties.attest_with; NamedActions.round_action_with               │ different shape │
│ get_sg_vote                      │ Protocol.get_sg_vote_with                                             │ renamed         │
│ get_fg_vote                      │ Protocol.get_fg_vote_with                                             │ renamed         │
│ finality_pair                    │ Protocol.finality_pair                                                 │ none            │
│ height_pair                      │ Protocol.height_pair plus NamedRecord.encodeHeight                      │ different shape │
│ create_attestation               │ Protocol.NamedRecord.create over Protocol.create_attestation            │ different shape │
│ record_attestation               │ Protocol.record_attestation plus rememberTimeout                       │ different shape │
│ state_transition                 │ Protocol.state_transition/transition_rows                              │ different shape │
│ process_attestation              │ process_attestation_with plus process_attestation                     │ different shape │
│ process_height_events            │ Protocol.process_height_events                                         │ none            │
│ advance_height                   │ Protocol.advance_height                                                │ none            │
└──────────────────────────────────┴────────────────────────────────────────────────────────────────────┴─────────────────┘
```

Corrections to the earlier map:

- SG `equivocates` is the raw-vote head-equivocation test. It is not
  the Goldfish compatibility helper.
- `state_transition` is active code. The named block path calls
  `Protocol.named_transition`.
- `stable_root` is `frameStableRoot`, not only an inlined expression.
- `on_goldfish_vote` includes the committee guard through its checked wrapper.
- `resolution_time` has active Goldfish and SG receipt/body representations.
- The clipping loop is an active part of the saved-grade update.
The execution and evidence declarations that support the complete protocol are
also part of the map:

```text
┌──────────────────────────────┬──────────────────────────────────────────────────────────┬─────────────────┐
│ Execution or evidence item   │ Active Lean declaration                                   │ Divergence      │
├──────────────────────────────┼──────────────────────────────────────────────────────────┼─────────────────┤
│ Store initialization         │ Protocol.Store.init; NamedStore.initial;                │ different shape │
│                              │ NamedNode.initial                                        │                 │
│ Timeout configuration        │ Execution.Setup.timeout_rounds; HeightConfig.timeoutDelay│ generalized     │
│ Object dispatch              │ Execution.NamedNode.process; NamedReceipt.process       │ not in paper    │
│ Object checks                │ NamedReceipt.wellFormed/depsPresent/processed/excludes  │ not in paper    │
│ Handler observation          │ Execution.handles; Execution.spec                        │ not in paper    │
│ Root idealization            │ Execution.RootInjectiveBelow;                          │ implicit paper  │
│                              │ Execution.RootInjectiveOnAncestors                       │                 │
│ Certificate evidence        │ Protocol.chain_attestations; Protocol.store_attestations │ different shape │
│ Slashing weight              │ Protocol.SlashableBetween;                              │ different shape │
│                              │ Protocol.HasIntersectionWeight;                         │                 │
│                              │ Protocol.HasSlashableWeightBetween                      │                 │
└──────────────────────────────┴──────────────────────────────────────────────────────────┴─────────────────┘
```

## Earlier-section families used by Section 7

```text
┌────────────────────────────────┬─────────────────────────────────────────────────────────────┬─────────────────┐
│ Paper family                   │ Lean family                                                 │ Divergence      │
├────────────────────────────────┼─────────────────────────────────────────────────────────────┼─────────────────┤
│ §1 substrate/wire objects      │ Objects/*; Protocol/ChainState.lean                         │ different shape │
│ §2 Goldfish store and merge    │ Protocol/StoreBase.lean; Protocol/Store.lean                │ different shape │
│ §2 Goldfish score and walk     │ Protocol/ForkChoice/Goldfish.lean                          │ none            │
│ §3 SG pool/window              │ Protocol/Grades.lean; Protocol/Store.lean                  │ different shape │
│ §4 chain state/transition      │ Protocol/ChainState.lean; Protocol/Handlers.lean            │ different shape │
│ §4 E1/E2                       │ Protocol/Evidence.lean                                      │ none            │
│ §5 FG tree and client          │ Protocol/ForkChoice/Goldfish.lean; Views.lean; Head.lean   │ different shape │
│ §6 schedule and grades         │ Protocol/Schedule.lean; Protocol/Grades.lean                 │ different shape │
│ Generic execution              │ Execution/* plus Generic ProtocolSpec/Run                   │ not in paper    │
└────────────────────────────────┴─────────────────────────────────────────────────────────────┴─────────────────┘
```

## Source-declaration inventory

This is a semantic inventory of hand-written declarations. Generated
constructors, recursors, `casesOn`, `noConfusion`, projections, and derived
instances remain grouped with their source type.

```text
┌──────────────────────────────────────────┬──────────────────────────────────────────────────────────────────────────────┐
│ Source family                            │ Hand-written declarations covered                                           │
├──────────────────────────────────────────┼──────────────────────────────────────────────────────────────────────────────┤
│ Substrate identifiers/time               │ Slot, Height, Round, BlockId, genesisRoot, Time, Stamp, Occurrence,          │
│                                          │ TimestampMap, stampedBefore, beforeCutoff, occurrenceBefore/Max,             │
│                                          │ slotStart, slotOfTime                                                       │
│ Substrate weights/environment            │ Electorate, totalWeight, weightOf, finalityThreshold, quorumCheck,           │
│                                          │ Committees, Env, committee, t, slotOf, W, q                                 │
│ Substrate pairs/blocks                   │ HeightPair, FinalityPair, GoldfishVote, CombinedAttestation, Block, all       │
│                                          │ block projections, ancestry, compatibility, depth/deeper, pickUnique?,       │
│                                          │ find?, deepest?                                                             │
│ Named substrate                          │ NamedHeightPair, erase, matchesEntry, NamedAttestation, NamedBlock and all    │
│                                          │ named projections/ancestry/erasure                                          │
│ Goldfish                                 │ Node; vote-set vocabulary; schedule functions; validity checks; Store;       │
│                                          │ resolution; pool/tau; raw/support/proposer/block views; score; walk;         │
│                                          │ no_second_vote_in                                                           │
│ Majority SG                              │ SGVote, Store, latest_window                                               │
│ Finality gadget                          │ HeightConfig, ChainState, initialization/quorum reads; E1/E2; transition      │
│                                          │ guards and updates; TimeoutBinding and targeted binding; row transitions     │
│ FG fork choice/client                   │ HeightId, Store, finalized_descendants, viable/tree/root/filter/gate/walk;    │
│                                          │ Record and pair/client functions; NamedRecord codec/history/client           │
│ Healing                                  │ HealConfig schedule; GradeView; Store projection; GradeRead/Contract;        │
│                                          │ chain/deepest-clear helpers; head/action/input/named-action functions        │
│ Grade runtime                            │ Token/CleanFrom/Supports/Opposes; raw/interpreted inputs; selectors; Frame;   │
│                                          │ Phase/Cache completion, alignment and clipping; frame contract               │
│ Protocol core                            │ Store and projections; confirmation policy/accessors; handlers; proposal     │
│                                          │ row window; scheduler operations                                             │
│ Named protocol                           │ NamedStore/admission/proposal-row/duty/tick declarations                    │
│ Concrete execution                       │ Setup; NamedObject/Event/Node/Profile/Receipt/Run; action and receipt         │
│                                          │ observers; root idealization; handles/spec; selected Run/storeAt                │
│ Root idealization                        │ RootInjectiveBelow, RootInjectiveOnAncestors                                │
└──────────────────────────────────────────┴──────────────────────────────────────────────────────────────────────────────┘
```

The inactive alternatives are not part of the selected complete protocol.
The old admission and candidate helper names were deleted after the
constant-closure check;
the active definitions are specialized to `.alsoCarried`, `.poolAndCarried`,
and `.optional`.

## Divergence analysis and unmade edits

**Typed timestamps.** The paper has one heterogeneous `timestamp[·]`; Lean has
three typed maps for blocks, Goldfish votes, and the SG projection. Every read
uses the correct map and the same strict comparison, so behavior is unchanged.
For line-by-line alignment, define a tagged `ProtocolObject` key and one
`timestamp : TimestampMap ProtocolObject`, then make the three current
accessors thin tag projections.

**Substrate wire shapes.** Lean uses recursive blocks, root references in votes,
and separate named/erased attestation and block types. The active named objects
retain every paper field, and the collision idealization makes root resolution
faithful, so behavior is unchanged. For line-by-line alignment, use the named
wire types as the only public wire types and keep structural erasure private to
ancestry and fork-choice helpers.

**List-backed pools and views.** The paper calls pools and row unions sets.
Lean uses lists where duties must copy payloads and converts to `Finset` for set
reads. Handler duplicate caps make reachable pools set-like. This is a
representation choice. For line-by-line alignment, define a deterministic
finite-set container with executable ordered enumeration and use it for both
storage and proposal construction.

**Attestation pool and named payloads.** The paper stores full attestations in
one pool. Lean keeps an erased `CombinedAttestation` pool in `Protocol.Store`
and the full timeout-entry rows in `Protocol.NamedStore.sg_rows`. The selected handler
updates both in one admission path. This preserves behavior and full evidence.
For line-by-line alignment, make `NamedAttestation` the sole pool element and
derive the erased SG and accountability views from it.

**Saved grades and store field count.** The paper stores three flat fields.
Lean stores a bounded `current` and `next` frame because next-round G2
completes before the round rotates. Readers use only the aligned frame, and
finality clips both frames, so behavior is unchanged. For line-by-line
alignment, add `Gtwo/Gone/Gzero` to the node store, overwrite `Gtwo` at its
early completion, and keep only an internal round label/completion marker if
proofs need it.

**Named store metadata.** `Protocol.NamedStore.bodies` and
`Protocol.NamedStore.sg_rows` retain signed/full
payloads while `Protocol.Store` keeps executable geometry. They do not add a
paper protocol choice. The exact edit is to merge the full payload types into
the cumulative `Store` and delete the core/named split.

**Anti-slashing record split.** The paper's four-field `Λ` is split between
`NamedRecord.legacy` and `timeoutHistory`. The Boolean timeout map and history
are updated together by `NamedRecord.create`; behavior is unchanged. The exact
edit is to make `target`, `timeout`, `lock`, and `timeouts` direct fields of one
record and delete `legacyCreate` and the codec layer.

**Tick composition.** The paper has one `on_tick`; Lean completes grades in
`NamedNode.tick`, then calls the generic `TickScheduler`, then clips the cache.
The ordering is the paper's ordering. The exact edit is to expose one named
`on_tick` that contains these three steps and make the generic scheduler a
private helper.

**Confirmation update and advance.** The paper passes an optional candidate to
`advance`; Lean handles `none` at the call site and gives `advance_confirmed` a
plain block. The record writes are one structure update but compute the same
three cases. The exact edit is `advance : Block → Option Block → Block`, a
named `update_user_confirmation_records`, and a direct call from
`update_confirmation`.

**Block and vote handlers.** The paper handlers are single functions. Lean
separates validation, the core geometry update, full named payload retention,
and carried-row admission. The selected composition preserves the guard and
write order, including SG admission after finality. The exact edit is to expose
one public handler per paper name and make the current `*_checked`, `*_using`,
`process_block_core`, and `admit_carried` declarations private local steps.

**Finality clipping.** The paper clips G2/G1/G0 inside `update_finality`. Lean
updates `F` in the core store and clips the node cache immediately after the
handler or tick. No duty can observe the un-clipped cache. The exact edit is to
move `clipCache` into the public finality-update result over the unified node
store and name the recursive helper `clip`.

**Resolution time.** Goldfish has a direct derived map. SG resolution is split
into receipt selection and the `bodyReady` test, whose conjunction is the same
maximum-timestamp and finality-compatibility test. The exact edit is to define
one overloaded/tagged `resolution_time` and use it in `resolved_votes`.

**Viable trees.** Lean's `viable_tree` takes the candidate block set explicitly,
so it implements paper `viable_tree_from`; paper `viable_tree` is inlined by
passing `st.T`. Behavior is unchanged. Rename the current function to
`viable_tree_from` and add the one-line store wrapper.

**SG equivocation/support/opposition.** Lean represents votes as tokens and
splits raw from body-ready views. `CleanFrom`, `Supports`, and `Opposes` encode
the paper's greatest-early-round and later-raw-equivocation rules. Behavior is
unchanged. Rename these declarations to the paper names and hide `Token`,
`rawView`, and `readyView` behind `resolved_votes`.

**Grades and update_grades.** The paper evaluates a set expression and saves a
block. Lean uses `gradeBool`, `freezeRoot`, and phase/cache completion helpers.
Exact-domain-time and once-only checks match the paper. Rename `gradeBool` to
`relative_majority`, add the one-line `grade`, rename `freezeRoot` to
`graded_block`, and expose one `update_grades` wrapper.

**Active prefix, G0 compatibility, and SG root.** Lean passes an already-derived
filtered tree to `activePrefix`, calls the G0 predicate `clear`, and obtains the
G1 fallback through the grade contract. Behavior is unchanged. Give
`active_prefix` the store and optional grade arguments, rename `clear` to
`G0_compatible`, and put the current `anchor` body directly in `get_sg_root`.

**Head functions.** Lean makes the selected grade contract explicit. The paper
has one fixed protocol, so this is dependency injection, not protocol choice in
the selected runtime. For line-by-line alignment, close the contract at the
module boundary and expose contract-free `get_head_in_tree` and `get_head`.

**Proposal and proposal-attestation selection.** Lean splits field reads,
full-parent lookup, row-source selection, `proposalRows`, construction,
local processing, and emitted output. The selected source is the paper source.
`proposalRows` excludes rows already on the parent chain and keeps at most two
distinct full rows per (validator, round). The paper copies every eligible row.
Line-by-line alignment would require the paper's all-eligible-row rule in place
of this bounded selector.

**Duplicate proposal rows.** Paper lines 2044–2049 use set union. Lean appends
pool and carried lists before `proposalRows` removes repeated full rows and
limits each (validator, round) to two rows. This bounds the payload while
retaining two distinct rows that can show equivocation.

**Goldfish vote and attestation duties.** Lean returns state/output tuples and
splits store reads from named payload construction. The selected calls perform
the same reads and writes. For alignment, expose the paper duty names over the
unified store and keep tuple/output plumbing private.

**Height-pair wire representation and client.** The erased `HeightPair.timeout`
drops the entry target, while `NamedHeightPair.vote h entry true` retains it.
`targetedHeightPair` checks the entry before the common transition, and
`NamedRecord` restores timeout history. This is representation-only. Use the
paper triple `(h,T,τ)` as the sole height-pair type and delete erasure/codec and
timeout-binding adapters.

**State transition.** The paper's asserts are receiver guards in
`on_block_using`; the fold itself is row-parametric and the active
specialization is `named_transition`. This is total-function factoring, not a
behavior change. Expose `state_transition` over the active block type, keep the
guards in `on_block`, and make `fold_rows`/`transition_rows` private.

**Generic execution (`not in paper`).** `Execution/*` supplies events, runs,
receipts, observations, and the `ProtocolSpec` instance. This is part of the
selected design and does not alter the protocol. No deletion is needed. Move
proof-only observation conveniences to ModelVocabulary only if a future change
requires the Model entry point to contain executable state alone.

**Inactive alternatives (`not in paper`).** The closure check showed that
`wireOnly`, `resolvedPool`, and `the obsolete candidate helper` were not needed
by `spec`. They were deleted, and the active functions are specialized to
`.alsoCarried`, `.poolAndCarried`, and `.optional`.
