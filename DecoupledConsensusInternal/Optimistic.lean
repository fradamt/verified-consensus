module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Availability
public import DecoupledConsensusInternal.Derived
public import DecoupledConsensusInternal.Definitions.PhaseGrades
public import DecoupledConsensusInternal.Definitions.NamedEvidence

@[expose] public section

/-!
# P4 optimistic operation, and P4-L finality liveness
(design note P4; rev. 3 §4.4, §5, §8; §5 for P4-L;
PROTOCOL.md#the-complete-protocol)

P4 is P3(b) with three more conclusions. Under `AlignedRound(r₀)` and
`a_{r₀} ≥ t_GST`:

> **(C0) Invariance.** `AlignedRound(r)` holds for every round `r ≥ r₀`, with a
> monotone `Can_r ⪰ Can_{r₀}`.
>
> **(C1) Available chain.** P3(b)'s conclusions, at every time from `a_{r₀}` on —
> not only at round boundaries.
>
> **(C2) Confirm then attest.** Every attestation an honest validator emits from
> `a_{r₀}` on carries height-pair and finality-pair targets that are ancestors of
> `Can_r`, or the empty pair. Hence every justification and every finalization
> any chain acquires is on the canonical chain.
>
> **(C3) Non-interference.** For every honest node and every time from `a_{r₀}`
> on: the fork-choice root is an ancestor of `Can_r` **and moves only forward
> along it**; `Can_r` is in the filtered block tree; the round's anchor is an
> ancestor of `Can_r`; the round action's gate is the node's own
> `live_confirmed`.

(C0) is round-indexed and (C1) is time-indexed, which is doc1's shape. (C3)'s
"moves only forward" is the load-bearing phrasing: it is what makes the finality
gadget's effect on the available chain provably null, and it is the argument
doc1 turned out not to contain (rev. 3 §8, §10).

**Deviation from the design note's "no mechanism in statements" rule.** (C3) names
the fork-choice root, the filtered block tree and the round anchor. It has to:
(C3) *is* the non-interference claim, and non-interference is a statement about
the mechanism. The rule bites on (C0)–(C2) and on P3, where it is kept. Recorded
in `docs/modeling-choices.md`, row W5.7.

**What is derived and therefore absent** (rev. 3 §4.4, rev. 4 §4). `Σ.J ⪯ Can`
and `Σ.F ⪯ Can` are consequences, not clauses: the finalization guard is
`σ.F ⪯ Σ.J` (PROTOCOL.md#the-complete-protocol) and `Σ.F ⪯ Σ.J` is a store invariant, so rev. 2's
separate no-conflicting-finalization clause is gone. `Can`'s viability needs no
ceiling clause either: by Lemma G4 a chain advances from `h` to `h+1` only if
`2q − W` of honest weight was confirmation-gated at `h`, and those gates are on
`Can`, so the ladder is climbed by `Can` or by nobody.

**Rev. 4's hypothesis change** (amended per rev. 4 review). P4, P4-L and P3(b)
now carry `BelowOneThird` where they carried `HonestQuorum`. The predicate's own
clauses (c) and (e) are gone, and what replaces them is two results carrying two
*different* bounds:

* (c)'s defence against a late conflicting finalization is
  `Proofs.AlignedRoundLemmas.no_off_can_finalization`, the quorum clash — and it
  runs on the **accountable** `Execution.SlashableBound` alone, counting no
  faulty weight;
* (e) is `Proofs.AlignedRoundLemmas.honest_no_double_target`, proved
  unconditionally.

Neither is why the hypothesis changed. `BelowOneThird` is carried for the Lemma
G4 sites — L1's gate-fires case, the (d′)-preservation half of the induction
below, and P4-L — every place a quorum has to be shown to *contain honest
weight*, which the accountable bound cannot show because fresh votes at a height
nobody has voted at are slashable against nothing.

The four derived lemmas L1–L4 live in that file. L1 `gate_selects_canonical` is
the statement (C3)'s first clause consumes: it concludes `⪯`, not merely
compatibility, and the step between the two is the depth bound its
`RootProvenance` bundle carries beside `crossed` — both are the same (C3)
viability fact, and both are owed to this proof rather than to the predicate.

**A wording correction the plan carried.** Grades *do* fire in benign runs: the
common honest head has absolute-majority direct support and therefore holds
grade 3 (PROTOCOL.md#the-complete-protocol). The true claim is that every graded root is on `Can`
and no conflicting block reaches grade 0, so the graded branch selects the chain
the ungraded one would (rev. 3 §4.4).
-/



namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The round-indexed canonical chain of an optimistic interval: `Can r` is the
aligned round `r`'s deepest honest confirmation. -/
def CanonicalFamily (S : Setup V) (ρ : Run V) (r₀ : Round) (Can : Round → Block V) :
    Prop :=
  ∀ r : Round, r₀ ≤ r → S.a r ≤ ρ.horizon →
    ∃ h_r : Height, AlignedRound S ρ r (Can r) h_r (ρ.roundView S r)


/-- **(C0) Invariance** (rev. 3 §5, §8). The predicate holds at every later
round, and the canonical chain grows away from the starting round.

Stability is P4's, not P5's: a P5 stated "for all later rounds" would duplicate
this induction, and doc1 shows the stronger form is not inductive
(rev. 3 §8).

**The monotonicity is `Can_r ⪰ Can_{r₀}`, not round-by-round.** rev. 3 §8 asks
for exactly that — "a monotone `Can_r ⪰ Can_{r₀}`" — and the check doc's H3 is
why the stronger reading is not available: `Can` is defined over
`Σ.live_confirmed`, which `update_confirmation` writes **unconditionally**
(PROTOCOL.md#the-complete-protocol guards only `Σ.latest_confirmed` with `⪯`). That the
confirmation walk does not retreat is a lemma about the walk, not a store
invariant, and it is unproved; the `Can_{r₀}`-relative form survives without it.
Recorded as choices row W5.17. -/
def C0Invariance (S : Setup V) (ρ : Run V) (r₀ : Round) (Can : Round → Block V) :
    Prop :=
  CanonicalFamily S ρ r₀ Can ∧
    ∀ r : Round, r₀ ≤ r → S.a r ≤ ρ.horizon → Block.Preceq (Can r₀) (Can r)

/-- **(C1) Available chain** (rev. 3 §8). P3(b)'s conclusions at every time from
`a_{r₀}` on, not only at round boundaries — **and** P3(b)'s own last clause, that
every confirmed block from `a_{r₀}` on is compatible with `Can`.

The second conjunct is what makes (C1) imply P3(b) rather than merely resemble
it: `AvailabilityFromAlignedRound` is `AvailableChainFrom` *plus* that clause,
so without it P4 does not deliver P3(b) and the two statements are independent
obligations. -/
def C1AvailableChain (S : Setup V) (ρ : Run V) (r₀ : Round)
    (Can : Round → Block V) : Prop :=
  AvailableChainFrom S ρ (S.a r₀) ∧
    ∀ v ∈ ρ.honest, ∀ t : Time, S.a r₀ ≤ t → t ≤ ρ.horizon →
      Block.compatible (Can r₀) (ρ.storeAt S v t).latest_confirmed = true

/-- **(C2) Confirm then attest** (rev. 3 §8; PROTOCOL.md#the-complete-protocol).
Every nonempty target an honest validator emits from `a_{r₀}` on names a block of
its own store on the canonical chain. The empty pair needs no clause:
`targetsAt` is empty on it.

By Lemma G4 this is also the statement that every justification and every
finalization any chain acquires is on the canonical chain — a quorum at a height
needs `2q − W` of honest weight signing there, and this clause says every such
signature is canonical.

Two corrections from the statement reviews.

* **The round index is `a.round + 1`, not `a.round`.** `a_r` is the opening
  slot's confirmation evaluation and `on_tick_emit` runs `update_confirmation`
  and *then* `attest` in that one tick (PROTOCOL.md#the-complete-protocol), while `Can r` is
  read at `roundView r = viewBeforeTime (a_r)` — before the tick. A block
  confirmed at that very tick is a strict **descendant** of `Can r`, so
  `B ⪯ Can r` is false for it while `Can r ⪯ B` holds. Indexing at the next
  round reads the `Can` that has seen the tick's own confirmation. The order is
  kept: (C3)'s "moves only forward along `Can`" is the load-bearing phrasing and
  weakening this to compatibility would discard it.
* **The witness is a block of the emitter's store**, matching clause (d) of
  `AlignedRound`. The bare `∃ B: Block V` form is satisfiable by a block nobody
  holds whenever two blocks share a root, and P4 carries no root-injectivity
  hypothesis. -/
def C2ConfirmThenAttest (S : Setup V) (ρ : Run V) (r₀ : Round)
    (Can : Round → Block V) : Prop :=
  ∀ v ∈ ρ.honest, ∀ (a : NamedAttestation V) (t : Time),
    ρ.emits S v (Object.attest a) t → S.a r₀ ≤ t → r₀ ≤ a.round →
    ∀ h : Height, ∀ T ∈ targetsAt a.erase h,
      ∃ B ∈ (ρ.storeAt S v t).T, B.root = T ∧ Block.Preceq B (Can (a.round + 1))

/-! ## P4-L — finality liveness

Stated per §5, **not** per rev. 3 §8. The
Q3 verification found rev. 3 §4.5's derivation of doc2's
`ass:clean-target-opportunity` sound in its conclusion and wrong in its argument,
and the repair moves three clauses into P4-L's hypotheses.

**What rev. 3 got wrong.** §4.5 read (d) as "no honest validator has signed a
target above `h*`" and concluded `Λ.target[h*+1] = ⊥`. (d) does not say that, and
rev. 3 §6 refutes the reading in its own base case: at round 1 of a GST = 0 run
every honest validator holds `Λ.target[1] = genesis.root`. The steady state does
the same, because the honest gates sit at `h* + 1`.

**Rev. 4 note.** The clause the paragraph above calls (c) is deleted from the
base predicate; the sentence survives because the frontier's position is
supplied here by `FrontierAligned.gates`, which is (GA), not by a common
`Σ.h_j`. Nothing in P4-L read (c) for anything else: `h_star` and `J` are
parameters of `AlignedRoundPlus`, `h_c = h_star + 1` is (L1)'s own conjunct, and
the carrier's `(h_j, J)` are premises of (L2).

**What replaces it.** Emptiness was never needed. (d) plus chain determinacy give
`Λ.target[h_c] ∈ {⊥, T_c}` for the frontier's entry block `T_c` — check doc
Lemma A — and `height_pair`'s rows 4 and 6 emit the **same** pair `.target h_c
T_c`, which `process_attestation` cannot tell apart. So an *aligned* record is as
good as an *empty* one. This derives doc2's `def:fresh-ordinary-action` clause 3
rather than assuming it, and F3's lock coupling makes doc2's separate
"no finality lock" clause redundant.

**What is left over.** Two clauses are not derivable and are carried as
hypotheses — and, per the statement reviews, two more that keep the three
below honest about **which block** they describe. The check doc's §5.1 states
(GA), (CF) and (FC) over every honest validator's *gate*, and only its §5.4 Lean
sketch reads `σ[live_confirmed]`. `round_action` gates on
`deepest_clear`, which returns a strict ancestor of `Σ.live_confirmed` whenever a
clearance test fails there, and `⊥` on the fresh-anchor branch when
`{B: root ⪯ B ⪯ C}` is empty — the §2.6 side condition, which the check doc
calls fatal for P4-L and which no other clause supplies. `FrontierAligned`'s
`gate_reachable` and `gate_clear` close both: they pin the gate to
`Σ.live_confirmed` on either branch, so the three clauses below describe the
block they name.

* **(CF)** `Λ.timeout` is a **non-emission**, so no history clause about emitted
  targets can bound it. Rows 5 and 7 of `height_pair` both write it from a
  pre-alignment gate, and `timeout` is monotone, so the write is permanent. P5
  supplies the base case: `lem:pre-confirmation-cap` caps every honest store's
  state height at `H+1` before the first recovery confirmation, so the records at
  `H+2` are genuinely empty.
* **(GA)** (b) gives only that the honest confirmations lie on **one chain**, not
  that they sit at one chain-state height. Two honest gates straddling a
  height-entry block land in different height slots, and neither collects `q`
  from honest weight alone. The natural source is an honest opening proposer:
  `a_r` is the opening slot's confirmation evaluation, and P3(a)(ii) makes every
  honest `live_confirmed` exactly the proposed block. **This is why P4-L cannot
  claim "every round"** — it is doc2's ρ-recurrence, recovered.

**(FC) and the `nj` step.** rev. 3 argued `¬nj` at `h*+1` from "Lemma S3 when
`h*` is periodic, otherwise the debt rule". The debt half needs the entry debt at
the frontier, which needs a current `h_F` — and P5 hands over a **stale** one by
construction, because it is stated over a nonfinality run. `nj` at the frontier
is also row 7, so it breaks (CF) as well: the two steps rev. 3 treats as
independent are the same condition, which is why (CF) is stated over heights
`≥ h_c` rather than `> h*`.

**The parameter finding.** `D ≥ 2` is necessary (rev. 3's Q4) and **not
sufficient**. In the honest-only pipeline the entry debt is always in `{1,2,3}`
and is `3` exactly at the second entry after a skipped height; with `D = 2` a
debt-3 entry is nonjustifiable when `K` divides it, and a skip at `h` puts that
entry at `h+2`, so the skip regenerates itself exactly when `K = 2`. At
`(K, D) = (2, 2)` the P5 hand-off enters a permanent two-cycle — justify at odd
heights, skip every even one, forever. Recommend `D ≥ 3`, or `K ≥ 3` with
`D ≥ 2`.

**ACCEPTED, and this is now the document's own domain** (PROTOCOL.md#the-complete-protocol,
baseline `d50fb59`): "Fix constants `K ≥ 3` and `D ≥ 2`; `K` is meant large and
`D` minimal. The steady pipeline enters heights at debt `h − h_F = 2`, so
`D ≥ 2`; `K ≥ 3` avoids a skip cadence that regenerates itself at `K = 2`."
That is the second of the two options recommended above, and the `(2,2)`
resonance simulation behind it is credited in the document's pending-feedback
resolution. `Protocol.HeightConfig` carries the new bounds as its fields;
the retired `K ≥ 2` and `D ≥ 1` survive there as derived theorems, since several
lemmas need only those. -/

/-- **(GA) + (CF)**: what P5's hand-off delivers, and P4-L's hypotheses minus the
debt clause (check doc §5.1).

Split out of `FrontierClean` so that the hand-off corollary can state exactly the
premise P5 supplies. The check doc's §5.4 shape is one structure with three
fields; extending preserves all three names on `FrontierClean`. -/
structure FrontierAligned (S : Setup V) (r : Round) (w : WorldView V)
    (h_c : Height) : Prop where
  /-- **(GR) The gate is reachable.** The fork-choice root is an ancestor of the
  node's own confirmation (check doc §2.6, second side condition).

  On the fresh-anchor branch `round_action` passes `height_pair` the gate
  `deepest_clear (some root) C clear`, which is `⊥` when `{B: root ⪯ B ⪯ C}` is
  empty; the gate then closes and the validator emits the **empty** pair
  (PROTOCOL.md#the-complete-protocol), refuting (L1). `Σ.F ⪯ Σ.live_confirmed` is not an
  invariant between confirmation evaluations and `get_fg_root(Σ)` may be
  `Σ.J` (`Healing/Action.lean`, F6.11), so the set really can be empty and no
  other clause of P4-L excludes it. The check doc calls the gap "fatal for
  P4-L". -/
  gate_reachable : ∀ v ∈ w.honest,
    Block.Preceq (Protocol.get_fg_root (w.state v).st.toHealing.toFG)
      (w.state v).st.live_confirmed
  /-- **(GC) The gate is the confirmation.** The node's own `live_confirmed`
  passes the clearance test `round_action` applies
  (PROTOCOL.md#the-complete-protocol).

  This is what lets the three clauses below read `σ[live_confirmed]`. The gate is
  `deepest_clear` over `chain_of C` — a chain whose deepest member is `C` itself
  — so `C` passing the filter makes the gate exactly `C`, on **both** branches:
  both filter on `g0_clear`, and the fresh-anchor branch additionally asks
  `root ⪯ B`, which `gate_reachable` supplies. Without it `deepest_clear` returns
  a strict ancestor of `C` whenever the test fails at `C`, and then `σ[gate].h`,
  `σ[gate].nj` and `σ[gate].T_h` are not the fields `gates`, `debt` and
  `frontierTarget` name — which is the substitution the check doc's §5.4 sketch
  makes silently while its §5.1 states all three over the **gate**.

  One clause rather than two since the tex fold that made activity filtered-tree
  membership: the fresh branch's `E_F(Σ)`-compatibility conjunct is gone from
  `round_action`, so the veto test is the whole of the filter on both branches.

  Under P4 it is a lemma rather than a hypothesis: by rev. 3 §4.4 no conflicting
  block holds any grade, so `g0_clear` vetoes nothing on `Can`. It is carried
  here because P4-L is stated over the predicate, not over P4's proof. -/
  gate_clear : ∀ v ∈ w.honest,
    PhaseGrades.nodeClear S (w.state v) r (w.state v).st.live_confirmed = true
  /-- **(GA) Gate agreement.** Every honest gate's chain state has the same
  height `h_c`. Agreement on the *height* is enough: along one chain each height
  has exactly one entry block and every block at that height reports it
  (PROTOCOL.md#the-complete-protocol), so the common `σ[·].T_h` follows. -/
  gates : ∀ v ∈ w.honest,
    ((w.state v).st.σ (w.state v).st.live_confirmed).h = h_c
  /-- **(CF) Clean frontier.** No honest validator has an anti-slashing timeout
  recorded at or above the frontier (PROTOCOL.md#the-complete-protocol). Contamination
  *below* the frontier is harmless — those heights are dead and no honest
  validator gates there again — which is why the clause is relative to the gate
  and not to `h*`. -/
  timeout : ∀ v ∈ w.honest, ∀ h : Height, h_c ≤ h →
    (w.state v).Λ.timeout h = false

/-- **(GA) + (CF) + (FC)**: P4-L's three clauses beside (c⁺) (check doc §5.1,
§5.4), over the gate the two clearance clauses pin. -/
structure FrontierClean (S : Setup V) (r : Round) (w : WorldView V)
    (h_c : Height) : Prop extends FrontierAligned S r w h_c where
  /-- **(FC) Finality currency.** The frontier is justifiable. Stated as `¬nj`
  rather than as the arithmetic `h_c − h_F ≤ D`, because `¬nj` is what
  `height_pair`'s row 7 reads (PROTOCOL.md#the-complete-protocol) and it avoids
  re-deriving the entry condition inside the branch analysis. The arithmetic form
  is the separate entry-debt lemma. -/
  debt : ∀ v ∈ w.honest,
    ((w.state v).st.σ (w.state v).st.live_confirmed).nj = false

/-- The frontier target `T_c`: the block that carried `v`'s gate's chain into its
current height (PROTOCOL.md#the-complete-protocol). Under (GA) it is the same block for every
honest validator, and under `FrontierAligned.gate_clear` the gate whose chain
state this reads really is `Σ.live_confirmed`. -/
def frontierTarget (w : WorldView V) (v : V) : Block V :=
  ((w.state v).st.σ (w.state v).st.live_confirmed).T_h

/-- **(L1)** Every honest round-`r` attestation carries the same nonempty target
at the frontier height, and the frontier is one above the common justification
(check doc §5.2, §5.3).

`height_pair`'s row 1 is excluded by (CF), rows 3 and 5 by Lemma A with (GA) and
the lock coupling, row 7 by (FC). Rows 2, 4 and 6 all emit `.target h_c T_c`. -/
def L1CleanTarget (S : Setup V) (ρ : Run V) (r : Round) (h_star h_c : Height)
    (T_c : Block V) : Prop :=
  h_c = h_star + 1 ∧
    (∀ v ∈ ρ.honest, frontierTarget (ρ.roundView S r) v = T_c) ∧
    (∀ v ∈ ρ.honest, ∀ (a : NamedAttestation V) (t : Time),
      ρ.emits S v (Object.attest a) t → a.round = r →
        a.height_pair = NamedHeightPair.vote h_c T_c.root false)

/-- **(L2)** A block **at the frontier** carrying a quorum of those attestations
justifies `h_c` and finalizes `h*` in the same transition, so the next round is
aligned at `h* + 1` with (c⁺) again (check doc §5.2, §5.3).
The finalization half is (c⁺)'s: by Lemma G3 the honest height-`h*` target
contributors are exactly the validators with `Λ.target[h*] = J`, and their
round-`(r−1)` emission established `Λ.timeout[h*] = false`, so `finality_pair`'s
record test passes (PROTOCOL.md#the-complete-protocol). Stated as `h* ≤ h_F` rather than
`h_F = h*` because the transition finalizes `h*` only when it was not already
finalized.
**The carrier is constrained to the frontier, and the attestations carry the
finality pair.** Both are repairs from the statement reviews, and both are
refutations of the earlier `∀ B` form rather than tightenings of it.
* `process_attestation` credits `target_participation` only when
  `a.height_pair =.target σ.h σ.T_h.root` at the **parent's** chain state
  (PROTOCOL.md#the-complete-protocol), and `Block` is a free inductive with an unconstrained
  attestation list. A block whose parent chain sits at any other height satisfies
  The previous premise, credits nothing, and leaves `h_j = 0 ≠ h_c` — so with (L1)'s
  `h_c = h* + 1`, every instance with `h* > 0` refuted the conclusion. The check
  doc's own wording is "any block that **includes the honest round-`r`
  attestations**", in a context where the block extends `Can` at the frontier;
  the four parent-state premises are that context.
* `h* ≤ h_F` needs `finalityReady`, hence a finality quorum, hence attestations
  carrying `a.finality_pair = some ⟨h*, J.root⟩` (PROTOCOL.md#the-complete-protocol). The
  height pair alone does not compose with it. `J` is threaded in from
  `AlignedRoundPlus` (corrected per rev. 4 review, finding 9: clause (c) is
  deleted and pins nothing). (c⁺) names it when `h* ≠ 0`, and the carrier
  premise `(derived_state B.parent).J.root = J.root` below pins it in either
  case — which is what the rev. 4 note above already says.
* `¬nj` at the carrier's parent is `targetReady`'s other half. It follows from
  `FrontierClean.debt` at the honest gates plus (GA) and chain determinacy, and
  is stated because the carrier is a block, not a store. -/
def L2Justifies (S : Setup V) (ρ : Run V) (r : Round) (h_star h_c : Height)
    (J T_c : Block V) : Prop :=
  (∀ (B p : NamedBlock V) (Q : Finset V),
      NamedBlock.parent? B = some p →
      (Protocol.derive_named S.E S.cfg p).h = h_c →
      (Protocol.derive_named S.E S.cfg p).T_h.root = T_c.root →
      (Protocol.derive_named S.E S.cfg p).h_j = h_star →
      (Protocol.derive_named S.E S.cfg p).J.root = J.root →
      (Protocol.derive_named S.E S.cfg p).nj = false →
      Q ⊆ ρ.honest → S.E.q ≤ S.E.electorate.weightOf Q →
      (∀ v ∈ Q, ∃ a ∈ B.attestations, a.val_index = v ∧ a.round = r ∧
        a.height_pair = NamedHeightPair.vote h_c T_c.root false ∧
        a.finality_pair = some ⟨h_star, J.root⟩) →
      (Protocol.derive_named S.E S.cfg B).h_j = h_c ∧
        (Protocol.derive_named S.E S.cfg B).J.root = T_c.root ∧
        h_star ≤ (Protocol.derive_named S.E S.cfg B).h_F) ∧
    (S.a (r + 1) ≤ ρ.horizon →
      ∃ (Can' J' : Block V),
        AlignedRoundPlus S ρ (r + 1) Can' h_c J' (ρ.roundView S (r + 1)))

/-- **(L3)** The three clauses are preserved, so (L1) and (L2) recur
(check doc §5.3).

Conditioned on round `r+1`'s opening proposer being honest, because (GA) is the
honest-opening-proposer premise — this is doc2's ρ-recurrence and the reason it
prices its opportunity in rounds rather than claiming every round.

The (FC) half is the steady-state invariant `h_F = h_j − 1`: entry debt `2`,
hence `¬nj` for every `K` once `D ≥ 2`. -/
def L3Recurs (S : Setup V) (ρ : Run V) (r : Round) (h_c : Height) : Prop :=
  S.E.proposer (S.hc.opening_slot (r + 1)) ∈ ρ.honest →
    S.a (r + 1) ≤ ρ.horizon →
    FrontierClean S (r + 1) (ρ.roundView S (r + 1)) (h_c + 1) ∧
      ∀ v ∈ ρ.honest,
        (ρ.storeBeforeTime S v (S.a (r + 1))).core.finalized_height + 1 =
          (ρ.storeBeforeTime S v (S.a (r + 1))).h_j

/-- **P4-L, finality liveness** (design note P4; check doc §5.3).

Under P4's hypotheses, plus (c⁺), (GA), (CF), (FC), `D ≥ 2`, and the
explicit height relation `h_c = h* + 1`: (L1) every honest round-`r₀`
attestation carries `.target h_c T_c`; (L2) a block including `q` of honest
weight justifies `h_c` and finalizes `h*`, so the next round is aligned with
(c⁺); (L3) the three clauses are preserved, so (L1) and (L2) recur every
round whose opening proposer is honest.

Separated from P4 because no safety conclusion uses any of it, and because both
source papers supply it only from an assumed opportunity premise. What the Q3
check buys is that the premise is now **reduced** — doc2's saved-target clause is
derived and its finality-lock clause is redundant — rather than removed. -/
def FinalityLiveness (S : Setup V) : Prop :=
  ∀ (ρ : Run V) (r₀ : Round) (Can₀ : Block V) (h_star h_c : Height) (J : Block V),
    Admissible S ρ → HonestCommittees S ρ.honest → BelowOneThird S ρ.honest →
    S.E.t_GST ≤ S.a r₀ → 2 ≤ S.cfg.D → h_c = h_star + 1 →
    AlignedRoundPlus S ρ r₀ Can₀ h_star J (ρ.roundView S r₀) →
    FrontierClean S r₀ (ρ.roundView S r₀) h_c →
    ∃ T_c : Block V,
      L1CleanTarget S ρ r₀ h_star h_c T_c ∧
        L2Justifies S ρ r₀ h_star h_c J T_c ∧ L3Recurs S ρ r₀ h_c

/-- **Corollary — the P5 hand-off** (check doc §4.3, §5.3).

P5's actual output is a **nonfinality run**, so it delivers (GA) and (CF) but not
(FC): the frontier is entered from a stale `h_F` and the entry debt is
arbitrarily large. The first successful finalization collapses the debt in one
assignment, so at most one height is skipped and the pipeline reaches (FC) within
two rounds — **unless `(K, D) = (2, 2)`**, where a skip at `h` puts the debt-3
entry at `h+2`, `K` divides it again, and the skip regenerates itself forever at
a cadence of one justification and one finalization every two rounds.

The exception is a parameter finding for the author, not a statement defect:
`(K, D) = (2, 2)` is excluded by hypothesis here, and the model's own `Fixture`
runs `K = 2`, `D = 1`. -/
def FinalityLivenessFromHealing (S : Setup V) : Prop :=
  ∀ (ρ : Run V) (r₀ : Round) (Can₀ : Block V) (h_star h_c : Height) (J : Block V),
    Admissible S ρ → HonestCommittees S ρ.honest → BelowOneThird S ρ.honest →
    S.E.t_GST ≤ S.a r₀ → 2 ≤ S.cfg.D → ¬(S.cfg.K = 2 ∧ S.cfg.D = 2) →
    h_c = h_star + 1 →
    AlignedRoundPlus S ρ r₀ Can₀ h_star J (ρ.roundView S r₀) →
    FrontierAligned S r₀ (ρ.roundView S r₀) h_c →
    (∀ r : Round, r₀ ≤ r → r ≤ r₀ + 2 →
      S.E.proposer (S.hc.opening_slot r) ∈ ρ.honest) →
    S.a (r₀ + 2) ≤ ρ.horizon →
    ∃ (r₁ : Round) (h₁ : Height), r₀ ≤ r₁ ∧ r₁ ≤ r₀ + 2 ∧
      FrontierClean S r₁ (ρ.roundView S r₁) h₁

end Internal
end DecoupledConsensusModel

end
