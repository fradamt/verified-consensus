module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Internal.GradeReads
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusInternal.Definitions.NamedCertificates
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

/-!
# The three-grade healing surface — L1–L8a and the healing theorem
(`the design` §9,;
`the design notes` §3a is the routing map from the retired material)

`Props/Healing.lean` carries P5's two headline statements, whose proofs retired
with the four-grade layer. This file carries the **new** surface: the eight
lemmas of `the design` §9 and the healing theorem assembled from them,
stated over the three-grade model.

Everything here is a statement. The proven subset lives in
`DecoupledConsensusProofs/HealingSurface/`, and the header of each definition
below says which of the three it is:

* **proved** — a theorem in `HealingSurface/` discharges it outright;
* **proved from a named premise** — a theorem discharges it given a conditional
  stated in this file, never a standing assumption;
* **Open** — stated, not proved; its comment identifies the missing premise.

**No new assumption.** The allowed set is `Admissible`, `HonestCommittees`,
`BelowOneThird`, `NonfinalityRun`, `BaselineAtRef`, the triple-proposer
`MultiProposerRecurrence`, and `IsRefRound` (`the design notes` §4).
Nothing below adds to it.
`HonestGradeDelivery` is a **conditional**, not an assumption. Its run-level
producer must derive the three fixed transports from `Admissible` when
`GradeRoundReady` holds.

## The shape of the surface

Four of the eight lemmas are store-level and cost nothing beyond the grade
algebra already in the tree:

* **L8a** is single-snapshot algebra at one `GradeView` — no run, no delivery,
  no maturity qualifier — and it is what justifies `attest`'s test-free
  fallbacks in the model rather than by citation.
* **L1** is `weightOf_filter_mono` over a Δ hop between two grade views. The hop
  is the premise; the ladder is arithmetic.
* **L3** uses the same hop as L1 but keeps the delivered sgSupporters clean
  through `Γ_r^1`, one window beyond grade 1's `Γ_r^0` cutoff. L8a turns that
  stronger support statement into clearance.
* **L5** is L1's contrapositive plus one unfold of `height_pair` at `⊥`.

A fifth, **L4**, splits: its arithmetic is proved here and its honest core —
`Internal.AlignedRound`'s deleted clause (e) — is the record layer's to return. The
rest (L2's across-store half for the grade-1 pair, L6, L7, L8) reach the run and
are stated here for the layer that will prove them.

## Statement-shape discipline carried over from the retired program

* **Two-instant hygiene** (`ExitRepair.lean`'s finding, `docs/triage` §3a): a
  cap holds *through* an interval and a witness holds *at* an instant. `L8`'s
  "one clean round after a certificate is public" has exactly that structure and
  carries the distinction in its two clause groups.
* **L6 is chain-ORDERING, not equality** (`docs/triage` §3a, the `Recovery.lean`
  row). The retired `VoteStoresAligned.merged` equality form is *refuted*
  (obligation O20); honest confirmations are comparable, their depths differ per
  validator, and liveness relays the deepest.
* **Every emission clause reads the run's past.** `Run.emits` quantifies over
  the whole event list, so a clause that neither guards with `t < …` nor pins
  with `a.round = …` reads the run's future (`Internal.AlignedRound`'s `history`
  comment). Each clause below does one or the other.
-/

/-! ## 0. Reading the grades at a run

Round `r`'s grades read the closed batch `Σ.sg_votes[r−1]` at the anchoring
instant `a_r⁻` (`Run.roundView`'s own comment): the unique instant at which the
batch this round will read is both complete and closed. Every reader below is
one of these three, and none of them re-derives the projection chain. -/



namespace DecoupledConsensusModel
namespace Internal
namespace HealingSurface

open Execution
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open PhaseGrades NamedRecoveryRead DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]



/-- `v`'s available confirmation at `a_r⁻` — the ceiling of both of `attest`'s
walks (PROTOCOL.md#the-complete-protocol). -/
def confirmedAt (S : Setup V) (ρ : Run V) (v : V) (r : Round) : Block V :=
  (ρ.storeBeforeTime S v (S.a r)).live_confirmed

/-! ## L1 — the delivery ladder (`the design` §9 L1)

> For grades whose last cutoff has passed at the reader: `G2@p ⟹ G1@v` and
> `G1@v ⟹ G0@u` when the graded block is active at the receiving store; at
> another store the block is inactive.

The active interface states the three exact transports that the final grades
consume. It does not quantify over arbitrary cutoffs.

**Why the hop needs both directions.** The step `G2 ⟹ G1` widens the head cutoff
by one Δ (`Γ_r^{−1} → Γ_r^0`) and narrows the equivocation cutoff to
`Γ_r^0`. The supporter clause travels forward — what the source resolved by
`Γ`, the target either counts by `Γ + Δ` or sees as an equivocation by then —
and the equivocation clause travels **backward**: an equivocation the target
sees by `Γ` the source sees by `Γ + Δ`. L1 needs target cleanliness through
`Γ_r^0`; L3 uses the full source sweep to keep the same sgSupporters clean through
`Γ_r^1`. -/


/-- Fixed-cutoff grade delivery between every ordered pair of honest readers,
windowed to sends at or after the round's G2 support window opens (
). The unwindowed `NamedHealthyPrefixDelivery` promises
delivery by `t + Δ` for EVERY honest emission with `t + Δ ≤ cut`, including
sends strictly before `t_GST`, which `NamedSynchrony`'s `max t t_GST + Δ`
deadline does not cover. `GradeRoundReady` only bounds `t_GST` from above (by
`early(r,.g2)`), never from below, so the window's lower bound is exactly
what makes `honestGradeDelivery_of_admissible` provable from `NamedSynchrony`:
every in-window send happens no earlier than `t_GST`, so its Synchrony
deadline collapses to `t + Δ`. -/
def HonestGradeDelivery (S : Setup V) (ρ : Run V) (r : Round) : Prop :=
  NamedHealthyWindowDelivery S ρ (early S.E S.hc r .g2) (domain S.E S.hc r .g0)


/-- Rounds of synchrony the graded mechanism needs before its first ready
round. The G2 support window of a round opens `5Δ` before
the round, `4Δ` earlier than the prior `Γ₋₁` cutoff; one round (`4ΔR ≥ 8Δ`)
covers it. A single constant so a future change of the windows is one edit. -/
def readyLag : Nat := 1

theorem readyLag_pos : 0 < readyLag := by decide


/-- GST shifted by `readyLag` rounds. Every public premise of the form
"round `r₀` is after GST" is stated on `gstLagged` in place of `t_GST`
; `GradeRoundReady` itself keeps `t_GST`. -/
def gstLagged (S : Setup V) : Time :=
  S.E.t_GST + 4 * S.E.Δ * (S.hc.R * readyLag : Nat)

/-- The finite-run and post-GST window in which round `r`'s three delivery
transports can be produced from the execution contract. -/
def GradeRoundReady (S : Setup V) (ρ : Run V) (r : Round) : Prop :=
  S.E.t_GST ≤ early S.E S.hc r .g2 ∧
    domain S.E S.hc r .g0 ≤ ρ.horizon

/-- **L1, the delivery ladder** (`the design` §9 L1).

**Proved from `HonestGradeDelivery`** —
`HealingSurface.Ladder.deliveryLadder_of`. The proof uses only the fixed G2,
G1, and sweep transports.

Note the asymmetry the second step exposes: `G1 ⟹ G0` consumes only the forward
supporter dichotomy. `G0` credits either arm. `G2 ⟹ G1` also consumes backward
equivocation delivery to rule out the second arm and to preserve the target's
cleanliness through `Γ_r^0`. -/
structure DeliveryLadder (S : Setup V) (ρ : Run V) (r : Round) : Prop where
  /-- A grade-2 block becomes grade 1 at an honest receiver or is inactive
  there. -/
  g2_g1 : ∀ p ∈ ρ.honest, ∀ v ∈ ρ.honest, ∀ B : Block V,
    storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r .g2) p).st r .g2 B = true →
      B ∉ filteredTree (readAt S ρ (domain S.E S.hc r .g1) v) ∨
        storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r .g1) v).st r .g1 B = true
  /-- A grade-1 block becomes grade 0 at an honest receiver or is inactive
  there. -/
  g1_g0 : ∀ v ∈ ρ.honest, ∀ u ∈ ρ.honest, ∀ B : Block V,
    storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r .g1) v).st r .g1 B = true →
      B ∉ filteredTree (readAt S ρ (domain S.E S.hc r .g0) u) ∨
        storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r .g0) u).st r .g0 B = true

/-! ## L2 — one chain (`the design` §9 L2)

> Direct-majority blocks lie on one chain within and across honest stores
> (`2m > W`; `e_v ≥ Γ_h + Δ` for every grade pair), so the deepest `G1` and `G2`
> are well defined and mutually comparable. -/

/-- The two ladder hops of the nested cutoffs: source phase to the next lower
reader phase. The previous arbitrary cutoff pairs with the sweep margin
`Γ_h + Δ ≤ Γ_e'` are exactly these two instances under the adopted offsets. -/
def LadderHop (q q' : Phase) : Prop :=
  (q = .g2 ∧ q' = .g1) ∨ (q = .g1 ∧ q' = .g0)

/-- **L2, one chain** (`the design` §9 L2; PROTOCOL.md#the-complete-protocol).

The **within** clause is proved outright and has been since the three-grade
re-cut: it is `HealingLemmas.Grades.direct_support_compatible`, two strict
majorities meeting in a validator that has one `C_v`. It is restricted to
*direct* support and has to be — `favorable_support`'s second set is
`B`-independent, so an equivocating majority credits every branch and two
conflicting blocks can both hold grade 0.

The **across** clause is **proved from `BatchDelivered`** —
`HealingSurface.oneChain_across`. Its conclusion has the final §7 split: the
source block is inactive at the receiving store, or it is compatible with the
receiver's direct-majority block. The explicit `Γ_h + Δ ≤ Γ_e'` premise is the
document's own sweep margin. If the delivered supporting vote is not the
receiver's first vote, it supplies equivocation evidence before the receiver's
cleanliness cutoff.

The **deepest** clause is **proved** —
`HealingSurface.fresh_anchor_isSome_of_G1`, through
`deepest?_isSome_of_compatible`. `Block.deepest?`'s degenerate tie cannot occur
on a pairwise-compatible set, so "the filtered tree holds a graded block"
implies "the selection is `some`" outright. This is the document's own
"conflicting blocks cannot both hold grade 1, so *deepest* is well defined"
(PROTOCOL.md#the-complete-protocol), and it needs no root injectivity. -/
structure OneChain (S : Setup V) (ρ : Run V) (r : Round) : Prop where
  /-- Within one store, at any two pairs of cutoffs. -/
  within : ∀ v ∈ ρ.honest, ∀ (p p' : Phase) (B B' : Block V),
    storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r p) v).st r p B = true →
    storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r p') v).st r p' B' = true →
      Block.compatible B B' = true
  /-- Across two honest stores: an active source block is compatible with the
  receiver's direct-majority block. -/
  across : ∀ p ∈ ρ.honest, ∀ v ∈ ρ.honest, ∀ (q q' : Phase) (B B' : Block V),
    LadderHop q q' →
    storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r q) p).st r q B = true →
    storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r q') v).st r q' B' = true →
      B ∉ filteredTree (readAt S ρ (domain S.E S.hc r q') v) ∨ Block.compatible B B' = true
  /-- The two selections are total where the tree is graded. -/
  deepest : ∀ v ∈ ρ.honest, ∀ B : Block V,
    B ∈ filteredTree (readAt S ρ (domain S.E S.hc r .g1) v) →
    storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r .g1) v).st r .g1 B = true →
      ∃ root : Block V, phaseResult (savedFrame S ρ (S.a r) v r) .g1 = some (some root)

/-! ## L3 — never vetoed (`the design` §9 L3)

> A `G2` block is vetoed in no honest store whose filtered tree contains it:
> the sweep runs one Δ past the veto window; boundary exact but strict. -/

/-- **L3, never vetoed** (`the design` §9 L3; PROTOCOL.md#the-complete-protocol).

**Proved from `HonestGradeDelivery`** —
`HealingSurface.Ladder.neverVetoed_of`.
The proof follows PROTOCOL.md directly. The source grade-2 sgSupporters arrive
at the far store by `Γ_r^0`. Any conflicting vote or evidence visible there by
`Γ_r^1` travels back by `Γ_r^2` and contradicts the source sweep. The resulting
far-store direct support is clean through `Γ_r^1`, so L8a closes clearance.
This stronger delivered-support statement is not the named grade-1 predicate,
which closes at `Γ_r^0`. -/
def NeverVetoed (S : Setup V) (ρ : Run V) (r : Round) : Prop :=
  ∀ p ∈ ρ.honest, ∀ B : Block V,
    storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r .g2) p).st r .g2 B = true →
      ∀ u ∈ ρ.honest,
        B ∉ filteredTree (actionDutyRead S ρ u r) ∨
          nodeClear S (actionDutyRead S ρ u r) r B = true




/-- **L4's honest core** — the retired `AlignedRoundLemmas.honest_no_double_target`,
same lemma, same name in both surfaces, and the deleted clause (e) of
`Internal.AlignedRound`.

**Proved outright** — `HealingSurface.honestNoDoubleTarget`. The record layer is
rebuilt against `record_attestation`, the single writer
(`HealingSurface/RecordCore.lean`), and the run-to-record bridge is the
induction `HealingSurface/Bridge.lean` runs: deliveries never touch `Λ`,
other validators' ticks never reach this entry, and the node's own tick is one
`create_attestation`. So `LockCompatible` is preserved and `Λ.target` only grows, and
the earlier emission's target is what every later one must name.

Stated over `targetsAt`, so it covers the height pair and the finality pair
together; that is the pair E1 convicts on, and it is what clause (d′) reads. -/
def HonestNoDoubleTarget (S : Setup V) (ρ : Run V) : Prop :=
  ∀ v ∈ ρ.honest, ∀ (a a' : NamedAttestation V) (t t' : Time),
    ρ.emits S v (Object.attest a) t → ρ.emits S v (Object.attest a') t' →
      ∀ (h : Height) (T T' : BlockId),
        T ∈ targetsAt a.erase h → T' ∈ targetsAt a'.erase h → T = T'

/-- A target at height `h` that honest weight alone could complete to a quorum:
`≥ q − b` of honest weight has signed it, written without the truncating
subtraction as `q ≤ w(Q) + w(faulty)`.

"Adversarial double-signing does not help, only honest weight counts" (§9 L4) is
what this definition says: `Q` is inside `ρ.honest` and the adversary
contributes its whole weight for free on **both** sides of L4's comparison. -/
def Completable (S : Setup V) (ρ : Run V) (h : Height) (T : BlockId) : Prop :=
  ∃ Q : Finset V, Q ⊆ ρ.honest ∧
    S.E.q ≤ S.E.electorate.weightOf Q +
      S.E.electorate.weightOf (Finset.univ \ ρ.honest) ∧
    ∀ v ∈ Q, ∃ (a : NamedAttestation V) (t : Time),
      ρ.emits S v (Object.attest a) t ∧ T ∈ targetsAt a.erase h

/-- **L4, per-height completability** (`the design` §9 L4).

**Proved outright** — `HealingSurface.perHeightCompletability`, under
`BelowOneThird` and nothing else, since the honest core is a theorem too. The
two honest backing sets are disjoint by the core, so `w(Q) + w(Q′) + b ≤ W`;
with both completable, `2q ≤ W + b`, hence `6q < 4W`, while `q = ⌈2W/3⌉` gives
`4W ≤ 6q`.

L4 carries no debt.

**It covers banked and future certificates alike**, which is the clause the
healing theorem's stock bound rests on: nothing here is scoped to a round, a
store or an instant. -/
def PerHeightCompletability (S : Setup V) (ρ : Run V) : Prop :=
  ∀ (h : Height) (T T' : BlockId),
    Completable S ρ h T → Completable S ρ h T' → T = T'

/-! ## L5 — abstention exclusivity (`the design` §9 L5)

> Post-GST, if an honest validator holds no `G1`, every remote `G2` block is
> inactive at that validator. In particular, its own filtered tree contains no
> `G2`, so its height pair is empty. -/

/-- **L5, abstention exclusivity** (`the design` §9 L5; design note §3).

**Proved from `HonestGradeDelivery`** in its grade form
(`HealingSurface.Ladder.abstentionExclusivity_of`), and the FG consequence with
it (`Ladder.height_pair_empty_of_no_G2`).

Two clauses, and the split is the point. `grades` is pure contraposition of L1's
activity-scoped first step: if a receiver holds no grade-1 block, every grade-2
block elsewhere is inactive there. `abstains` is the consequence the healing
argument actually consumes — with no active grade-2 block,
`Protocol.fg_source` is `⊥`, `attest` passes `(⊥, ⊥, ⊥)`, `height_pair`'s
first branch returns `.empty`, and the validator is FG-silent for the round
while its finality pair still flows.

**The unsafe corner is exactly the totality corner.** The raw-anchor fallback —
the third tier of `get_sg_vote`, taken only when there is no grade-2 block —
is the only one L8a does not clear. The result is local: the reader abstains when
its own filtered tree has no grade-2 block. It does not claim that an inactive
grade at another store disappears there. -/
structure AbstentionExclusivity (S : Setup V) (ρ : Run V) (r : Round) : Prop where
  /-- The grade form: without local grade 1, every remote grade-2 block is
  inactive at this reader. -/
  grades : ∀ v ∈ ρ.honest, (∀ B : Block V,
      storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r .g1) v).st r .g1 B = false) →
    ∀ p ∈ ρ.honest, ∀ B : Block V,
      storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r .g2) p).st r .g2 B = true →
        B ∉ filteredTree (readAt S ρ (domain S.E S.hc r .g1) v)
  /-- The FG form: a store with no active grade-2 block emits the **empty**
  height pair, whatever else it holds.

  Stated over the prepared action duty read of round `r` (the store and
  cache the named action actually consumes inside its own tick, after the
  clock staging), so the clause is about round `r`'s frozen grades and not
  about a re-read at `a_r⁻`. "No active grade-2 block" is the read's own
  selector returning none. -/
  abstains : ∀ v ∈ ρ.honest,
    (nodeRead S (actionDutyRead S ρ v r) r).Q2 = none →
      (Protocol.NamedActions.round_action_with
        (NamedProfile.gradeContract (actionDutyRead S ρ v r).cache) S.E S.hc
        (S.node v) (actionDutyRead S ρ v r).st.core.toHealing
        (actionDutyRead S ρ v r).record).2.height_pair = NamedHeightPair.empty


/-- **An active graded anchor reached an honest veto test before its freeze**
(PROTOCOL.md#the-complete-protocol).

`g0_clear` ranges over the reader's own filtered tree and freezes its block
filter at `Γ_r^1`, so a cross-store veto claim needs the vetoing block to be a
*candidate* of that test — in the tree, and stamped before the freeze. The grade
half of "anchor-at-me ⟹ delivered protection where active" is proved
(`GradedAnchorDelivered`); this is its reader-side half.

**The tex now states this caveat inline** (baseline `d19f47e`): §6.3 reads "a
veto wherever it also lies in that store's filtered tree — the delivered
protection", and §6.5 "every honest anchor whose filtered tree holds it is at
least as deep". So the side condition this conditional carries is the document's
own phrasing rather than a gap the model invented. This predicate does not
assert blanket membership. It says that if the anchor remains active at the
reader, its block stamp precedes the veto freeze.

**R45b — the anchor is the action read's own frame, as earlier's
`fresh_anchor (healStoreAt …)`.** The action frame is the frame used by the
prepared round action after clipping against its own finalized root. The
saved-frame result is retained as the root identity serves to select the active
prefix, but the grade result in this predicate is the action read's result.
The run layer also supplies `BatchDelivered`. -/
def AnchorVisible (S : Setup V) (ρ : Run V) (r : Round) : Prop :=
  ∀ u ∈ ρ.honest, ∀ root A : Block V,
    DecoupledConsensusModel.Protocol.phaseResult (DecoupledConsensusModel.Protocol.readFrame
      (actionDutyRead S ρ u r).cache
      (actionDutyRead S ρ u r).st.core.toHealing r) .g1 = some (some root) →
    DecoupledConsensusModel.Protocol.activePrefix (filteredTree (actionDutyRead S ρ u r)) root =
      some A →
    ∀ v ∈ ρ.honest,
      A ∈ filteredTree (actionDutyRead S ρ v r) →
        stampedBefore (actionDutyRead S ρ v r).st.core.timestamp_block
          (late S.E S.hc r .g0) A = true



/- Part B retirement candidate 1: use
DecoupledConsensusModel.Proofs.HealingSurface.NamedGradeFormsAt.
The previous command and context are frozen in n36-part-b-candidate/v1.
Consumer ports remain open; no alias or replacement proof is declared here. -/


/-- **L6, convergent feeding** (`the design` §9 L6; the 
correction recorded at `the design notes` §3a, `Recovery.lean` row).

**`ordered`, not `equal` — this is a correction, not a weakening.** The retired
`Recovery.lean` carried a compatibility-versus-equality note and its own
objection was right: the equality form (`VoteStoresAligned.merged`) is
**refuted** by obligation O20's counterexample. Depths differ per validator, and
what is true is the ordering:

* same-slot conflicting TSQ confirmations are impossible post-GST — each
  confirmer's early support lands in the other's late denominator, forcing
  `s_u > s_v` and `s_v > s_u`;
* across slots the first confirmation's support is visible to every next-slot
  voter, keeping later confirmations on its chain (the first-confirmation-
  persists analogue of doc2).

**`deepest_relayed` is the liveness clause**, and it is there because ordering
alone is not enough to feed the ladder: the honest values form a chain, but the
FG needs the *deepest* of them in every honest store. Splitting it out is what
keeps L6 from silently re-asserting the refuted equality.

`floor` is **proved** — `HealingLemmas.Grades.grade2_preceq_fg_source`, which
needs nothing: the walk is floored at `Q₂` and the empty case returns `Q₂`
itself.

`no_anchor_conflict` is **proved from `HonestGradeDelivery` and
`AnchorVisible`** —
`HealingSurface.convergentFeeding_no_anchor_conflict`. It has the final §7
split: the far anchor is inactive at the feeding store, or it is a stamped
grade-0 veto there and therefore compatible with the veto-free fed value.

`ordered` and `deepest_relayed` are **Open**. Their availability
arguments require `ordered` is the TSQ counting (same-slot denominator absorption,
cross-slot first-confirmation-persists) and `deepest_relayed` is this
statement's own declared liveness residual.

**Re-pedigree under the confirmation rewire** (baseline `579000a`,
confirm-sync). The `confirmedAt` these clauses read can now be the
**fork-choice root** — an unconfirmed slot's value — and `Σ.live_confirmed`
can retreat to it. `floor` and `no_anchor_conflict` are untouched (they read
`fg_source`, whose floor is `A_G2`, and the root sits below it —
`Availability.confRoot_preceq_grade2`). `ordered`'s TSQ discharge now runs on
the **genuine-confirmation** slots: two roots, or a root against a genuine
confirmation, are compatible because the root sits below every walk floor
(`Availability.live_confirmed_preceq_root`), so the counting burden is exactly
the same-slot genuine case (`Availability.live_confirmed_compatible`, now
anchor-independent) plus the cross-slot anchor clauses
(`Optimistic.ConeAtTicks`). `deepest_relayed` inherits the same split. -/
structure ConvergentFeeding (S : Setup V) (ρ : Run V) (r : Round) : Prop where
  /-- Every fed value is at or above its own emitter's grade-2 block. -/
  floor : ∀ v ∈ ρ.honest, ∀ Q₂ Q : Block V,
    nodeQ2 S (actionDutyRead S ρ v r) r = some Q₂ →
    nodeFGSource S (actionDutyRead S ρ v r) r = some Q →
      Block.preceq Q₂ Q = true
  /-- A graded anchor is inactive at the feeding store or compatible with its
  veto-free fed value. -/
  no_anchor_conflict : ∀ v ∈ ρ.honest, ∀ u ∈ ρ.honest, ∀ (Q root : Block V),
    nodeFGSource S (actionDutyRead S ρ v r) r = some Q →
    phaseResult (savedFrame S ρ (S.a r) u r) .g1 = some (some root) →
      nodeAnchor S (actionDutyRead S ρ u r) r ∉ filteredTree (actionDutyRead S ρ v r) ∨
        Block.compatible Q (nodeAnchor S (actionDutyRead S ρ u r) r) = true
  /-- **Chain-ordered, NOT equal.** -/
  ordered : ∀ v ∈ ρ.honest, ∀ u ∈ ρ.honest,
    Block.compatible (confirmedAt S ρ v r) (confirmedAt S ρ u r) = true
  
  deepest_relayed : ∃ C : Block V, (∃ v ∈ ρ.honest, confirmedAt S ρ v r = C) ∧
    (∀ v ∈ ρ.honest, Block.Preceq (confirmedAt S ρ v r) C) ∧
    Proofs.HealingSurface.NamedGradeFormsAt S ρ (r + 1) C

/-! ## L7 — burn accounting (`the design` §9 L7)

> A burn = a mid-round release of withheld FG material. The released certificate
> is its height's unique one (L4); the release advances `h_j`; the burn can mint
> at most one certificate at the newly opened height. Each banked certificate is
> either released — one strike, justified prefix advances — or goes permanently
> stale when the chain justifies or times out past its height. -/

/-- An attestation the run puts in play: delivered as an object, or carried by a
block the run reached.

The two-clause shape is `Execution.RunBlock`'s and is there for the same reason:
`Run.objects` reads deliveries alone, so a node's own emission is missing from
it whenever the horizon cuts off before relay. A **banked** certificate is
exactly one the adversary has not delivered, so it must be readable off carried
attestations or the definition would miss its own subject. -/
def RunAttestation (S : Setup V) (ρ : Run V) (a : NamedAttestation V) : Prop :=
  Object.attest a ∈ NamedRun.objects ρ ∨
    ∃ B : NamedBlock V, RunBlock S ρ B ∧ a ∈ Protocol.named_chain_attestations B

/-- A height-`h` certificate for target `T`: `q` of weight signed `.target h T`
in attestations the run puts in play.

Weight, not cardinality, and no honesty: a certificate the adversary banked is
still a certificate. What L4 says about it is that its *honest* contribution is
unique per height, which is the completability statement, not this one. -/
def Certificate (S : Setup V) (ρ : Run V) (h : Height) (T : BlockId) : Prop :=
  ∃ Q : Finset V, S.E.q ≤ S.E.electorate.weightOf Q ∧
    ∀ v ∈ Q, ∃ a : NamedAttestation V, RunAttestation S ρ a ∧
      a.val_index = v ∧ a.height_pair = NamedHeightPair.vote h T false



/-- The certificate's pair appeared as an honest store's installed
justification no later than `t`. -/
def ReleasedThrough (S : Setup V) (ρ : Run V) (h : Height)
    (T : BlockId) (t : Time) : Prop :=
  ∃ v ∈ ρ.honest, ∃ u : Time, u ≤ t ∧
    (ρ.storeAt S v u).h_j = h ∧ (ρ.storeAt S v u).J.root = T

/-- At `t`, every honest store has moved strictly beyond height `h`. -/
def HonestStoresCrossedAt (S : Setup V) (ρ : Run V)
    (h : Height) (t : Time) : Prop :=
  ∀ v ∈ ρ.honest, h < (ρ.storeAt S v t).h_j

/-- From `t` onward, every in-horizon honest store remains strictly beyond
height `h`. -/
def PermanentlyCrossedFrom (S : Setup V) (ρ : Run V)
    (h : Height) (t : Time) : Prop :=
  ∀ u : Time, t ≤ u → u ≤ ρ.horizon →
    ∀ v ∈ ρ.honest, h < (ρ.storeAt S v u).h_j

/-- An unreleased certificate is permanently stale from `t`: it existed in
the run, was not installed through `t`, and every honest store has permanently
crossed its height. -/
def UnreleasedCertificateStaleFrom (S : Setup V) (ρ : Run V)
    (h : Height) (T : BlockId) (t : Time) : Prop :=
  Certificate S ρ h T ∧ ¬ ReleasedThrough S ρ h T t ∧
    PermanentlyCrossedFrom S ρ h t

structure BurnAccounting (S : Setup V) (ρ : Run V) : Prop where
  /-- The released certificate is its height's unique one (L4). -/
  unique : ∀ (h : Height) (T T' : BlockId),
    Certificate S ρ h T → Certificate S ρ h T' → T = T'
  /-- The release advances the justified prefix: a carrier at the certificate's
  height justifies it. -/
  advances : ∀ (B p : NamedBlock V) (h : Height) (T : BlockId) (Q : Finset V),
    NamedBlock.parent? B = some p →
    (Protocol.derive_named S.E S.cfg p).h = h →
    (Protocol.derive_named S.E S.cfg p).T_h.root = T →
    (Protocol.derive_named S.E S.cfg p).nj = false →
    S.E.q ≤ S.E.electorate.weightOf Q →
    (∀ v ∈ Q, ∃ a ∈ B.attestations, a.val_index = v ∧
      a.height_pair = NamedHeightPair.vote h T false) →
      (Protocol.derive_named S.E S.cfg B).h_j = h ∧
        (Protocol.derive_named S.E S.cfg B).J.root = T
  /-- A burn mints at most one certificate at the newly opened height. This is
  the same run-global proposition as `unique`. -/
  no_remint : ∀ (h : Height) (T T' : BlockId),
    Certificate S ρ h T → Certificate S ρ h T' → T = T'
  /-- Once every honest store crosses a certificate height, the certificate
  was already released or it is permanently stale. Producing that crossing is
  the separate clean-round progress obligation. -/
  release_or_stale : ∀ (h : Height) (T : BlockId), Certificate S ρ h T →
    ∀ t : Time, t ≤ ρ.horizon → HonestStoresCrossedAt S ρ h t →
      ReleasedThrough S ρ h T t ∨ UnreleasedCertificateStaleFrom S ρ h T t

/-! ## L8 — the finality march (`the design` §9 L8)

> One clean round after a certificate is public, all honest finality pairs agree
> and `W − b ≥ q` finalizes it; accountable safety then closes every height at
> or below. Caveat: a finality pair locks its target at `h_j`, but Rule B does
> not require that the target row was already present. -/


/-- **L8, the finality march** (`the design` §9 L8;
`the design notes` §3a routes `Exit.lean`'s pre-confirmation cap and
`exit_is_agreement` here).

**Two-instant hygiene, applied from the start** — the `ExitRepair.lean` finding,
which §3a records as a shape constraint rather than a lemma. "One clean round
after a certificate is public" has two instants in it, and the two clause groups
below keep them apart:

* `public_through` is a **cap through an interval**: every honest store holds
  the justification at every instant of `[a_r, a_{r+1}]`. A premise stated at one
  instant would not survive the round it is supposed to span.
* `agree_at` and `quorum` are **witnesses at an instant**: what the honest
  validators emit at `a_{r+1}`, and how much weight that is.

**`target_gate` records Rule B's exact write.** A nonempty finality pair writes
its target to `Λ.lock[h_j]`. The target entry can remain empty. Thus a finality
vote does not prove that the validator first emitted a target row at that
height.

The emission-level lock fact is **proved**
(`HealingSurface.emits_finality_locked`). The other three clauses are
**Open**, and `HealingSurface/March.lean` takes each as far as run level
allows and names what is left:

* `public_through` is **premise-shaped**. "A certificate is public for the whole
  clean round" is the hypothesis of L8's sentence, not a consequence of it;
  producing it is post-GST relay of the certificate plus monotonicity of `Σ.h_j`
  across the interval. The two-instant condition
  above is what keeps this visible — a cap through an interval is not produced by
  a witness at an instant.
* `agree_at` reduces to `March.agree_at_of_head` plus **two** named things, both
  real. First, `Λ.timeout h = false`, which does *not* follow from
  `target h = some J`: `height_pair`'s target-repeat row emits `.timeout h`
  whenever the store's height source names a target other than the recorded one
  (PROTOCOL.md#the-complete-protocol), and that validator can never finality-vote at `h`
  again. That is O-c's designed time-out seen from the finality side, and the
  sharp form of §9's "the march may rely on finalizing a later height instead".
  Second, `round_action` reads `(Σ.σ[H]).h_j`, `(Σ.σ[H]).J` and `(Σ.σ[H]).h_F`
  at the fork-choice **head**, while `public_through` speaks about the store
  fields `Σ.h_j` and `Σ.J`; the two readers are deliberately different
  (PROTOCOL.md#the-complete-protocol) and no lemma relates them. Carried as
  `March.NoMarchTimeout` and `March.HeadJustifies`.
* `quorum` **asks for more weight than the certificate supplies**. The
  certificate proves that its honest height-target voters have weight at least
  `q − b`. Rule B permits additional finality voters with an empty target row,
  so an exact characterization of the finality-voting set is not
  valid. The residual is still the missing honest target-row weight up to `q`,
  plus transport from an emission index to the instant `a_{r+1}`. -/
structure FinalityMarch (S : Setup V) (ρ : Run V) (r : Round) (h : Height)
    (J : BlockId) : Prop where
  /-- **Cap through the interval.** The certificate is public for the whole
  clean round. -/
  public_through : ∀ t : Time, S.a r ≤ t → t ≤ S.a (r + 1) →
    ∀ v ∈ ρ.honest, h ≤ (ρ.storeAt S v t).h_j ∧ (ρ.storeAt S v t).J.root = J
  /-- **Witness at the instant.** Every honest validator whose record admits the
  justification emits the finality pair at `a_{r+1}`. -/
  agree_at : ∀ v ∈ ρ.honest, (ρ.recordAt S v (S.a (r + 1))).target h = some J →
    ∀ (a : NamedAttestation V) (t : Time),
      ρ.emits S v (Object.attest a) t → a.round = r + 1 →
        a.finality_pair = some ⟨h, J⟩
  /-- **Rule B's exact write.** A nonempty finality pair records its target in
  the lock. The target entry can remain empty. -/
  target_gate : ∀ v ∈ ρ.honest, ∀ (a : NamedAttestation V) (t : Time),
    ρ.emits S v (Object.attest a) t → a.finality_pair = some ⟨h, J⟩ →
      (ρ.recordAt S v t).lock h = some J
  /-- **Witness at the instant.** The finality voters carry a quorum. -/
  quorum : ∃ Q : Finset V, Q ⊆ ρ.honest ∧ S.E.q ≤ S.E.electorate.weightOf Q ∧
    ∀ v ∈ Q, (ρ.recordAt S v (S.a (r + 1))).target h = some J




/-- **L8a, single-store self-clearance** (`the design` §9 L8a;
`the design notes` §6).

**Proved outright** — `HealingSurface.SelfClearance.g0_clear_of_direct_support`.
Pure single-snapshot algebra: one `GradeView`, one instant, two weights. No run,
no delivery, no maturity qualifier, no fault bound — `2m > W` is the whole
counting argument, and the marks `t_v` and `e_v` are immutable, so the
inequality is between fixed sums and cannot be provisional.

This closes the single-store clearance claim for support whose equivocation
window reaches the veto cutoff. In particular, `Q₂` has
`Γ_e = Γ_r^2 ≥ Γ_r^1`, so the untested grade-2 fallback in both selectors is
self-clear. Grade 1 closes at `Γ_r^0`; a fresh anchor is therefore not a
corollary of L8a. It belongs to the raw SG fallback used when `Q₂` is absent,
where the protocol keeps voting total but emits no height pair. The maturity
paragraph remains necessary for the cross-store claims L1, L2, and L3. -/
def SelfClearance (S : Setup V) : Prop :=
  ∀ (gv : GradeView V) (F : Block V) (r : Round) (B root : Block V),
    phaseGrade S.E S.hc gv F r .g2 B = true →
    phaseRoot S.E S.hc gv F r .g0 = some root →
      Block.compatible B root = true


/-- **L8a's companion fact**: an unsafe untriggered vote cannot corrupt later
grading, because the support functions are aggregate-weight sums robust to any
single vote (`the design` §9 L8a; `the design notes` §6).

**Proved outright** — `HealingSurface.SelfClearance.direct_support_le_add_weight`
and its favorable twin. Stated as the quantitative form rather than as prose:
two grade views whose summaries agree off one validator have supports within
that validator's weight of each other, so no single vote flips a grade whose
margin exceeds `w(v)`.

This is the fact that retires the last version of the original O14 worry. The
worry was that a `g0_clear` read could be provisional; L8a says it cannot be for
a block with a direct grade, and this says the *inputs* to a later round's
grading are not corruptible one vote at a time either. -/
def SingleVoteRobust (S : Setup V) : Prop :=
  ∀ (gv gv' : GradeView V) (F : Block V) (r : Round) (p : Phase) (B : Block V) (v : V),
    gv.T = gv'.T → gv.timestamp_block = gv'.timestamp_block →
    (∀ u : V, u ≠ v → ∀ c : Time,
      DecoupledConsensusModel.Protocol.rawInputs gv S.hc.η_SG r c u =
        DecoupledConsensusModel.Protocol.rawInputs gv' S.hc.η_SG r c u) →
      S.E.electorate.weightOf (phaseSupporters S.E S.hc gv F r p B) ≤
        S.E.electorate.weightOf (phaseSupporters S.E S.hc gv' F r p B) +
          S.E.electorate.weightOf {v}




/-- **The graded anchor carries a delivered veto wherever active**
(`the design` §9, the `fresh_anchor` invariant;
PROTOCOL.md#the-complete-protocol).

This is the safety property that replaced strictness as `fresh_anchor`'s
rationale, and it is why the anchor ordering is a *safety-source* ordering
rather than a depth ordering. **Proved from `HonestGradeDelivery`** —
`HealingSurface.Ladder.gradedAnchorDelivered_of` — since a fresh anchor holds
`G1` at its own store and L1's second step carries `G1` to `G0` at every
receiver where the anchor remains active.

The invariant's *converse* is what makes the relative anchor the fallback and
not the peer: `majority_fork_choice` carries represented weight and no
assurance at all, which is the retracted-rationale correction of. -/
def GradedAnchorDelivered (S : Setup V) (ρ : Run V) (r : Round) : Prop :=
  ∀ v ∈ ρ.honest, ∀ root : Block V,
    phaseResult (savedFrame S ρ (S.a r) v r) .g1 = some (some root) →
      ∀ u ∈ ρ.honest,
        nodeAnchor S (actionDutyRead S ρ v r) r ∉
            filteredTree (readAt S ρ (domain S.E S.hc r .g0) u) ∨
          storeGrade S.E S.hc (readAt S ρ (domain S.E S.hc r .g0) u).st r .g0
            (nodeAnchor S (actionDutyRead S ρ v r) r) = true


/-- **The `W_r` pigeonhole gap, as a negative statement**
(`Optimistic/Anchor.lean` §5; `the design notes` §6a).

`e_v ≥ Γ_e` keeps a supporter clean at the *grade's* cutoffs; it does **not**
keep that validator's vote unique in its round bucket by `a_r`, and `sg_support`
reads `sole_vote?` over the whole bucket at receipt. So a validator can hold a
grade-2 grade and still supply no `sg_support`, and the relative walk can miss a
grade-2-supported block outright.

**Proved** — `HealingSurface.Dispersion.supportMissesGrade`. The `Fin 2` fixture
of `Model/Fixture.lean` is too small to carry it; the witness is the dispersion
electorate's own, `W = 100` across three cohorts of weight `34/33/33`. Cohort
`0` casts its second vote at `Γ_r^2` exactly: `e_v ≥ Γ_r^2` still holds —
boundary exact — so the cohort keeps its place in `direct_support` and `Xa`
carries grade 2 on `34 + 33 = 67`, while `sole_vote?` reads the whole round
bucket at receipt, finds two votes, and leaves `sg_support` with `33`.

The note at `Anchor.lean` §5 predicted a ten-validator counterexample; three
cohorts carry it, because every rule involved counts **weight** and none counts
heads.

Why it is worth stating at all: it is the reason the graded and relative anchors
are **alternatives** rather than one refining the other, which is exactly what
the delta's rationale says from the other side. Anyone who tries to
prove `Q₂ ⪯ A` through the relative walk will re-derive this counterexample; the
statement is the sign that says so. -/
def SupportMissesGrade (S : Setup V) : Prop :=
  ∃ (st : Protocol.HealingStore V) (r : Round) (B : Block V),
    phaseGrade S.E S.hc st.gradeView st.F r .g2 B = true ∧
      Protocol.sg_support S.E st.sg_votes S.hc.η_SG st.T r B <
        S.E.electorate.weightOf (phaseSupporters S.E S.hc st.gradeView st.F r .g2 B)


/-- **`confirmed ⪯ Q`** — the SG vote is an ancestor of the pair source, not
merely compatible with it (`the design` §9 O-a, bonus invariant;
PROTOCOL.md#the-complete-protocol).

**Proved outright** — `HealingSurface.sg_vote_preceq_source`.
`HealingLemmas/Grades.lean` §7 reduced the invariant to three residuals and all
three have available: the `Q₂` tier, `Q₂ ⪯ A` (the delta's
`grade2_preceq_fresh_anchor`), and F6.6 — "`Block.deepest?` over a chain is
`some` when the range is nonempty" — now `deepest?_isSome_of_chain`.

The `fresh_anchor = ⊥` fallback, which was the last side condition, **discharges
itself**: `deepest?_isSome_of_compatible` makes "deepest" total on any nonempty
pairwise-compatible set, and a `Q₂` with grade 2 is a grade-1 block of the same
filtered tree, so the anchor's range is never empty while a height pair exists.
The tree tie-break needs no root injectivity — comparability alone forces it.

Do not route this through the `W_r` pigeonhole; see `SupportMissesGrade`.

: stated at a runtime read of an honest node in the
round's closed window (as `Q17_graded_lifts_source`), because the selector
algebra needs the frame's G2 block below the frame's G1 anchor (row Q10), a
fact of the runtime, false for an arbitrary node state. -/
def VoteBelowSource (S : Setup V) : Prop :=
  ∀ (rho : NamedRun V), NamedAdmissibleCore S rho →
    ∀ (t : Time) (v : V) (r : Round) (Q : Block V), v ∈ rho.honest → 0 < r →
      domain S.E S.hc r .g0 ≤ t → t < opening S.E S.hc (r + 1) → t ≤ rho.horizon →
      let n := NamedRun.readAt S rho t v
      nodeFGSource S n r = some Q → Block.preceq (nodeSGVote S n r) Q = true




/-- **The divergence is E1-safe, within one attestation and across rounds**
(`the design` §9 O-e; `Healing/Action.lean`'s `round_action` note).

**The record layer is proved outright** —
`HealingSurface.Divergence.create_attestation_no_self_E1` and
`Divergence.height_pair_agrees_lock`. Both are branch analysis over
`Protocol.height_pair` and neither needs a run:

* within one attestation, `own_lock`'s same-height override makes `height_pair`
  read *this* attestation's own finality pair, so the two pairs cannot name
  different targets at one height;
* across rounds, `record_attestation` persists `Λ.lock[h_f] ← T_f`, and a later
  `height_pair` at that height emits `.target` only at the locked value and
  otherwise returns the **empty** pair — the "wasted vote, not evidence"
  outcome.

**The run-level lift below is Open**, and its debt is one bridge, not a
protocol fact: every honest emission comes out of `create_attestation`
(`on_tick_emit` → `Protocol.attest_with` → `round_action_with`), which is the same
emission analysis `Optimistic/Emission.lean` performs for the SG fibre.

This is the flagged strong result, and it is the machine-checked version of the
two independent traces that refuted the E1 alarm. It is also a
"do-not-repair" marker: the divergence is by design, the head feeds the finality
pair and the height source feeds the height pair, and nothing forces one chain. -/
def DivergenceE1Safe (S : Setup V) (ρ : Run V) : Prop :=
  ∀ v ∈ ρ.honest, ∀ (a : NamedAttestation V) (t : Time),
    ρ.emits S v (Object.attest a) t →
      ∀ (h : Height) (T T' : BlockId),
        a.height_pair = NamedHeightPair.vote h T false →
        a.finality_pair = some ⟨h, T'⟩ →
          T = T'

/-! ## The healing theorem (`the design` §9, Theorem)

> After GST + full participation: (1) rounds before the first fresh quorum are
> FG-silent and heal SG (`b < W/2` relative machinery); (2) from the first fresh
> quorum on, honest feeding is convergent except in burn rounds (L6); (3) the
> stock of conflicting certificates is bounded by the unjustified backlog at GST
> plus one per burnt height, and every resolution advances `h_j` or is stale
> (L4, L7); (4) hence finitely many strikes, the justified prefix ratchets,
> finality marches (L8), and "confirmation ⟹ safety" holds for every
> confirmation formed outside strike rounds once the local stock is spent. -/

/-- **The healing theorem** (`the design` §9).

**Open — stated, not proved.** It is the
assembly of everything above rather than an independent obligation. Each clause
names the lemmas it consumes, so the theorem's debt is exactly the union of its
lemmas' debts and nothing more.

Read against the retired `Composition.lean`, which §3a routes to clauses (3) and
(4): the `(K+1)(gap+1)+2` round bound is replaced by L7's burn accounting —
"each banked certificate is released (one strike, `h_j` advances) or goes
stale" — so the counting survives in a different currency, and the bound below
is existential in the strike count rather than arithmetic in `K` and `gap`.

**The hypotheses are the allowed set, unchanged.** `Admissible`,
`HonestCommittees`, `BelowOneThird`, plus the schedule reach `S.a r₀ ≤
ρ.horizon`. Full participation is not an assumption of this statement: it is
`the design` §9's own scoping of the *claim* (obligation O-d records the
partial-participation regime as out of scope), and it enters through the lemmas
that need it.

Clause (1) is stated as FG silence plus the §5 reduction, which is where "heal
SG with `b < W/2` relative machinery" lives: with no grades, `fresh_anchor` is
`⊥`, `get_sg_root` is `majority_fork_choice`, and §6 reduces exactly to §§2–5. -/
structure HealingTheorem (S : Setup V) (ρ : Run V) (r₀ : Round) : Prop where
  /-- **(1)** Rounds before the first fresh quorum are FG-silent. -/
  fg_silent_before : ∀ r : Round, r₀ ≤ r → S.a r ≤ ρ.horizon →
    (∀ v ∈ ρ.honest, nodeQ2 S (actionDutyRead S ρ v r) r = none) →
      AbstentionExclusivity S ρ r
  /-- **(2)** From the first fresh quorum on, honest feeding is convergent
  except in burn rounds. -/
  convergent_from : ∀ r : Round, r₀ ≤ r → S.a r ≤ ρ.horizon →
    (∃ v ∈ ρ.honest, (nodeQ2 S (actionDutyRead S ρ v r) r).isSome = true) →
      ConvergentFeeding S ρ r ∨ ∃ (h : Height) (T : BlockId), Certificate S ρ h T
  /-- **(3)** The stock of conflicting certificates is bounded, and every
  resolution advances the justified prefix or is stale (L4, L7). -/
  stock_bounded : PerHeightCompletability S ρ ∧ BurnAccounting S ρ
  /-- **(4)** Finitely many strikes: past a round, every honest confirmation is
  safe, and the finality march runs. -/
  strikes_finite : ∃ r₁ : Round, r₀ ≤ r₁ ∧
    (∀ r : Round, r₁ ≤ r → S.a r ≤ ρ.horizon → ConvergentFeeding S ρ r) ∧
      ∀ r : Round, r₁ ≤ r → S.a (r + 1) ≤ ρ.horizon →
        ∀ (h : Height) (J : BlockId), Certificate S ρ h J →
          FinalityMarch S ρ r h J

end HealingSurface
end Internal
end DecoupledConsensusModel

end
