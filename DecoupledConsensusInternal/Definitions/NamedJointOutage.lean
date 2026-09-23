module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedStableChainOutage
public import DecoupledConsensusInternal.Definitions.OutageEntryRevision
public import DecoupledConsensusInternal.Definitions.NamedOutageEntry

@[expose] public section

/-!
# Shared named P1/P2 round checkpoint — review draft

One internal invariant for both proof steps. It uses the strict pre-action
confirmation stage at round r. The step to r+1 must derive both sides from
The previous checkpoint and the intervening actual events. Neither side may
assume the other at r+1. Event, phase and user-read interpolation is a separate
remaining proof obligation; this structure alone does not prove it.

The full named protected prefix is the actual run-scoped representative
produced from the outer stable geometry, not an added outer premise. Under
1311- its own derive_named height replaces every reader frontier in
the active high-entry history and conflicting-carrier bound. No arbitrary
view or included-reader callback occurs. All honest readers are included.
-/


namespace DecoupledConsensusModel.Internal.NamedJointOutage
open Execution NamedOutageEntry NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

def RoundIncluded (S : Setup V) (rho : NamedRun V) (b0 : Time) (r : Round) : Prop :=
  0 < r ∧ b0 ≤ S.a r ∧ S.a r ≤ rho.horizon


/-- Addendum 34 12: the inclusion condition of the round
invariant. Only the HORIZON bound moves to the round's opening, written
`domain S.E S.hc r.g1` since the G1 domain offset is `0`. The invariant's SG
field reads at that opening, so the round is usable as soon as the opening is
inside the horizon; the action time, `6Δ` later, may be past it.

The lower bound stays at the action. A round whose opening precedes `b0` but
whose action follows it is INCLUDED: its SG field is then stated at a pre-outage
read, where the prefix is healthy, and its certificate is inventoried at
`min b0 (early S.E S.hc r.g2)`, which is what 9 exists
for. Keeping the lower bound at the action is also what makes
`first_checkpoint_history_cases` produce the base round unchanged. -/
def DomainIncluded (S : Setup V) (rho : NamedRun V) (b0 : Time) (r : Round) : Prop :=
  0 < r ∧ b0 ≤ S.a r ∧ domain S.E S.hc r .g1 ≤ rho.horizon

/-- Exact same checkpoint for the SG and FG fields. -/
def checkpoint (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) : NamedNodeState V :=
  roundConfirmationRead S rho v r


/-- Addendum 34 14: the exemption uses the finalized
block, which is monotone along the run; the FG root is not.

`Protocol.get_fg_root st` is `st.J` when the cascade gate `h_max = h_j + 1`
holds and `st.F` otherwise, so a block that raises `h_max` past the gate drops
the root to a strictly shallower block. Only `st.F` grows. Testing the exemption
on `st.F` therefore transports forward to every later read, and it still gives
the FG-root form where that is wanted, because `F ⪯ J` makes `F ⪯ get_fg_root`
hold in both branches.

Addendum 34 12 fixes the read: the round's opening,
`domain S.E S.hc r.g1`, rather than the pre-action checkpoint, and not the G2
domain either. The G2 domain is `opening r - Δ`, which lies in slot `rR - 1` and
therefore has clock round `r - 1`; `activeG2` addresses the frame of the read's
own clock round, so at the G2 domain the SG field below would pair the round-`r`
raw frame with the round-`(r-1)` active prefix. The round-`r` G2 result is
already frozen at `opening r - Δ`, so the opening read loses nothing. -/
def NeedsSG (S : Setup V) (rho : NamedRun V) (P : NamedBlock V) (r : Round) (v : V) : Prop :=
  ¬ Block.Preceq P.erase (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F

local instance (S : Setup V) (rho : NamedRun V) (P : NamedBlock V) (r : Round) (v : V) :
    Decidable (NeedsSG S rho P r v) :=
  inferInstanceAs (Decidable (¬ Block.Preceq P.erase
    (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F))

/-- Common honest support at a renewable support boundary. supportRound
is the retained support frame at supportBoundary; r is the current phase.
At every SG-needed reader the latest ready boundary set is nonempty, every
maximal ready tie covers P and is eligible for r, no old stale risk is present,
and the sender is positive at the actual current G2 phase read. There is no
permanent initial-frame-positive or initial-cohort membership requirement. -/
def commonSupporters (S : Setup V) (rho : NamedRun V) (supportBoundary : Time)
    (P : NamedBlock V) (supportRound r : Round) : Finset V :=
  rho.honest.filter (fun u => ∀ v ∈ rho.honest, NeedsSG S rho P r v →
    let entry := (NamedRun.stateBeforeTime S rho supportBoundary v).st.core
    let current := (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core
    let latest := OutageEntryRevision.latest
      (OutageEntryRevision.retainedReady S entry supportRound supportBoundary u)
    latest.Nonempty ∧
    (∀ a ∈ latest, OutageEntryRevision.covers entry P.erase a = true ∧
      a.round ∈ Protocol.latest_window S.hc.η_SG r) ∧
    OutageEntryRevision.staleAt S entry supportRound supportBoundary P.erase u = false ∧
    DecoupledConsensusModel.Protocol.positive current.toHealing.gradeView current.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2) u P.erase = true)

/-- Complete conservative stale inventory at the strict support boundary, using
the actual support-frame retainedRaw/latest/covers test. This includes every
unknown, empty or non-covering maximal raw head and conflicting maximal-round
ties at any SG-needed honest reader. It is not just the current opponent set. -/
def commonStaleRisks (S : Setup V) (rho : NamedRun V) (supportBoundary : Time)
    (P : NamedBlock V) (supportRound r : Round) : Finset V :=
  rho.honest.filter (fun u => ∃ v ∈ rho.honest, NeedsSG S rho P r v ∧
    OutageEntryRevision.staleAt S (NamedRun.stateBeforeTime S rho supportBoundary v).st.core
      supportRound supportBoundary P.erase u = true)

/-- Concrete JointAt at the same named checkpoint, with no proof-module import. -/
def JointAt (S : Setup V) (rho : NamedRun V) (P : NamedBlock V) (r : Round) (v : V) : Prop :=
  let st := (checkpoint S rho v r).st.core
  (Block.Preceq P.erase (Protocol.get_fg_root st.toHealing.toFG) ∨
    P.erase ∈ Protocol.get_filtered_block_tree st.toHealing.toFG) ∧
  Block.compatible P.erase st.F = true

/-- Historical 1286 predicate, retained only for declaration compatibility.
The revised RoundInvariant does not use this source/P compatibility target.
An original full row from a strictly earlier actual action. Its source is
the full body held at that computed action store, not merely a signed entry.
Full source/P compatibility is the history conclusion to be derived using
the earlier round's joint invariant. -/
def EarlierSource (S : Setup V) (rho : NamedRun V) (P : NamedBlock V)
    (r : Round) (a : NamedAttestation V) : Prop :=
  a.round < r ∧
  ∃ i : Nat, rho.events[i]? = some (.tick a.val_index (S.a a.round)) ∧
    let before := NamedRun.stateBefore S rho i a.val_index
    let n := actionReadFrom S before a.round
    let gc := NamedProfile.gradeContract n.cache
    NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index (S.a a.round) ∧
    (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node a.val_index)
      n.st n.record).2.2 = a ∧
    ∃ source ∈ n.st.bodies,
      Protocol.fg_source_with gc S.E S.hc n.st.core.toHealing a.round
        (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing a.round) =
          some source.erase ∧
      (∃ timeout : Bool, a.height_pair = .vote
        (Protocol.derive_named S.E S.cfg source).h
        (Protocol.derive_named S.E S.cfg source).T_h.root timeout) ∧
      NamedBlock.compatible P source = true

/-- Historical 1286 predicate, retained only for declaration compatibility.
The revised RoundInvariant uses PriorCarrierRows and IntrinsicHighEntryHistory instead.
All original rows at all ancestors of a held full carrier. Each carrier
has only its own upper round bound. There is no eta_SG expiry for FG rows.
The low-height branch uses P's state height, not P's justified height. -/
def OldRowSourceHistory (S : Setup V) (rho : NamedRun V) (P : NamedBlock V)
    (r : Round) (v : V) : Prop :=
  ∀ B ∈ (checkpoint S rho v r).st.bodies, ∀ A : NamedBlock V, NamedBlock.Preceq A B →
    Protocol.carried_attestations_admissible S.hc A.erase = true ∧
    ∀ a ∈ A.attestations,
      a.round ≤ S.hc.round_of A.slot ∧
      (a.val_index ∈ rho.honest →
        (∀ h entry timeout, a.height_pair = .vote h entry timeout →
          h ≤ (Protocol.derive_named S.E S.cfg P).h) ∨
        EarlierSource S rho P r a)

/-- Exact full signed source and full named entry at one actual action.
The source need not be compatible with a later protected prefix. -/
def SignedSourceAt (S : Setup V) (rho : NamedRun V) (i : Nat)
    (a : NamedAttestation V) (source entry : NamedBlock V) : Prop :=
  rho.events[i]? = some (.tick a.val_index (S.a a.round)) ∧
  let before := NamedRun.stateBefore S rho i a.val_index
  let n := actionReadFrom S before a.round
  let gc := NamedProfile.gradeContract n.cache
  NamedObject.attest a ∈ NamedRun.emittedAt S rho i a.val_index (S.a a.round) ∧
  (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node a.val_index)
    n.st n.record).2.2 = a ∧
  source ∈ n.st.bodies ∧
  Protocol.fg_source_with gc S.E S.hc n.st.core.toHealing a.round
    (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing a.round) = some source.erase ∧
  NamedBlock.Preceq entry source ∧
  entry.erase = (Protocol.derive_named S.E S.cfg source).T_h ∧
  (Protocol.derive_named S.E S.cfg entry).h =
    (Protocol.derive_named S.E S.cfg source).h ∧
  ∃ timeout : Bool, a.height_pair = .vote
    (Protocol.derive_named S.E S.cfg source).h entry.root timeout

/-- Global actual prior-emission history. It includes original honest rows
not yet received by any reader, but no arbitrary future honest emission. -/
def SignedSourceHistory (S : Setup V) (rho : NamedRun V) (r : Round) : Prop :=
  ∀ a : NamedAttestation V, a.val_index ∈ rho.honest → a.round < r →
    NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) →
    ∀ h root timeout, a.height_pair = .vote h root timeout →
      ∃ i : Nat, ∃ source entry : NamedBlock V, SignedSourceAt S rho i a source entry ∧
        (Protocol.derive_named S.E S.cfg source).h = h ∧ entry.root = root

/-- Entry named by an original honest row at an actual earlier action.
Its height is the named source's state height, not a justified height. -/
def HonestEntryBefore (S : Setup V) (rho : NamedRun V) (r : Round)
    (h : Height) (entry : NamedBlock V) : Prop :=
  ∃ i : Nat, ∃ a : NamedAttestation V, ∃ source : NamedBlock V,
    a.val_index ∈ rho.honest ∧ a.round < r ∧ SignedSourceAt S rho i a source entry ∧
    (Protocol.derive_named S.E S.cfg source).h = h

/-- Every original row on every ancestral carrier has its carrier's actual
upper round bound. Honest rows have prior actual emissions. There is no SG
expiry bound for FG rows, and no source/P compatibility clause. -/
def PriorCarrierRows (S : Setup V) (rho : NamedRun V) (r : Round) (B : NamedBlock V) : Prop :=
  ∀ A : NamedBlock V, NamedBlock.Preceq A B →
    Protocol.carried_attestations_admissible S.hc A.erase = true ∧
    ∀ a ∈ A.attestations, a.round ≤ S.hc.round_of A.slot ∧
      (a.val_index ∈ rho.honest → a.round < r ∧
        NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))

/-- Historical 1297 local-frontier history, retained with its exact old body.
The active invariant uses IntrinsicHighEntryHistory instead. -/
def HighEntryHistory (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (P : NamedBlock V) (r : Round) (reader : V) : Prop :=
  ∀ h entry, HonestEntryBefore S rho r h entry →
    boundaryFrontier S rho b0 reader < h → NamedBlock.Preceq P entry

/-- Historical 1297 local-frontier band, retained with its exact old body.
The active invariant uses IntrinsicConflictingCarrierBand instead. -/
def ConflictingCarrierBand (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (P : NamedBlock V) (r : Round) (reader : V) : Prop :=
  ∀ B : NamedBlock V, NamedRun.blockInRun S rho B → PriorCarrierRows S rho r B →
    NamedBlock.compatible P B = false →
      (Protocol.derive_named S.E S.cfg B).h ≤ boundaryFrontier S rho b0 reader + 1

/-- Historical 1297 frontier witnesses, retained with their exact old body.
The 1311 invariant has no frontier_witnesses field or boundary-frontier premise. -/
def FrontierWitnesses (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (P : NamedBlock V) (r : Round) (reader : V) : Prop :=
  (∃ W : NamedBlock V, W ∈ (NamedRun.stateBeforeTime S rho b0 reader).st.bodies ∧
    NamedBlock.Preceq P W ∧
    (Protocol.derive_named S.E S.cfg W).h = boundaryFrontier S rho b0 reader) ∧
  (∃ W : NamedBlock V, W ∈ (checkpoint S rho reader r).st.bodies ∧
    NamedBlock.Preceq P W ∧
    boundaryFrontier S rho b0 reader ≤ (Protocol.derive_named S.E S.cfg W).h)


/-- 1311, revised by 1368/1369: global prior honest
entries at any height must be compatible with P. Pre-b0 entries use
NoHonestConflictAbove; later entries must follow from earlier SG history.
The historical public name is retained; there is no height threshold.
This is an internal invariant target, not an extra outer history premise. -/
def IntrinsicHighEntryHistory (S : Setup V) (rho : NamedRun V)
    (P : NamedBlock V) (r : Round) : Prop :=
  ∀ h entry, HonestEntryBefore S rho r h entry →
    NamedBlock.compatible P entry = true

/-- Full run-scoped conflicting carriers with actual prior honest rows have
height at most h(P)+1. The bound includes later-revealed private carriers.
It does not bound the height of P-descendants or any reader's global h_max. -/
def IntrinsicConflictingCarrierBand (S : Setup V) (rho : NamedRun V)
    (P : NamedBlock V) (r : Round) : Prop :=
  ∀ B : NamedBlock V, NamedRun.blockInRun S rho B → PriorCarrierRows S rho r B →
    NamedBlock.compatible P B = false →
      (Protocol.derive_named S.E S.cfg B).h ≤
        (Protocol.derive_named S.E S.cfg P).h + 1


/-- Shared checkpoint target. The support boundary/frame and common
inequality are internal renewable certificate data. Initial entry can use b0;
recovery can replace both labels and accept new honest supporters. The risk
inventory is complete at that chosen boundary. Post-boundary honest head
coverage must be derived from earlier-action SG history, not assumed here or
replaced by a new old-risk bound. Renewal, retention and event interpolation
remain proof obligations of the joint r-to-r+1 step.

Addendum 34 14: exemption by the finalized block; the
frame arm on the raw frozen root.

The SG field reads at the round's opening ( 12) rather than
at the pre-action checkpoint, `included` is the matching opening condition, and
the two remaining checkpoint-based fields `fg` and `old_rows` are guarded by
`S.a r ≤ rho.horizon`, which the opening condition no longer implies.

The frame arm asserts the RAW frozen root and nothing else. The active candidate
is not asserted, because a reader with `F ≺ P ⪯ J = get_fg_root` has an empty
active candidate at the opening while the raw root still covers `P`: the freeze
runs over the processed tree before clipping, `freezeRoot` over `gv.T`, and does
not consult the FG root. The candidate form is derived at each read that needs
it, from this arm together with the reader's own filtered-tree membership. -/
structure RoundInvariant (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (P : NamedBlock V) (r : Round) : Prop where
  included : DomainIncluded S rho b0 r
  prefix_scope : NamedRun.blockInRun S rho P
  sg : ∀ v ∈ rho.honest,
    let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) v
    Block.Preceq P.erase n.st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 = some (some raw) ∧
        Block.Preceq P.erase raw
  
  common_support : ∃ supportBoundary : Time, ∃ supportRound : Round,
    supportBoundary = min b0 (early S.E S.hc r .g2) ∧ supportRound ≤ r ∧
    (∀ v ∈ rho.honest,
      S.hc.round_of (NamedRun.stateBeforeTime S rho supportBoundary v).st.core.s = supportRound) ∧
    S.E.electorate.weightOf
        ((Finset.univ \ rho.honest) ∪ commonStaleRisks S rho supportBoundary P supportRound r) <
      S.E.electorate.weightOf (commonSupporters S rho supportBoundary P supportRound r)
  fg : S.a r ≤ rho.horizon → ∀ v ∈ rho.honest, JointAt S rho P r v
  source_history : SignedSourceHistory S rho r
  old_rows : S.a r ≤ rho.horizon → ∀ v ∈ rho.honest,
    ∀ B ∈ (checkpoint S rho v r).st.bodies, PriorCarrierRows S rho r B
  entry_history : IntrinsicHighEntryHistory S rho P r
  conflicting_band : IntrinsicConflictingCarrierBand S rho P r

end DecoupledConsensusModel.Internal.NamedJointOutage

end
