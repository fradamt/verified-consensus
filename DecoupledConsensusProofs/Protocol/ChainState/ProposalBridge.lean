module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.BlockProcessingDefaults
public import DecoupledConsensusProofs.Protocol.ChainState.LeakLedger
public import DecoupledConsensusInternal.Definitions.NamedEvidence
public import DecoupledConsensusProofs.Generic.SlotFreshness
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.ProposalRows
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
open Internal Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Totality

The prepared read only stages the clock on top of a prefix state, and
`Proofs.NamedStoreRoots.invariant_clock` carries the invariant across exactly that. -/

/-- The named-store root invariant at the proposer's prepared read. No
honesty and no schedule premise: `stateBeforeTime_invariants` is local. -/
theorem proposerReadAt_invariant (S : Setup V) (rho : Run V) (s : Slot) :
    Proofs.NamedStoreRoots.Invariant S.E S.cfg (proposerReadAt S rho s).st :=
  Proofs.NamedStoreRoots.invariant_clock S.E S.cfg
    (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s)).st
    (Protocol.proposal_time S.E s)
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.proposal_time S.E s) (S.E.proposer s)).1.1


/-- **The graded proposal reader is total** (E1; discharges Q-PR3). The
selected parent is a member of the read's core tree, the tree view makes it the
erasure of a retained named body, and scoped erasure uniqueness makes that body
the one `parentBody?` returns. -/
theorem proposedBlockAt_isSome (S : Setup V) (rho : Run V) (s : Slot) :
    ∃ B : NamedBlock V, proposedBlockAt S rho s = some B :=
  Proofs.NamedActions.runtime_proposal_some (proposerReadAt S rho s).cache
    .poolAndCarried S.E S.hc S.cfg (S.node (S.E.proposer s))
    (proposerReadAt S rho s).st (proposerReadAt_invariant S rho s)



/-- The selected parent is in the read's own tree: the `hmem` premise
`Availability/Final.lean` carries, now free. -/
theorem proposedParent_mem (S : Setup V) (rho : Run V) (s : Slot) :
    proposedParent S rho s ∈ (proposerReadAt S rho s).st.core.T :=
  NamedProposalParent.proposal_parent_mem (proposerReadAt S rho s).cache
    S.E S.hc (S.node (S.E.proposer s)) (proposerReadAt S rho s).st
    (proposerReadAt_invariant S rho s).2


/-! ## 2. The field readers -/

/-- **The proposal carries the slot it was computed at** (E2). The proof is
`Proofs.Optimistic.proposedBlockAt_slot`; this is the short name in the namespace
where `proposedBlockAt` itself lives. -/
theorem proposedBlockAt_slot (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B) : B.slot = s :=
  Proofs.Optimistic.proposedBlockAt_slot S rho s hB


/-- **The proposal names its own proposer** (E4). The duty's input takes the
identity field from the node record, and `Setup.node_val_index` ties that
record to the validator the schedule chose for the slot. -/
theorem proposedBlockAt_proposer (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B) : B.proposer? = some (S.E.proposer s) := by
  have hpay := Proofs.NamedActions.proposal_payload (NamedProfile.gradeContract
    (proposerReadAt S rho s).cache) .poolAndCarried S.E S.hc
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB
  rw [hpay.2.2.2.2.2.2.2]
  exact congrArg some (S.node_val_index (S.E.proposer s))


/-- **The proposal's parent is the retained body of the selected head** (E5;
this is Q-PR1, `ProposedBlockParentQuery`). `NamedBlock.parent?` returns a
`NamedBlock V`, so the only statement that typechecks is about the parent's
*erasure*, and the block it erases to is `Proofs.HealingSurface.proposedParent` —
the graded head on the prepared read, never `Protocol.get_head` on a tick
store (that correspondence is the open Q-PR2). -/
theorem proposedBlockAt_parent (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B) :
    ∃ p : NamedBlock V, NamedBlock.parent? B = some p ∧ p.erase = proposedParent S rho s := by
  have hB' : ((Protocol.NamedActions.parentBody? (proposerReadAt S rho s).st
      (proposalInputAt S rho s).parent).map fun parent =>
        NamedBlock.node parent (proposalInputAt S rho s).slot (proposalInputAt S rho s).root
          (proposalInputAt S rho s).gf_votes (proposalInputAt S rho s).gf_support_votes
          (Protocol.NamedProposalRows.proposalRows parent
            (Protocol.NamedProposalRows.select .poolAndCarried S.hc (proposerReadAt S rho s).st))
          (proposalInputAt S rho s).proposer) = some B := hB
  rw [Option.map_eq_some_iff] at hB'
  obtain ⟨p, hp, hBeq⟩ := hB'
  exact ⟨p, by rw [← hBeq]; rfl, (Proofs.NamedActions.parent_body_spec _ _ p hp).2⟩


/-! ## 3. The honest proposer's tick -/

/-- **The honest slot-`s` proposer computes a block and emits it** (E6). The
witness comes from E1, so no retention premise is left on the caller. -/
theorem proposedBlockAt_emits_of_honest (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon) :
    ∃ B : NamedBlock V, proposedBlockAt S rho s = some B ∧ B.slot = s ∧
      NamedRun.emits S rho (S.E.proposer s) (.block B)
        (Protocol.proposal_time S.E s) := by
  obtain ⟨B, hB⟩ := proposedBlockAt_isSome S rho s
  obtain ⟨hslot, hemit⟩ := Proofs.Optimistic.proposalTick S sch s hs hprop hhor hB
  exact ⟨B, hB, hslot, hemit⟩

omit [Fintype V] in
/-- Row admission never changes the retained bodies. -/
private theorem admit_rows_bodies (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rest ih =>
    show (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st row) rest).bodies = st.bodies
    rw [ih, NamedAdmission.admit_row_bodies]

/-- **A fresh, admitted proposal is retained as a named body.** The three
premises are exactly the guards `NamedStore.commitBlock` reads: the named
parent is held, the geometry is new, and the erased handler inserted it. -/
theorem mem_bodies_on_block_with (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hp : B.parent ∈ st.bodies) (hnew : B.erase ∉ st.core.T)
    (hins : B.erase ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B.erase
        (fun parentState => Protocol.named_transition E cfg parentState B)) hc st.core
      B.erase).T) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B).bodies := by
  have hcore : (Protocol.NamedStore.process_block_core E hc cfg st B).bodies =
      insert B st.bodies := by
    show (if B.parent ∉ st.bodies then st else
      Protocol.NamedStore.commitBlock st _ B).bodies = insert B st.bodies
    rw [if_neg (not_not.mpr hp), Protocol.NamedStore.commitBlock,
      if_pos (And.intro hnew hins)]
  have hmem : B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies := by
    rw [hcore]; exact Finset.mem_insert_self _ _
  show B ∈ (Protocol.NamedAdmission.admit_carried .alsoCarried hc st
    (Protocol.NamedStore.process_block_core E hc cfg st B) B).bodies
  dsimp only [Protocol.NamedAdmission.admit_carried]
  split
  · rw [admit_rows_bodies]; exact hmem
  · exact hmem

/-- The retained-parent premise of `mem_bodies_on_block_with` is free for a
computed proposal: the duty found the parent body before it built the block. -/
theorem proposedBlockAt_on_block_with_bodies (S : Setup V) (rho : Run V) (s : Slot)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hnew : B.erase ∉ (proposerReadAt S rho s).st.core.T)
    (hins : B.erase ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc (proposerReadAt S rho s).st.core B.erase).T) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
      (proposerReadAt S rho s).st B).bodies :=
  mem_bodies_on_block_with S.E S.hc S.cfg (proposerReadAt S rho s).st B
    (Proofs.NamedActions.proposal_payload (NamedProfile.gradeContract (proposerReadAt S rho s).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB).1
    hnew hins

/-- At a proposal tick no later branch touches the retained bodies: the vote and
confirmation instants are distinct from the proposal instant, and a coincident
round action only admits rows. -/
private theorem tick_bodies_proposal (S : Setup V) (v : V) (n : NodeState V) (s : Slot)
    (hs : 0 < s) (hpr : S.E.proposer s = (S.node v).val_index) :
    (Execution.NamedNode.tick S v n (Protocol.proposal_time S.E s)).1.st.bodies =
      (Protocol.NamedDuties.propose_block_with
        (NamedProfile.gradeContract (NamedActionReads.confirmationReadFrom S n
          (Protocol.proposal_time S.E s)).cache) S.E S.hc S.cfg (S.node v)
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.proposal_time S.E s)).st).1.bodies := by
  have hslot : S.E.slotOf (Protocol.proposal_time S.E s) = s :=
    Proofs.Optimistic.slotOf_proposal_time S.E s
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock,
    Proofs.Optimistic.proposal_time_ne_vote_time S.E s,
    Proofs.Optimistic.proposal_time_ne_support_cutoff S.E s, hpr, hs,
    and_false, and_true, if_false, if_true, Protocol.NamedDuties.attest_with,
    Protocol.NamedAdmission.admit_row]
  split
  · split <;> rfl
  · rfl

/-- **The proposer holds its own proposal right after its tick** (E7'). -/
theorem proposedBlockAt_mem_bodies_after_tick (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hadmit : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
      (proposerReadAt S rho s).st B).bodies) :
    ∃ i : Nat, rho.events[i]? =
        some (.tick (S.E.proposer s) (Protocol.proposal_time S.E s)) ∧
      B ∈ (NamedRun.stateBefore S rho (i + 1) (S.E.proposer s)).st.bodies := by
  obtain ⟨-, i, hi, -⟩ := Proofs.Optimistic.proposalTick S sch s hs hprop hhor hB
  refine ⟨i, hi, ?_⟩
  have hst : NamedRun.stateBefore S rho i (S.E.proposer s) =
      NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s) :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch hi
  rw [Proofs.NamedRuntime.stateBefore_tick S rho hi, hst,
    tick_bodies_proposal S (S.E.proposer s)
      (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s)) s hs
      (S.node_val_index (S.E.proposer s)).symm]
  have hB' : Protocol.NamedActions.proposal_with
      (NamedProfile.gradeContract (proposerReadAt S rho s).cache) .poolAndCarried
      S.E S.hc (S.node (S.E.proposer s)) (proposerReadAt S rho s).st = some B := hB
  show B ∈ (Protocol.NamedDuties.propose_block_with
    (NamedProfile.gradeContract (proposerReadAt S rho s).cache) S.E S.hc S.cfg
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st).1.bodies
  simp only [Protocol.NamedDuties.propose_block_with, hB']
  exact hadmit

/-- **The proposal is a block of the run** (E7). -/
theorem proposedBlockAt_blockInRun (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hadmit : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
      (proposerReadAt S rho s).st B).bodies) :
    NamedRun.blockInRun S rho B := by
  obtain ⟨i, -, hmem⟩ :=
    proposedBlockAt_mem_bodies_after_tick S sch s hs hprop hhor hB hadmit
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Or.inr ⟨S.E.proposer s, hprop, i + 1, hmem⟩)

/-- **The proposal is determined by the slot** (E8). -/
theorem proposedBlockAt_unique (S : Setup V) (rho : Run V) (s : Slot)
    {B B' : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hB' : proposedBlockAt S rho s = some B') : B = B' :=
  Option.some.inj (hB ▸ hB')



/-- **The named height law at one block**. `fold_rows` is the state after the
block's targeted rows, before the height events; the fold leaves `h` alone, so
the two gates are the whole story. -/
theorem named_transition_height (E : Env V) (cfg : Protocol.HeightConfig)
    (st : Protocol.ChainState V) (B : NamedBlock V) :
    (Protocol.named_transition E cfg st B).h =
      (let pre := Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
          st B.erase B.attestations
       if Protocol.targetReady E pre then st.h + 1
       else if Protocol.progReady E cfg pre then st.h + 1 else st.h) := by
  have hpre : (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
      st B.erase B.attestations).h = st.h :=
    (NamedDerivationGeometry.fold_context_fields (Protocol.TimeoutBinding.targeted V)
      B.attestations { st with s := B.erase.slot }).2.1
  show (Protocol.process_height_events E cfg
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
      st B.erase B.attestations)).h = _
  rw [LeakLedger.height_event_counter, hpre]

/-- The same law along a named chain: the parent's derivation is the state the
block's own transition starts from. -/
theorem derive_named_height (E : Env V) (cfg : Protocol.HeightConfig)
    {B p : NamedBlock V} (hp : NamedBlock.parent? B = some p) :
    (Protocol.derive_named E cfg B).h =
      (let st := Protocol.derive_named E cfg p
       let pre := Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
          st B.erase B.attestations
       if Protocol.targetReady E pre then st.h + 1
       else if Protocol.progReady E cfg pre then st.h + 1 else st.h) := by
  cases B with
  | genesis => exact absurd hp (by simp [NamedBlock.parent?])
  | node q s root votes support rows proposer =>
    have hq : q = p := Option.some.inj hp
    subst hq
    rw [BlockProcessingDefaults.derive_named_node]
    exact named_transition_height E cfg (Protocol.derive_named E cfg q) _

/-- The dichotomy consumers of the retired `derived_state … + 1` sites need. -/
theorem derive_named_height_cases (E : Env V) (cfg : Protocol.HeightConfig)
    {B p : NamedBlock V} (hp : NamedBlock.parent? B = some p) :
    (Protocol.derive_named E cfg B).h =
        (Protocol.derive_named E cfg p).h + 1 ∨
      (Protocol.derive_named E cfg B).h = (Protocol.derive_named E cfg p).h := by
  rw [derive_named_height E cfg hp]
  dsimp only
  split_ifs
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The proposal's named height, relative to its retained parent** (E9, in
the only form that is true). The parent comes from E5, so the caller supplies
nothing beyond the proposal itself. -/
theorem proposedBlockAt_height (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B) :
    ∃ p : NamedBlock V, NamedBlock.parent? B = some p ∧
      p.erase = proposedParent S rho s ∧
      ((Protocol.derive_named S.E S.cfg B).h =
          (Protocol.derive_named S.E S.cfg p).h + 1 ∨
        (Protocol.derive_named S.E S.cfg B).h =
          (Protocol.derive_named S.E S.cfg p).h) := by
  obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho s hB
  exact ⟨p, hp, hpe, derive_named_height_cases S.E S.cfg hp⟩

/-! ## 5. Admission before a cutoff, over a named block

`Protocol.AdmittedBefore` takes a `Block V` while `VoteStoresExtend` and
`EvaluationStoreOk` take a `NamedBlock V`, so the membership-class consumers of
the retired reader split between the two spellings. Restating the erased
definition would touch its 157 use sites across the tree, most of them in green
modules, so the twin is added beside it instead: the two are interderivable in
one step, and the erased definition already carries the named witness. -/

/-- The `NamedBlock`-typed twin of `Protocol.AdmittedBefore`. -/
def NamedAdmittedBefore (S : Setup V) (rho : Run V) (v : V) (B : NamedBlock V)
    (Gamma : Time) : Prop :=
  ∃ (i : Nat) (t : Time), NamedRun.acceptsAt S rho i v (Object.block B) t ∧ t < Gamma



#print axioms proposerReadAt_invariant
#print axioms proposedBlockAt_isSome
#print axioms proposedBlockAt_slot
#print axioms proposedBlockAt_proposer
#print axioms proposedBlockAt_parent
#print axioms proposedBlockAt_emits_of_honest
#print axioms mem_bodies_on_block_with
#print axioms proposedBlockAt_on_block_with_bodies
#print axioms proposedBlockAt_mem_bodies_after_tick
#print axioms proposedBlockAt_blockInRun
#print axioms named_transition_height
#print axioms derive_named_height
#print axioms derive_named_height_cases
#print axioms proposedBlockAt_height
#print axioms proposedBlockAt_unique


/-! ## The frame contract's anchor stays above the FG root

`StoreFinality`'s chain from the finalized block to the head is stated at the
default grade contract, but a duty runs at `NamedProfile.gradeContract` of its
own cache, which is `DecoupledConsensusModel.Protocol.frameContract`. Both links twin here.
The second is generic already; only the first needs the frame anchor's own
shape. -/

/-- The frame contract's anchor is above the FG root. For a completed G1 the
anchor is the deepest filtered-tree block below the recorded root, and every
filtered-tree block is above the FG root; in every other case, including a
completed-empty G1 and a clipped root, the anchor is the FG root itself. -/
theorem fg_root_preceq_get_sg_root_with_frame (c : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    Block.Preceq (Protocol.get_fg_root st.toFG)
      (Protocol.get_sg_root_with (DecoupledConsensusModel.Protocol.frameContract c) E hc st r) := by
  show Block.Preceq (Protocol.get_fg_root st.toFG)
    (DecoupledConsensusModel.Protocol.anchor E hc st r (DecoupledConsensusModel.Protocol.readFrame c st r).g1)
  unfold DecoupledConsensusModel.Protocol.anchor
  match hg : (DecoupledConsensusModel.Protocol.readFrame c st r).g1 with
  | none => exact Block.preceq_self _
  | some none => exact Block.preceq_self _
  | some (some root) =>
    cases ha : DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree st.toFG) root with
    | none => simpa only [ha, Option.getD_none] using Block.preceq_self _
    | some A =>
      have hA : A ∈ (Protocol.get_filtered_block_tree st.toFG).filter
          (fun B => Block.preceq B root = true) := Proofs.Engine.deepest?_mem ha
      simpa only [ha, Option.getD_some] using
        Proofs.Records.preceq_get_fg_root_of_mem_filtered (Finset.mem_filter.mp hA).1

/-- Every contract's head descends from that contract's own anchor: the walk
is `ghost` from the anchor, whatever the anchor is. -/
theorem get_sg_root_with_preceq_get_head_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (votes support : Finset (GoldfishVote V)) (k : Slot) :
    Block.Preceq (Protocol.get_sg_root_with contract E hc st (hc.round_of st.s))
      (Protocol.get_head_with contract E hc st votes support k) :=
  Protocol.ghost_preceq _ _ _ _


/-- **The proposer's finalized block is below its own selected parent.** The
staged read keeps the prefix state's `F` and `J`, so the finalized block is
below the FG root, the FG root is below the frame anchor, and the anchor is
below the head the duty walks to. -/
theorem finalized_preceq_proposedParent (S : Setup V) (rho : Run V) (s : Slot) :
    Block.Preceq (proposerReadAt S rho s).st.core.F (proposedParent S rho s) := by
  have hFJ : Block.preceq (proposerReadAt S rho s).st.core.F
      (proposerReadAt S rho s).st.core.J = true :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
      (Protocol.proposal_time S.E s) (S.E.proposer s)
  have hroot := StoreFinality.finalized_preceq_fgRoot (st := (proposerReadAt S rho s).st.core) hFJ
  exact Block.preceq_trans hroot
    (Block.preceq_trans
      (fg_root_preceq_get_sg_root_with_frame (proposerReadAt S rho s).cache S.E S.hc
        (proposerReadAt S rho s).st.core.toHealing
        (S.hc.round_of (proposerReadAt S rho s).st.core.toHealing.s))
      (get_sg_root_with_preceq_get_head_with
        (NamedProfile.gradeContract (proposerReadAt S rho s).cache) S.E S.hc
        (proposerReadAt S rho s).st.core.toHealing _ _ _))


/-- Every row the named selector offers sits in the store's own SG window, so
its round is at or below the store's round. Both arms of `select` filter on
`ProposalRows.inWindow` at the same store. -/
theorem selected_row_round_le (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    {a : NamedAttestation V}
    (ha : a ∈ Protocol.NamedProposalRows.select .poolAndCarried hc st) :
    a.round ≤ hc.round_of st.core.s := by
  rw [NamedProposalRows.selected_source_exact] at ha
  have hw : Protocol.ProposalRows.inWindow hc st.core a.round = true := by
    rcases List.mem_append.mp ha with hp | hcarr
    · exact (List.mem_filter.mp hp).2
    · obtain ⟨B, -, hrow⟩ := List.mem_flatMap.mp hcarr
      by_cases hb : Protocol.NamedProposalRows.eligibleBody hc st B
      · rw [if_pos hb] at hrow
        exact (List.mem_filter.mp hrow).2
      · rw [if_neg hb] at hrow
        exact absurd hrow (List.not_mem_nil)
  have hw' : hc.round_of st.core.s - hc.η_SG ≤ a.round ∧ a.round ≤ hc.round_of st.core.s := by
    simpa only [Protocol.ProposalRows.inWindow, decide_eq_true_eq] using hw
  exact hw'.2

/-- An honest row in the proposer's selected source was emitted by its signer. -/
private theorem honest_selected_row_emission (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (s : Slot) {a : NamedAttestation V}
    (ha : a ∈ Protocol.NamedProposalRows.select .poolAndCarried S.hc
      (proposerReadAt S rho s).st)
    (hhon : a.val_index ∈ rho.honest) :
    rho.emits S a.val_index (.attest a) (S.a a.round) := by
  let st := (proposerReadAt S rho s).st
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.proposal_time S.E s)
  rw [NamedProposalRows.selected_source_exact] at ha
  rcases List.mem_append.mp ha with hpool | hcarried
  · have hprocessed := (List.mem_filter.mp hpool).1
    obtain ⟨k, -, hak⟩ := List.mem_flatMap.mp hprocessed
    have hrounds : Proofs.NamedStoreBridge.SgRowRounds st := by
      simpa only [st, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
          Proofs.NamedStoreBridge.sgRowRounds_stateBeforeTime S rho
            (Protocol.proposal_time S.E s) (S.E.proposer s)
    have har : a.round = k := hrounds k a hak
    have haOwn : a ∈ st.sg_rows a.round := by
      rw [har]
      exact hak
    have haN : a ∈ (rho.stateBefore S n (S.E.proposer s)).st.sg_rows a.round := by
      rw [← congrFun hn (S.E.proposer s)]
      simpa only [st, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using haOwn
    obtain ⟨_, _, _, _, _, hem⟩ :=
      Proofs.Bridges.heldArePastEmissions_of_admissibleCore
        S adm.toNamedAdmissibleCore n (S.E.proposer s) haN hhon
    exact hem
  · obtain ⟨B, hB, _, hrow, _⟩ :=
      (NamedProposalRows.mem_carried_rows S.hc st a).mp hcarried
    have hbody : B ∈ st.bodies := NamedProposalRows.ordered_bodies_mem hB
    have hbodyN : B ∈ (rho.stateBefore S n (S.E.proposer s)).st.bodies := by
      rw [← congrFun hn (S.E.proposer s)]
      simpa only [st, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hbody
    obtain ⟨_, _, _, _, _, hem⟩ :=
      Proofs.NamedOutageProvenance.honest_held_ancestor_row_emission
        S rho adm.toNamedAdmissibleCore.toNamedUnforgeable n
        (S.E.proposer s) hbodyN (Proofs.NamedAncestry.named_self B) hrow hhon
    exact hem

/-- Honest rows selected at one proposer read have one full payload per signer
and round. -/
theorem honest_selected_row_unique (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (s : Slot)
    {a b : NamedAttestation V}
    (ha : a ∈ Protocol.NamedProposalRows.select .poolAndCarried S.hc
      (proposerReadAt S rho s).st)
    (hb : b ∈ Protocol.NamedProposalRows.select .poolAndCarried S.hc
      (proposerReadAt S rho s).st)
    (hhon : a.val_index ∈ rho.honest)
    (hval : b.val_index = a.val_index) (hround : b.round = a.round) :
    b = a := by
  have hbHon : b.val_index ∈ rho.honest := by simpa only [hval] using hhon
  have hbe := honest_selected_row_emission S adm s hb hbHon
  have hae := honest_selected_row_emission S adm s ha hhon
  have hbe' : rho.emits S a.val_index (.attest b) (S.a b.round) := by
    simpa only [hval] using hbe
  exact Proofs.NamedOutageProvenance.emitted_same_round_unique S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hbe' hae hround

/-- **The proposal's carried rows pass the receiver's round guard.** Its rows
come from the selected SG window after on-chain exclusion and the signer cap. -/
theorem proposedBlockErased_carried_admissible (S : Setup V) (rho : Run V) (s : Slot)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    Protocol.carried_attestations_admissible S.hc B.erase = true := by
  have hpay := Proofs.NamedActions.proposal_payload (NamedProfile.gradeContract
    (proposerReadAt S rho s).cache) .poolAndCarried S.E S.hc
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB
  have hslot : B.erase.slot = (proposerReadAt S rho s).st.core.s := by
    rw [Proofs.NamedWire.erase_slot, hpay.2.2.1]; rfl
  rw [Protocol.carried_attestations_admissible, hslot, Proofs.NamedWire.erase_attestations]
  refine List.all_eq_true.mpr ?_
  intro a ha
  obtain ⟨row, hrow, hae⟩ := List.mem_map.mp ha
  rw [hpay.2.2.2.2.2.2.1] at hrow
  have hsel := NamedProposalRows.mem_proposalRows B.parent _ row hrow
  have := selected_row_round_le S.hc (proposerReadAt S rho s).st hsel.1
  rw [← hae]
  exact decide_eq_true this


/-- Restated from the private `handler_inserts` of
`Availability/BlockAdmissionRun`, whose proof is not exported. Candidate for
promotion there. With every erased guard met, the checked core handler admits
the block's erasure into the tree. -/
theorem erased_handler_inserts (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hparentTree : B.erase.parent ∈ st.core.T) (hfresh : B.erase ∉ st.core.T)
    (hslot : B.erase.slot ≤ st.core.s) (hF : Block.Preceq st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hparent : B.erase.parent.slot < B.erase.slot)
    (hcarried : Protocol.carried_attestations_admissible S.hc B.erase = true) :
    B.erase ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase).T := by
  have hfirst : ¬ (st.core.s < B.erase.slot ∨ B.erase ∈ st.core.T ∨
      B.erase.parent ∉ st.core.T) := by
    simp only [not_or]
    exact ⟨Nat.not_lt.mpr hslot, hfresh, not_not.mpr hparentTree⟩
  have hfinal : (!Block.preceq st.core.F B.erase) = false := by rw [hF]; rfl
  simp [Protocol.on_block_checked_using, hcarried,
    Protocol.on_block_using, hfirst, hfinal, hproposer, hparent,
    Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T S.E]


/-! ## The retention guard of the two run-membership exports -/

/-- **The proposal's geometry is fresh at its own tick.** Every block the
proposer already holds when it reads at `proposal_time s` sits at a slot
strictly below `s`, while the proposal itself sits at `s`. So the proposal's
erasure is not in that read's tree, which is exactly the freshness
`NamedStore.commitBlock` tests before it retains a body. This discharges the
`hadmit` side condition of `proposedBlockAt_mem_bodies_after_tick` and
`proposedBlockAt_blockInRun` on its geometry half. -/
theorem proposedBlockErased_fresh_at_tick (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (s : Slot) (hs : 0 < s)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    B.erase ∉ (proposerReadAt S rho s).st.core.T := by
  intro hmem
  have hlt := Proofs.NamedSlotFreshness.block_slot_lt_of_mem_beforeTime_of_le_proposal
    S adm hs (le_refl (Protocol.proposal_time S.E s)) hmem
  rw [Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho s hB] at hlt
  exact Nat.lt_irrefl s hlt

#print axioms proposedBlockErased_fresh_at_tick

/-- The proposal's erased parent is exactly the selected head. -/
theorem proposedBlockErased_parent (S : Setup V) (rho : Run V) (s : Slot)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    B.erase.parent = proposedParent S rho s := by
  obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho s hB
  rw [Proofs.NamedWire.erase_parent]
  cases B with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hp
  | node q _ _ _ _ _ _ =>
    simp only [NamedBlock.parent?, Option.some.injEq] at hp
    subst hp
    exact hpe

/-- **The retention guard, free.** Every input the erased handler checks is a
consequence of the proposal being the duty's own computed block at its own
read, so the proposer retains it with no caller-supplied premise. -/
theorem proposedBlockAt_admit (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (s : Slot) (hs : 0 < s) {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
      (proposerReadAt S rho s).st B).bodies := by
  have hpay := Proofs.NamedActions.proposal_payload (NamedProfile.gradeContract
    (proposerReadAt S rho s).cache) .poolAndCarried S.E S.hc
    (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB
  have hstore : B.erase.slot = (proposerReadAt S rho s).st.core.s := by
    rw [Proofs.NamedWire.erase_slot, hpay.2.2.1]; rfl
  have hsslot : B.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]; exact proposedBlockAt_slot S rho s hB
  have hpar : B.erase.parent = proposedParent S rho s :=
    proposedBlockErased_parent S rho s hB
  have hfresh := proposedBlockErased_fresh_at_tick S adm s hs hB
  have hparentTree : B.erase.parent ∈ (proposerReadAt S rho s).st.core.T := by
    rw [hpar]; exact proposedParent_mem S rho s
  have hparent : B.erase.parent.slot < B.erase.slot := by
    rw [hsslot, hpar]
    exact Proofs.NamedSlotFreshness.block_slot_lt_of_mem_beforeTime_of_le_proposal S adm hs
      (le_refl (Protocol.proposal_time S.E s)) (proposedParent_mem S rho s)
  have hparentPreceq : Block.Preceq B.erase.parent B.erase := by
    cases B with
    | genesis => exact Block.preceq_self _
    | node q sl r gv sup rows pr =>
      exact Protocol.preceq_of_parent?
        (show (NamedBlock.node q sl r gv sup rows pr : NamedBlock V).erase.parent? =
          some (NamedBlock.node q sl r gv sup rows pr : NamedBlock V).erase.parent from rfl)
  have hF : Block.Preceq (proposerReadAt S rho s).st.core.F B.erase :=
    Block.preceq_trans (hpar ▸ finalized_preceq_proposedParent S rho s) hparentPreceq
  have hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot) := by
    rw [Proofs.NamedWire.erase_proposer, hsslot]
    exact proposedBlockAt_proposer S rho s hB
  exact proposedBlockAt_on_block_with_bodies S rho s hB hfresh
    (erased_handler_inserts S (proposerReadAt S rho s).st B hparentTree hfresh
      (le_of_eq hstore) hF hproposer hparent
      (proposedBlockErased_carried_admissible S rho s hB))



/-- **The proposer holds its own proposal, with no retention premise** (E7').
The guard is discharged from the admissible core alone. -/
theorem proposedBlockAt_mem_bodies_after_tick_of_admissible (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    ∃ i : Nat, rho.events[i]? =
        some (.tick (S.E.proposer s) (Protocol.proposal_time S.E s)) ∧
      B ∈ (NamedRun.stateBefore S rho (i + 1) (S.E.proposer s)).st.bodies :=
  proposedBlockAt_mem_bodies_after_tick S adm.toNamedScheduleWellFormed s hs hprop hhor hB
    (proposedBlockAt_admit S adm s hs hB)

/-- **An honest proposal is a run block, with no retention premise.** -/
theorem proposedBlockAt_blockInRun_of_admissible (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    NamedRun.blockInRun S rho B :=
  proposedBlockAt_blockInRun S adm.toNamedScheduleWellFormed s hs hprop hhor hB
    (proposedBlockAt_admit S adm s hs hB)

#print axioms fg_root_preceq_get_sg_root_with_frame
#print axioms get_sg_root_with_preceq_get_head_with
#print axioms finalized_preceq_proposedParent
#print axioms honest_selected_row_unique
#print axioms proposedBlockErased_carried_admissible
#print axioms proposedBlockAt_admit
#print axioms proposedBlockAt_mem_bodies_after_tick_of_admissible
#print axioms proposedBlockAt_blockInRun_of_admissible

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
