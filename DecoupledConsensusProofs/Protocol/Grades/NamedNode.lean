module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Execution.Node
public import DecoupledConsensusProofs.Protocol.Handlers.Receipt
public import DecoupledConsensusProofs.Protocol.ValidatorClient.TickRecord

@[expose] public section

/-! Local named-node equations and invariants. Store and record preservation
use checked initial/per-duty producers. Cache clipping is a local fixed-point
fact; actual capture origins and strict event prefixes require the later run. -/
namespace DecoupledConsensusModel.Proofs.NamedNode
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V]

-- Proof-only reuse of the checked resilience clipping argument. The source
-- hashes are archived with NamedNode-third-leaf/validation1261.
private theorem clip_grade_compatible (g F : Block V) :
    Block.compatible (DecoupledConsensusModel.Protocol.clipGrade g F) F = true := by
  induction g with
  | genesis => simp [DecoupledConsensusModel.Protocol.clipGrade, Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
    simp only [DecoupledConsensusModel.Protocol.clipGrade]
    split
    · assumption
    · exact ih

private theorem clip_grade_keeps (g F : Block V) (h : Block.compatible g F = true) :
    DecoupledConsensusModel.Protocol.clipGrade g F = g := by
  cases g with
  | genesis => rfl
  | node p s root gv gsv ats v =>
    simp only [DecoupledConsensusModel.Protocol.clipGrade, h, ↓reduceIte]

private theorem clip_grade_idempotent (g F : Block V) :
    DecoupledConsensusModel.Protocol.clipGrade (DecoupledConsensusModel.Protocol.clipGrade g F) F =
      DecoupledConsensusModel.Protocol.clipGrade g F :=
  clip_grade_keeps _ _ (clip_grade_compatible g F)

private theorem clip_result_idempotent (F : Block V) (result : Option (Option (Block V))) :
    clipResult F (clipResult F result) = clipResult F result := by
  cases result with
  | none => rfl
  | some result =>
    cases result with
    | none => rfl
    | some B => simp only [clipResult, Option.map_some, clip_grade_idempotent]

private theorem clip_frame_idempotent (F : Block V) (f : DecoupledConsensusModel.Protocol.Frame V) :
    clipFrame F (clipFrame F f) = clipFrame F f := by
  cases f
  simp only [clipFrame, clip_result_idempotent]

private theorem clip_cache_idempotent (F : Block V) (c : Cache V) :
    clipCache F (clipCache F c) = clipCache F c := by
  cases c
  simp only [clipCache, clip_frame_idempotent]




theorem tick_cache_eq [Fintype V] (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    (Execution.NamedNode.tick S v n t).1.cache =
      clipCache (Execution.NamedNode.tick S v n t).1.st.core.F
        (onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) := rfl

/-- Alignment is local; it does not assert that any named phase was captured. -/
theorem tick_cache_round [Fintype V] (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    (Execution.NamedNode.tick S v n t).1.cache.round = S.hc.round_of (S.E.slotOf t) := by
  change (alignRound n.cache (S.hc.round_of (S.E.slotOf t))).round = _
  simp only [alignRound]
  split_ifs with h
  · exact h.symm
  · rfl
  · rfl


theorem process_record_eq [Fintype V] (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    (Execution.NamedNode.process S n o).record = n.record := rfl

theorem process_cache_eq [Fintype V] (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    (Execution.NamedNode.process S n o).cache =
      clipCache (Execution.NamedNode.process S n o).st.core.F n.cache := rfl

theorem process_cache_round [Fintype V] (S : Setup V) (n : NamedNodeState V)
    (o : NamedObject V) :
    (Execution.NamedNode.process S n o).cache.round = n.cache.round := rfl


theorem process_clock [Fintype V] (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    (Execution.NamedNode.process S n o).st.core.t = n.st.core.t ∧
      (Execution.NamedNode.process S n o).st.core.s = n.st.core.s :=
  NamedReceipt.process_clock S n.st o

theorem initial_invariants [Fintype V] (S : Setup V) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (Execution.NamedNode.initial : NamedNodeState V).st ∧
    NamedTickRecord.Invariant (Execution.NamedNode.initial : NamedNodeState V).record :=
  ⟨Proofs.NamedConfirmationMembership.invariant_initial S.E S.cfg, NamedTickRecord.invariant_initial⟩

private theorem confirmation_named_tick [Fintype V] (S : Setup V) (cache : Cache V)
    (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg st) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (Protocol.NamedTick.tick (DecoupledConsensusModel.Protocol.frameContract cache)
        S.E S.hc S.cfg (S.node v) st record t).1 := by
  let gc := DecoupledConsensusModel.Protocol.frameContract cache
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
      S.E.proposer s = (S.node v).val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg st0 :=
    Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg st t h
  have h1 : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg st1 := by
    dsimp only [st1]
    split_ifs
    · exact Proofs.NamedConfirmationMembership.invariant_propose gc S.E S.hc S.cfg (S.node v) st0 h0
    · exact h0
  have h2 : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg st2 := by
    dsimp only [st2]
    split_ifs
    · exact Proofs.NamedConfirmationMembership.invariant_goldfish_vote gc S.E S.hc S.cfg
        (S.node v) st1 h1
    · exact h1
  have h3 : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg st3 := by
    dsimp only [st3]
    split_ifs
    · exact Proofs.NamedConfirmationMembership.invariant_update cache S.E S.hc S.cfg
        st2 (s - 1) h2
    · exact h2
  have hstage : (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1 =
      if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          (S.node v).awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) st3 record).1
      else st3 := by
    rw [NamedTick.tick_computed_duties]
    dsimp only
    rw [apply_ite (fun out : Protocol.NamedStore V × Protocol.NamedRecord ×
      List (NamedObject V) => out.1)]
  change Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1
  rw [hstage]
  split_ifs
  · exact Proofs.NamedConfirmationMembership.invariant_attest gc S.E S.hc S.cfg
      (S.node v) st3 record h3
  · exact h3

/-- All confirmation producers see their actual current duty store. -/
theorem confirmation_invariant_tick [Fintype V] (S : Setup V) (v : V)
    (n : NamedNodeState V) (t : Time)
    (h : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (Execution.NamedNode.tick S v n t).1.st :=
  confirmation_named_tick S _ v n.st n.record t h

theorem record_invariant_tick [Fintype V] (S : Setup V) (v : V)
    (n : NamedNodeState V) (t : Time) (h : NamedTickRecord.Invariant n.record) :
    NamedTickRecord.Invariant (Execution.NamedNode.tick S v n t).1.record :=
  NamedTickRecord.invariant_tick _ S.E S.hc S.cfg (S.node v) n.st n.record t h

theorem invariants_process [Fintype V] (S : Setup V) (n : NamedNodeState V)
    (o : NamedObject V) (hStore : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st)
    (hRecord : NamedTickRecord.Invariant n.record) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (Execution.NamedNode.process S n o).st ∧
    NamedTickRecord.Invariant (Execution.NamedNode.process S n o).record :=
  ⟨NamedReceipt.confirmation_invariant_process S n.st o hStore, hRecord⟩

private theorem proposal_clock [Fintype V] (gc : Protocol.GradeContract V)
    (S : Setup V) (v : V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st).1.core.t =
        st.core.t ∧
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st).1.core.s =
        st.core.s := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact ⟨rfl, rfl⟩
  · exact NamedAdmission.on_block_clock .alsoCarried S.E S.hc S.cfg st _

private theorem proposal_time [Fintype V] (gc : Protocol.GradeContract V)
    (S : Setup V) (v : V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st).1.core.t =
      st.core.t := (proposal_clock gc S v st).1

private theorem proposal_slot [Fintype V] (gc : Protocol.GradeContract V)
    (S : Setup V) (v : V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st).1.core.s =
      st.core.s := (proposal_clock gc S v st).2

private theorem gf_time [Fintype V] (gc : Protocol.GradeContract V)
    (S : Setup V) (v : V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st).1.core.t = st.core.t := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_time S.E st.core _
  · rfl

private theorem gf_slot [Fintype V] (gc : Protocol.GradeContract V)
    (S : Setup V) (v : V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st).1.core.s = st.core.s := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact Proofs.Optimistic.on_goldfish_vote_checked_slot S.E st.core _
  · rfl

private theorem confirmation_time [Fintype V] (gc : Protocol.GradeContract V)
    (S : Setup V) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core.t = st.core.t := rfl

private theorem confirmation_slot [Fintype V] (gc : Protocol.GradeContract V)
    (S : Setup V) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core.s = st.core.s := rfl



private theorem attestation_time [Fintype V] (gc : Protocol.GradeContract V)
    (S : Setup V) (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) st record).1.core.t = st.core.t :=
  (NamedAdmission.admit_row_fixed_fields S.hc st _).1

private theorem attestation_slot [Fintype V] (gc : Protocol.GradeContract V)
    (S : Setup V) (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) st record).1.core.s = st.core.s :=
  (NamedAdmission.admit_row_fixed_fields S.hc st _).2.1

theorem tick_clock [Fintype V] (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    (Execution.NamedNode.tick S v n t).1.st.core.t = t ∧
      (Execution.NamedNode.tick S v n t).1.st.core.s = S.E.slotOf t := by
  change (Protocol.NamedTick.tick _ S.E S.hc S.cfg (S.node v) n.st n.record t).1.core.t = t ∧
    (Protocol.NamedTick.tick _ S.E S.hc S.cfg (S.node v) n.st n.record t).1.core.s = _
  rw [NamedTick.tick_computed_duties]
  dsimp only
  split_ifs <;> simp only [attestation_time, attestation_slot, confirmation_time,
    confirmation_slot, gf_time, gf_slot, proposal_time, proposal_slot,
    Protocol.NamedStore.setClock, and_self]

/-- The initial empty/pending cache is already clipped at its initial root. -/
theorem cache_clipped_initial :
    clipCache (Execution.NamedNode.initial : NamedNodeState V).st.core.F
      (Execution.NamedNode.initial : NamedNodeState V).cache =
        (Execution.NamedNode.initial : NamedNodeState V).cache := rfl

/-- Final clipping produces the local cache property without an input premise. -/
theorem cache_clipped_tick [Fintype V] (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    clipCache (Execution.NamedNode.tick S v n t).1.st.core.F
      (Execution.NamedNode.tick S v n t).1.cache =
        (Execution.NamedNode.tick S v n t).1.cache :=
  clip_cache_idempotent _ _

theorem cache_clipped_process [Fintype V] (S : Setup V) (n : NamedNodeState V)
    (o : NamedObject V) :
    clipCache (Execution.NamedNode.process S n o).st.core.F
      (Execution.NamedNode.process S n o).cache =
        (Execution.NamedNode.process S n o).cache :=
  clip_cache_idempotent _ _

#print axioms tick_cache_eq
#print axioms tick_cache_round
#print axioms process_record_eq
#print axioms process_cache_eq
#print axioms process_clock
#print axioms initial_invariants
#print axioms confirmation_invariant_tick
#print axioms record_invariant_tick
#print axioms invariants_process
#print axioms tick_clock
#print axioms cache_clipped_initial
#print axioms cache_clipped_tick
#print axioms cache_clipped_process
end DecoupledConsensusModel.Proofs.NamedNode

end
