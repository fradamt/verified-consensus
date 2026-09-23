module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ViabilityHistory
public import DecoupledConsensusProofs.Protocol.Handlers.NumericStore
public import DecoupledConsensusProofs.Execution.PrefixThroughHistory
public import DecoupledConsensusProofs.Protocol.Handlers.HandlerAdmissionGuards
public import DecoupledConsensusProofs.Protocol.Handlers.MaximumCarrier
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotone
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Execution.ReceiptCalls
public import DecoupledConsensusProofs.Execution.ReceiptCallsBase
public import DecoupledConsensusProofs.Protocol.Grades.NamedDuties
public import DecoupledConsensusProofs.Protocol.Schedule.NamedTick
public import DecoupledConsensusProofs.Protocol.Handlers.Admission
public import DecoupledConsensusProofs.Protocol.Handlers.NamedStore
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2

@[expose] public section

/-! Producer bridges for the held-skip gate.

Gap 1: an actual `NamedRun.acceptsAt` for a body produces the exact block call,
the fresh core-tree gate and the post-core membership its guards consume.
Gap 3: the same event carries the post-core finality forward to the recipient's
next prefix, for both the delivery and the self-emitted tick case. -/
namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.HeldSkipProducers
open Execution Execution.NamedReceiptCalls Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Stage-level bodies and finality equations -/

omit [Fintype V] in
private theorem rows_bodies (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    change (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st a) rows).bodies = _
    rw [ih, NamedAdmission.admit_row_bodies]

omit [Fintype V] in
private theorem rows_F (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.F = st.core.F := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    change (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st a) rows).core.F = _
    rw [ih, NamedAdmission.admit_row_core, on_sg_vote_F]

private theorem block_with_bodies (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (C : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st C).bodies =
      (Protocol.NamedStore.process_block_core E hc cfg st C).bodies := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact rows_bodies hc _ C.attestations
  · rfl

private theorem block_with_core_F (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (C : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st C).core.F =
      (Protocol.NamedStore.process_block_core E hc cfg st C).core.F := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact rows_F hc _ C.attestations
  · rfl

private theorem new_body_eq_input (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (C B : NamedBlock V)
    (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st C).bodies) :
    B = C := by
  rw [block_with_bodies] at hpost
  unfold Protocol.NamedStore.process_block_core at hpost
  split_ifs at hpost <;> first
    | exact False.elim (hpre hpost)
    | (dsimp only at hpost
       unfold Protocol.NamedStore.commitBlock at hpost
       split_ifs at hpost
       · exact (Finset.mem_insert.mp hpost).resolve_right hpre
       · exact False.elim (hpre hpost))

private theorem duty_attest_bodies (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.bodies = st.bodies :=
  NamedAdmission.admit_row_bodies hc st _

private theorem duty_attest_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.F = st.core.F := by
  rw [NamedDuties.attest_core]
  exact on_sg_vote_F hc st.core _

private theorem duty_goldfish_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.F = st.core.F := by
  rw [NamedDuties.goldfish_vote_core]
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_F E st.core _
  · rfl

/-! ## Gap 3, self-emitted case: the named tick -/

/-- A body that is absent before the actual named tick and present after it was
inserted by that tick's own proposal core, and the tick's returned finality is
that core's finality. No emission, open or duty premise is supplied. -/
theorem tick_new_body_core (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (B : NamedBlock V) (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.bodies) :
    B ∈ (Protocol.NamedStore.process_block_core E hc cfg
        (Protocol.NamedStore.setClock E st t) B).bodies ∧
      (Protocol.NamedStore.process_block_core E hc cfg
        (Protocol.NamedStore.setClock E st t) B).core.F =
        (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.F := by
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let due := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
  let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
  let st1 := if due then proposed.1 else st0
  let emitted1 : List (NamedObject V) := if due then
    match proposed.2 with | none => [] | some C => [.block C]
    else []
  let voteDue := 0 < s ∧ t = Protocol.vote_time E s
  let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
  let st2 := if voteDue then voted.1 else st1
  let emitted2 : List (NamedObject V) :=
    if voteDue then voted.2.toList.map NamedObject.gfVote else []
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
    Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  have h32 : st3.bodies = st1.bodies := by
    dsimp only [st3, st2]
    split_ifs <;> rfl
  have hF2 : st2.core.F = st1.core.F := by
    dsimp only [st2]
    split_ifs
    · exact duty_goldfish_F gc E hc nd st1
    · rfl
  have hF3 : st3.core.F = st2.core.F := by
    dsimp only [st3]
    split_ifs <;> rfl
  have hout := NamedTick.tick_computed_duties gc E hc cfg nd st record t
  change Protocol.NamedTick.tick gc E hc cfg nd st record t =
    (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
      let a := Protocol.NamedDuties.attest_with gc E hc nd st3 record
      (a.1, a.2.1, emitted1 ++ emitted2 ++ [.attest a.2.2])
    else (st3, record, emitted1 ++ emitted2)) at hout
  have hbodies : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.bodies = st1.bodies := by
    rw [hout]
    split_ifs
    · rw [duty_attest_bodies, h32]
    · exact h32
  have hFtick : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.F = st1.core.F := by
    rw [hout]
    split_ifs
    · rw [duty_attest_F, hF3, hF2]
    · rw [hF3, hF2]
  rw [hbodies] at hpost
  by_cases hd : due
  · cases hp : Protocol.NamedActions.proposal_with gc .poolAndCarried E hc nd st0 with
    | none =>
      have he := NamedDuties.propose_none gc E hc cfg nd st0 hp
      exact False.elim (hpre (by simpa only [st1, proposed, if_pos hd, he] using hpost))
    | some C =>
      have he := NamedDuties.propose_some gc E hc cfg nd st0 C hp
      have hC : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st0 C).bodies := by
        simpa only [st1, proposed, if_pos hd, he] using hpost
      have hpre0 : B ∉ st0.bodies := hpre
      have hBC := new_body_eq_input E hc cfg st0 C B hpre0 hC
      subst B
      have hst1 : st1 = Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st0 C := by
        simp only [st1, proposed, if_pos hd, he]
      refine ⟨?_, ?_⟩
      · rw [← block_with_bodies E hc cfg st0 C]
        exact hC
      · rw [hFtick, hst1, block_with_core_F]
  · exact False.elim (hpre (by simpa only [st1, if_neg hd] using hpost))

/-! ## Gap 1: the fresh core gate from actual bodies -/

/-- A body absent from the call input and present after the core call fixes the
fresh geometry gate and the post-core tree membership. Only prefix coherence
is used; no erasure-injectivity premise is added. -/
theorem fresh_core_of_bodies (S : Setup V) (rho : NamedRun V) (j : Nat) (v : V)
    (B : NamedBlock V) (before : Protocol.NamedStore V)
    (hcall : blockCallAt S rho j v B before)
    (hpre : B ∉ before.bodies) (hbody : B ∈ (postCore S before B).bodies) :
    B.erase ∉ before.core.T ∧ B.erase ∈ (postCore S before B).core.T := by
  have hco : Proofs.NamedStore.Coherent S.E S.cfg before :=
    (Proofs.NamedReceiptCallsBase.block_call_before_invariant S rho hcall).1.1
  have hnew : B.erase ∉ before.core.T := by
    intro hmem
    apply hpre
    have h := NamedStore.existing_geometry_keeps_bodies S.E S.hc S.cfg before B hmem
    change (postCore S before B).bodies = before.bodies at h
    rw [← h]
    exact hbody
  have hcoPost : Proofs.NamedStore.Coherent S.E S.cfg (postCore S before B) :=
    NamedStore.coherent_process_block S.E S.hc S.cfg before B hco
  refine ⟨hnew, ?_⟩
  rw [hcoPost.1]
  exact Finset.mem_image_of_mem NamedBlock.erase hbody

/-! ## Gaps 1 and 3 together, at the actual run -/

/-- An actual accepted block at index `j` produces its call input, the fresh
core gate, the post-core tree membership, and the transfer of the post-core
finality to the recipient's prefix at `j + 1`. -/
theorem accepted_block_fresh_call (S : Setup V) (rho : NamedRun V) (j : Nat) (v : V)
    (B : NamedBlock V) (t : Time)
    (hacc : NamedRun.acceptsAt S rho j v (.block B) t) :
    ∃ before : Protocol.NamedStore V,
      blockCallAt S rho j v B before ∧
      B.erase ∉ before.core.T ∧
      B.erase ∈ (postCore S before B).core.T ∧
      Block.Preceq (postCore S before B).core.F
        (NamedRun.stateBefore S rho (j + 1) v).st.core.F := by
  obtain ⟨⟨hidx, -⟩, hpre0, hpost0⟩ := hacc
  have hpre : B ∉ (NamedRun.stateBefore S rho j v).st.bodies := by
    simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hpre0
  have hpost : B ∈ (NamedRun.stateBefore S rho (j + 1) v).st.bodies := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hpost0
  change NamedRun.processesAtIndex S rho j v (.block B) at hidx
  rcases hidx with ⟨tt, hi, hem⟩ | ⟨tt, hi⟩
  · refine ⟨Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho j v).st tt, ?_, ?_⟩
    · exact Proofs.NamedReceiptCallsBase.blockCallAt_self S rho hi hem
    · rw [Proofs.NamedRuntime.stateBefore_tick S rho hi] at hpost ⊢
      obtain ⟨hbody, hF⟩ := tick_new_body_core
        (DecoupledConsensusModel.Protocol.frameContract (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc
          (NamedRun.stateBefore S rho j v).st.core.toHealing tt
          (NamedRun.stateBefore S rho j v).cache))
        S.E S.hc S.cfg (S.node v) (NamedRun.stateBefore S rho j v).st
        (NamedRun.stateBefore S rho j v).record tt B hpre hpost
      obtain ⟨hnew, hin⟩ := fresh_core_of_bodies S rho j v B
        (Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho j v).st tt)
        (Proofs.NamedReceiptCallsBase.blockCallAt_self S rho hi hem) hpre hbody
      refine ⟨hnew, hin, ?_⟩
      rw [show (postCore S (Protocol.NamedStore.setClock S.E
          (NamedRun.stateBefore S rho j v).st tt) B).core.F =
        (Execution.NamedNode.tick S v (NamedRun.stateBefore S rho j v) tt).1.st.core.F
        from hF]
      exact Block.preceq_self _
  · refine ⟨(NamedRun.stateBefore S rho j v).st,
      Proofs.NamedReceiptCallsBase.blockCallAt_delivery S rho hi, ?_⟩
    have hst := Proofs.NamedReceiptCallsBase.delivery_result S rho hi
    rw [hst] at hpost ⊢
    have hbody : B ∈ (postCore S (NamedRun.stateBefore S rho j v).st B).bodies := by
      change B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg
        (NamedRun.stateBefore S rho j v).st B).bodies at hpost
      rwa [block_with_bodies] at hpost
    obtain ⟨hnew, hin⟩ := fresh_core_of_bodies S rho j v B
      (NamedRun.stateBefore S rho j v).st
      (Proofs.NamedReceiptCallsBase.blockCallAt_delivery S rho hi) hpre hbody
    refine ⟨hnew, hin, ?_⟩
    rw [show (NamedReceipt.process S (NamedRun.stateBefore S rho j v).st
        (NamedObject.block B)).core.F =
      (postCore S (NamedRun.stateBefore S rho j v).st B).core.F from
      block_with_core_F S.E S.hc S.cfg (NamedRun.stateBefore S rho j v).st B]
    exact Block.preceq_self _

#print axioms tick_new_body_core
#print axioms fresh_core_of_bodies
#print axioms accepted_block_fresh_call
end DecoupledConsensusModel.Proofs.NamedOutageHistory.HeldSkipProducers

end
