module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.BodyRetention
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Protocol.Handlers.Blocks

@[expose] public section

/-!
Local body/stamp producers needed by later body-ready transport. The public
surface is exactly the final two theorems.

The local `StampCarry` proof follows the same concrete named transition split
as `NamedBodyRetention.stateBefore_bodies_mono`. `TimedBodies` is used only for
the strict-read theorem. Its stamp witness is a `Stamp`, so genesis stays `⊥`.
-/
namespace DecoupledConsensusModel.Proofs.NamedBlockStamp
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

private def StampCarry (before after : Protocol.NamedStore V) : Prop :=
  ∀ B : NamedBlock V, B ∈ before.bodies →
    after.core.timestamp_block B.erase = before.core.timestamp_block B.erase

omit [DecidableEq V] [Fintype V] in
private theorem stampCarry_refl (st : Protocol.NamedStore V) : StampCarry st st :=
  fun _ _ => rfl

omit [DecidableEq V] [Fintype V] in
private theorem stampCarry_trans {a b c : Protocol.NamedStore V}
    (hab : StampCarry a b) (hbc : StampCarry b c)
    (hmem : a.bodies ⊆ b.bodies) : StampCarry a c := by
  intro B hB
  exact (hbc B (hmem hB)).trans (hab B hB)

omit [DecidableEq V] [Fintype V] in
private theorem stampCarry_fields {before after : Protocol.NamedStore V}
    (h : after.core.timestamp_block = before.core.timestamp_block) :
    StampCarry before after := by
  intro B _
  exact congrFun h B.erase

private theorem checked_old_block_stamp (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (incoming held : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (hheld : held ∈ st.T) :
    (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current incoming buildState)
      hc st incoming).timestamp_block held = st.timestamp_block held := by
  by_cases heq : held = incoming
  · subst held
    rw [BlockProcessingDefaults.checked_existing E hc st incoming buildState hheld]
  · dsimp only [Protocol.on_block_checked_using]
    split_ifs
    · simp only [Protocol.on_block_using]
      split_ifs <;> first
        | rfl
        | (rw [Protocol.update_finality_timestamp_block,
              Protocol.foldl_on_goldfish_vote_checked_timestamp_block]
           simp [heq])
    · rfl

omit [Fintype V] in
private theorem rows_block_stamp (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.timestamp_block =
      st.core.timestamp_block := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).core.timestamp_block = _
      rw [ih]
      exact (NamedAdmission.admit_row_fixed_fields hc st row).2.2.2.1

private theorem core_block_stampCarry (S : Setup V) (st : Protocol.NamedStore V)
    (incoming : NamedBlock V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    StampCarry st
      (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st incoming) := by
  intro held hheld
  have htree : held.erase ∈ st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hheld
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · rw [NamedStore.commit_core]
    exact checked_old_block_stamp S.E S.hc st.core incoming.erase held.erase
      (fun parentState => Protocol.named_transition S.E S.cfg parentState incoming) htree
  · rfl

private theorem block_stampCarry (S : Setup V) (st : Protocol.NamedStore V)
    (incoming : NamedBlock V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    StampCarry st
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st incoming) := by
  have hcore := core_block_stampCarry S st incoming hcoh
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · intro held hheld
    rw [rows_block_stamp]
    exact hcore held hheld
  · exact hcore

private theorem propose_coherent (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Proofs.NamedStore.Coherent S.E S.cfg
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact hcoh
  · exact NamedAdmission.coherent_on_block .alsoCarried
      S.E S.hc S.cfg st _ hcoh

omit [Fintype V] in
private theorem commit_body_mono (before : Protocol.NamedStore V)
    (after : Protocol.Store V) (B : NamedBlock V) :
    before.bodies ⊆ (Protocol.NamedStore.commitBlock before after B).bodies := by
  unfold Protocol.NamedStore.commitBlock
  split_ifs
  · exact fun _ h => Finset.mem_insert_of_mem h
  · exact fun _ h => h

private theorem core_block_body_mono (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    st.bodies ⊆
      (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · exact commit_body_mono st _ B
  · exact fun _ h => h

omit [Fintype V] in
private theorem rows_bodies (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).bodies = _
      rw [ih, NamedAdmission.admit_row_bodies]

private theorem block_body_mono (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    st.bodies ⊆
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies := by
  have hcore := core_block_body_mono S st B
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · intro C hC
    rw [rows_bodies]
    exact hcore hC
  · exact hcore

private theorem checked_new_block_stamp (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (hpre : B ∉ st.T)
    (hpost : B ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B).T) :
    (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState)
      hc st B).timestamp_block B = some (st.t : Stamp) := by
  dsimp only [Protocol.on_block_checked_using] at hpost ⊢
  by_cases hvalid : Protocol.carried_attestations_admissible hc B = true
  · simp only [hvalid, if_true] at hpost ⊢
    by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
    · simp only [Protocol.on_block_using, if_pos hfirst] at hpost
      exact False.elim (hpre hpost)
    · by_cases hfinal : (!Block.preceq st.F B) = true
      · simp only [Protocol.on_block_using, if_neg hfirst, if_pos hfinal] at hpost
        exact False.elim (hpre hpost)
      · by_cases hproposer : B.proposer? ≠ some (E.proposer B.slot)
        · simp only [Protocol.on_block_using, if_neg hfirst, if_neg hfinal,
            if_pos hproposer] at hpost
          exact False.elim (hpre hpost)
        · by_cases hparent : ¬ B.parent.slot < B.slot
          · simp only [Protocol.on_block_using, if_neg hfirst, if_neg hfinal,
              if_neg hproposer, if_pos hparent] at hpost
            exact False.elim (hpre hpost)
          · simp only [Protocol.on_block_using, if_neg hfirst, if_neg hfinal,
              if_neg hproposer, if_neg hparent,
              Protocol.update_finality_timestamp_block,
              Protocol.foldl_on_goldfish_vote_checked_timestamp_block]
            simp
  · have hfalse : Protocol.carried_attestations_admissible hc B = false :=
      Bool.eq_false_of_not_eq_true hvalid
    simp only [hfalse, Bool.false_eq_true, if_false] at hpost
    exact False.elim (hpre hpost)

private theorem core_new_body_stamp (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.timestamp_block B.erase =
      some (st.core.t : Stamp) := by
  unfold Protocol.NamedStore.process_block_core at hpost ⊢
  by_cases hp : B.parent ∉ st.bodies
  · simp only [hp] at hpost
    exact False.elim (hpre hpost)
  · rw [if_neg hp] at hpost ⊢
    let after := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase
    change B ∈ (Protocol.NamedStore.commitBlock st after B).bodies at hpost
    change (Protocol.NamedStore.commitBlock st after B).core.timestamp_block B.erase = _
    by_cases hfresh : B.erase ∉ st.core.T ∧ B.erase ∈ after.T
    · unfold Protocol.NamedStore.commitBlock
      rw [if_pos hfresh]
      exact checked_new_block_stamp S.E S.hc st.core B.erase _ hfresh.1 hfresh.2
    · unfold Protocol.NamedStore.commitBlock at hpost ⊢
      rw [if_neg hfresh] at hpost
      exact False.elim (hpre hpost)

private theorem block_new_body_stamp (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hpre : B ∉ st.bodies)
    (hpost : B ∈
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies) :
    (Protocol.NamedAdmission.on_block_with
      .alsoCarried S.E S.hc S.cfg st B).core.timestamp_block B.erase =
        some (st.core.t : Stamp) := by
  let core := Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B
  have hcore : B ∈ core.bodies := by
    unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried at hpost
    split_ifs at hpost
    · simpa only [rows_bodies] using hpost
    · exact hpost
  have hs := core_new_body_stamp S st B hpre hcore
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · simpa only [rows_block_stamp] using hs
  · exact hs

private theorem propose_body_mono (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    st.bodies ⊆
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.bodies := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact fun _ h => h
  · exact block_body_mono S st _

private theorem propose_stampCarry (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    StampCarry st
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact stampCarry_refl st
  · exact block_stampCarry S st _ hcoh

private theorem gf_stampCarry (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    StampCarry st
      (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact stampCarry_fields
      (Protocol.on_goldfish_vote_checked_timestamp_block S.E st.core _)
  · exact stampCarry_refl st

private theorem confirmation_stampCarry (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) :
    StampCarry st
      (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s) :=
  stampCarry_fields rfl

private theorem row_stampCarry (S : Setup V) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    StampCarry st (Protocol.NamedAdmission.admit_row S.hc st row) :=
  stampCarry_fields (NamedAdmission.admit_row_fixed_fields S.hc st row).2.2.2.1

private theorem tick_stampCarry (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    StampCarry st
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
      S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have hc0 := NamedStore.coherent_clock S.E S.cfg st t hcoh
  have hc1 : Proofs.NamedStore.Coherent S.E S.cfg st1 := by
    dsimp only [st1]
    split_ifs
    · exact propose_coherent gc S nd st0 hc0
    · exact hc0
  have hc2 : Proofs.NamedStore.Coherent S.E S.cfg st2 := by
    dsimp only [st2]
    split_ifs
    · exact NamedDuties.coherent_goldfish_vote gc S.E S.hc S.cfg nd st1 hc1
    · exact hc1
  have hc3 : Proofs.NamedStore.Coherent S.E S.cfg st3 := by
    dsimp only [st3]
    split_ifs
    · exact NamedDuties.coherent_confirmation gc S.E S.hc S.cfg st2 (s - 1) hc2
    · exact hc2
  have h01 : StampCarry st st1 := by
    dsimp only [st1]
    split_ifs
    · exact stampCarry_trans (stampCarry_fields rfl)
        (propose_stampCarry gc S nd st0 hc0) (fun _ h => h)
    · exact stampCarry_fields rfl
  have h12 : StampCarry st1 st2 := by
    dsimp only [st2]
    split_ifs
    · exact gf_stampCarry gc S nd st1
    · exact stampCarry_refl st1
  have h23 : StampCarry st2 st3 := by
    dsimp only [st3]
    split_ifs
    · exact confirmation_stampCarry gc S st2 (s - 1)
    · exact stampCarry_refl st2
  have hb01 : st.bodies ⊆ st1.bodies := by
    dsimp only [st1]
    split_ifs
    · exact propose_body_mono gc S nd st0
    · exact fun _ h => h
  have hb12 : st1.bodies ⊆ st2.bodies := by
    dsimp only [st2]
    split_ifs <;> exact fun _ h => h
  have hb23 : st2.bodies ⊆ st3.bodies := by
    dsimp only [st3]
    split_ifs <;> exact fun _ h => h
  have h03 := stampCarry_trans
    (stampCarry_trans h01 h12 hb01) h23 (fun _ h => hb12 (hb01 h))
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact stampCarry_trans h03 (row_stampCarry S st3 _)
      (fun _ h => hb23 (hb12 (hb01 h)))
  · exact h03

private theorem process_stampCarry (S : Setup V) (st : Protocol.NamedStore V)
    (o : NamedObject V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    StampCarry st (NamedReceipt.process S st o) := by
  cases o with
  | block B => exact block_stampCarry S st B hcoh
  | gfVote u =>
      exact stampCarry_fields
        (Protocol.on_goldfish_vote_checked_timestamp_block S.E st.core u)
  | attest a => exact row_stampCarry S st a

private theorem stampCarry_succ (S : Setup V) (rho : NamedRun V)
    (i : Nat) (reader : V) :
    StampCarry (NamedRun.stateBefore S rho i reader).st
      (NamedRun.stateBefore S rho (i + 1) reader).st := by
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1
  rw [Proofs.NamedRuntime.stateBefore_succ]
  cases he : rho.events[i]? with
  | none => exact stampCarry_refl _
  | some e =>
      change StampCarry (NamedRun.stateBefore S rho i reader).st
        (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st
      by_cases hv : reader = e.node
      · cases e with
        | tick v t =>
            change reader = v at hv
            subst v
            rw [Proofs.NamedRuntime.step_tick]
            exact tick_stampCarry _ S (S.node reader) _ _ t hcoh
        | deliver v o t =>
            change reader = v at hv
            subst v
            rw [Proofs.NamedRuntime.step_deliver]
            exact process_stampCarry S _ o hcoh
      · rw [Proofs.NamedRuntime.step_other S _ e reader hv]
        exact stampCarry_refl _

private theorem stateBefore_stamp_mono (S : Setup V) (rho : NamedRun V)
    (reader : V) {i j : Nat} (hij : i ≤ j) {B : NamedBlock V}
    (hB : B ∈ (NamedRun.stateBefore S rho i reader).st.bodies) :
    (NamedRun.stateBefore S rho j reader).st.core.timestamp_block B.erase =
      (NamedRun.stateBefore S rho i reader).st.core.timestamp_block B.erase := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
      have hBj := NamedBodyRetention.stateBefore_bodies_mono S rho reader hij hB
      exact (stampCarry_succ S rho j reader B hBj).trans ih

/-- A held full body and its erased-core block stamp both survive to a later
event prefix. No schedule premise is needed. -/
theorem stateBefore_body_stamp_mono (S : Setup V) (rho : NamedRun V)
    (reader : V) {i j : Nat} (hij : i ≤ j) {B : NamedBlock V}
    (hB : B ∈ (NamedRun.stateBefore S rho i reader).st.bodies) :
    B ∈ (NamedRun.stateBefore S rho j reader).st.bodies ∧
      (NamedRun.stateBefore S rho j reader).st.core.timestamp_block B.erase =
        (NamedRun.stateBefore S rho i reader).st.core.timestamp_block B.erase :=
  ⟨NamedBodyRetention.stateBefore_bodies_mono S rho reader hij hB,
    stateBefore_stamp_mono S rho reader hij hB⟩

private def TimedBodies (bound : Time) (st : Protocol.NamedStore V) : Prop :=
  ∀ B : NamedBlock V, B ∈ st.bodies →
    ∃ stamp : Stamp, stamp < (bound : Stamp) ∧
      st.core.timestamp_block B.erase = some stamp

private theorem clock_after_event_le (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {n : Nat} {e : NamedEvent V}
    (he : rho.events[n]? = some e) {reader : V} (hnode : e.node = reader) :
    (NamedRun.stateBefore S rho (n + 1) reader).st.core.t ≤ e.time := by
  cases e with
  | tick v eventTime =>
      change v = reader at hnode
      subst v
      rw [Proofs.NamedRuntime.stateBefore_tick S rho he]
      exact (Proofs.NamedNode.tick_clock S reader
        (NamedRun.stateBefore S rho n reader) eventTime).1.le
  | deliver v o eventTime =>
      change v = reader at hnode
      subst v
      rw [Proofs.NamedRuntime.stateBefore_deliver S rho he,
        (Proofs.NamedNode.process_clock S (NamedRun.stateBefore S rho n reader) o).1]
      exact Proofs.NamedRuntime.stateBefore_clock_le_event S rho sch.sorted he
        (sch.in_horizon _ (List.mem_of_getElem? he)).1 reader

private theorem emitted_block_due (gc : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) (B : NamedBlock V)
    (hB : NamedObject.block B ∈
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2) :
    0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
      E.proposer (E.slotOf t) = nd.val_index := by
  by_contra hnot
  rw [NamedTick.tick_computed_duties] at hB
  dsimp only at hB
  simp only [if_neg hnot] at hB
  split_ifs at hB <;>
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, or_false, and_false, exists_false] at hB

private theorem tick_proposal_stage_fields (gc : Protocol.GradeContract V)
    (S : Setup V) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    let s := S.E.slotOf t
    let st0 := Protocol.NamedStore.setClock S.E st t
    let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
        S.E.proposer s = nd.val_index then
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.bodies = st1.bodies ∧
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core.timestamp_block =
        st1.core.timestamp_block := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
      S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have hb31 : st3.bodies = st1.bodies := by
    dsimp only [st3, st2]
    split_ifs <;> rfl
  have hs21 : st2.core.timestamp_block = st1.core.timestamp_block := by
    dsimp only [st2, Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    split_ifs <;> first
      | exact Protocol.on_goldfish_vote_checked_timestamp_block S.E _ _
      | rfl
  have hs31 : st3.core.timestamp_block = st1.core.timestamp_block := by
    dsimp only [st3]
    split_ifs <;> exact hs21
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact ⟨by
      simp only [Protocol.NamedDuties.attest_with, NamedAdmission.admit_row_bodies]
      exact hb31,
      (NamedAdmission.admit_row_fixed_fields S.hc st3 _).2.2.2.1.trans hs31⟩
  · exact ⟨hb31, hs31⟩

private theorem timedBodies_prefix (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (bound : Time)
    (n : Nat)
    (hearly : ∀ k e, k < n → rho.events[k]? = some e → e.time < bound)
    (reader : V) : TimedBodies bound (NamedRun.stateBefore S rho n reader).st := by
  /- The event induction keeps old stamps through `stampCarry_succ`. A new body
  uses the exact direct-delivery or self-proposal handler and receives its
  active clock. Genesis uses `genesisStamp: Stamp = ⊥`. -/
  induction n with
  | zero =>
      intro B hB
      have hgen : B = NamedBlock.genesis := by
        simpa [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
          Protocol.NamedStore.initial] using hB
      subst B
      refine ⟨genesisStamp, ?_, ?_⟩
      · exact WithBot.bot_lt_coe bound
      · simp [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
          Protocol.NamedStore.initial, Protocol.Store.init, genesisStamp,
          NamedBlock.erase]
  | succ n ih =>
      have hold := ih (fun k e hk he => hearly k e (Nat.lt_succ_of_lt hk) he)
      intro B hB
      by_cases hpre : B ∈ (NamedRun.stateBefore S rho n reader).st.bodies
      · obtain ⟨stamp, hs, heq⟩ := hold B hpre
        refine ⟨stamp, hs, ?_⟩
        exact (stampCarry_succ S rho n reader B hpre).trans heq
      · obtain ⟨eventTime, hacc⟩ :=
          Proofs.NamedReceiptCalls.new_block_accepts S rho n reader B hpre hB
        obtain ⟨hactual, e, he, hnode, het⟩ := hacc.1
        have htime : eventTime < bound := by
          rw [← het]
          exact hearly n e (Nat.lt_succ_self n) he
        refine ⟨(NamedRun.stateBefore S rho (n + 1) reader).st.core.t,
          ?_, ?_⟩
        · have hclock := clock_after_event_le S rho sch he hnode
          exact_mod_cast hclock.trans_lt (het.trans_lt htime)
        · rcases hactual with ⟨tickTime, htick, hem⟩ | ⟨_deliveryTime, hdeliver⟩
          · have hcall := Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hem
            let pre := NamedRun.stateBefore S rho n reader
            let c := DecoupledConsensusModel.Protocol.onPhaseTick
              S.E S.hc pre.st.core.toHealing tickTime pre.cache
            let gc := DecoupledConsensusModel.Protocol.frameContract c
            let before := Protocol.NamedStore.setClock S.E pre.st tickTime
            have hemTick := hem
            change NamedObject.block B ∈
              (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node reader)
                pre.st pre.record tickTime).2.2 at hemTick
            have hdue := emitted_block_due gc S.E S.hc S.cfg (S.node reader)
              pre.st pre.record tickTime B hemTick
            have hstage := tick_proposal_stage_fields gc S (S.node reader)
              pre.st pre.record tickTime
            rw [Proofs.NamedRuntime.stateBefore_tick S rho htick] at hB ⊢
            change B ∈ (Protocol.NamedTick.tick gc S.E S.hc S.cfg
              (S.node reader) pre.st pre.record tickTime).1.bodies at hB
            change (Protocol.NamedTick.tick gc S.E S.hc S.cfg
              (S.node reader) pre.st pre.record tickTime).1.core.timestamp_block B.erase =
                some ((Protocol.NamedTick.tick gc S.E S.hc S.cfg
                  (S.node reader) pre.st pre.record tickTime).1.core.t : Stamp)
            have hpostProposal : B ∈
                (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
                  (S.node reader) before).1.bodies := by
              rw [hstage.1] at hB
              simpa only [if_pos hdue] using hB
            have hcallStore :
                (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
                  (S.node reader) before).1 =
                (Protocol.NamedAdmission.on_block_with
                  .alsoCarried S.E S.hc S.cfg before B) := by
              exact congrArg Prod.fst hcall
            have hpostOn : B ∈ (Protocol.NamedAdmission.on_block_with
                .alsoCarried S.E S.hc S.cfg before B).bodies := by
              rw [← hcallStore]
              exact hpostProposal
            have hpreBefore : B ∉ before.bodies := by
              simpa only [before, Protocol.NamedStore.setClock] using hpre
            have hnew := block_new_body_stamp S before B hpreBefore hpostOn
            have hstamp :
                (Protocol.NamedTick.tick gc S.E S.hc S.cfg
                  (S.node reader) pre.st pre.record tickTime).1.core.timestamp_block B.erase =
                    some (before.core.t : Stamp) := by
              calc
                _ = (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg
                    (S.node reader) before).1.core.timestamp_block B.erase := by
                      rw [hstage.2]
                      simp only [if_pos hdue]
                      rfl
                _ = (Protocol.NamedAdmission.on_block_with
                    .alsoCarried S.E S.hc S.cfg before B).core.timestamp_block B.erase := by
                      rw [hcallStore]
                _ = _ := hnew
            calc
              _ = some (before.core.t : Stamp) := hstamp
              _ = _ := by
                have hclock := (Proofs.NamedNode.tick_clock S reader pre tickTime).1
                change (Protocol.NamedTick.tick gc S.E S.hc S.cfg
                  (S.node reader) pre.st pre.record tickTime).1.core.t = tickTime at hclock
                rw [show before.core.t = tickTime by rfl, hclock]
          · rw [Proofs.NamedRuntime.stateBefore_deliver S rho hdeliver] at hB ⊢
            let pre := NamedRun.stateBefore S rho n reader
            have hpost : B ∈ (Protocol.NamedAdmission.on_block_with
                .alsoCarried S.E S.hc S.cfg pre.st B).bodies := by
              exact hB
            have hnew := block_new_body_stamp S pre.st B hpre hpost
            have hclock := (Proofs.NamedNode.process_clock S pre (.block B)).1
            change (Protocol.NamedAdmission.on_block_with
              .alsoCarried S.E S.hc S.cfg pre.st B).core.t = pre.st.core.t at hclock
            change (Protocol.NamedAdmission.on_block_with
              .alsoCarried S.E S.hc S.cfg pre.st B).core.timestamp_block B.erase =
                some ((Protocol.NamedAdmission.on_block_with
                  .alsoCarried S.E S.hc S.cfg pre.st B).core.t : Stamp)
            rw [hclock]
            exact hnew

/-- Every full body held at a strict named read has its erased-core block stamp
strictly before that read. Schedule well-formedness is the only run premise.
Genesis is discharged with its bottom stamp, without a finite genesis time. -/
theorem held_body_stampedBefore_stateBeforeTime (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) (t : Time)
    (B : NamedBlock V)
    (hB : B ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    stampedBefore
      (NamedRun.stateBeforeTime S rho t reader).st.core.timestamp_block
      t B.erase = true := by
  obtain ⟨n, hread, hearly⟩ :=
    Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hB ⊢
  obtain ⟨stamp, hlt, hstamp⟩ :=
    timedBodies_prefix S rho sch t n hearly reader B hB
  simp only [stampedBefore, hstamp, decide_eq_true_eq]
  exact hlt

end DecoupledConsensusModel.Proofs.NamedBlockStamp

end
