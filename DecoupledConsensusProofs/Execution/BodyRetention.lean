module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ReceiptCalls

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedBodyRetention
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

private def BodyStep (before after : Protocol.NamedStore V) : Prop :=
  before.bodies ⊆ after.bodies

omit [DecidableEq V] [Fintype V] in
private theorem bodyStep_refl (st : Protocol.NamedStore V) : BodyStep st st :=
  fun _ h => h

omit [DecidableEq V] [Fintype V] in
private theorem bodyStep_trans {a b c : Protocol.NamedStore V}
    (hab : BodyStep a b) (hbc : BodyStep b c) : BodyStep a c :=
  fun _B hB => hbc (hab hB)

omit [Fintype V] in
private theorem commitBlock_step (before : Protocol.NamedStore V)
    (after : Protocol.Store V) (B : NamedBlock V) :
    BodyStep before (Protocol.NamedStore.commitBlock before after B) := by
  unfold Protocol.NamedStore.commitBlock BodyStep
  split_ifs
  · intro C hC
    exact Finset.mem_insert_of_mem hC
  · intro C hC
    exact hC

private theorem process_block_core_step (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    BodyStep st (Protocol.NamedStore.process_block_core E hc cfg st B) := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · exact commitBlock_step st _ B
  · exact bodyStep_refl st

omit [Fintype V] in
private theorem row_step (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    BodyStep st (Protocol.NamedAdmission.admit_row hc st a) := by
  unfold BodyStep
  rw [NamedAdmission.admit_row_bodies]

omit [Fintype V] in
private theorem rows_step (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    BodyStep st (Protocol.NamedAdmission.admit_rows hc st rows) := by
  induction rows generalizing st with
  | nil => exact bodyStep_refl st
  | cons a rows ih =>
      exact bodyStep_trans (row_step hc st a) (ih _)

private theorem block_step (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    BodyStep st
      (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B) := by
  have hcore := process_block_core_step E hc cfg st B
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact bodyStep_trans hcore (rows_step hc _ B.attestations)
  · exact hcore

private theorem clock_step (E : Env V) (st : Protocol.NamedStore V) (t : Time) :
    BodyStep st (Protocol.NamedStore.setClock E st t) :=
  bodyStep_refl st

private theorem propose_step (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    BodyStep st
      (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact bodyStep_refl st
  · exact block_step E hc cfg st _

private theorem gf_step (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    BodyStep st (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1 :=
  bodyStep_refl st

private theorem confirmation_step (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    BodyStep st (Protocol.NamedDuties.update_confirmation_with gc E hc st s) :=
  bodyStep_refl st

private theorem attest_step (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) :
    BodyStep st (Protocol.NamedDuties.attest_with gc E hc nd st record).1 :=
  row_step hc st _

private theorem tick_step (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    BodyStep st (Protocol.NamedTick.tick gc E hc cfg nd st record t).1 := by
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time E s then
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
    Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  have h01 : BodyStep st0 st1 := by
    dsimp only [st1]
    split_ifs
    · exact propose_step gc E hc cfg nd st0
    · exact bodyStep_refl st0
  have h12 : BodyStep st1 st2 := by
    dsimp only [st2]
    split_ifs
    · exact gf_step gc E hc nd st1
    · exact bodyStep_refl st1
  have h23 : BodyStep st2 st3 := by
    dsimp only [st3]
    split_ifs
    · exact confirmation_step gc E hc st2 (s - 1)
    · exact bodyStep_refl st2
  have h03 := bodyStep_trans (clock_step E st t)
    (bodyStep_trans h01 (bodyStep_trans h12 h23))
  have hstore : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1 =
      (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧
          nd.awake (hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc E hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact bodyStep_trans h03 (attest_step gc E hc nd st3 record)
  · exact h03

private theorem node_tick_step (S : Setup V) (v : V)
    (n : NamedNodeState V) (t : Time) :
    BodyStep n.st (Execution.NamedNode.tick S v n t).1.st :=
  tick_step (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
    S.E S.hc S.cfg (S.node v) n.st n.record t

private theorem node_process_step (S : Setup V) (n : NamedNodeState V)
    (o : NamedObject V) :
    BodyStep n.st (Execution.NamedNode.process S n o).st := by
  cases o with
  | block B => exact block_step S.E S.hc S.cfg n.st B
  | gfVote u => exact bodyStep_refl n.st
  | attest a => exact row_step S.hc n.st a

private theorem world_step (S : Setup V) (w : NamedWorld V)
    (e : NamedEvent V) (v : V) :
    BodyStep (w v).st (NamedWorld.step S w e v).st := by
  cases e with
  | tick u t =>
      by_cases h : v = u
      · subst u
        simpa only [NamedWorld.step, Function.update_self] using
          node_tick_step S v (w v) t
      · simpa only [NamedWorld.step, Function.update_of_ne h] using
          bodyStep_refl (w v).st
  | deliver u o t =>
      by_cases h : v = u
      · subst u
        simpa only [NamedWorld.step, Function.update_self] using
          node_process_step S (w v) o
      · simpa only [NamedWorld.step, Function.update_of_ne h] using
          bodyStep_refl (w v).st


/-- **Public twin of the body-retention step**: one world
event never removes a held named body. Exposed for the time-indexed folds that
`Protocol.stateAt_eq_foldl` produces, which no index-prefix form covers. -/
theorem step_bodies_subset (S : Setup V) (w : NamedWorld V)
    (e : NamedEvent V) (v : V) :
    (w v).st.bodies ⊆ (NamedWorld.step S w e v).st.bodies :=
  world_step S w e v

/-- Bodies held by a named node are retained across event-index prefixes. -/
theorem stateBefore_bodies_mono (S : Setup V) (rho : NamedRun V) (v : V)
    {i j : Nat} (hij : i ≤ j) :
    (NamedRun.stateBefore S rho i v).st.bodies ⊆
      (NamedRun.stateBefore S rho j v).st.bodies := by
  have hs (k : Nat) : BodyStep
      (NamedRun.stateBefore S rho k v).st
      (NamedRun.stateBefore S rho (k + 1) v).st := by
    rw [Proofs.NamedRuntime.stateBefore_succ]
    cases he : rho.events[k]? with
    | none =>
        simp only [Option.toList_none, List.foldl_nil]
        exact bodyStep_refl _
    | some e =>
        simpa only [Option.toList_some, List.foldl_cons, List.foldl_nil] using
          world_step S (NamedRun.stateBefore S rho k) e v
  unfold BodyStep at hs
  exact Nat.rel_of_forall_rel_succ_of_le (fun A B : Finset (NamedBlock V) => A ⊆ B)
    hs hij

end DecoupledConsensusModel.Proofs.NamedBodyRetention

end
