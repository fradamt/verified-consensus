module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The named admission/duty/tick chain, `.core.F` version -/

/-- The shared core advances F for any offered state builder. -/
theorem on_block_using_F (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V) :
    Block.Preceq st.F (Protocol.on_block_using E st B buildState).F := by
  unfold Protocol.on_block_using
  split_ifs <;> first
    | exact Block.preceq_self _
    | (let stored : Protocol.Store V :=
          { st with
            σ := fun C => if C = B then buildState (st.σ B.parent) else st.σ C
            T := insert B st.T
            timestamp_block := fun C =>
              if C = B then some (st.t : Stamp) else st.timestamp_block C }
       have h := Proofs.update_finality_F
         (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored)
         ((B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored).σ B)
       simpa only [Proofs.foldl_on_goldfish_vote_checked_F E] using h)

private theorem checked_using_F (E : Env V) (hc : HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V) :
    Block.Preceq st.F
      (Protocol.on_block_checked_using
        (fun current => Protocol.on_block_using E current B buildState) hc st B).F := by
  unfold Protocol.on_block_checked_using
  split_ifs
  · exact on_block_using_F E st B buildState
  · exact Block.preceq_self _

omit [Fintype V] in
private theorem commitBlock_F (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock before after B).core.F = after.F := by
  simp only [Protocol.NamedStore.commitBlock]
  split_ifs <;> rfl

/-- Missing named parents preserve F; successful checks use the same shared
guard. -/
theorem process_block_core_F (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    Block.Preceq st.core.F
      (Protocol.NamedStore.process_block_core E hc cfg st B).core.F := by
  by_cases hp : B.parent ∈ st.bodies
  · simp only [Protocol.NamedStore.process_block_core, if_neg (not_not_intro hp)]
    rw [commitBlock_F]
    exact checked_using_F E hc st.core B.erase
      (fun parentState => Protocol.named_transition E cfg parentState B)
  · simp only [Protocol.NamedStore.process_block_core, if_pos hp]
    exact Block.preceq_self _

omit [Fintype V] in
private theorem admit_row_F (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).core.F = st.core.F := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> exact Proofs.on_sg_vote_F hc st.core row.erase

omit [Fintype V] in
private theorem foldl_admit_row_F (hc : HealConfig) (l : List (NamedAttestation V))
    (st : Protocol.NamedStore V) :
    (l.foldl (Protocol.NamedAdmission.admit_row hc) st).core.F = st.core.F := by
  induction l generalizing st with
  | nil => rfl
  | cons row l ih => rw [List.foldl_cons, ih, admit_row_F]

omit [Fintype V] in
private theorem admit_rows_F (hc : HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.F = st.core.F :=
  foldl_admit_row_F hc rows st

omit [Fintype V] in
private theorem admit_carried_F (admission : Protocol.CarriedAdmission) (hc : HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission hc before after B).core.F = after.core.F := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_F hc after B.attestations
      · rfl

/-- The actual F1 tail preserves the core handler's finality advance. -/
theorem on_block_with_F (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    Block.Preceq st.core.F
      (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.F := by
  simp only [Protocol.NamedAdmission.on_block_with]
  rw [admit_carried_F]
  exact process_block_core_F E hc cfg st B

/-- Either proposal outcome is monotone; no lookup-success premise is
required. -/
theorem propose_block_with_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    Block.Preceq st.core.F
      (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.F := by
  simp only [Protocol.NamedDuties.propose_block_with]
  cases Protocol.NamedActions.proposal_with gc .poolAndCarried E hc nd st with
  | none => exact Block.preceq_self _
  | some B => exact on_block_with_F .alsoCarried E hc cfg st B

private theorem goldfish_vote_with_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    (Protocol.goldfish_vote_with gc E hc nd st).1.F = st.F := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact Proofs.on_goldfish_vote_checked_F E st _
  · rfl

private theorem named_goldfish_vote_with_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.F = st.core.F := by
  simp only [Protocol.NamedDuties.goldfish_vote_with]
  exact goldfish_vote_with_F gc E hc nd st.core

private theorem confirmation_with_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.F = st.core.F := rfl

private theorem attest_with_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.F = st.core.F := by
  simp only [Protocol.NamedDuties.attest_with]
  exact admit_row_F hc st _

/-- Local restatement of `Proofs.NamedTick.tick_computed_duties` (not
imported: that file's cone loops back to this one through
`Proofs.Optimistic.TickBridges`/`Protocol.Main`). Byte-identical to the
`Availability/Monotone.lean` restatement, against the same Model-level
primitives. -/
private theorem named_tick_computed_duties (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    Protocol.NamedTick.tick gc E hc cfg nd st record t =
      let s := E.slotOf t
      let st0 := Protocol.NamedStore.setClock E st t
      let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
      let proposalDue := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
      let st1 := if proposalDue then proposed.1 else st0
      let emitted1 := if proposalDue then
        match proposed.2 with
        | none => []
        | some B => [NamedObject.block B]
      else []
      let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
      let voteDue := 0 < s ∧ t = Protocol.vote_time E s
      let st2 := if voteDue then voted.1 else st1
      let emitted2 := if voteDue then voted.2.toList.map NamedObject.gfVote else []
      let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
        Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
      if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        let attested := Protocol.NamedDuties.attest_with gc E hc nd st3 record
        (attested.1, attested.2.1, emitted1 ++ emitted2 ++ [NamedObject.attest attested.2.2])
      else (st3, record, emitted1 ++ emitted2) := by
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps,
    Protocol.NamedStore.setClock]
  unfold Protocol.TickScheduler.runWith.match_1 named_tick_computed_duties.match_1
  rfl

/-- The actual shared tick composes its concrete named duty calls in order. -/
private theorem tick_F (gc : Protocol.GradeContract V) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    Block.Preceq st.core.F
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.F := by
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time E s then
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
    Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  have h1 : Block.Preceq st.core.F st1.core.F := by
    dsimp only [st1]
    split_ifs
    · exact propose_block_with_F gc E hc cfg nd st0
    · exact Block.preceq_self _
  have h2 : st2.core.F = st1.core.F := by
    dsimp only [st2]
    split_ifs
    · exact named_goldfish_vote_with_F gc E hc nd st1
    · rfl
  have h3 : st3.core.F = st2.core.F := by
    dsimp only [st3]
    split_ifs
    · exact confirmation_with_F gc E hc st2 (s - 1)
    · rfl
  have hout : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1 =
      (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc E hc nd st3 record).1 else st3) := by
    rw [named_tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hout]
  split_ifs
  · rw [attest_with_F, h3, h2]
    exact h1
  · rw [h3, h2]
    exact h1

/-- The closed receipt dispatcher preserves or advances core finality. -/
private theorem receipt_F (S : Setup V) (st : Protocol.NamedStore V) (o : NamedObject V) :
    Block.Preceq st.core.F (NamedReceipt.process S st o).core.F := by
  cases o with
  | block B =>
      simp only [NamedReceipt.process]
      exact on_block_with_F .alsoCarried S.E S.hc S.cfg st B
  | gfVote u =>
      simp only [NamedReceipt.process]
      rw [Proofs.on_goldfish_vote_checked_F]
      exact Block.preceq_self _
  | attest a =>
      simp only [NamedReceipt.process]
      rw [admit_row_F]
      exact Block.preceq_self _

/-- Phase preparation and final cache clipping leave the actual returned
store intact. -/
private theorem node_tick_F (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    Block.Preceq n.st.core.F (NamedNode.tick S v n t).1.st.core.F :=
  tick_F (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
    S.E S.hc S.cfg (S.node v) n.st n.record t

/-- Delivery's cache clip and retained signing record do not change the
returned F. -/
private theorem node_process_F (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    Block.Preceq n.st.core.F (NamedNode.process S n o).st.core.F :=
  receipt_F S n.st o

/-- One world event moves the finalized root forward along its chain. -/
theorem step_F_mono
    (S : Setup V) (w : World V) (e : Event V) (v : V) :
    Block.Preceq (w v).st.core.F ((World.step S w e) v).st.core.F := by
  cases e with
  | tick u t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact node_tick_F S v (w v) t
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact Block.preceq_self _
  | deliver u o t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact node_process_F S (w v) o
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact Block.preceq_self _

/-- The finalized root is monotone between any two event prefixes. -/
theorem stateBefore_F_mono
    (S : Setup V) (rho : Run V) (v : V) {m n : Nat} (hmn : m ≤ n) :
    Block.Preceq (rho.stateBefore S m v).st.core.F
      (rho.stateBefore S n v).st.core.F := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => exact Block.preceq_self _
  | succ k ih =>
      have hIH := ih (Nat.le_add_right m k)
      have hstep : Block.Preceq
          (rho.stateBefore S (m + k) v).st.core.F
          (rho.stateBefore S (m + k + 1) v).st.core.F := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases he : rho.events[m + k]? with
        | none => exact Block.preceq_self _
        | some e =>
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            exact step_F_mono S _ e v
      exact Block.preceq_trans hIH (by simpa [Nat.add_assoc] using hstep)

end Protocol
end DecoupledConsensusModel

end
