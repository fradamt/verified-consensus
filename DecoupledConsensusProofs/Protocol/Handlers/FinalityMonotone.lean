module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Execution.Node
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants
public import DecoupledConsensusProofs.Protocol.Schedule.NamedTick

@[expose] public section

/-! Core finality advances through the shared handler guard. These proofs
use the actual named operations without a runtime-erasure, coherence, root
membership, record, cache, source, delay or participation premise. -/
namespace DecoupledConsensusModel.Proofs.NamedFinalityMonotone
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

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
       have h := update_finality_F
         (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored)
         ((B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored).σ B)
       simpa only [foldl_on_goldfish_vote_checked_F E] using h)

private theorem checked_using_F (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V) :
    Block.Preceq st.F
      (Protocol.on_block_checked_using
        (fun current => Protocol.on_block_using E current B buildState) hc st B).F := by
  unfold Protocol.on_block_checked_using
  split_ifs
  · exact on_block_using_F E st B buildState
  · exact Block.preceq_self _

/-- Missing named parents preserve F; successful checks use the same shared guard. -/
theorem process_block_core_F (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    Block.Preceq st.core.F
      (Protocol.NamedStore.process_block_core E hc cfg st B).core.F := by
  by_cases hp : B.parent ∈ st.bodies
  · simp only [Protocol.NamedStore.process_block_core, if_neg (not_not_intro hp),
      NamedStore.commit_core]
    exact checked_using_F E hc st.core B.erase
      (fun parentState => Protocol.named_transition E cfg parentState B)
  · simp only [Protocol.NamedStore.process_block_core, if_pos hp]
    exact Block.preceq_self _

omit [Fintype V] in
private theorem admit_row_F (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).core.F = st.core.F := by
  rw [NamedAdmission.admit_row_core]
  exact on_sg_vote_F hc st.core row.erase

omit [Fintype V] in
private theorem admit_rows_F (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.F = st.core.F := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
    change (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st row) rows).core.F = st.core.F
    rw [ih, admit_row_F]

omit [Fintype V] in
private theorem admit_carried_F (admission : Protocol.CarriedAdmission)
    (hc : Protocol.HealConfig) (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission hc before after B).core.F = after.core.F := by
  cases admission with
  | alsoCarried =>
    unfold Protocol.NamedAdmission.admit_carried
    split_ifs
    · exact admit_rows_F hc after B.attestations
    · rfl

/-- The actual F1 tail preserves the core handler's finality advance. -/
theorem on_block_with_F (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    Block.Preceq st.core.F
      (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.F := by
  unfold Protocol.NamedAdmission.on_block_with
  rw [admit_carried_F]
  exact process_block_core_F E hc cfg st B

/-- Either proposal outcome is monotone; no lookup-success premise is required. -/
theorem propose_block_with_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    Block.Preceq st.core.F
      (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.F := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact Block.preceq_self _
  · exact on_block_with_F .alsoCarried E hc cfg st _

private theorem goldfish_vote_with_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.F = st.core.F := by
  rw [NamedDuties.goldfish_vote_core]
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_F E st.core _
  · rfl

private theorem confirmation_with_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.F = st.core.F := rfl

private theorem attest_with_F (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.F = st.core.F := by
  rw [NamedDuties.attest_core]
  exact on_sg_vote_F hc st.core _

/-- The actual shared tick composes its concrete named duty calls in order. -/
theorem tick_F (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
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
    · exact goldfish_vote_with_F gc E hc nd st1
    · rfl
  have h3 : st3.core.F = st2.core.F := by
    dsimp only [st3]
    split_ifs
    · exact confirmation_with_F gc E hc st2 (s - 1)
    · rfl
  have hout : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1 =
      (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc E hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hout]
  split_ifs
  · rw [attest_with_F, h3, h2]
    exact h1
  · rw [h3, h2]
    exact h1

/-- The closed receipt dispatcher preserves or advances core finality. -/
theorem receipt_F (S : Setup V) (st : Protocol.NamedStore V) (o : NamedObject V) :
    Block.Preceq st.core.F (NamedReceipt.process S st o).core.F := by
  cases o with
  | block B => exact on_block_with_F .alsoCarried S.E S.hc S.cfg st B
  | gfVote u =>
    change Block.Preceq st.core.F (Protocol.on_goldfish_vote_checked S.E st.core u).F
    rw [on_goldfish_vote_checked_F]
    exact Block.preceq_self _
  | attest row =>
    change Block.Preceq st.core.F (Protocol.NamedAdmission.admit_row S.hc st row).core.F
    rw [admit_row_F]
    exact Block.preceq_self _

/-- Phase preparation and final cache clipping leave the actual returned store intact. -/
theorem node_tick_F (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    Block.Preceq n.st.core.F (NamedNode.tick S v n t).1.st.core.F := by
  exact tick_F (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v) n.st n.record t

/-- Delivery's cache clip and retained signing record do not change the returned F. -/
theorem node_process_F (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    Block.Preceq n.st.core.F (NamedNode.process S n o).st.core.F := by
  exact receipt_F S n.st o

#print axioms on_block_using_F
#print axioms process_block_core_F
#print axioms on_block_with_F
#print axioms propose_block_with_F
#print axioms tick_F
#print axioms receipt_F
#print axioms node_tick_F
#print axioms node_process_F
end DecoupledConsensusModel.Proofs.NamedFinalityMonotone

end
