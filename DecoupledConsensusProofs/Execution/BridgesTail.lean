module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Execution.ReceiptCalls
public import DecoupledConsensusProofs.Execution.BridgesCore

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace Bridges

open Execution
open Execution.NamedReceiptCalls
open NamedReceiptCallsBase

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Copied from `Proofs.NamedReceiptCalls.lean` (private there; needed for
`on_tick_emit_T_mem` and unreachable from here by import). -/

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

private theorem block_bodies (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (C : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st C).bodies =
      (Protocol.NamedStore.process_block_core E hc cfg st C).bodies := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact rows_bodies hc _ C.attestations
  · rfl

private theorem new_body_eq_input (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (C B : NamedBlock V)
    (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st C).bodies) :
    B = C := by
  rw [block_bodies] at hpost
  unfold Protocol.NamedStore.process_block_core at hpost
  split_ifs at hpost <;> first
    | exact False.elim (hpre hpost)
    | (dsimp only at hpost
       unfold Protocol.NamedStore.commitBlock at hpost
       split_ifs at hpost
       · exact (Finset.mem_insert.mp hpost).resolve_right hpre
       · exact False.elim (hpre hpost))

private theorem attest_bodies (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.bodies = st.bodies :=
  NamedAdmission.admit_row_bodies hc st _

private theorem tick_new_body_origin (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (B : NamedBlock V) (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.bodies) :
    NamedObject.block B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 := by
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
  have hout := NamedTick.tick_computed_duties gc E hc cfg nd st record t
  change Protocol.NamedTick.tick gc E hc cfg nd st record t =
    (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
      let a := Protocol.NamedDuties.attest_with gc E hc nd st3 record
      (a.1, a.2.1, emitted1 ++ emitted2 ++ [.attest a.2.2])
    else (st3, record, emitted1 ++ emitted2)) at hout
  have hbodies : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.bodies = st1.bodies := by
    rw [hout]
    split_ifs
    · rw [attest_bodies, h32]
    · exact h32
  rw [hbodies] at hpost
  have hemit : ∀ o ∈ emitted1,
      o ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 := by
    intro o ho
    rw [hout]
    split_ifs <;> simp [List.mem_append, ho]
  by_cases hd : due
  · cases hp : Protocol.NamedActions.proposal_with gc .poolAndCarried E hc nd st0 with
    | none =>
      have he := NamedDuties.propose_none gc E hc cfg nd st0 hp
      exact False.elim (hpre (by simpa only [st1, proposed, if_pos hd, he] using hpost))
    | some C =>
      have he := NamedDuties.propose_some gc E hc cfg nd st0 C hp
      have hC : B ∈
          (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st0 C).bodies := by
        simpa only [st1, proposed, if_pos hd, he] using hpost
      have hBC := new_body_eq_input E hc cfg st0 C B hpre hC
      subst B
      apply hemit (.block C)
      simp only [emitted1, proposed, if_pos hd, he, List.mem_singleton]
  · exact False.elim (hpre (by simpa only [st1, if_neg hd] using hpost))

/-! ## The two theorems moved up from `Proofs.Bridges.lean`. -/

/-- The tick's tree grows by at most the block the tick emits
(PROTOCOL.md#the-complete-protocol). Branches 3–5 leave the store's bodies alone,
so the proposal branch is the only one that can add a block, and it emits
exactly the block it adds. -/
theorem on_tick_emit_T_mem (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    {B : NamedBlock V} (hB : B ∈ (NamedNode.tick S v n t).1.st.bodies) :
    B ∈ n.st.bodies ∨ Object.block B ∈ (NamedNode.tick S v n t).2 := by
  by_cases hpre : B ∈ n.st.bodies
  · exact Or.inl hpre
  · refine Or.inr ?_
    exact tick_new_body_origin
      (DecoupledConsensusModel.Protocol.frameContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v) n.st n.record t B hpre hB

end Bridges
end Proofs
end DecoupledConsensusModel

end
