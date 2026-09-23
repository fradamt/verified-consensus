module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PrefixThroughHistory
public import DecoupledConsensusProofs.Protocol.Handlers.PrefixCarrier
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.ReceiptCallsGF
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardProofsTime
open Execution Execution.NamedReceiptCalls Protocol
open Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]










private theorem gf_state_fields (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    let out := Protocol.on_goldfish_vote_checked E st u
    out.σ = st.σ ∧ out.F = st.F := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem gf_fold_state_fields (E : Env V) (st : Protocol.Store V)
    (votes : List (GoldfishVote V)) :
    let out := votes.foldl (Protocol.on_goldfish_vote_checked E) st
    out.σ = st.σ ∧ out.F = st.F := by
  induction votes generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons u votes ih =>
    have rest := ih (Protocol.on_goldfish_vote_checked E st u)
    have one := gf_state_fields E st u
    exact ⟨rest.1.trans one.1, rest.2.trans one.2⟩

theorem fresh_receipt_derived_and_admitted
    (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg before)
    (hnew : B.erase ∉ before.core.T)
    (hpost : B.erase ∈ (postCore S before B).core.T) :
    let stored : Protocol.Store V := { before.core with
      σ := fun X => if X = B.erase then
        named_transition S.E S.cfg (before.core.σ B.erase.parent) B
        else before.core.σ X
      T := insert B.erase before.core.T
      timestamp_block := fun X => if X = B.erase then
        some (before.core.t : Stamp) else before.core.timestamp_block X }
    let U := B.gf_votes.foldl (Protocol.on_goldfish_vote_checked S.E) stored
    U.σ B.erase = derive_named S.E S.cfg B ∧
      Block.Preceq U.F B.erase := by
  let stored : Protocol.Store V := { before.core with
    σ := fun X => if X = B.erase then
      named_transition S.E S.cfg (before.core.σ B.erase.parent) B
      else before.core.σ X
    T := insert B.erase before.core.T
    timestamp_block := fun X => if X = B.erase then
      some (before.core.t : Stamp) else before.core.timestamp_block X }
  let U := B.gf_votes.foldl (Protocol.on_goldfish_vote_checked S.E) stored
  change U.σ B.erase = derive_named S.E S.cfg B ∧ Block.Preceq U.F B.erase
  have hp : B.parent ∈ before.bodies := by
    by_contra hn
    have hsame : (postCore S before B).core = before.core := by
      simp only [postCore, Protocol.NamedStore.process_block_core, if_pos hn]
    exact hnew (hsame ▸ hpost)
  have hne : B ≠ NamedBlock.genesis := by
    intro heq
    subst B
    apply hnew
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hcoh.2.2.1.1
  have hadmit : Block.Preceq before.core.F B.erase := by
    by_contra hn
    have hfalse : Block.preceq before.core.F B.erase = false :=
      Bool.eq_false_of_not_eq_true hn
    have hreject : Protocol.on_block_using S.E before.core B.erase
        (fun parentState => named_transition S.E S.cfg parentState B) = before.core := by
      simp [Protocol.on_block_using, hfalse]
    have hsame : (postCore S before B).core = before.core := by
      simp only [postCore, Protocol.NamedStore.process_block_core,
        if_neg (not_not_intro hp), NamedStore.commit_core,
        Protocol.on_block_checked_using]
      split_ifs
      · exact hreject
      · rfl
    exact hnew (hsame ▸ hpost)
  have fields := gf_fold_state_fields S.E stored B.gf_votes
  constructor
  · change U.σ B.erase = _
    rw [fields.1]
    change (if B.erase = B.erase then
      named_transition S.E S.cfg (before.core.σ B.erase.parent) B
      else before.core.σ B.erase) = _
    rw [if_pos rfl, Proofs.NamedWire.erase_parent, hcoh.2.2.2.2 B.parent hp]
    exact (BlockProcessingDefaults.derive_named_of_not_genesis S.E S.cfg B hne).symm
  · change Block.Preceq U.F B.erase
    rw [fields.2]
    exact hadmit



#print axioms fresh_receipt_derived_and_admitted
end DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardProofsTime

end
