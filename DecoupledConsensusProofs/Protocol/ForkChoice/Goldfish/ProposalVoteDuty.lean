module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalTransportCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalCanonicality
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.VoteStoreExtends

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## No honest round action between proposal and vote -/

/-- A round action before slot `s`'s vote instant is already before slot
`s`'s proposal instant. Round actions are support-cutoff instants, and the
slot schedule has no support cutoff in the open proposal-to-vote interval. -/
theorem action_time_lt_proposal_of_lt_vote
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.vote_time S.E s) :
    S.a r < Protocol.proposal_time S.E s := by
  change S.hc.a S.E.Δ r < Protocol.vote_time S.E s at h
  change S.hc.a S.E.Δ r < Protocol.proposal_time S.E s
  rw [Protocol.a_eq_support_cutoff_succ S.hc S.E r] at h ⊢
  exact support_cutoff_lt_vote_time_imp_lt_proposal_time S.E h

/-- Proposal time precedes the same slot's vote time. -/
theorem proposal_time_lt_vote_time (E : Env V) (s : Slot) :
    Protocol.proposal_time E s < Protocol.vote_time E s := by
  unfold Protocol.vote_time
  exact Int.lt_add_of_pos_right _ E.Δ_pos


/-- If every member of a GHOST tree is its anchor, the walk stays at that
anchor. -/
theorem ghost_eq_anchor_of_all_mem_eq
    (anchor : Block V) (tree : Finset (Block V))
    (score : Block V → Nat) (eligible : Block V → Bool)
    (hall : ∀ C ∈ tree, C = anchor) :
    Protocol.ghost anchor tree score eligible = anchor := by
  have hnone : Protocol.ghost_step tree score eligible anchor = none :=
    ghost_step_none (by
      intro C hC hparent
      rw [hall C hC] at hparent
      exfalso
      have hdepth := depth_of_parent? hparent
      omega)
  unfold Protocol.ghost
  cases tree.card with
  | zero => rfl
  | succ n =>
      simp only [Protocol.ghost_walk]
      rw [hnone]

#print axioms action_time_lt_proposal_of_lt_vote
#print axioms ghost_eq_anchor_of_all_mem_eq

end Protocol
end DecoupledConsensusModel

end
