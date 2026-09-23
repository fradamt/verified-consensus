module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Execution.Node
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership

@[expose] public section

/-! Exact named markers, dispatch and local invariant preservation.
The input invariants have checked Proofs.NamedStoreRoots.invariant_initial and
Proofs.NamedConfirmationMembership.invariant_initial producers. Their eventual
preservation over an event run is a separate induction. -/
namespace DecoupledConsensusModel.Proofs.NamedReceipt
open Execution
variable {V : Type} [DecidableEq V]

theorem depsPresent_block_iff (st : Protocol.NamedStore V) (B : NamedBlock V) :
    Execution.NamedReceipt.depsPresent st (.block B) = true ↔ B.parent ∈ st.bodies := by
  simp only [Execution.NamedReceipt.depsPresent, decide_eq_true_eq]










/-- Both retained confirmation values remain members of the processed tree. -/
theorem confirmation_invariant_process [Fintype V] (S : Setup V) (st : Protocol.NamedStore V)
    (o : NamedObject V) (h : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg st) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (Execution.NamedReceipt.process S st o) := by
  cases o with
  | block B =>
    exact Proofs.NamedConfirmationMembership.invariant_on_block_with .alsoCarried S.E S.hc S.cfg st B h
  | gfVote u =>
    dsimp only [Execution.NamedReceipt.process,
      Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
    split_ifs <;> exact h
  | attest a => exact Proofs.NamedConfirmationMembership.invariant_admit_row S.E S.hc S.cfg st a h

/-- Processing retains the receiver clock and slot used by receipt stamps. -/
theorem process_clock [Fintype V] (S : Setup V) (st : Protocol.NamedStore V) (o : NamedObject V) :
    (Execution.NamedReceipt.process S st o).core.t = st.core.t ∧
      (Execution.NamedReceipt.process S st o).core.s = st.core.s := by
  cases o with
  | block B => exact NamedAdmission.on_block_clock .alsoCarried S.E S.hc S.cfg st B
  | gfVote u =>
    exact ⟨on_goldfish_vote_checked_time S.E st.core u,
      Proofs.Optimistic.on_goldfish_vote_checked_slot S.E st.core u⟩
  | attest a =>
    have h := NamedAdmission.admit_row_fixed_fields S.hc st a
    exact ⟨h.1, h.2.1⟩

#print axioms depsPresent_block_iff
#print axioms confirmation_invariant_process
#print axioms process_clock
end DecoupledConsensusModel.Proofs.NamedReceipt

end
