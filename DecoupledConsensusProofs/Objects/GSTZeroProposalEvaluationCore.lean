module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.GSTZeroProposalEvaluation

@[expose] public section

/-! # Core-strength GST-zero honest-proposal evaluation -/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `VoteStoresExtend` makes every honest committee vote name the exact bound
proposal `B`; only the named schedule interface is needed. -/
theorem honestVotesName_of_voteStoresExtend_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {B : NamedBlock V}
    (hstores : VoteStoresExtend S rho s B) :
    Proofs.HealingSurface.NamedHonestVotesName S rho s B.erase :=
  Proofs.Optimistic.honestVotesName_of_extends S rho s B
    (Proofs.Optimistic.voteTickExtends_of_extends S
      adm.toNamedScheduleWellFormed hs hvoteHor hstores)

#print axioms honestVotesName_of_voteStoresExtend_core

end Protocol
end DecoupledConsensusModel

end
