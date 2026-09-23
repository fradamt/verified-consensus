module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroReorgResilienceCoreNamed

@[expose] public section

/-! # Honest proposal read safety from weak genesis -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named proposal/read adapter for the reorganization surface. -/
theorem honestProposalReadSafety_of_reorg
    {S : Setup V} {rho : Run V} {s : Slot}
    (h : HonestProposalReorgResilience S rho s) : HonestProposalReadSafety S rho s := by
  constructor
  · intro B hB k hsk hhor hprop
    exact h.proposal_calls hsk hhor hprop B hB
  · intro B hB k hsk hhor v hv
    exact h.vote_calls hsk hhor B hB hv
  · intro B hB r hsr hhor v hv
    have hcut : Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) ≤
        rho.horizon := by
      rw [← Protocol.a_eq_support_cutoff_succ S.hc S.E r]
      exact hhor
    exact h.action_calls B hB hsr hcut hv (r := r)
      (Protocol.a_eq_support_cutoff_succ S.hc S.E r)

#print axioms honestProposalReadSafety_of_reorg

namespace WeakGenesis

/-- Every positive honest proposal is safe at all covered prepared reads. -/
theorem honestProposalReadSafety_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    ∀ s, 0 < s → Protocol.confirmation_time S.E s ≤ rho.horizon →
      S.E.proposer s ∈ rho.honest → HonestProposalReadSafety S rho s := by
  intro s hs hhor hprop
  exact honestProposalReadSafety_of_reorg
    (Protocol.honestProposal_reorgResilience_gstZero_core
      S h hs hhor hprop)

#print axioms honestProposalReadSafety_of_weakGenesis_named

end WeakGenesis

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
