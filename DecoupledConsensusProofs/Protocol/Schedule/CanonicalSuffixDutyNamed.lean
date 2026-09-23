module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone

@[expose] public section

/-! # Core-strength canonical suffix duty assembly -/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Post-GST counting and the candidate path complete the proposal duty under
core admissibility. -/
theorem CanonicalSuffixProposalStoreFacts.duty_core
    {S : Setup V} {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (h : CanonicalSuffixProposalStoreFacts S rho s B) :
    CanonicalProposalDutyAt S rho s B := by
  apply CanonicalProposalDutyAt.ofLocalFacts
    S rho s B h.run h.names h.validLate h.anchor
  · intro v hv C hanchorC hCne hCB
    exact confPath_of_candidate S (h.candidate v hv)
      C hanchorC hCne hCB
  · exact h.resolve
  · intro v hv u hus huHon huCommittee huEmit
    have hnamed := h.names u.val_index huHon huCommittee
    have hueq : u = ⟨u.val_index, s, B.erase.root⟩ :=
      Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed
        huEmit hnamed (by simpa only using hus)
    have harr : Proofs.Optimistic.HeadArrivesBefore
        (Proofs.Optimistic.confStore S rho v s).T
        (Proofs.Optimistic.confStore S rho v s).timestamp_block
        (Protocol.support_cutoff S.E s) u := by
      obtain ⟨hfind, hstamp⟩ :=
        h.resolve v hv B.erase
          ⟨u.val_index, huHon, huCommittee, ⟨B, rfl, h.run⟩, hnamed⟩
      refine ⟨B.erase, ?_, hstamp⟩
      rw [hueq]
      simpa only using hfind
    exact Proofs.HealingSurface.WeakGoldfish.canonicalSuffixHonestVoteCounted_core
      S adm hs hpost hhor v hv u hus huHon huEmit harr

#print axioms CanonicalSuffixProposalStoreFacts.duty_core

end Protocol
end DecoupledConsensusModel

end
