module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4A1Emission
public import DecoupledConsensusProofs.Protocol.Grades.W4A2GSTZeroLiveConfirmation
public import DecoupledConsensusProofs.Execution.GSTZeroSafetyClosedNamed
public import DecoupledConsensusProofs.Execution.RecoveryWindowClosure
public import DecoupledConsensusInternal.Legacy.Liveness

@[expose] public section

/-!
# W4 B1: the public honest-proposal-confirmation field

`Statements.HonestProposalConfirmation S`. GST zero uses the shared emission
bridge (A1), the exact named live confirmation (A2), and the available
`gstZeroSafety`'s `latestAtProposal` field for the matching `latest_confirmed`
half. After GST, `boundedSafetyRecovery_closed` supplies the phase-shift
safety package at every continuation; its `honestProposalLive` and
`userConfirmation.proposals` fields give the two store equalities. See the
liveness audit `the proof record` §5 B1.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The exact public honest-proposal-confirmation field. -/
theorem honestProposalConfirmation (S : Setup V) :
    Statements.HonestProposalConfirmation S := by
  constructor
  · intro rho h s hs hhor hp
    obtain ⟨P, hP, hemit⟩ := proposedBlock_emitted_of_core S h.core hs hp hhor
    have hlive := WeakGenesis.honestProposal_liveConfirmed_named_of_gstZero
      S h hs hhor hp hP
    have hsafe := gstZeroSafety S h.core h.committees h.gstZero h.windows
    obtain ⟨B', hB', hlatest⟩ := hsafe.latestAtProposal s hs hhor hp
    have hPB' : P = B' := Option.some.inj (hP.symm.trans hB')
    refine ⟨P, hP, hemit, ?_⟩
    intro v hv
    refine ⟨hlive v hv, ?_⟩
    rw [hPB']
    exact hlatest v hv
  · intro rho rGST gap extra n h
    obtain ⟨m, hlo, hhi, hend, P, hP, hcontinue⟩ :=
      boundedSafetyRecovery_closed S rho rGST gap extra n h
    refine ⟨m, hlo, hhi, hend, ?_⟩
    intro rho' hw s hs hhor hp
    have hsafe := hcontinue rho' hw
    have hs0 : 0 < s := (Nat.zero_le _).trans_lt hs
    obtain ⟨Q, hQ, hemit⟩ := proposedBlock_emitted_of_core S hw.core hs0 hp hhor
    obtain ⟨B1, hB1, hlive⟩ := hsafe.honestProposalLive s hs hhor hp
    obtain ⟨B2, hB2, hlatest, -⟩ := hsafe.userConfirmation.proposals s hs hhor hp
    have hQB1 : Q = B1 := Option.some.inj (hQ.symm.trans hB1)
    have hQB2 : Q = B2 := Option.some.inj (hQ.symm.trans hB2)
    refine ⟨Q, hQ, hemit, ?_⟩
    intro v hv
    refine ⟨?_, ?_⟩
    · rw [hQB1]; exact hlive v hv
    · rw [hQB2]; exact hlatest v hv

#print axioms honestProposalConfirmation

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
