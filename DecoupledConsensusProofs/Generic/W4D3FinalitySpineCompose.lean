module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.W4D2OpeningCarrierFinality
public import DecoupledConsensusProofs.Execution.W4D3FinalityAfterGST
public import DecoupledConsensusProofs.Execution.W4RecoverySpine
public import DecoupledConsensusProofs.Execution.W4FinalityProjection
public import DecoupledConsensusProofs.Protocol.Grades.W4FKChainCompose
public import DecoupledConsensusProofs.Execution.W4FKChainSpine
public import DecoupledConsensusProofs.Execution.W4FKChainAdvanceFold
public import DecoupledConsensusProofs.Protocol.ChainState.W4CarrierFirstHalf

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # W4 branches d2: the finality spine, D1 through D3

This leaf is the selection twin of earlier
`OpeningCarrierAssemblyRun.lean:23-109`
(`finalityFrom_of_openingCarrierRecurrence` and
`uniformCanonicalRecoveryWithFinality_after_GST_openingCarrierRecurrence`). It
takes the corresponding branch's recovery spine, runs 's finality producer at every
`start` above the recovery round, projects the result through the two
finality adapters, and packages the pair as the `UniformRecoveryFinalityPin`
that  turns into `FinalityAfterGSTPin` and the corresponding branch turns into the two
public finality fields.

Everything between the spine and the public fields is proved here. The
residual is exactly six hypotheses: the corresponding branch's own record residual, D2's
four carrier-side pins, and the two finality projections
`recurringFinalityCarrierFrom_of_commonFinalityAboveFrontier`
(`CommonFinalityFrontierRun.lean:33`) and
`honestProposalFinalityFrom_of_commonFinalityAboveFrontier`
(`HonestProposalFinalityRun.lean:144`), both of which are blocked declarations
in the selection: the first waits for `commonFinalizedHeight_lt_honestHMaxAt` and
`preceq_of_commonFinalityAdvance`, the second for
`Protocol.honestProposalLifecycleFrom_of_canonicalSuffixExecution`. None of
the three has a live declaration anywhere outside `the compatibility layer`.

The deadline arithmetic, the phase lag and the monotone deadline are live and
are used directly, exactly as earlier's assembly uses them. -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]









/-- Pin for `recurringFinalityCarrierFrom_of_commonFinalityAboveFrontier`
(`CommonFinalityFrontierRun.lean:33`, blocked). -/
def W4RecurringProjectionPin (S : Setup V) : Prop :=
  ∀ (rho : Run V) (q lag deadline : Round),
    Admissible S rho → BelowOneThird S rho.honest →
    lag ≤ deadline →
    (∀ start : Round, q ≤ start → S.a (start + lag) ≤ rho.horizon →
      ∃ H : Height, honestHMaxAt S rho (S.a start) < H ∧
        AlreadyCommonFinalizedAtOrAbove S rho q start (start + lag) H) →
    RecurringFinalityCarrierFrom S rho q (healingBoundaryTime S q) deadline


/-- Pin for `honestProposalFinalityFrom_of_commonFinalityAboveFrontier`
(`HonestProposalFinalityRun.lean:144`, blocked). -/
def W4ProposalProjectionPin (S : Setup V) : Prop :=
  ∀ (rho : Run V) (q deadline : Round),
    Admissible S rho → HonestCommittees S rho.honest →
    CanonicalSuffixFrom S rho (healingBoundaryTime S q) →
    (∀ s : Slot, 0 < s →
      healingBoundaryTime S q < Protocol.proposal_time S.E s →
      S.E.proposer s ∈ rho.honest →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
        Protocol.CanonicalProposalDutyAt S rho s B) →
    (∀ start : Round, q ≤ start → S.a (start + deadline) ≤ rho.horizon →
      ∃ H : Height, honestHMaxAt S rho (S.a start) < H ∧
        AlreadyCommonFinalizedAtOrAbove S rho q start (start + deadline) H) →
    HonestProposalFinalityFrom S rho q deadline


/--  consumer: the corresponding branch available the recurring projection
(`W4FinalityProjectionRun.lean:200`, committed at be015a79) with exactly the
pinned statement, so pin 6 is discharged. -/
theorem w4RecurringProjectionPin_landed (S : Setup V) :
    W4RecurringProjectionPin S :=
  fun _ _ _ _ adm hbot hlag hproduce =>
    recurringFinalityCarrierFrom_of_commonFinalityAboveFrontier S adm hbot hlag
      hproduce


/--  consumer: the corresponding branch available the honest-proposal projection
(`W4FinalityProjectionRun.lean:379`, same commit), so pin 7 is discharged. -/
theorem w4ProposalProjectionPin_landed (S : Setup V) :
    W4ProposalProjectionPin S :=
  fun _ _ _ adm hcom hsuffix hdutyAt hproduce =>
    honestProposalFinalityFrom_of_commonFinalityAboveFrontier S adm hcom
      hsuffix hdutyAt hproduce






/-! ## Axiom roster. Every public theorem of this file. Each must report a
subset of `propext`, `Classical.choice`, `Quot.sound` and nothing else. A
theorem reporting NO axioms is hollow: it means an import's olean lacked a name
and Lean recovered silently, which still exits zero. -/

#print axioms w4RecurringProjectionPin_landed
#print axioms w4ProposalProjectionPin_landed


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
