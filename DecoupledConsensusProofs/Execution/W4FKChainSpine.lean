module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.W4FKChainCommonFinalized
public import DecoupledConsensusProofs.Execution.W4FKChainStoreFinality

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # The finality-chain spine over its two residuals

One theorem recording what the corresponding branch's carrier-chain pin now rests on. The
finality kernel's own content is proved; what is left are two facts that belong
to other layers:

* `W4SecondCarrierActionHeadPin` — the carrier's honest action heads are its
  slot-`+1` proposal. Owned by the corresponding branch, which pins the same fact.
* `W4ProcessedFinalityAdvancePin` — an honest reader's finalized block
  dominates the candidate checkpoint of every named body it holds. A store
  invariant over `NamedReceiptCalls`; see the Open in
  `W4FKChainStoreFinalityRun.lean`.
-/

/-! ##: the same over the execution record's fields

The two composers above read the execution record only through
`canonicalSuffixFrom` (the proposal link and the carrier parent equalities) and
`duty` (the live-confirmation half). Both fields are shared by name with
`CanonicalSuffixExecutionPrepared`, so the field-level forms below serve either
record, and the record-level forms above are their wrappers. -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol

variable {V : Type} [DecidableEq V] [Fintype V]






theorem w4CarrierChainFinalityPin_of_fields
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    (hcom : HonestCommittees S rho.honest) {q0 : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hduty : ∀ s : Slot, 0 < s →
      healingBoundaryTime S q0 < Protocol.proposal_time S.E s →
      S.E.proposer s ∈ rho.honest →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
        Protocol.CanonicalProposalDutyAt S rho s B)
    (hheadPin : ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      W4SecondCarrierActionHeadPin S rho r)
    (hadvance : W4ProcessedFinalityAdvancePin S rho) :
    W4CarrierChainFinalityPin S rho q0 :=
  w4CarrierChainFinalityPin_of_pins_of_suffix S adm hbot hsuffix hheadPin
    (w4CommonFinalityAtConfirmationPin_of_duty S adm hcom hduty hadvance)


#print axioms w4CarrierChainFinalityPin_of_fields

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
