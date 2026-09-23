module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.MovingChainBandCover
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainFold
public import DecoupledConsensusProofs.Protocol.ValidatorClient.CanonicalRegimeFirstVote
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainFloorBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.SeedRelativeGrade
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Protocol.ChainState.RowFreshness
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainBatch
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBase
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainCeiling
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainRoundRead
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainNextEntry
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Execution.WeakReadDirectedAnchors
public import DecoupledConsensusProofs.Protocol.Handlers.RelayGuards
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.HeightProgressClosureg0ClearAtAction
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryConeConfirmation

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]








/-! ## 2. `_of_selectedG2_preceq_honestPreviousCarrier`

The pin says the selected grade-2 block of an honest round-`(k+1)` action read
lies below some honest node's exact round-`k` SG carrier.

The route is earlier's `G2 → honest supporter → that supporter's previous-round
carrier`, adapted to the prepared selector. The prepared `Q2` is not itself
graded at the reader's store: it is the ACTIVE CLIPPED PREFIX of the round's
frozen grade-2 root, and the root is what the phase-domain read grades
(`namedG2At_freezeRoot_of_nodeQ2`). The graded root then has an honest
round-`k` voter below which it sits
(`relativeGrade_has_roundCarrier`), and that voter is honest
(`Proofs.NamedOutageInputs.honestRoundVoters_iff`). The grade-forming majority is
derived here from `BelowOneThird`, so the only residual input is the relative
carrier window of round `k` in phase `g2`. -/

/-- **`_of_selectedG2_preceq_honestPreviousCarrier` at one round**, from the
round's relative carrier window. -/
theorem selectedG2_preceq_honestPreviousCarrier_of_carrierWindow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {k : Round}
    (hwindow : RelativeCarrierWindowAt S rho k DecoupledConsensusModel.Protocol.Phase.g2)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc (k + 1) DecoupledConsensusModel.Protocol.Phase.g2 ≤
      rho.horizon) :
    ∀ v ∈ rho.honest, ∀ A : Block V,
      PhaseGrades.nodeQ2 S (actionReadAt S rho v (k + 1)) (k + 1) = some A →
      ∃ u ∈ rho.honest, Block.Preceq A (actionSGBlockAt S rho u k) := by
  intro v hv A hA
  have hmaj : Internal.NamedOutageEntry.GradeFormingMajority S rho (k + 1) :=
    gradeFormingMajority_of_admissible_belowOneThird S adm hfb (Nat.succ_pos k) hhor
  obtain ⟨raw, hgrade, hAraw⟩ :=
    namedG2At_freezeRoot_of_nodeQ2 S adm.toNamedAdmissibleCore hA
  have hgrade' : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (k + 1) DecoupledConsensusModel.Protocol.Phase.g2)
          v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (k + 1) DecoupledConsensusModel.Protocol.Phase.g2)
          v).st.core.F
      S.hc.η_SG (k + 1)
      (DecoupledConsensusModel.Protocol.early S.E S.hc (k + 1) DecoupledConsensusModel.Protocol.Phase.g2)
      (DecoupledConsensusModel.Protocol.late S.E S.hc (k + 1) DecoupledConsensusModel.Protocol.Phase.g2) raw = true := by
    simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade] using hgrade
  obtain ⟨u, hu, hpre⟩ :=
    relativeGrade_has_roundCarrier S adm.toNamedAdmissibleCore hwindow hmaj hv hgrade'
  exact ⟨u, ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mp hu).1,
    Block.preceq_trans hAraw hpre⟩


/-! ## 3. `_of_successorHeightSource`

The pin says: the height an honest node writes in its round-`(q+1)` action row
has an exact named FG source that is a run block, sits below the fold endpoint
at the opening of a later round, and carries that very height.

`MovingSlotFoldAt.heightSource_preceq_endpoint_of_genuine`
(`PostRecoveryLivenessSourceRun.lean:287`) is live and proves exactly this at a
fold slot `e` the action precedes. The two facts it needs beyond the pin's own
hypotheses are the fold range (`MovingSlotFoldCovers`) and the schedule fact
that the round-`(q+1)` action is strictly before the opening proposal of a
round above `q + 1`; both are supplied here. Its own residual, the prepared
form of `MovingFrontierChainState.genuineConfirmations` at the action's tick
index, is relayed unchanged.

The pin is stated WITHOUT a guard on its round `r`; as written it also claims
the endpoint bound at rounds at or below `q + 1`, where the fold has not run.
The guarded form below is what every call site of the two record exports uses.
-/



/-! ## 4. `_of_preparedBoundaryOutput` and `_of_preparedSuccessorConfirmation`

Both pins say that an honest node's slot confirmation OUTPUT at a round opening
is a genuine confirmation under that node's own prepared grade contract — the
retained FG-root fallback did not fire — and, at the handoff round, that the
output is below the handoff block.

The genuineness half has a live producer,
`MovingSlotPreEntry.confOutcome_atPrev_of_ceiling_named`
(`MovingChainCeilingRun.lean:117`), which reads the node's cache through
`confirmationInputRead` at the opening slot; the pins read it through
`NamedActionReads.confirmationReadAt` at the round action. Those are the same
read, which the bridge below records once.

The upper bound at the handoff round is NOT part of that producer: in
`MovingChainCeilingRun` it comes from the moving frontier state's own
`genuinePreceq` field at the boundary endpoint, which is why it is carried here
as an explicit input. -/




/-! ## 5. The floor assembler with the named-band pin removed

Because filtered-tree membership already carries the viability witness, the
band input of the floor assembler can be the protocol fact "the fold endpoint
is a candidate at every honest reader's round action" instead of the pinned
`_of_namedBand`. The `derived_state` reading survives in exactly one place,
the record's own `frontierBand` field, which this assembler still takes as
`_of_actionFrontier_sub_one_le_endpointHeight`; nothing else in the floor
record mentions the erased derivation. -/











/-! ## Axiom roster (audit): every public theorem of this leaf. -/

#print axioms selectedG2_preceq_honestPreviousCarrier_of_carrierWindow

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
