module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4FKChainSpine
public import DecoupledConsensusProofs.Protocol.ChainState.W4CarrierFirstHalf

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-! ## The round-local prepared action-head adapter -/

/-- The support cutoff of the carrier's `+1` slot is in the round horizon. -/
private theorem w4cfs_supportCutoff_plusOne_le_horizon
    (S : Setup V) {rho : Run V} {q0 r : Round}
    (hround : CanonicalRegimeRoundAt S rho q0 r) :
    Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) ≤ rho.horizon := by
  refine le_trans ?_ hround.inHorizon
  rw [Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono S.E
    (Nat.add_le_add_right (Nat.le_add_right (S.hc.opening_slot r) 2) 1)

/-- Build the action-head pin from a frame whose per-round callback retains the
moving carrier record and the previous-action post-GST bound. -/
theorem w4CarrierActionHeadPin_of_frame_inputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpostGST : S.E.t_GST ≤ S.a rGST)
    {q0 : Round}
    (hgst : ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r + 1))
    (hframe : ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      ∃ C End : Block V,
        MovingChainAtCarrierFor S rho q0 r C End ∧
        S.E.t_GST ≤ S.a (r - 1) ∧
        S.hc.opening_slot
            (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
          S.hc.opening_slot r + 1) :
    ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      W4SecondCarrierActionHeadPin S rho r := by
  intro r hround
  obtain ⟨C, End, hchain, hpostPrev, hdeadline⟩ := hframe r hround
  exact w4CarrierActionHeadPin_pinFree S adm hcom hbelow hrec hdelay hpostGST
    hround hchain hpostPrev hdeadline (hgst r hround)
    (w4cfs_supportCutoff_plusOne_le_horizon S hround)

#print axioms w4CarrierActionHeadPin_of_frame_inputs

/-! ## Scoped field-level composers -/

/-- The carrier-chain finality pin from the available field-level composer, with
the prepared-frame inputs carried at each canonical regime round. -/
theorem w4CarrierChainFinalityPin_of_fields_of_frame_inputs
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
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpostGST : S.E.t_GST ≤ S.a rGST)
    (hgst : ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r + 1))
    (hframe : ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      ∃ C End : Block V,
        MovingChainAtCarrierFor S rho q0 r C End ∧
        S.E.t_GST ≤ S.a (r - 1) ∧
        S.hc.opening_slot
            (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
          S.hc.opening_slot r + 1)
    (hadvance : W4ProcessedFinalityAdvancePin S rho) :
    W4CarrierChainFinalityPin S rho q0 := by
  exact w4CarrierChainFinalityPin_of_fields S adm hbot hcom hsuffix hduty
    (w4CarrierActionHeadPin_of_frame_inputs S adm hcom hbot hrec hdelay
      hpostGST hgst hframe) hadvance

#print axioms w4CarrierChainFinalityPin_of_fields_of_frame_inputs



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
