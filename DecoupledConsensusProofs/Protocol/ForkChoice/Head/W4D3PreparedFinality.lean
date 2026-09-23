module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.W4D3FinalitySpineCompose
public import DecoupledConsensusProofs.Protocol.Grades.W4D2PreparedFinality
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.W4D2PreparedRegime
public import DecoupledConsensusProofs.Protocol.Grades.W4D2LandedPins
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix
public import DecoupledConsensusProofs.Protocol.Grades.W4GSTZeroOpeningLifecycle

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! # D3 finality over the prepared D2 path
This is an additive D3 consumer. The recovery spine, graded chain,
first-half, carrier-finality, and domain-activity inputs remain explicit
residuals. The execution core, regime pin, and density record are discharged
through the prepared field-level producers; the two finality projections are
the available D3 projections.
-/




/-- The selected predecessor's prepared action anchor is below its honest
opening proposal. The prepared confirmation write gives the direct live arm;
the root arm uses the same proposal duty's exact prepared anchor. -/
theorem w4PreparedD3AnchorAt_of_executionPrepared
    (S : Setup V) {rho : Run V} (hcom : HonestCommittees S rho.honest)
    {q : Round} (hexec : CanonicalSuffixExecutionPrepared S rho q) :
    ∀ (r : Round), q + 2 < r →
      ProposerOpeningCarrierAt S rho r →
      ∀ {Pprev : NamedBlock V},
        proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Pprev →
        S.a (r - 1) ≤ rho.horizon →
        ∀ v ∈ rho.honest,
          Block.Preceq
            (PhaseGrades.nodeAnchor S (actionReadAt S rho v (r - 1)) (r - 1))
            Pprev.erase := by
  intro r hlate hopening Pprev hPprev hhor v hv
  have hprevLate : q + 1 < r - 1 :=
    Nat.lt_sub_of_add_lt (by simpa only [Nat.add_assoc] using hlate)
  have hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot (r - 1)) := by
    have hfirst := Nat.add_le_add_right
      (openingSlot_add_two_le_openingSlot_of_lt S (Nat.lt_succ_self q)) 1
    have hslots : S.hc.opening_slot q + 3 ≤ S.hc.opening_slot (r - 1) :=
      hfirst.trans ((Nat.le_succ (S.hc.opening_slot (q + 1) + 1)).trans
        (openingSlot_add_two_le_openingSlot_of_lt S hprevLate))
    exact (lt_trans (by rw [← vote_time_add_delta]
                        exact Int.lt_add_of_pos_right _ S.E.Δ_pos)
          (support_cutoff_lt_proposal_time_succ S.E (S.hc.opening_slot q + 2))).trans_le
      (proposal_time_mono S.E hslots)
  have hprevious := canonicalOpeningLifecycleAt_of_executionPrepared S hcom hexec
    hafter hopening.2.1 hhor
  have hlive := (hprevious Pprev hPprev v hv).1
  rcases w4_anchor_preceq_liveConfirmed_or_fgRoot S rho v (r - 1) with
    hanchor | _hroot
  · rwa [hlive] at hanchor
  · have hprevPos : 0 < r - 1 := Nat.zero_lt_of_lt hprevLate
    have hslotPos : 0 < S.hc.opening_slot (r - 1) := by
      have hRpos : 0 < S.hc.R := Nat.lt_of_lt_of_le (by decide) S.hc.R_ge_two
      simpa only [Protocol.HealConfig.opening_slot] using
        (Nat.mul_pos hprevPos hRpos)
    have hconfHor : Protocol.confirmation_time S.E
        (S.hc.opening_slot (r - 1)) ≤ rho.horizon := by
      simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hhor
    have hduty := hexec.duty (S.hc.opening_slot (r - 1)) hslotPos hafter
      hopening.2.1 hconfHor Pprev hPprev
    have hroundConf : S.hc.round_of
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot (r - 1))).st.core.s =
          r - 1 := by
      simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Proofs.HealingSurface.opening_confirmation_time_eq_action,
        Protocol.NamedStore.setClock] using Proofs.HealingLemmas.round_of_slotOf_a S (r - 1)
    have hconfAnchor : namedConfirmationAnchor S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot (r - 1))) =
          PhaseGrades.nodeAnchor S
            (Internal.NamedRecoveryRead.confirmationInputRead S rho v
              (S.hc.opening_slot (r - 1))) (r - 1) := by
      simpa only [namedConfirmationAnchor, PhaseGrades.nodeAnchor,
        PhaseGrades.nodeRead, Protocol.get_sg_root_with, hroundConf]
    have hnode : PhaseGrades.nodeAnchor S (actionReadAt S rho v (r - 1)) (r - 1) =
        PhaseGrades.nodeAnchor S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v
            (S.hc.opening_slot (r - 1))) (r - 1) := rfl
    rw [hnode, ← hconfAnchor]
    exact hduty.anchor v hv

#print axioms w4PreparedD3AnchorAt_of_executionPrepared



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
