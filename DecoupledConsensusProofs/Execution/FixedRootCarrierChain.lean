module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FixedHeightRootCore
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierFirst
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierInteriorInputs
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedOpeningWindow

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Fixed-root carrier proposal facts

The fixed-root promotion reads an honest proposal from the slot two steps after
the first opening. This leaf derives the local existence, timing, run, and
fixed-frontier facts for that named proposal. The ancestry step is kept
separate: these facts do not by themselves identify the proposal with a later
opening parent.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem plusTwo_slot_le_nextOpening (S : Setup V) (q : Round) :
    S.hc.opening_slot q + 2 ≤ S.hc.opening_slot (q + 1) := by
  change q * S.hc.R + 2 ≤ (q + 1) * S.hc.R
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add_left S.hc.R_ge_two _

/-- The `+2` proposal is before the next round action. -/
private theorem plusTwo_proposal_time_le_nextAction (S : Setup V) (q : Round) :
    Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ S.a (q + 1) := by
  calc
    Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤
        Protocol.proposal_time S.E (S.hc.opening_slot (q + 1)) :=
      Protocol.proposal_time_mono S.E (plusTwo_slot_le_nextOpening S q)
    _ ≤ Protocol.confirmation_time S.E (S.hc.opening_slot (q + 1)) :=
      Protocol.proposal_time_le_confirmation_time S.E _
    _ = S.a (q + 1) := by
      simp only [Setup.a, Protocol.a_eq_confirmation_time]



/-- An honest fixed-root carrier has a named `+2` proposal with the local
timing and frontier facts needed by row carriage. -/
theorem fixedRoot_plusTwoProposal_facts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {u : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho M u read)
    {q endpoint : Round}
    (hpost : S.E.t_GST ≤ read)
    (hdelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2))
    (hcarrier : ProposerCarrierAt S rho q)
    (hqEnd : q + 1 ≤ endpoint)
    (hendHor : S.a endpoint ≤ rho.horizon)
    (hcapEnd : honestHMaxAt S rho (S.a endpoint) ≤ M) :
    ∃ Bplus : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot q + 2) = some Bplus ∧
      RunBlock S rho Bplus ∧
      S.E.proposer (S.hc.opening_slot q + 2) ∈ rho.honest ∧
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon ∧
      Protocol.get_fg_root
          (rho.storeBeforeTime S
            (S.E.proposer (S.hc.opening_slot q + 2))
            (Protocol.proposal_time S.E (S.hc.opening_slot q + 2))).toHealing.toFG =
        (rho.storeBeforeTime S u read).J ∧
      (rho.storeBeforeTime S
        (S.E.proposer (S.hc.opening_slot q + 2))
        (Protocol.proposal_time S.E (S.hc.opening_slot q + 2))).h_max = M := by
  have hprop : S.E.proposer (S.hc.opening_slot q + 2) ∈ rho.honest :=
    hcarrier.2.2
  have hproposalAction : Protocol.proposal_time S.E
      (S.hc.opening_slot q + 2) ≤ S.a (q + 1) :=
    plusTwo_proposal_time_le_nextAction S q
  have hproposalEnd : Protocol.proposal_time S.E
      (S.hc.opening_slot q + 2) ≤ S.a endpoint :=
    hproposalAction.trans (Assembly.a_mono S hqEnd)
  have hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q + 2) ≤ rho.horizon :=
    hproposalEnd.trans hendHor
  have hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q + 2)) ≤ M :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hproposalEnd).trans
      hcapEnd
  have hrootMax :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm (slashableBound_of_admissible_belowOneThird S adm hfb) hfix hprop hpost
      hdelay hproposalHor hproposalCap
  obtain ⟨Bplus, hBplus⟩ :=
    proposedBlockAt_isSome S rho (S.hc.opening_slot q + 2)
  have hrun : RunBlock S rho Bplus :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot q + 2)
      (by
        change 0 < q * S.hc.R + 2
        exact (by decide : 0 < 2).trans_le (Nat.le_add_left _ _))
      hprop hproposalHor hBplus
  exact ⟨Bplus, hBplus, hrun, hprop, hproposalHor, hrootMax.1, hrootMax.2⟩

#print axioms fixedRoot_plusTwoProposal_facts

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
