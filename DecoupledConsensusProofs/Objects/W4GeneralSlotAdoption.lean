module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4HealedTwoSlotHandoff
public import DecoupledConsensusProofs.Protocol.Schedule.W4MovingParent
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarryBranch2
public import DecoupledConsensusProofs.Protocol.Schedule.W4VoteStoreExtendsSlot
public import DecoupledConsensusProofs.Execution.MovingChainIterate

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The healed honest proposal at a GENERAL slot, named (W4 branches gs)

earlier proves the adoption package at every slot past the safety deadline
(`honestProposal_canonicalDuty_after_SG_healing`, then
`genuineConfirmation_of_dutyExecution`, earlier
`ProposalConfirmationSafetyRun.lean:188`). The selection has the named twin only
at an OPENING slot, in `ProposalAdoptionNamedClosedRun`. Two consumers need it
one slot off an opening: the corresponding branch's fold branch
(`MovingChainIterateRun.lean:326`) and this result's prepared two-slot handoff at
`S.hc.opening_slot q + 1`.

The package splits cleanly at the honest head equality. Once every honest
voter's head at the slot IS the proposal, the slot's vote cone and the
prepared genuine confirmation both follow by general-slot producers, and this
leaf lands those two reductions. The head equality itself is the open item;
the Open at the end records exactly where the opening-slot proof uses its
opening slot.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}




/-- **Deliverable 2: the slot's honest vote cone, from the head equality.**

This is the general-slot form of
`honestProposal_openingVoteCone_after_SG_healing_named`
(`ProposalAdoptionNamedClosedRun.lean:1058`), whose only use of its slot's
shape was out slot zero; that is a hypothesis here. The body is the
committee-member step `voteDutyHead_runBlock_and_emits` read through the head
equality, which is `protectedVoteSlot_of_coreHeads`'s body
(`WeakProposalHeadRun.lean:20`) inlined: that module is not importable right
now because the olean of `RecoveryFinalityEntranceRun` in its closure is
missing from the tree.

the corresponding branch consumes exactly this term at `MovingChainIterateRun.lean:326`,
where the fold's honest-proposer branch is handed the slot-`s` cone above the
previous endpoint and needs the slot-`(s+1)` cone above the new proposal. -/
theorem honestProposal_slotVoteCone_after_SG_healing_named_of_heads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V}
    (hheads : ∀ v ∈ rho.honest, voterHeadAt S rho v s = P.erase) :
    NamedHonestVotesCone S rho s (fun X => Block.Preceq P.erase X) := by
  intro w hw hcommittee
  obtain ⟨X, hXhead, hXrun, hXemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm hs hhor hw hcommittee
  refine ⟨X, ?_, hXrun, hXemit⟩
  simpa only [hXhead, Protocol.voteDutyHead, hheads w hw] using
    Block.preceq_self P.erase

#print axioms honestProposal_slotVoteCone_after_SG_healing_named_of_heads





/-- **The fold's honest adoption bundle at an honest proposal slot**
( gs, the `MovingSlotAdoptionSupply` consumer).

The conclusion is `MovingSlotAdoptionSupplyAt S rho c End`, the corresponding branch's
endpoint-parameterised supply (`MovingChainIterateRun`, 0ffcc9ea). The earlier
`MovingSlotAdoptionSupply`, which quantified the prior endpoint, was not
derivable here: the corresponding branch's parent producer is stated at the endpoint the
entry state carries, and a frontier record over a DIFFERENT old endpoint is a
different premise. The frontier record's determinacy settles the NEW endpoint
given the same old one and says nothing about the prior one.

Three of the four conjuncts are discharged here from the available general-slot
family and its neighbours: the parent above the window endpoint is branches
w4-mc2's `movingSlotAdoptionParent_of_ceiling`, the slot's vote cone is this
leaf's `honestProposal_slotVoteCone_after_SG_healing_named_of_heads` over the
general-slot head equality, and the proposal-walk transfer is the corresponding branch's
`w4_honestProposal_voteStoreExtends_after_SG_healing_named_slot`.

The compatibility conjunct stays an explicit input. Its producer, the corresponding branch's
`MovingSlotPreEntryN.confCompatible_honest_closed`, reads a PRE-entry at the
entered slot, which the fold step builds and this consumer does not hold, so
the corresponding branch discharges it inside `MovingChainIterateRun`. -/
theorem movingSlotAdoptionSupplyAt_of_generalSlot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hfb : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowDataC S rho M0 c Prev)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfacts : ∀ Next : Block V,
      MovingSlotFrontierAt S rho c End Next →
      NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    {v : V} (hv : v ∈ rho.honest)
    (hdeadline : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ c + 1 + 1)
    (hvoteHor : Protocol.vote_time S.E (c + 1 + 1) ≤ rho.horizon)
    (_of_confCompatible : ∀ Next : Block V,
      MovingSlotFrontierAt S rho c End Next →
      S.E.proposer (c + 1 + 1) ∈ rho.honest →
      ∀ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P →
        ∀ w ∈ rho.honest, ∀ D : Block V,
          GenuineConfirmationWith
            (NamedProfile.gradeContract
              (confirmationInputRead S rho w (c + 1)).cache)
            S.E S.hc (Proofs.Optimistic.confStore S rho w (c + 1)) (c + 1) D →
            Block.compatible D P.erase = true) :
    MovingSlotAdoptionSupplyAt S rho c End := by
  intro Next hfrontier hprop P hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact MovingSlotEntryStateN.honestParent_mixed_named S adm hcom hfb hentry
      hdata hdata' hfrontier (hfacts Next hfrontier) hprop hv
  · have hheads : ∀ u ∈ rho.honest,
        voterHeadAt S rho u (c + 1 + 1) = P.erase :=
      honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
        S adm hcom hfb hrec hdelay hpost hdeadline hvoteHor hprop hP
    exact honestProposal_slotVoteCone_after_SG_healing_named_of_heads
      S adm (Nat.succ_pos (c + 1)) hvoteHor hheads
  · exact w4_honestProposal_voteStoreExtends_after_SG_healing_named_slot
      S adm hcom hfb hrec hdelay hpost hdeadline hvoteHor hprop hP
  · exact _of_confCompatible Next hfrontier hprop P hP

#print axioms movingSlotAdoptionSupplyAt_of_generalSlot

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
