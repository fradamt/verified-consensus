module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedBoundaryEntry
public import DecoupledConsensusProofs.Protocol.Schedule.W4ConfCompatibleHonest

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The honest named boundary fold

This is the additive named-core twin of
`w4_movingSlotFoldAtN_boundary_honest`. It uses the prepared four-field
confirmation freeze and the named proposal history. The local call-site
facts remain explicit in this leaf; the higher composer supplies them from
the pin-free general-slot producers.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}


private theorem w4nhbf_preEntry_honest
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hprop : S.E.proposer (S.hc.opening_slot q + 3) ∈ rho.honest)
    (hparent : Block.Preceq D.erase
      (proposedParent S rho (S.hc.opening_slot q + 3))) :
    ∃ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot q + 3) = some P ∧
      MovingSlotPreEntryN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (S.hc.opening_slot q + 3) D.erase P.erase := by
  let o := S.hc.opening_slot q
  have hconfHor : Protocol.confirmation_time S.E (o + 1) ≤ rho.horizon := by
    have hslots : o + 1 ≤ o + 3 := by
      show o + 1 ≤ o + 3
      exact Nat.add_le_add_left (by decide : (1 : Nat) ≤ 3) _
    exact (Int.add_le_add_right
      (Protocol.proposal_time_mono S.E hslots) _).trans
      (by simpa only [o] using hbaseTiming.2.2)
  have hvoteHor : Protocol.vote_time S.E (o + 2) ≤ rho.horizon := by
    have hslots : o + 2 ≤ o + 3 := by
      show o + 2 ≤ o + 3
      exact Nat.le_succ _
    exact (Protocol.vote_time_mono_slots S.E hslots).trans
      ((Protocol.vote_time_le_confirmation_time S.E (o + 3)).trans
        (by simpa only [o] using hbaseTiming.2.2))
  have hcone : NamedHonestVotesCone S rho (o + 2)
      (fun X => Block.Preceq D.erase X) :=
    hhandoff.honestVotesCone_two_after adm hvoteHor
  obtain ⟨EndAt, hstate, hconstAll⟩ :=
    w4NamedBoundaryHistoryN_toFreeze S adm hhandoff hboundary hconfHor
  have hconst : EndAt
      (inclusiveEventIndex rho (Protocol.view_freeze S.E (o + 2))) =
        D.erase := hconstAll _ (Nat.le_refl _)
  obtain ⟨P, hP, EndAt', hstate', hstrict, hincl⟩ :=
    movingBoundaryHistoryN_toProposal_honest S adm hstate hconst
      ⟨D, rfl, hboundary.run⟩ hprop
      ((Protocol.proposal_time_le_confirmation_time S.E (o + 3)).trans
        (by simpa only [o] using hbaseTiming.2.2))
      hparent
  exact ⟨P, hP,
    movingBoundaryPreEntryN_honest_of_prevEndpoint S
      ⟨EndAt', hstate', hstrict, hincl⟩ hcone⟩

/-- The honest initial named fold, with the new named boundary core. -/
theorem w4MovingSlotFoldAtN_boundary_honest_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q + 3) = some P)
    (hprop : S.E.proposer (S.hc.opening_slot q + 3) ∈ rho.honest)
    (hparent : Block.Preceq D.erase
      (proposedParent S rho (S.hc.opening_slot q + 3)))
    (hprevVotes : NamedHonestVotesCone S rho
      (S.hc.opening_slot q + 3)
      (fun X => Block.Preceq D.erase X))
    (hheadEq : ∀ w ∈ rho.honest,
      voteDutyHead S rho w (S.hc.opening_slot q + 3) = P.erase)
    (hconf : ∀ w ∈ rho.honest, ∀ C : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w (S.hc.opening_slot q + 2)).cache)
        S.E S.hc
        (Proofs.Optimistic.confStore S rho w (S.hc.opening_slot q + 2))
        (S.hc.opening_slot q + 2) C →
      Block.compatible C P.erase = true) :
    ∃ F : Slot → Block V, ∃ End : Block V,
      MovingSlotFoldAtN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (S.hc.opening_slot q + 3) (S.hc.opening_slot q + 3) F End ∧
      F (S.hc.opening_slot q + 3) = D.erase := by
  obtain ⟨P0, hP0, hpre⟩ :=
    w4nhbf_preEntry_honest S adm hhandoff hboundary hbaseTiming hprop hparent
  have hP0eq : P0 = P := proposedBlockAt_unique S rho
      (S.hc.opening_slot q + 3) hP0 hP
  subst P0
  have hbaseVoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot q + 3) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E
      (S.hc.opening_slot q + 3)).trans hbaseTiming.2.2
  have hentry := hpre.toEntryN_of_voteHorizon S adm hbaseVoteHor
    (fun _ => hheadEq)
    (fun hbyz => (hbyz hprop).elim) hprevVotes hconf
  have hfold := movingSlotFoldAtN_of_entry S hentry
    (fun _ => ⟨P, hP, rfl⟩) (fun _ => hparent)
  exact ⟨fun _ => D.erase, P.erase, hfold, rfl⟩

#print axioms w4MovingSlotFoldAtN_boundary_honest_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
