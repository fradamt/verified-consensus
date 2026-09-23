module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.W4NamedCeilingStep
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarryBranch2

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The named mixed fold step

The mixed step is the boundary case between the ceiling and ordinary schedule
families. The slot being left keeps a ceiling record. The slot being entered
keeps the ordinary record. The fold state is rebuilt directly so no
ceiling-to-ordinary record coercion is introduced.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem w4nms_nat_not_succ_succ_le (c : Nat) :
    ¬ c + 1 + 1 ≤ c + 1 := by omega

/-- The mixed fold step, with the ceiling record on the left and the ordinary
entered-slot record on the right. -/
theorem w4MovingSlotFoldAtN_step_of_mixed_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {t1 : Time} {M0 : Height} {s0 c : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hdata : MovingSlotWindowDataC S rho M0 c (F (c + 1)))
    (htiming : MovingSlotActionCeiling S rho c (F (c + 1)))
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    {v : V} (hv : v ∈ rho.honest)
    (hdeadline : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ c + 1 + 1)
    (hvoteHor : Protocol.vote_time S.E (c + 1 + 1) ≤ rho.horizon) :
    ∃ (F' : Slot → Block V) (End' : Block V),
      MovingSlotFoldAtN S rho t1 M0 s0 (c + 1 + 1) F' End' ∧
        ∀ d : Slot, d ≤ c + 1 → F' d = F d := by
  classical
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  obtain ⟨Next, hfrontier, hfacts⟩ :=
    hfold.entry.windowFacts_of_ceiling S adm hcom hfb hdata.pos hround hupper
      hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor htiming
  let F' : Slot → Block V := fun d =>
    if d ≤ c + 1 then F d else Next
  have hlow : ∀ d : Slot, d ≤ c + 1 → F' d = F d := by
    intro d hd
    simp only [F', if_pos hd]
  have hhigh : F' (c + 1 + 1) = Next := by
    simp only [F', if_neg (w4nms_nat_not_succ_succ_le c)]
  have hendNext : Block.Preceq End Next := hfrontier.oldPreceq
  have hprevNext : Block.Preceq (F (c + 1)) Next :=
    Block.preceq_trans hfold.entry.prevLe hendNext
  have hmono : ∀ d e : Slot, s0 ≤ d → d ≤ e → e ≤ c + 1 + 1 →
      Block.Preceq (F' d) (F' e) := by
    intro d e hd hde he
    by_cases hec : e ≤ c + 1
    · rw [hlow d (hde.trans hec), hlow e hec]
      exact hfold.mono d e hd hde hec
    · simp only [F', if_neg hec]
      by_cases hdle : d ≤ c + 1
      · simp only [F', if_pos hdle]
        exact Block.preceq_trans
          (hfold.mono d (c + 1) hd hdle (Nat.le_refl _)) hprevNext
      · simp only [F'] at *
        rw [if_neg hdle]
        exact Block.preceq_self Next
  have habsorbed : ∀ d : Slot, s0 ≤ d → d < c + 1 + 1 →
      S.E.proposer d ∈ rho.honest →
      ∃ P : NamedBlock V, proposedBlockAt S rho d = some P ∧
        Block.Preceq P.erase (F' (d + 1)) := by
    intro d hd hdlt hdprop
    rcases Nat.lt_or_ge d (c + 1) with hlt | hge
    · rw [hlow (d + 1) (Nat.succ_le_of_lt hlt)]
      exact hfold.absorbed d hd hlt hdprop
    · have hdeq : d = c + 1 := by
        exact Nat.le_antisymm (Nat.le_of_lt_succ hdlt) hge
      subst hdeq
      obtain ⟨P, hP, hEnd⟩ := hfold.endpointProposal hdprop
      rw [hhigh]
      exact ⟨P, hP, hEnd ▸ hendNext⟩
  have hconfAbsorbed : ∀ d : Slot, s0 ≤ d → d + 1 < c + 1 + 1 →
      ∀ u ∈ rho.honest,
        GenuineConfirmationWith
            (NamedProfile.gradeContract (confirmationInputRead S rho u d).cache)
            S.E S.hc (Proofs.Optimistic.confStore S rho u d) d
            (movingSlotConfirmationOutput S rho d u) ∧
          Block.Preceq (movingSlotConfirmationOutput S rho d u) (F' (d + 2)) := by
    intro d hd hdlt u hu
    rcases Nat.lt_or_ge (d + 1) (c + 1) with hlt | hge
    · rw [hlow (d + 2) (Nat.succ_le_of_lt hlt)]
      exact hfold.confAbsorbed d hd hlt u hu
    · have hdeq : d = c := by
        exact Nat.le_antisymm
          (Nat.le_of_succ_le_succ (Nat.le_of_lt_succ hdlt))
          (Nat.le_of_succ_le_succ hge)
      subst hdeq
      have hout := hfold.entry.confOutcome_atPrev_of_ceiling_named S adm hcom
        hfb hdata.pos hround hupper hpostAction hcut hdata.postVote
        hdata.slotHor hu
      refine ⟨hout.1, ?_⟩
      simp only [F', if_neg (Nat.not_succ_le_self (d + 1))]
      exact hfrontier.genuinePreceq u hu _ hout.1
  have hconfAbove : ∀ d : Slot, s0 ≤ d → d + 1 < c + 1 + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (F' (d + 1))
          (movingSlotConfirmationOutput S rho d u) := by
    intro d hd hdlt u hu
    rcases Nat.lt_or_ge (d + 1) (c + 1) with hlt | hge
    · rw [hlow (d + 1) (le_of_lt hlt)]
      exact hfold.confAbove d hd hlt u hu
    · have hdeq : d = c := by
        exact Nat.le_antisymm
          (Nat.le_of_succ_le_succ (Nat.le_of_lt_succ hdlt))
          (Nat.le_of_succ_le_succ hge)
      subst hdeq
      simp only [F', if_pos (Nat.le_refl (d + 1))]
      exact (hfold.entry.confOutcome_atPrev_of_ceiling_named S adm hcom hfb
        hdata.pos hround hupper hpostAction hcut hdata.postVote hdata.slotHor
        hu).2
  have hcone := hfold.entry.windowVotesCone_of_ceiling S adm hcom hfb
    hdata.pos hround hupper hpostAction hcut hdata.postVote hdata.postProp
    hdata.slotHor hfrontier
  have hwindowCone : ∀ d : Slot, s0 ≤ d → d < c + 1 + 1 →
      NamedHonestVotesCone S rho d (fun X => Block.Preceq (F' (d + 1)) X) := by
    intro d hd hdlt
    rcases Nat.lt_or_ge d (c + 1) with hlt | hge
    · rw [hlow (d + 1) (Nat.succ_le_of_lt hlt)]
      exact hfold.windowCone d hd hlt
    · have hdeq : d = c + 1 := by
        exact Nat.le_antisymm (Nat.le_of_lt_succ hdlt) hge
      subst hdeq
      rw [hhigh]
      exact hcone
  have hhistoryAt : ∀ E' : Block V,
      MovingSlotEntryStateN S rho t1 M0 (c + 1 + 1) Next E' →
      ∀ d : Slot, s0 ≤ d → d ≤ c + 1 + 1 →
        ∃ EndAt : Nat → Block V,
          MovingFrontierChainStateN S rho t1 M0
            (strictEventIndex rho t1)
            (strictEventIndex rho (Protocol.proposal_time S.E d)) EndAt ∧
          EndAt (strictEventIndex rho (Protocol.proposal_time S.E d)) = F' d := by
    intro E' hentry' d hd hdle
    rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
    · obtain ⟨EndAt, hstate, hval⟩ := hfold.historyAt d hd
        (Nat.le_of_lt_succ hlt)
      refine ⟨EndAt, hstate, ?_⟩
      rw [hlow d (Nat.le_of_lt_succ hlt)]
      exact hval
    · have hdeq : d = c + 1 + 1 := Nat.le_antisymm hdle hge
      subst hdeq
      obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hentry'.prevEndpoint
      refine ⟨EndAt, hhistory.prefix
        (strictEventIndex_mono rho hentry'.startTime)
        (strictEventIndex_le_inclusiveEventIndex rho _), ?_⟩
      exact hhigh ▸ hprev
  refine ⟨F', ?_⟩
  by_cases hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest
  · have hadopt := w4MovingSlotAdoptionSupplyAt_of_mixedFoldStep S adm hcom hfb
      hrec hdelay hpost hfold hdata htiming hdata' hv hdeadline hvoteHor
    obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (c + 1 + 1)
    obtain ⟨hparent, _hvotes, _hwalk, _hconf⟩ :=
      hadopt Next hfrontier hprop P hP
    obtain ⟨P, hP, hentry'⟩ :=
      MovingSlotEntryStateN.stepHonest_mixed_of_supply S adm hcom hfb
        hfold.entry hdata hdata' hfrontier hfacts hprop hv hadopt
    refine ⟨P.erase, ?_, hlow⟩
    refine
      { base := hfold.base.trans (Nat.le_succ _)
        entry := by rw [hhigh]; exact hentry'
        endpointProposal := fun _ => ⟨P, hP, rfl⟩
        mono := hmono
        parent := ?_
        absorbed := habsorbed
        confAbsorbed := hconfAbsorbed
        confAbove := hconfAbove
        windowCone := hwindowCone
        historyAt := hhistoryAt _ hentry' }
    intro d hd hdle hdprop
    rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
    · rw [hlow d (Nat.le_of_lt_succ hlt)]
      exact hfold.parent d hd (Nat.le_of_lt_succ hlt) hdprop
    · have hdeq : d = c + 1 + 1 := Nat.le_antisymm hdle hge
      subst hdeq
      rw [hhigh]
      exact hparent
  · have hentry' := MovingSlotEntryStateN.stepByzantine_mixed_named S adm
      hcom hfb hfold.entry hdata hdata' hfrontier hfacts hprop hv
    refine ⟨Next, ?_, hlow⟩
    refine
      { base := hfold.base.trans (Nat.le_succ _)
        entry := by rw [hhigh]; exact hentry'
        endpointProposal := fun hp => absurd hp hprop
        mono := hmono
        parent := ?_
        absorbed := habsorbed
        confAbsorbed := hconfAbsorbed
        confAbove := hconfAbove
        windowCone := hwindowCone
        historyAt := hhistoryAt _ hentry' }
    intro d hd hdle hdprop
    rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
    · rw [hlow d (Nat.le_of_lt_succ hlt)]
      exact hfold.parent d hd (Nat.le_of_lt_succ hlt) hdprop
    · have hdeq : d = c + 1 + 1 := Nat.le_antisymm hdle hge
      subst hdeq
      exact absurd hdprop hprop

#print axioms w4MovingSlotFoldAtN_step_of_mixed_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
