module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
public import DecoupledConsensusProofs.Protocol.Grades.CleanReadBridge
public import DecoupledConsensusProofs.Execution.StoreFinalityCore

@[expose] public section

/-! # Raw opening-proposer selection

These are local selection facts for an honest opening proposer. They use the
preceding clean action to obtain the proposer's grade, then use only the fresh
anchor and final head floors. They do not use a recovery pivot or a reflection
premise.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A protected block has grade one in the current honest opening proposer's
store when the preceding common grade has a clean next action and the block is
active in the current proposer duty. -/
theorem proposerG1_of_gradeFormsAt_prev_and_active
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {q : Round} (hq : 0 < q) {P : Block V}
    (hformsPrev : NamedGradeFormsAt S rho (q - 1) P)
    (hwindowPrev : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w (S.a (q - 1)) P)
    (hdomainWindow : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (domain S.E S.hc q .g2) P)
    (hpostPrev : S.E.t_GST ≤ S.a (q - 1))
    (hcutPrev : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    (hactiveAtAction : ∀ w ∈ rho.honest,
      P ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w q).toFG)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hactive : P ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing.toFG) :
    Protocol.G1 S.E
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing.gradeView S.hc q P = true := by
  let s := S.hc.opening_slot q
  let duty := Protocol.proposerDutyStore S rho s
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hqPrev : 0 < q - 1 := by
    by_contra hnonpos
    have hzero : q - 1 = 0 := Nat.eq_zero_of_not_pos hnonpos
    have hnonempty : rho.honest.Nonempty := by
      by_contra hnone
      have hzeroWeight : S.E.electorate.weightOf rho.honest = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hnone]
        simp [Electorate.weightOf]
      have hsum := S.E.electorate.weightOf_add_weightOf_sdiff rho.honest
      unfold HonestWeightMajority at hmajority
      omega
    obtain ⟨w, hw⟩ := hnonempty
    have hgrade := (hformsPrev w hw).2
    rw [hzero] at hgrade
    simp [storeGrade, phaseGrade, Protocol.latest_window_zero,
      DecoupledConsensusModel.Protocol.gradeBool, DecoupledConsensusModel.Protocol.positive,
      DecoupledConsensusModel.Protocol.opposing, DecoupledConsensusModel.Protocol.readyView,
      DecoupledConsensusModel.Protocol.rawView, DecoupledConsensusModel.Protocol.interpretedInputs,
      DecoupledConsensusModel.Protocol.rawInputs, DecoupledConsensusModel.Protocol.Supports,
      DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom,
      Electorate.weightOf] at hgrade
  have hdomainWindow' : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (domain S.E S.hc (q - 1 + 1) .g2) P := by
    intro w hw
    simpa only [hpred] using hdomainWindow w hw
  have hactiveAtAction' : ∀ w ∈ rho.honest,
      P ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w (q - 1 + 1)).toFG := by
    intro w hw
    simpa only [hpred] using hactiveAtAction w hw
  have hclean : CleanActionReadFor S rho (q - 1) P := by
    exact cleanActionReadFor_of_namedGradeFormsAt_and_retained_active
      S adm hqPrev hformsPrev hpostPrev
        (by simpa only [hpred] using hcutPrev)
        hwindowPrev hactiveAtAction' hdomainWindow'
  have hprop' : S.E.proposer (S.hc.opening_slot (q - 1 + 1)) ∈ rho.honest := by
    simpa only [hpred] using hprop
  have hactive' : P ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot (q - 1 + 1))).toHealing.toFG := by
    simpa only [hpred] using hactive
  have hG2 : Protocol.G2 S.E duty.toHealing.gradeView S.hc q P = true := by
    have h := G2_nextOpeningProposer_of_cleanActionRead
      S adm hmajority hclean hprop' hactive'
    simpa only [duty, s, hpred] using h
  exact G2_imp_G1 S.E duty.toHealing.gradeView S.hc q P hG2
end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms proposerG1_of_gradeFormsAt_prev_and_active
end DecoupledConsensusModel.Proofs.HealingSurface

end
