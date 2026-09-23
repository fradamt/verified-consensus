module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.CarrierInteriorAdoption
public import DecoupledConsensusProofs.Protocol.Schedule.WeakProcessedTree
public import DecoupledConsensusProofs.Protocol.Handlers.FrameFloorBridge
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff
public import DecoupledConsensusProofs.Execution.SeedCommonRootComplement

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem interior_ancestor_body_mem
    {st : Protocol.NamedStore V} (hpc : NamedStore.NamedParentClosed st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

/-- Store-local named derivation height is monotone along retained ancestry. -/
theorem interior_sigma_height_mono
    (S : Setup V) (rho : Run V) (w : V) (t : Time)
    {A B : Block V}
    (hA : A ∈ (rho.storeBeforeTime S w t).core.T)
    (hB : B ∈ (rho.storeBeforeTime S w t).core.T)
    (hAB : Block.Preceq A B) :
    ((rho.storeBeforeTime S w t).core.σ A).h ≤
      ((rho.storeBeforeTime S w t).core.σ B).h := by
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1.1.1
  obtain ⟨An, hAn, hAe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t w hA
  obtain ⟨Bn, hBn, hBe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t w hB
  have hABn : Block.Preceq An.erase Bn.erase := by
    rw [hAe, hBe]
    exact hAB
  obtain ⟨An', hAn'B, hAn'e⟩ := Proofs.NamedAncestry.erased_ancestor_lift Bn hABn
  have hAn'mem := interior_ancestor_body_mem hcoh.2.2.1 hBn hAn'B
  have hEq : An' = An := hcoh.2.1 An' hAn'mem An hAn hAn'e
  calc
    ((rho.storeBeforeTime S w t).core.σ A).h =
        (Protocol.derive_named S.E S.cfg An).h := by
      rw [← hAe]
      exact congrArg (fun x => x.h)
        (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t w An hAn)
    _ = (Protocol.derive_named S.E S.cfg An').h := by rw [hEq]
    _ ≤ (Protocol.derive_named S.E S.cfg Bn).h :=
      Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hAn'B
    _ = ((rho.storeBeforeTime S w t).core.σ B).h := by
      rw [← hBe]
      exact (congrArg (fun x => x.h)
        (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t w Bn hBn)).symm

/-- Named prepared proof of the candidate/path core used by
`WeakProposal.proposedBlock_voterCandidate_of_readFacts`. Only the store-local
lower band is required; the proposal may itself advance one height. -/
theorem interiorProposal_candidateAndPivotPath
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s) {v : V} (hv : v ∈ rho.honest)
    {P1 Parent : NamedBlock V} {pivot : Block V}
    (hP1 : proposedBlockAt S rho s = some P1)
    (hparent : NamedBlock.parent? P1 = some Parent)
    (hadmit : AdmittedBefore S rho v P1.erase (Protocol.vote_time S.E s))
    (hband : (voteDutyStore S rho v s).h_max - 1 ≤
      ((voteDutyStore S rho v s).σ P1.erase).h)
    (hrootPivot : Block.Preceq
      (Protocol.get_fg_root (voteDutyStore S rho v s).toHealing.toFG) pivot)
    (hpivotParent : Block.Preceq pivot Parent.erase)
    (hpivotNe : pivot ≠ P1.erase) :
    P1.erase ∈ voterCandidateTreeAt S rho v s ∧
      pivot ∈ namedWalkTargetTree S rho s v P1 ∧
      ∀ D : Block V, Block.Preceq (voterAnchorAt S rho v s) D →
        D ≠ voterAnchorAt S rho v s → Block.Preceq D pivot →
        D ∈ namedWalkTargetTree S rho s v P1 := by
  let duty := voteDutyStore S rho v s
  have hP1T : P1.erase ∈ duty.T :=
    (Protocol.admittedBefore_mem_and_stamp_at S
      adm.toNamedScheduleWellFormed hadmit (le_refl _)).1
  have hP1slot : P1.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact proposedBlockAt_slot S rho s hP1
  have hprocessed : P1.erase ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.s := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨hP1T, Or.inr ⟨P1.erase, ⟨hP1T, ?_⟩, Block.preceq_self _⟩⟩
    simpa only [duty, Proofs.Optimistic.voteDutyStore_slot] using hP1slot
  have hparentPre : Block.Preceq Parent.erase P1.erase := by
    cases P1 with
    | genesis => cases hparent
    | node p sl rt vs sp rows proposer =>
        simp only [NamedBlock.parent?] at hparent
        have hp : p = Parent := Option.some.inj hparent
        subst Parent
        exact preceq_parent
          (NamedBlock.node p sl rt vs sp rows proposer).erase
  have hpivotP1 : Block.Preceq pivot P1.erase :=
    Block.preceq_trans hpivotParent hparentPre
  have hFJ : Block.Preceq duty.F duty.J := by
    simpa only [duty, voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore]
      using Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.vote_time S.E s) v
  have hFP1 : Block.Preceq duty.F P1.erase :=
    Block.preceq_trans (Proofs.Records.preceq_get_fg_root_of_F
      (st := duty.toHealing.toFG) hFJ)
      (Block.preceq_trans hrootPivot hpivotP1)
  have hrootP1 : Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG) P1.erase :=
    Block.preceq_trans hrootPivot hpivotP1
  have hcandidate : P1.erase ∈ voterCandidateTreeAt S rho v s := by
    simp only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Protocol.voter_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hprocessed, hFP1⟩, P1.erase, hprocessed,
      Block.preceq_self _, hband⟩, hrootP1⟩
  have hpivotCandidate : pivot ∈ voterCandidateTreeAt S rho v s := by
    have hpivotProcessed := WeakGoldfish.ancestorProcessed_of_voterProcessed
      S adm.toNamedAdmissibleCore hv (s := s - 1) (B := P1.erase) (by simpa only [Nat.sub_add_cancel hs] using hprocessed)
      pivot hpivotP1
    simp only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Protocol.voter_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨by simpa only [Nat.sub_add_cancel hs] using hpivotProcessed,
      Block.preceq_trans (Proofs.Records.preceq_get_fg_root_of_F
        (st := duty.toHealing.toFG) hFJ)
        hrootPivot⟩, P1.erase, hprocessed, hpivotP1, hband⟩, hrootPivot⟩
  refine ⟨hcandidate, Finset.mem_erase.mpr ⟨hpivotNe, hpivotCandidate⟩, ?_⟩
  intro D hAD _ hDP
  have hDP1 := Block.preceq_trans hDP hpivotP1
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG)
      (voterAnchorAt S rho v s) := by
    simpa only [duty, voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
      Internal.PhaseGrades.nodeRead, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      NamedOutageClosure.fg_root_preceq_anchor S.E S.hc
        (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.toHealing
        (S.hc.round_of
          (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.s)
        (DecoupledConsensusModel.Protocol.readFrame
          (Internal.NamedRecoveryRead.voteDutyRead S rho v s).cache
          (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.toHealing
          (S.hc.round_of
            (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.s)).g1
  have hDprocessed := WeakGoldfish.ancestorProcessed_of_voterProcessed
    S adm.toNamedAdmissibleCore hv (s := s - 1) (B := P1.erase) (by simpa only [Nat.sub_add_cancel hs] using hprocessed)
    D hDP1
  have hDcandidate : D ∈ voterCandidateTreeAt S rho v s := by
    simp only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Protocol.voter_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨by simpa only [Nat.sub_add_cancel hs] using hDprocessed,
      Block.preceq_trans (Proofs.Records.preceq_get_fg_root_of_F
        (st := duty.toHealing.toFG) hFJ)
        (Block.preceq_trans hrootAnchor hAD)⟩,
      P1.erase, hprocessed, hDP1, hband⟩,
      Block.preceq_trans hrootAnchor hAD⟩
  exact Finset.mem_erase.mpr
    ⟨fun h => hpivotNe (Block.preceq_antisymm hpivotP1 (by rw [← h]; exact hDP)),
      hDcandidate⟩

#print axioms interiorProposal_candidateAndPivotPath
#print axioms interior_sigma_height_mono



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
