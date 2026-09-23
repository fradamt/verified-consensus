module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.CommitteePools
public import DecoupledConsensusProofs.Protocol.Schedule.Alignment
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.VoteSetValidityCore
public import DecoupledConsensusProofs.Execution.BridgesCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-! The carried-block committee bridge and the higher voter-view surface. -/
namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Committee validity of every vote carried by a held erased block. -/
theorem carriedVote_committee_of_mem_T_core (S : Setup V) {rho : Run V}
    (adm : Proofs.AdmissibleCore S rho) (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (rho.stateBefore S n w).st.T) :
    ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
  obtain ⟨D, hD, hDB⟩ := Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore
    S rho n w hB
  have hDcommittee : ∀ u ∈ D.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    rcases Proofs.Bridges.processes_block_of_mem_T S rho w n D hD with
      rfl | ⟨j, e, -, -, hproc⟩
    · intro u hu
      exact absurd hu (by simp [NamedBlock.gf_votes])
    · rcases hproc with hem | ⟨i, hi⟩
      · obtain ⟨i, hi, hmem⟩ := hem
        let beforeState := NamedRun.stateBefore S rho i w
        let gc := DecoupledConsensusModel.Protocol.frameContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc beforeState.st.core.toHealing e.time
            beforeState.cache)
        let before := Protocol.NamedStore.setClock S.E beforeState.st e.time
        have hproposal : Protocol.NamedDuties.propose_block_with gc
            S.E S.hc S.cfg (S.node w) before =
            (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg before D,
              some D) := by
          simpa only [gc, before, beforeState] using
            (Proofs.NamedReceiptCallsBase.self_proposal_call S rho hi hmem)
        have hproposal' : Protocol.NamedActions.proposal_with gc
            .poolAndCarried S.E S.hc (S.node w) before = some D := by
          have hoption := congrArg Prod.snd hproposal
          cases hp : Protocol.NamedActions.proposal_with
              gc .poolAndCarried S.E S.hc (S.node w) before with
          | none =>
              have hbad : (none : Option (NamedBlock V)) = some D := by
                simpa only [Protocol.NamedDuties.propose_block_with, hp] using hoption
              cases hbad
          | some C =>
              have hC : C = D := by
                apply Option.some.inj
                simpa only [Protocol.NamedDuties.propose_block_with, hp] using hoption
              simpa only [hC] using hp
        have hgf := Proofs.Optimistic.proposal_with_gf_votes
          gc .poolAndCarried S.E S.hc (S.node w) before hproposal'
        intro u hu
        rw [hgf] at hu
        have hu' : u ∈ (rho.stateBefore S i w).st.core.gf_votes
            (S.E.slotOf e.time - 1) := by
          simpa only [NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hu
        have hslot := (poolStamps_stateBefore S
          adm.toNamedScheduleWellFormed w i).slot
          (S.E.slotOf e.time - 1) u hu'
        rw [hslot]
        exact CommitteePools.stateBefore S rho w i
          (S.E.slotOf e.time - 1) u hu'
      · have hwf := adm.toNamedDeliveryWellFormed.wire
          i w (Object.block D) e.time hi
        simp only [NamedReceipt.wellFormed, Bool.and_eq_true] at hwf
        have hcommittee := hwf.2
        simp only [List.all_eq_true, decide_eq_true_eq] at hcommittee
        simpa only [Proofs.NamedWire.erase_goldfish_votes] using hcommittee
  intro u hu
  have hu' : u ∈ D.gf_votes := by
    rw [← Proofs.NamedWire.erase_goldfish_votes, hDB]
    exact hu
  exact hDcommittee u hu'

theorem carriedVote_committee_of_mem_T (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (rho.stateBefore S n w).st.T) :
    ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot :=
  carriedVote_committee_of_mem_T_core S adm.toNamedAdmissibleCore w n hB

#print axioms carriedVote_committee_of_mem_T



end Protocol
end DecoupledConsensusModel

end
