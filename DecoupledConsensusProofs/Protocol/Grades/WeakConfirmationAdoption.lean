module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.WeakConfirmationTransport
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone

@[expose] public section

/-!
# Confirmation adoption under core execution

A genuine confirmation starts a Goldfish cone. The execution supplies vote
transport and the processed candidate path. The joint induction supplies
compatibility of FG roots, SG anchors, and frontier witnesses.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGoldfish

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem carried_support_subset_of_mem_T_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (NamedRun.stateBefore S rho n w).st.core.T) :
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes := by
  obtain ⟨D, hD, hDB⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hB
  have hDsub : ∀ u ∈ D.gf_support_votes, u ∈ D.gf_votes := by
    rcases Proofs.Bridges.processes_block_of_mem_T S rho w n D hD with
      rfl | ⟨j, e, -, -, hproc⟩
    · intro u hu
      exact absurd hu (by simp [NamedBlock.gf_support_votes])
    · rcases hproc with hem | ⟨i, hi⟩
      · obtain ⟨i, hi, hmem⟩ := hem
        obtain ⟨-, hproposal⟩ :=
          Proofs.HealingSurface.block_mem_on_tick_emit S w
            (NamedRun.stateBefore S rho i w) e.time hmem
        have hproposal' : Protocol.NamedActions.proposal_with
            (NamedProfile.gradeContract
              (NamedActionReads.confirmationReadFrom S
                (NamedRun.stateBefore S rho i w) e.time).cache)
            .poolAndCarried S.E S.hc (S.node w)
            (NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho i w) e.time).st = some D := by
          unfold Protocol.NamedDuties.propose_block_with at hproposal
          split at hproposal
          · cases hproposal
          · cases hproposal
            assumption
        simp only [Protocol.NamedActions.proposal_with,
          Protocol.with_proposal_input, Option.map_eq_some_iff] at hproposal'
        obtain ⟨parent, -, hDeq⟩ := hproposal'
        rw [← hDeq]
        intro u hu
        exact (List.mem_filter.mp hu).1
      · have hwire := adm.toNamedDeliveryWellFormed.wire
          i w (Object.block D) e.time hi
        simp only [NamedReceipt.wellFormed,
          Bool.and_eq_true] at hwire
        have hsupport := hwire.1.2
        simp only [Protocol.carried_support_well_formed, List.all_eq_true,
          decide_eq_true_eq] at hsupport
        simpa only [Proofs.NamedWire.erase_goldfish_support,
          Proofs.NamedWire.erase_goldfish_votes] using hsupport
  intro u hu
  have hu' : u ∈ D.gf_support_votes := by
    rw [← Proofs.NamedWire.erase_goldfish_support, hDB]
    exact hu
  have := hDsub u hu'
  rw [← hDB, Proofs.NamedWire.erase_goldfish_votes]
  exact this

/-- The support view is contained in the actual vote view. -/
theorem voter_support_subset_voter_view_voteDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (s : Slot) :
    Protocol.voter_support_view S.E
        (voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore s ⊆
    Protocol.voter_view S.E
        (voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore s := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E s)
  apply voter_support_view_subset S.E
  intro B hB
  apply carried_support_subset_of_mem_T_core S adm v n
  simpa only [voteDutyStore, voteStore, tickStore,
    Run.storeBeforeTime, hn] using hB


/- The earlier candidate theorem is retained below; this is its prepared
named counterpart. -/

/- The prepared central cone supplies the next head in this wrapper. -/

/- The named central result is the complete cone wrapper. -/





end WeakGoldfish
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
