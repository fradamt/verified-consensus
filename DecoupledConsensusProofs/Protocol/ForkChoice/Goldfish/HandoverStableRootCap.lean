module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Handlers.StableRecordWrites

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem stableRootAt_mem_stateBefore_for_cap
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} (hv : v ∈ rho.honest) {i : Nat} {R : Block V}
    (hroot : StableRecord.StableRootAt S rho v i R) :
    R ∈ (rho.stateBefore S i v).st.core.T := by
  obtain ⟨time, hi, hpos, htime, hR⟩ := hroot
  let nd := NamedActionReads.confirmationReadFrom S
    (rho.stateBefore S i v) time
  have hstate : NamedRun.stateBefore S rho i v =
      NamedRun.stateBeforeTime S rho time v :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch hi
  have hfg : Protocol.get_fg_root nd.st.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree nd.st.core.toHealing.toFG := by
    have hfg' := named_fgRoot_mem_filtered_stateBeforeTime S rho time v
    simpa only [nd, hstate, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hfg'
  change (match ((DecoupledConsensusModel.Protocol.readFrame nd.cache nd.st.core.toHealing
      (S.hc.round_of nd.st.core.s)).g2.bind id).bind
        (DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree nd.st.core.toHealing.toFG)) with
    | some Q => some Q
    | none => some (Protocol.get_fg_root nd.st.core.toHealing.toFG)) = some R at hR
  cases hslot : (DecoupledConsensusModel.Protocol.readFrame nd.cache nd.st.core.toHealing
      (S.hc.round_of nd.st.core.s)).g2.bind id with
  | none =>
      simp only [hslot] at hR
      have hEq : Protocol.get_fg_root nd.st.core.toHealing.toFG = R :=
        Option.some.inj hR
      rw [← hEq]
      exact Proofs.Records.get_filtered_block_tree_subset _ hfg
  | some raw =>
      rw [hslot] at hR
      cases hactive : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree nd.st.core.toHealing.toFG) raw with
      | none =>
          simp [Option.bind, hactive] at hR
          have hEq : Protocol.get_fg_root nd.st.core.toHealing.toFG = R := hR
          rw [← hEq]
          exact Proofs.Records.get_filtered_block_tree_subset _ hfg
      | some Q =>
          simp [Option.bind, hactive] at hR
          have hEq : Q = R := hR
          rw [← hEq]
          exact Proofs.Records.get_filtered_block_tree_subset _
            (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1



/-- Additive provenance-carrying twin of
`stableRootAt_namedHeight_le_cap_of_before`. -/
theorem stableRootAt_namedHeight_le_cap_of_before_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {i : Nat} {R : Block V}
    {deadline : Time} {cap : Height}
    (hi : i < inclusiveEventIndex rho deadline)
    (hcap : honestHMaxAt S rho deadline ≤ cap)
    (hroot : StableRecord.StableRootAt S rho v i R) :
    ∃ Rn : NamedBlock V, Rn.erase = R ∧ RunBlock S rho Rn ∧
      (Protocol.derive_named S.E S.cfg Rn).h ≤ cap := by
  have hRmem := stableRootAt_mem_stateBefore_for_cap S
    adm.toNamedScheduleWellFormed hv hroot
  obtain ⟨Rn, hRnBody, hRnErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho i v hRmem
  have hRnRun : RunBlock S rho Rn :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hRnBody
  have hheight :=
    Proofs.NamedStoreBridge.heights_le_hMax_stateBefore S rho i v Rn hRnBody
  have hlocal := localHMax_le_honestHMaxBeforeIndex S rho i hv
  have hindex : honestHMaxBeforeIndex S rho i ≤
      honestHMaxBeforeIndex S rho (inclusiveEventIndex rho deadline) :=
    honestHMaxBeforeIndex_mono S rho (Nat.le_of_lt hi)
  have hfrontier : honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho deadline) ≤ honestHMaxAt S rho deadline := by
    rw [honestHMaxAt_eq_honestHMaxBeforeIndex S adm.toNamedScheduleWellFormed]
  refine ⟨Rn, hRnErase, hRnRun, ?_⟩
  exact hheight.trans (hlocal.trans (hindex.trans (hfrontier.trans hcap)))

#print axioms stableRootAt_namedHeight_le_cap_of_before_runBlock

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
