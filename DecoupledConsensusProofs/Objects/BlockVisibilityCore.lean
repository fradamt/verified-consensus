module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Blocks
public import DecoupledConsensusProofs.Execution.Runtime

@[expose] public section

/-!
# Low admitted-block visibility

Tree-membership and block-stamp transport from genesis or an accepted block to
a later pre-time store.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Genesis is present with its bottom stamp at every pre-time store. -/
theorem genesis_mem_and_stamp_storeBeforeTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (Gamma cutoff : Time) :
    Block.genesis ∈ (rho.storeBeforeTime S v Gamma).T ∧
      stampedBefore (rho.storeBeforeTime S v Gamma).timestamp_block
        cutoff Block.genesis = true := by
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hstore : rho.storeBeforeTime S v Gamma = (rho.stateBefore S n v).st :=
    congrArg NamedNodeState.st (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S sch Gamma) v)
  have hcarry : BlockCarry (rho.stateBefore S 0 v).st.core
      (rho.stateBefore S n v).st.core :=
    block_carry S sch v n (Nat.zero_le n)
  have hmem0 : Block.genesis ∈ (rho.stateBefore S 0 v).st.core.T := by
    simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
      Protocol.NamedStore.initial, Protocol.Store.init]
  have hstamp0 : (rho.stateBefore S 0 v).st.core.timestamp_block Block.genesis =
      some genesisStamp := by
    simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init, NamedNode.initial,
      Protocol.NamedStore.initial, Protocol.Store.init]
  rw [hstore]
  refine ⟨hcarry.mem Block.genesis hmem0, ?_⟩
  simp only [stampedBefore, hcarry.stamp Block.genesis genesisStamp hstamp0,
    genesisStamp, decide_eq_true_eq]
  exact WithBot.bot_lt_coe cutoff

/-- Admission before `Gamma` gives membership at any later read `Gamma'`, while
keeping the original strict stamp bound `Gamma`. -/
theorem admittedBefore_mem_and_stamp_at
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} {B : Block V} {Gamma Gamma' : Time}
    (hadmit : AdmittedBefore S rho v B Gamma) (hle : Gamma ≤ Gamma') :
    B ∈ (rho.storeBeforeTime S v Gamma').T ∧
      stampedBefore (rho.storeBeforeTime S v Gamma').timestamp_block Gamma B = true := by
  obtain ⟨C, hCerase, i, t, hacc, hlt⟩ := hadmit
  obtain ⟨_, ⟨e, he, _, het⟩⟩ := hacc.1
  have hpostBodies : C ∈ (rho.stateBefore S (i + 1) v).st.bodies := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.stateBefore S (i + 1) v).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho (i + 1) v).1.1.1
  have hpost : B ∈ (rho.stateBefore S (i + 1) v).st.core.T := by
    rw [hcoh.1, ← hCerase]
    exact Finset.mem_image_of_mem NamedBlock.erase hpostBodies
  let N := (rho.events.filter (fun x => decide (x.time < Gamma'))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hGamma'e : Gamma' ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S sch (t := Gamma') (j := i) (e := e)
        (by simpa [N] using hNle) he
    rw [het] at hGamma'e
    exact (not_le_of_gt (lt_of_lt_of_le hlt hle)) hGamma'e
  have hcarry : BlockCarry (rho.stateBefore S (i + 1) v).st.core
      (rho.stateBefore S N v).st.core :=
    block_carry S sch v N (Nat.succ_le_of_lt hiN)
  have hsource : BlockStamps (rho.stateBefore S (i + 1) v).st.core :=
    blockStamps_stateBefore S sch v (i + 1)
  obtain ⟨c, hc⟩ : ∃ c : Stamp,
      (rho.stateBefore S (i + 1) v).st.core.timestamp_block B = some c :=
    Option.isSome_iff_exists.mp (hsource.stamped B hpost)
  have hcfinal : (rho.stateBefore S N v).st.core.timestamp_block B = some c :=
    hcarry.stamp B c hc
  have hclock : (rho.stateBefore S (i + 1) v).st.core.t ≤ t := by
    have ht := block_store_time_after_event_le S sch he v
    simpa only [het] using ht
  have hcGamma : c < (Gamma : Stamp) :=
    lt_of_le_of_lt
      (le_trans (hsource.bounded B c hc) (WithBot.coe_le_coe.mpr hclock))
      (WithBot.coe_lt_coe.mpr hlt)
  have hstore : rho.storeBeforeTime S v Gamma' = (rho.stateBefore S N v).st :=
    congrArg NamedNodeState.st (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S sch Gamma') v)
  rw [hstore]
  refine ⟨hcarry.mem B hpost, ?_⟩
  simp only [stampedBefore, hcfinal, decide_eq_true_eq]
  exact hcGamma

end Protocol
end DecoupledConsensusModel

end
