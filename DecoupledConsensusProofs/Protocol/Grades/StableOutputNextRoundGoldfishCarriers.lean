module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.StableLaterConfirmation
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote

@[expose] public section

/-!
# T_out, step 2: genuine-clear Goldfish protection

This leaf starts the source-specific Goldfish arm. It uses the bounded
healthy-prefix protected-slot fold, so the result does not introduce the
stronger `Admissible` premise used by the older frozen-read construction.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

set_option maxHeartbeats 400000 in
/-- A genuine source confirmation protects a later round checkpoint.

The source fields retain the action/Q2 split used by T_out. The clear
specificity is in `hsource`: it is the genuine-clear arm returned by the
prepared source split, not an arbitrary confirmation supplied independently
of the source action.
-/
theorem genuineClear_protectedCheckpoint_before_boundary
    (S : Setup V) (rho : Run V) (b0 b1 : Time) (p : V)
    (r s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hmargin : FormationMargin S s b0)
    (hp : p ∈ rho.honest)
    {Q B : Block V}
    (hclear : ∃ C',
      Protocol.GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho p (S.a r)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho p (S.hc.opening_slot r))
          (S.hc.opening_slot r) C' ∧
      C' = (actionStoreAt S rho p r).st.core.live_confirmed ∧
      Protocol.deepest_clear (some Q)
        (actionStoreAt S rho p r).st.core.live_confirmed
        ((NamedProfile.gradeContract
          (actionStoreAt S rho p r).cache).read S.E S.hc
          (actionStoreAt S rho p r).st.core.toHealing r).clear = some B ∧
      Block.Preceq Q B ∧ Block.Preceq P C')
    (hrs : r < s) :
    Proofs.HealingSurface.ProtectedVoteSlot S rho (S.hc.opening_slot s) P := by
  have hcap : S.a s ≤ b0 := by
    exact (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before
    S rho b0 b1 hexec hcom hsleep hroundOne
  let d := S.hc.opening_slot s
  have hd : 1 ≤ d := by
    dsimp only [d, Protocol.HealConfig.opening_slot]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.ne_of_gt (Nat.zero_lt_of_lt hrs))
      (Nat.ne_of_gt (Nat.zero_lt_of_lt S.hc.R_ge_two)))
  have hdCap : Protocol.vote_time S.E d + S.E.Δ ≤ b0 := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E d).trans
      (by simpa only [d, Proofs.HealingSurface.opening_confirmation_time_eq_action] using hcap)
  have hqd : S.hc.opening_slot r < d := by
    dsimp only [d, Protocol.HealConfig.opening_slot]
    exact Nat.mul_lt_mul_of_pos_right hrs
      (Nat.zero_lt_of_lt S.hc.R_ge_two)
  obtain ⟨C', hC, -, -, -, hPC⟩ := hclear
  have hprotectedC := (hT1 d hd hdCap).2
      (S.hc.opening_slot r) hqd p hp C' hC
  exact Proofs.HealingSurface.ProtectedVoteSlot.of_ancestor
    (hprotectedC) hPC

#print axioms genuineClear_protectedCheckpoint_before_boundary

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
