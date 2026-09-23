module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4ProtectedVoteAtVoteCore

@[expose] public section

/-! # Prepared V4 protection at an actual vote horizon
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_settledSlot_positive
    (S : Setup V) {rho : Run V} {fresh base : Round} {start s : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hs : start ≤ s) : 0 < s := by
  have hc : 0 < base + S.hc.η_SG :=
    (Nat.zero_lt_of_lt S.hc.η_SG_ge_one).trans_le (Nat.le_add_left _ _)
  exact (Nat.mul_pos hc
    (lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two)).trans_le
      (hboot.settled.trans hs)

private theorem preparedV4_previousConfirmationHor
    (S : Setup V) {rho : Run V} {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon) :
    Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Nat.sub_add_cancel hs]
  exact (support_cutoff_le_vote_time_succ S.E s).trans hhor

theorem SettledBootstrapPreparedV4.protectedVoteSlot_at_vote_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d) (hhor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ProtectedVoteSlot S rho d P.erase := by
  by_cases heq : start = d
  · subst d
    exact ⟨hboot.seedAll, hboot.seed.cone⟩
  cases d with
  | zero =>
      exact False.elim
        ((Nat.lt_irrefl 0) (preparedV4_settledSlot_positive S hboot hd))
  | succ s =>
      have hds : start ≤ s :=
        Nat.le_of_lt_succ (lt_of_le_of_ne hd heq)
      have hs := preparedV4_settledSlot_positive S hboot hds
      have hprevHor := preparedV4_previousConfirmationHor S hs hhor
      have hprev := SettledBootstrapPreparedV4.protectedVoteSlots_core
        S adm hcom hboot hawake hfinality hprevHor s hds
          (Nat.sub_add_cancel hs).symm.le
      exact SettledBootstrapPreparedV4.protectedVoteSlot_succ_at_vote_core
        S adm hcom hboot hawake hfinality hds hhor
          (Block.preceq_self P.erase) hprev.1

#print axioms SettledBootstrapPreparedV4.protectedVoteSlot_at_vote_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
