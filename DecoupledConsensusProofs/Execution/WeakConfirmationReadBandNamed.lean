module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakConfirmationReadAnchorsNamed
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness

@[expose] public section

/-! # Named height band at a prepared confirmation read -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem actionTime_lt_nextVote_of_lt_confirmation_band_named
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.confirmation_time S.E s) :
    S.a r < Protocol.vote_time S.E (s + 1) := by
  exact (action_time_lt_proposal_of_lt_previous_confirmation
    S (s := s + 1) (Nat.zero_lt_succ s)
      (by simpa only [Nat.add_sub_cancel] using h)).trans
        (proposal_time_lt_vote_time S.E (s + 1))

/-- The prepared confirmation reader's height filter retains a named honest
vote-duty head. -/
theorem confirmationReadBand_le_voterHeadHeight_of_gstZero_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v x : V} (hx : x ∈ rho.honest)
    {X : NamedBlock V} (hX : X.erase = voterHeadAt S rho x s)
    (hXrun : NamedRun.blockInRun S rho X) :
    (NamedRecoveryRead.confirmationInputRead S rho v s).st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h := by
  let conf := Proofs.Optimistic.confStore S rho v s
  change conf.h_max - 1 ≤ (Protocol.derive_named S.E S.cfg X).h
  by_cases hlarge : 1 < conf.h_max
  · have hmajority := honestWeightMajority_of_finiteWindows S h.windows hhor
    obtain ⟨a, ta, D, K, ha, hemit, hat, -, hfgK, -, -, hKentry,
        hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
      S h.core hmajority (v := v) (time := Protocol.confirmation_time S.E s)
        (by simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hlarge)
    have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
    have hactionTime : S.a a.round < Protocol.vote_time S.E (s + 1) := by
      exact actionTime_lt_nextVote_of_lt_confirmation_band_named S (by
        rw [← htime]
        exact hat)
    have hsafe : Block.Preceq K.erase (voterHeadAt S rho x s) := by
      have hsource := ((actionSources_preceq_voteDutyHead_of_gstZero
        S h.core h.committees h.gstZero h.windows hhor
          (Nat.succ_le_iff.mpr hs) (Nat.le_succ s) hx
          a.round hactionTime).2 a.val_index ha).2 _ hfgK
      rw [← hKentry]
      simpa only [Protocol.voteDutyHead] using hsource
    have hKX : Block.Preceq K.erase X.erase := by
      rw [hX]
      exact hsafe
    obtain ⟨K', hK'X, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hKX
    have hK'run : NamedRun.blockInRun S rho K' :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
    have hK'eq : K' = K := by
      apply h.core.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
        K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
          (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
    have hKXnamed : NamedBlock.Preceq K X := by
      rw [← hK'eq]
      exact hK'X
    have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
        conf.h_max - 1 := by
      simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hKheight
    rw [← hKheight']
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKXnamed
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
    exact Nat.zero_le _

#print axioms confirmationReadBand_le_voterHeadHeight_of_gstZero_named

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
