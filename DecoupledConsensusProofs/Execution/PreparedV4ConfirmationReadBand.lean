module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4ActionSourcesCore
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness

@[expose] public section

/-! # Prepared V4 confirmation-read height band -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem actionTime_lt_nextVote_of_lt_confirmation_v4_band
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.confirmation_time S.E s) :
    S.a r < Protocol.vote_time S.E (s + 1) := by
  exact (action_time_lt_proposal_of_lt_previous_confirmation
    S (s := s + 1) (Nat.zero_lt_succ s)
      (by simpa only [Nat.add_sub_cancel] using h)).trans
        (proposal_time_lt_vote_time S.E (s + 1))

/-- A prepared confirmation reader's frontier band is below the derived height
of every honest named vote-duty head at the same post-cut slot. -/
theorem SettledBootstrapPreparedV4.confirmationReadBand_le_voterHeadHeight_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {s : Slot} (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v x : V} (hx : x ∈ rho.honest)
    {X : NamedBlock V} (hX : X.erase = voterHeadAt S rho x s)
    (hXrun : NamedRun.blockInRun S rho X) :
    (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h := by
  let conf := Proofs.Optimistic.confStore S rho v s
  change conf.h_max - 1 ≤ (Protocol.derive_named S.E S.cfg X).h
  by_cases hlarge : 1 < conf.h_max
  · have hcutpos : 0 < base + S.hc.η_SG :=
      Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
    have hmajority := honestWeightMajority_of_finiteWindowsFrom
      S hawake hcutpos (hboot.settled.trans hs) (Nat.le_succ s) hhor
    obtain ⟨a, ta, D, K, ha, hemit, hat, hrow, hfgK, -, -, hKentry,
        hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
      S adm hmajority (v := v) (time := Protocol.confirmation_time S.E s)
        (by simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hlarge)
    have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
    have hactionTime : S.a a.round < Protocol.vote_time S.E (s + 1) := by
      exact actionTime_lt_nextVote_of_lt_confirmation_v4_band S (by
        rw [← htime]
        exact hat)
    have hPhead : Block.Preceq P.erase (voterHeadAt S rho x s) :=
      (SettledBootstrapPreparedV4.protectedVoteSlots_core
        S adm hcom hboot hawake hfinality hhor s hs (Nat.le_succ s)).1.heads x hx
    have hPX : Block.Preceq P.erase X.erase := by
      rw [hX]
      exact hPhead
    obtain ⟨P', hP'X, hP'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hPX
    have hP'run : NamedRun.blockInRun S rho P' :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hP'X
    have hP'eq : P' = P := by
      apply adm.toNamedRootCollisionFree.root_injective P' P hP'run hboot.runBlock
        P' P (Or.inl (Proofs.NamedAncestry.named_self P'))
          (Or.inr (Proofs.NamedAncestry.named_self P))
      rw [← Proofs.NamedWire.erase_root P', ← Proofs.NamedWire.erase_root P, hP'erase]
    have hPheight : (Protocol.derive_named S.E S.cfg P).h ≤
        (Protocol.derive_named S.E S.cfg X).h := by
      apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
      rw [← hP'eq]
      exact hP'X
    by_cases hold : a.round < base + S.hc.η_SG
    · by_cases hpre : a.round < fresh
      · have hbound := hboot.oldRows a ta _ ha hemit hpre hrow
        have hbound' : conf.h_max - 1 ≤ cap := by
          simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hbound
        exact hbound'.trans (hboot.heightCap.trans hPheight)
      · have hKP := hboot.fgAll a ta _
            (Protocol.derive_named S.E S.cfg K).T_h
            ha hemit hrow (Nat.le_of_not_gt hpre) hold hfgK
        rw [hKentry] at hKP
        have hKX : Block.Preceq K.erase X.erase := Block.preceq_trans hKP hPX
        obtain ⟨K', hK'X, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hKX
        have hK'run : NamedRun.blockInRun S rho K' :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
        have hK'eq : K' = K := by
          apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
            K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
              (Or.inr (Proofs.NamedAncestry.named_self K))
          rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
        have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
            conf.h_max - 1 := by
          simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hKheight
        rw [← hKheight']
        apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        rw [← hK'eq]
        exact hK'X
    · have hsource :=
        ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
          S adm hcom hboot hawake hfinality hhor hs (Nat.le_succ s) hx
            a.round (Nat.le_of_not_gt hold) hactionTime).2 a.val_index ha).2 _ hfgK
      have hKX : Block.Preceq K.erase X.erase := by
        rw [← hKentry, hX]
        simpa only [Protocol.voteDutyHead] using hsource
      obtain ⟨K', hK'X, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hKX
      have hK'run : NamedRun.blockInRun S rho K' :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
      have hK'eq : K' = K := by
        apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
          K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
            (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
      have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
          conf.h_max - 1 := by
        simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hKheight
      rw [← hKheight']
      apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
      rw [← hK'eq]
      exact hK'X
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
    exact Nat.zero_le _

#print axioms SettledBootstrapPreparedV4.confirmationReadBand_le_voterHeadHeight_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
