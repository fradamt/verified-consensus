module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.WeakProcessedTree
public import DecoupledConsensusProofs.Execution.WeakFGWitness
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGWitnessCandidate
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Adoption
public import DecoupledConsensusProofs.Execution.StoreFinalityCore

@[expose] public section

/-!
# Reader-local frontier candidates under core admissibility

If the protected block reaches the reader's height band, the prior honest
Goldfish cone supplies a processed descendant. Otherwise the reader's
crossing quorum supplies an honest FG checkpoint witness. The witness
covers timeout rows as well as target rows.

Processed-tree closure and the store-local candidate kernel then derive
the filtered path. The final step needs only prior witness compatibility,
FG-root compatibility, and SG-anchor compatibility from the joint induction.
It does not assume equal honest frontiers, full participation, grades,
an accountable fault bound, or candidate retention.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGoldfish

open Internal Execution
open Proofs.Optimistic Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A relayed witness is retained and stamped before the freeze. -/
theorem relayedWitness_mem_and_stamp
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {w : V} {W : Block V} {freeze read : Time} (hle : freeze ≤ read)
    (h : W = Block.genesis ∨ AdmittedBefore S rho w W freeze) :
    W ∈ (rho.storeBeforeTime S w read).T ∧
      stampedBefore (rho.storeBeforeTime S w read).timestamp_block freeze W = true := by
  rcases h with hgen | hadmit
  · simpa only [hgen] using
      (Protocol.genesis_mem_and_stamp_storeBeforeTime S
        sch w read freeze)
  · exact Protocol.admittedBefore_mem_and_stamp_at S
      sch hadmit hle



/-
/-- The preceding honest cone supplies processed heads at the next duty. -/
theorem honestHead_voterProcessed_at_nextDuty_of_postHealingCone
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    {s: Slot} (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C H: Block V}
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    (hH: Proofs.Optimistic.HonestHead S rho s H)
    {w: V} (hw: w ∈ rho.honest)
    (hroot: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) C):
    H ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s:= by
  let duty:= Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hcutHor: Protocol.support_cutoff S.E s ≤ rho.horizon:=
    (support_cutoff_le_confirmation_time S.E s).trans hhor
  have havailable:= honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    S adm hw hpost hcutHor hroot hvotes
  have hslot: duty.toHealing.s = s + 1:= by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  rcases havailable H hH with hgen | hadmit
  · subst H
    have hgenesis:= genesis_mem_and_stamp_storeBeforeTime S
      adm.toScheduleWellFormed w (Protocol.vote_time S.E (s + 1))
        (Protocol.view_freeze S.E s)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.2)⟩
  · have hvisible:= admittedBefore_mem_and_stamp_at S
      adm.toScheduleWellFormed hadmit
        (le_trans (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s))
          (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
    have hstampCut: stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.support_cutoff S.E s) H = true:= by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.2
    have hstampFreeze: stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.view_freeze S.E s) H = true:= by
      rw [stampedBefore_eq_occurrenceBefore] at hstampCut ⊢
      exact occurrenceBefore_mono
        (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)) hstampCut
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.1,
      Or.inl hstampFreeze⟩

/-- A prior action block is processed by the next duty when its FG guard permits it. -/
theorem actionBlock_voterProcessed_at_nextDuty
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    {u w: V} (hu: u ∈ rho.honest) (hw: w ∈ rho.honest)
    {r: Round} {s: Slot} {T: Block V}
    (hmem: T ∈ (actionStoreAt S rho u r).T)
    (haction: S.a r < Protocol.vote_time S.E (s + 1))
    (hpost: S.E.t_GST ≤ Protocol.support_cutoff S.E s)
    (hhor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hroot: Block.Preceq
      (Protocol.get_fg_root (voteDutyStore S rho w (s + 1)).toHealing.toFG) T):
    T ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w (s + 1)).toHealing.s:= by
  have hfields:= Proofs.Optimistic.attestStore_fields S
    (rho.storeBeforeTime S u (S.a r)) (S.a r)
  have htree: (actionStoreAt S rho u r).T =
      (rho.storeBeforeTime S u (S.a r)).T:= by
    simpa only [actionStoreAt, Run.storeBeforeTime] using hfields.2.1
  have hpre: T ∈ (rho.storeBeforeTime S u (S.a r)).T:= by
    exact htree ▸ hmem
  have hcut:= action_le_supportCutoff_of_lt_nextVote S haction
  have hfreezeVote:= le_of_lt (Protocol.view_freeze_lt_vote_time_succ S.E s)
  have hrelay: T = Block.genesis ∨
      Protocol.AdmittedBefore S rho w T (Protocol.view_freeze S.E s):= by
    rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
        adm.toScheduleWellFormed u (S.a r) hpre with hgen | ⟨i, t, hacc, ht⟩
    · exact Or.inl hgen
    · right
      apply WeakBlock.block_admittedBefore_of_accepted_after_cutoff
        S adm hu hw
        (Nat.zero_lt_of_lt (Protocol.parent_slot_lt_of_acceptsAt_block S hacc))
        hacc (ht.trans_le hcut) hpost
        (Protocol.support_cutoff_add_delta_eq_view_freeze S.E s)
        (hfreezeVote.trans hhor)
      intro j t' hj _ hlt
      exact finalized_preceq_at_delivery_of_voteDutyRoot_preceq
        S adm hroot hj hlt
  have hvis:= relayedWitness_mem_and_stamp S adm.toScheduleWellFormed hfreezeVote hrelay
  have hslot: (voteDutyStore S rho w (s + 1)).toHealing.s = s + 1:=
    voteDutyStore_slot S rho w (s + 1)
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
  rw [hslot, Nat.add_sub_cancel]
  exact ⟨by
    simpa only [voteDutyStore, voteStore, tickStore, Protocol.Store.toHealing]
      using hvis.1, Or.inl (by
    simpa only [voteDutyStore, voteStore, tickStore, Protocol.Store.toHealing]
      using hvis.2)⟩

/-- A higher reader frontier supplies a processed descendant through an honest FG row. -/
theorem higherFrontierWitness_processedDescendant
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {s: Slot} {C: Block V} {w: V} (hw: w ∈ rho.honest)
    (hpost: S.E.t_GST ≤ Protocol.support_cutoff S.E s)
    (hhor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hhigh: (derived_state S.E S.cfg C).h < (voteDutyStore S rho w (s + 1)).h_max - 1)
    (hwitnesses: FGFrontierWitnessesCompatibleAt S rho w (s + 1) C)
    (hroot: Block.Preceq
      (Protocol.get_fg_root (voteDutyStore S rho w (s + 1)).toHealing.toFG) C):
    ∃ D: Block V, Block.Preceq C D ∧
      (voteDutyStore S rho w (s + 1)).h_max - 1 ≤ (derived_state S.E S.cfg D).h ∧
      D ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w (s + 1)).toHealing.s:= by
  have hlarge: 1 < (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (s + 1))).h_max:= by
    by_contra hn
    have hzero: (voteDutyStore S rho w (s + 1)).h_max - 1 = 0:=
      Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hn)
    rw [hzero] at hhigh
    exact Nat.not_lt_zero _ hhigh
  obtain ⟨a, ta, T, ha, hemit, hta, hrow, hselected, hTmem, _, hTheight⟩:=
    WeakFG.frontier_confirmationWitness S adm hmajority hlarge
  have hcompatible: Block.compatible C T = true:=
    hwitnesses a ta T ha hemit hta hrow hselected
  have hCT: Block.Preceq C T:= by
    have hcases: Block.Preceq C T ∨ Block.Preceq T C:= by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompatible
    rcases hcases with hCT | hTC
    · exact hCT
    · exact False.elim ((Nat.not_le_of_gt hhigh)
        (hTheight ▸ Protocol.derived_h_mono S.E S.cfg hTC))
  refine ⟨T, hCT, le_of_eq hTheight.symm, ?_⟩
  exact actionBlock_voterProcessed_at_nextDuty S adm ha hw hTmem
    (by simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hta)
    hpost hhor (Block.preceq_trans hroot hCT)

/-- Each reader has a processed descendant in its own frontier band. -/
theorem coneBandDescendant_of_frontierWitnesses
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {s: Slot} {C: Block V}
    (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: HonestVotesCone S rho s (fun X => Block.Preceq C X))
    {w: V} (hw: w ∈ rho.honest)
    (hwitnesses: (derived_state S.E S.cfg C).h <
      (voteDutyStore S rho w (s + 1)).h_max - 1 →
      FGFrontierWitnessesCompatibleAt S rho w (s + 1) C)
    (hroot: Block.Preceq
      (Protocol.get_fg_root (voteDutyStore S rho w (s + 1)).toHealing.toFG) C):
    ∃ D: Block V, Block.Preceq C D ∧
      (voteDutyStore S rho w (s + 1)).h_max - 1 ≤ (derived_state S.E S.cfg D).h ∧
      D ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w (s + 1)).toHealing.s:= by
  by_cases hband: (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
      (derived_state S.E S.cfg C).h
  · have hpositive: 0 < ((S.E.committee s) ∩ rho.honest).card:= by
      have hc:= hcom s
      omega
    obtain ⟨u, hu⟩:= Finset.card_pos.mp hpositive
    have huHon:= (Finset.mem_inter.mp hu).2
    have huCommittee:= (Finset.mem_inter.mp hu).1
    obtain ⟨D, hCD, hDrun, hDemits⟩:= hvotes u huHon huCommittee
    exact ⟨D, hCD, hband.trans (Protocol.derived_h_mono S.E S.cfg hCD),
      honestHead_voterProcessed_at_nextDuty_of_postHealingCone S adm hpost hhor
        hvotes ⟨u, huHon, huCommittee, hDrun, hDemits⟩ hw hroot⟩
  · have hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon:= by
      apply le_trans (le_of_lt ?_) hhor
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    apply higherFrontierWitness_processedDescendant S adm hmajority hw
      (hpost.trans (le_of_lt ?_)) hvoteHor (Nat.lt_of_not_ge hband)
      (hwitnesses (Nat.lt_of_not_ge hband)) hroot
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos

/-- A processed band descendant supplies the entire filtered path. -/
theorem candidatePath_of_processedBandDescendant
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    {w: V} (hw: w ∈ rho.honest) {s: Slot} {C D: Block V}
    (hCD: Block.Preceq C D)
    (hband: (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
      (derived_state S.E S.cfg D).h)
    (hDprocessed: D ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w (s + 1)).toHealing.s)
    (hroot: Block.Preceq
      (Protocol.get_fg_root (voteDutyStore S rho w (s + 1)).toHealing.toFG) C):
    C ∈ voter_candidate_tree S.E (voteDutyStore S rho w (s + 1)).toHealing ∧
      ∀ B: Block V,
        Block.Preceq (healAnchor S.E S.hc (voteDutyStore S rho w (s + 1)).toHealing) B →
        B ≠ healAnchor S.E S.hc (voteDutyStore S rho w (s + 1)).toHealing →
        Block.Preceq B C → B ≠ C →
        B ∈ voter_candidate_tree S.E (voteDutyStore S rho w (s + 1)).toHealing:= by
  let duty:= voteDutyStore S rho w (s + 1)
  let pre:= rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))
  have hdep:= Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
    adm.toDeliveryWellFormed (Protocol.vote_time S.E (s + 1)) w
  have hFJ: Block.Preceq duty.F duty.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg (S.node w) pre
      (Proofs.Bridges.reachableStore_of_depReachableStore S.E S.hc S.cfg (S.node w) hdep)
  have hDmem: D ∈ pre.T:= (Finset.mem_filter.mp hDprocessed).1
  have hagree:= derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hband': duty.h_max - 1 ≤ (duty.σ D).h:= by
    change pre.h_max - 1 ≤ (pre.σ D).h
    rw [hagree D hDmem]
    exact hband
  have hcand: ∀ B: Block V,
      Block.Preceq (Protocol.get_fg_root duty.toHealing.toFG) B →
      Block.Preceq B D → B ∈ voter_candidate_tree S.E duty.toHealing:= by
    intro B hrootB hBD
    exact Handover.candidate_mem_of_bandDescendant duty
      (Protocol.voter_processed_block_tree S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s)
      hFJ (ancestorProcessed_of_voterProcessed S adm hw hDprocessed B hBD)
      hDprocessed hBD hband' hrootB
  refine ⟨hcand C hroot hCD, ?_⟩
  intro B hAB _ hBC _
  have hrootA: Block.Preceq (Protocol.get_fg_root duty.toHealing.toFG)
      (healAnchor S.E S.hc duty.toHealing):= by
    simpa only [healAnchor_eq_get_sg_root] using
      StoreFinality.get_fg_root_preceq_get_sg_root S.E S.hc duty
  exact hcand B (Block.preceq_trans hrootA hAB) (Block.preceq_trans hBC hCD)

/-- Prior compatible FG witnesses and anchors preserve the actual next honest votes. -/
theorem goldfishCone_succ_of_frontierWitnesses
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {s: Slot} {C: Block V} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: HonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hwitnesses: ∀ w ∈ rho.honest,
      (derived_state S.E S.cfg C).h < (voteDutyStore S rho w (s + 1)).h_max - 1 →
      FGFrontierWitnessesCompatibleAt S rho w (s + 1) C)
    (hroots: ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root (voteDutyStore S rho w (s + 1)).toHealing.toFG) C = true)
    (hanchors: ∀ w ∈ rho.honest, Block.compatible
      (healAnchor S.E S.hc (voteDutyStore S rho w (s + 1)).toHealing) C = true):
    (∀ w ∈ rho.honest, Block.Preceq C (voteDutyHead S rho w (s + 1))) ∧
      HonestVotesCone S rho (s + 1) (fun X => Block.Preceq C X):= by
  have hheads: ∀ w ∈ rho.honest,
      Block.Preceq C (voteDutyHead S rho w (s + 1)):= by
    intro w hw
    apply goldfishCone_step' S adm hcom hs hpost hhor hvotes hw
    refine { anchor:= hanchors w hw, rootSide:= ?_ }
    have hcases: Block.Preceq
        (Protocol.get_fg_root (voteDutyStore S rho w (s + 1)).toHealing.toFG) C ∨
        Block.Preceq C
          (Protocol.get_fg_root (voteDutyStore S rho w (s + 1)).toHealing.toFG):= by
      simpa only [Block.compatible, Bool.or_eq_true] using hroots w hw
    rcases hcases with hroot | habove
    · obtain ⟨D, hCD, hband, hprocessed⟩:= coneBandDescendant_of_frontierWitnesses
        S adm hcom hmajority hpost hhor hvotes hw (hwitnesses w hw) hroot
      exact Or.inl ⟨hroot,
        candidatePath_of_processedBandDescendant S adm hw hCD hband hprocessed hroot⟩
    · exact Or.inr habove
  refine ⟨hheads, ?_⟩
  have hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon:= by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  intro w hw hwCommittee
  exact ⟨voteDutyHead S rho w (s + 1), hheads w hw,
    voteDutyHead_runBlock S adm hw (s + 1),
    seedVoteDutyHead_emits S adm.toScheduleWellFormed hw (Nat.succ_pos s) hwCommittee hvoteHor⟩

 -/

end WeakGoldfish
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
