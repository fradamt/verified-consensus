module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory
public import DecoupledConsensusProofs.Objects.PostExitWindows
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-! # Reader-local candidates from FG confirmation witnesses
A height change does not require equal honest frontiers. If the previous cone
block reaches the reader's band, an previous honest Goldfish head supplies the
candidate. Otherwise an honest action in a progress quorum supplies a higher
checkpoint. Compatibility with that checkpoint is an induction obligation;
its height, provenance, and timely relay are proved here.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.Optimistic
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]




/-- An action before the slot-(s+1) vote evaluates a confirmation from a
strictly earlier slot than s. This also covers two-slot rounds. -/
theorem openingNext_le_of_action_before_nextVote
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.vote_time S.E (s + 1)) :
    S.hc.opening_slot r + 1 ≤ s := by
  change S.hc.a S.E.Δ r < Protocol.vote_time S.E (s + 1) at h
  rw [Protocol.a_eq_support_cutoff_succ S.hc S.E r] at h
  by_contra hn
  have hs : s + 1 ≤ S.hc.opening_slot r + 1 :=
    Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
  have hvote : Protocol.vote_time S.E (s + 1) <
      Protocol.support_cutoff S.E (s + 1) := by
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  exact (not_lt_of_ge (le_of_lt h))
    (hvote.trans_le (Proofs.Optimistic.support_cutoff_mono S.E hs))

/-- An action before the next vote is no later than the previous slot's
support cutoff. This leaves one delay for relay before the freeze. -/
theorem action_le_supportCutoff_of_lt_nextVote
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.vote_time S.E (s + 1)) :
    S.a r ≤ Protocol.support_cutoff S.E s := by
  change S.hc.a S.E.Δ r ≤ Protocol.support_cutoff S.E s
  rw [Protocol.a_eq_support_cutoff_succ S.hc S.E r]
  exact Proofs.Optimistic.support_cutoff_mono S.E (openingNext_le_of_action_before_nextVote S h)






/-
/-- The next duty has a processed descendant of the cone block at its own
height band. Neither a shared frontier nor a below-one-third bound is used. -/
theorem coneBandDescendant_of_frontierWitnesses
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
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

/-- A processed band descendant preserves the cone block and its walk path
in the candidate tree. Root ancestry supplies the finalized-root guard. -/
theorem candidatePath_of_processedBandDescendant
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
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
  let pre:= rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))
  have hdep:= Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
    adm.toDeliveryWellFormed (Protocol.vote_time S.E (s + 1)) w
  have hDmem: D ∈ pre.T:= by
    exact (Finset.mem_filter.mp hDprocessed).1
  have hclosed:= parentClosed_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hCmem: C ∈ pre.T:=
    Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hclosed).2 C D hDmem hCD
  have hagree:= derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hFC: Block.Preceq pre.F C:=
    Block.preceq_trans (finalizedRoot_preceq_fgRoot S adm) hroot
  have hV: C ∈ Protocol.V_tree pre.toHealing.toFG:= by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq]
    refine ⟨⟨hCmem, hFC⟩, D, hDmem, hCD, ?_⟩
    rw [hagree D hDmem]
    exact hband
  have hfiltered: C ∈ Protocol.get_filtered_block_tree
      (voteDutyStore S rho w (s + 1)).toHealing.toFG:=
    Proofs.Records.mem_filtered_of_mem_V_tree hV hroot
  have hmax:= Nat.sub_le_iff_le_add.mp hband
  refine ⟨ancestorCandidate_of_processedDescendant_and_hMax
    S adm hw hDprocessed hCD hfiltered hmax, ?_⟩
  intro B hanchor hne hBC _
  exact ancestorCandidate_of_processedDescendant_and_hMax S adm hw hDprocessed
    (Block.preceq_trans hBC hCD)
    (Protocol.votePath_of_candidate S adm hfiltered B hanchor hne hBC) hmax

/-- One safety step with reader-local frontier witnesses. The compatibility
fields are obligations of the joint FG/SG induction. Candidate retention is
not an additional premise, and the step uses no fixed-height frame, source
upper bound, full SG representation, or below-one-third bound. -/
theorem goldfishCone_succ_of_frontierWitnesses
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
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
    seedVoteDutyHead_emits S adm hw (Nat.succ_pos s) hwCommittee hvoteHor⟩

 -/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
