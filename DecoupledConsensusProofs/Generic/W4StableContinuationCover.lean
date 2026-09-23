module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.W4GSTZeroOpeningLifecycle

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Selected-opening continuation cover

The phase-shift safety record starts at the selected opening. Its honest
proposal clauses apply only to openings strictly after that start. This leaf
keeps the start guard in the stable-record continuation route.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace W4StableWrite

open Internal Execution Statements Proofs.HealingSurface
open Internal.PhaseGrades DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The selected honest proposal remains below every later honest action
read's live confirmation. This is the continuation twin of
`w4_proposal_preceq_actionLiveConfirmed_gstZero` in
`W4GSTZeroOpeningLifecycleRun`: the phase-shift record supplies the opening
equality and the post-start monotonicity. -/
theorem w4_proposal_preceq_actionLiveConfirmed_afterGST
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    {cut q k : Round} {start : Slot} {seed : Block V}
    (hphase : PhaseShiftSafety S rho cut start seed)
    (hq : start < S.hc.opening_slot q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hqk : q ≤ k) (hhor : S.a k ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.Preceq P.erase
        (actionStoreAt S rho v k).st.core.live_confirmed := by
  intro v hv
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S hqk).trans hhor
  have hconfq : Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤
      rho.horizon := by
    simpa only [Proofs.HealingSurface.opening_confirmation_time_eq_action S q] using hqhor
  obtain ⟨P', hP', hrecord⟩ :=
    hphase.honestProposalLive (S.hc.opening_slot q) hq hconfq hprop
  have hPP' : P' = P := by
    have h := hP'.symm.trans hP
    exact Option.some.inj h
  subst P'
  have hstartq : Protocol.confirmation_time S.E start ≤ S.a q := by
    exact confirmation_start_le_action S hq.le
  have hmono := hphase.liveMonotone v hv (S.a q) (S.a k)
    hstartq (Assembly.a_mono S hqk)
  rw [w4_actionStore_liveConfirmed_eq_storeAt S
    core.toNamedScheduleWellFormed hv k hhor]
  rw [← Proofs.HealingSurface.opening_confirmation_time_eq_action S q, hrecord v hv] at hmono
  exact hmono

#print axioms w4_proposal_preceq_actionLiveConfirmed_afterGST

/-- The prepared four-tier SG selector carries the selected proposal once the
round's live confirmation is clear. On the root-write arm, the proposal is
below the FG root, and every selected Q2 is itself in the FG-root-filtered
tree. The selected-Q2 tier therefore needs no grade premise here. -/
theorem w4_persistenceCoverStep_afterGST_of_localReads
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    {cut q k : Round} {start : Slot} {seed : Block V}
    (hphase : PhaseShiftSafety S rho cut start seed)
    (hq : start < S.hc.opening_slot q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hqk : q ≤ k) (hhor : S.a k ≤ rho.horizon)
    (hclear : ∀ v ∈ rho.honest,
      nodeClear S (actionReadAt S rho v k) k
        (actionStoreAt S rho v k).st.core.live_confirmed = true) :
    ∀ v ∈ rho.honest,
      Block.Preceq P.erase (actionSGBlockAt S rho v k) := by
  intro v hv
  have hlive : Block.Preceq P.erase
      (actionStoreAt S rho v k).st.core.live_confirmed :=
    w4_proposal_preceq_actionLiveConfirmed_afterGST S core hphase hq
      hprop hP hqk hhor v hv
  rcases w4_anchor_preceq_liveConfirmed_or_fgRoot S rho v k with hanch | hroot
  · have hvote : actionSGBlockAt S rho v k =
        (actionStoreAt S rho v k).st.core.live_confirmed :=
      w4_actionSGBlockAt_eq_liveConfirmed S rfl (Block.preceq_self _) rfl
        hanch (hclear v hv)
    rw [hvote]
    exact hlive
  · have hBfg : Block.Preceq P.erase
        (Protocol.get_fg_root
          (actionReadAt S rho v k).st.core.toHealing.toFG) := by
      rw [← hroot]
      exact hlive
    have hBanchor : Block.Preceq P.erase
        (nodeAnchor S (actionReadAt S rho v k) k) :=
      Block.preceq_trans hBfg
        (w4_fgRoot_preceq_nodeAnchor S (actionReadAt S rho v k) k)
    rcases Proofs.HealingSurface.actionSGBlockAt_tiers S rho v k with
      ⟨hA, -, -⟩ | ⟨Q, hQ, hvote⟩ | ⟨-, -, hvote⟩ | ⟨-, -, hvote⟩
    · exact Block.preceq_trans hBanchor hA
    · rw [hvote]
      exact Block.preceq_trans hBfg
        (Proofs.Records.preceq_get_fg_root_of_mem_filtered
          (Proofs.HealingSurface.actionQ2_mem_filteredTree S rho v k hQ))
    · rw [hvote]
      exact hBfg
    · rw [hvote]
      exact hBanchor

#print axioms w4_persistenceCoverStep_afterGST_of_localReads

end W4StableWrite
end Proofs
end DecoupledConsensusModel

end
