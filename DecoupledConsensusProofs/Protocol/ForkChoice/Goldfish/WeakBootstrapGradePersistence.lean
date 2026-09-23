module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG

@[expose] public section

/-!
# Prepared G1 grade persistence to a vote duty

The frame stores the relative G1 result formed at the round's G1 domain
read. This module transports that grade to the later vote-duty read of the
same round.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakSG

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

theorem phaseGrade_g1_persists_sameReader_of_finalizedBelow
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {r : Round} (hr : 0 < r)
    {earlier later : Time} (hread : earlier ≤ later)
    (hearly : DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 ≤ earlier)
    (hlate : DecoupledConsensusModel.Protocol.late S.E S.hc r .g1 ≤ earlier)
    {B : Block V}
    (hfinalized : Block.Preceq
      (NamedRun.stateBeforeTime S rho later w).st.core.F B)
    (hgrade : Internal.PhaseGrades.phaseGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho earlier w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho earlier w).st.core.F r .g1 B = true) :
    Internal.PhaseGrades.phaseGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho later w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho later w).st.core.F r .g1 B = true := by
  let gva := (NamedRun.stateBeforeTime S rho earlier w).st.core.toHealing.gradeView
  let gvb := (NamedRun.stateBeforeTime S rho later w).st.core.toHealing.gradeView
  let Fa := (NamedRun.stateBeforeTime S rho earlier w).st.core.F
  let Fb := (NamedRun.stateBeforeTime S rho later w).st.core.F
  let ea := DecoupledConsensusModel.Protocol.early S.E S.hc r .g1
  let la := DecoupledConsensusModel.Protocol.late S.E S.hc r .g1
  apply NamedOutageClosure.q10_gradeBool_transport S.E gva gvb Fa Fb
    S.hc.η_SG r ea la ea la B
  · exact fun sender => NamedOutageClosure.q10_readyView_cut gva Fa S.hc.η_SG r
      (NamedOutageClosure.q10_early_le_late S r .g1) sender
  · exact fun sender =>
      NamedOutageClosure.q10_ready_subset_raw gva Fa S.hc.η_SG r la sender
  · exact fun sender => NamedOutageClosure.q10_readyView_cut gvb Fb S.hc.η_SG r
      (NamedOutageClosure.q10_early_le_late S r .g1) sender
  · exact fun sender =>
      NamedOutageClosure.q10_ready_subset_raw gvb Fb S.hc.η_SG r la sender
  · intro sender
    exact (Finset.image_subset_image
      (NamedOutageClosure.q10_interpreted_back S rho adm w hw
        (NamedOutageClosure.q10_early_g1_public S r hr) hearly hread
        S.hc.η_SG r sender)).trans
      (NamedOutageClosure.q10_readyView_cut gva Fa S.hc.η_SG r
        (NamedOutageClosure.q10_early_le_late S r .g1) sender)
  · intro sender
    exact Finset.image_subset_image
      (NamedOutageClosure.q10_interpreted_back S rho adm w hw
        (NamedOutageClosure.q10_late_g1_public S r hr) hlate hread
        S.hc.η_SG r sender)
  · intro sender
    exact Finset.image_subset_image
      (NamedOutageClosure.q10_rawInputs_back S rho
        adm.toNamedScheduleWellFormed w
        (NamedOutageClosure.q10_late_g1_public S r hr) hlate
        (hlate.trans hread) S.hc.η_SG r sender)
  · intro sender token htoken hcovers
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp htoken
    exact Finset.mem_image_of_mem _
      (NamedOutageClosure.q10_interpreted_fwd_cover S rho adm w hw hread
        (le_refl _) S.hc.η_SG r sender B hfinalized hu hcovers)
  · exact fun key hkey =>
      NamedOutageClosure.q10_localCovers_fwd S rho adm w hw hread key B hkey
  · simpa only [Internal.PhaseGrades.phaseGrade, gva, gvb, Fa, Fb, ea, la] using hgrade

#print axioms phaseGrade_g1_persists_sameReader_of_finalizedBelow

theorem phaseGrade_voteDuty_of_preparedFrame_g1_of_finalizedBelow
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {d : Slot} {r : Round} (hroundDuty : S.hc.round_of d = r)
    (hr : 0 < r)
    (hnext : Protocol.vote_time S.E d ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1))
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    {read : NamedNodeState V}
    (hread : Internal.NamedRecoveryRead.voteDutyRead S rho w d = read) :
    ∀ raw,
      (DecoupledConsensusModel.Protocol.readFrame
        read.cache read.st.core.toHealing r).g1 = some (some raw) →
      Block.Preceq read.st.core.F raw →
      Internal.PhaseGrades.phaseGrade S.E S.hc
        read.st.core.toHealing.gradeView read.st.core.F r .g1 raw = true := by
  intro raw hframe hfinalized
  have hopen : S.hc.opening_slot (S.hc.round_of d) ≤ d :=
    Nat.div_mul_le_self d S.hc.R
  have hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc
      r .g1 < Protocol.vote_time S.E d := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (proposal_time_mono S.E (by simpa only [hroundDuty] using hopen)).trans_lt
      (proposal_time_lt_vote_time S.E d)
  have hround : S.hc.round_of
      (S.E.slotOf (Protocol.vote_time S.E d)) = r := by
    simpa only [Proofs.Optimistic.slotOf_vote_time] using hroundDuty
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc
      r .g1 ≤ rho.horizon :=
    hdomainVote.le.trans hhor
  have hdomainGrade := phaseGrade_of_preparedFrame_g1 S rho adm w hw
    r hr (Protocol.vote_time S.E d) hround hdomainVote hnext hdomainHor
    (by simpa only [← hread] using hframe)
  have hearly : DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 :=
    NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r
  have hlate : DecoupledConsensusModel.Protocol.late S.E S.hc r .g1 ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 := by
    simp only [DecoupledConsensusModel.Protocol.late, DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.lateOffset, DecoupledConsensusModel.Protocol.Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have hpersist := phaseGrade_g1_persists_sameReader_of_finalizedBelow
    S adm hw hr hdomainVote.le hearly hlate
    (by simpa only [← hread, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hfinalized)
    hdomainGrade
  simpa only [← hread, Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
    using hpersist

#print axioms phaseGrade_voteDuty_of_preparedFrame_g1_of_finalizedBelow

private theorem persistentAncestorCompatible {A C B : Block V}
    (hAC : Block.Preceq A C) (hCB : Block.compatible C B = true) :
    Block.compatible A B = true := by
  have hcases : Block.Preceq C B ∨ Block.Preceq B C := by
    simpa only [Block.compatible, Bool.or_eq_true] using hCB
  rcases hcases with h | h
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hAC h)
  · exact Block.compatible_of_preceq_common hAC h

/-- A completed G1 root keeps its grade when it has an active prefix at the
later vote read. Activity supplies the finalized-chain floor needed by
same-reader transport. -/
theorem phaseGrade_voteDuty_of_preparedFrame_g1_of_activePrefix
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {d : Slot} {r : Round} (hroundDuty : S.hc.round_of d = r)
    (hr : 0 < r)
    (hnext : Protocol.vote_time S.E d ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1))
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    {read : NamedNodeState V}
    (hread : Internal.NamedRecoveryRead.voteDutyRead S rho w d = read)
    {raw A : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
      read.cache read.st.core.toHealing r).g1 = some (some raw))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (Protocol.get_filtered_block_tree read.st.core.toHealing.toFG) raw =
        some A) :
    Internal.PhaseGrades.phaseGrade S.E S.hc
      read.st.core.toHealing.gradeView read.st.core.F r .g1 raw = true := by
  have hAdata := Proofs.Engine.deepest?_mem hactive
  have hAmem : A ∈ Protocol.get_filtered_block_tree
      read.st.core.toHealing.toFG := (Finset.mem_filter.mp hAdata).1
  have hAraw : Block.Preceq A raw := (Finset.mem_filter.mp hAdata).2
  have hFbelowA : Block.Preceq read.st.core.F A :=
    NamedOutageClosure.q10_filtered_F hAmem
  have hFbelowRaw : Block.Preceq read.st.core.F raw :=
    Block.preceq_trans hFbelowA hAraw
  exact phaseGrade_voteDuty_of_preparedFrame_g1_of_finalizedBelow
    S adm hroundDuty hr hnext hhor hw hread raw hframe hFbelowRaw





#print axioms phaseGrade_voteDuty_of_preparedFrame_g1_of_activePrefix



/-- A prepared vote-duty G1 anchor is compatible with the retained batch.
Only its active prefix needs grade persistence; an inactive saved root uses
the FG-root fallback. -/
theorem getSgRoot_compatible_of_windowHistory_at_voteDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {d : Slot} {r : Round} (hroundDuty : S.hc.round_of d = r)
    (hr : 0 < r)
    (hnext : Protocol.vote_time S.E d ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1))
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {B : Block V}
    (hbatch : Internal.PhaseGrades.BatchCompatibleAt S.hc
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.gradeView
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F
      rho.honest r (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) B)
    (hmajority : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.gradeView
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F
      rho.honest r (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1))
    (hroot : Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG)
      B = true) :
    Block.compatible
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).cache)
        S.E S.hc
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing r)
      B = true := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w d
  change Block.compatible
    (DecoupledConsensusModel.Protocol.anchor S.E S.hc read.st.core.toHealing r
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing r).g1) B = true
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame
      read.cache read.st.core.toHealing r).g1 with
  | none => exact hroot
  | some opt =>
      cases opt with
      | none => exact hroot
      | some raw =>
          unfold DecoupledConsensusModel.Protocol.anchor
          simp only [Option.getD]
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree
                read.st.core.toHealing.toFG) raw with
          | none => exact hroot
          | some A =>
              have hrawGrade :=
                phaseGrade_voteDuty_of_preparedFrame_g1_of_activePrefix
                S adm hroundDuty hr hnext hhor hw (read := read) rfl hframe hactive
              have hrawCompat : Block.compatible raw B = true := by
                by_contra hn
                have hconf : Block.conflicts raw B = true := by
                  rw [Bool.not_eq_true] at hn
                  simp only [Block.conflicts, hn, Bool.not_false]
                have hfalse := Proofs.HealingLemmas.q7_grade_eq_false_of_conflicts
                  S.E S.hc read.st.core.toHealing.gradeView read.st.core.F
                  rho.honest r B raw .g1 hbatch hmajority hconf
                rw [hfalse] at hrawGrade
                cases hrawGrade
              have hAraw : Block.Preceq A raw := by
                unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
                exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
              have hAcompat := persistentAncestorCompatible hAraw hrawCompat
              simpa only [hactive, Option.getD_some] using hAcompat



end WeakSG
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
