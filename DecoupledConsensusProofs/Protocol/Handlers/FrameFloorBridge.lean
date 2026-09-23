module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Protocol.Schedule.RecordAtBoundary
public import DecoupledConsensusProofs.Execution.PreparedReadBridge

@[expose] public section

/-!
# Frame floors for later reads

This module connects the raw phase freeze at a domain read to the phase result
seen by a later strict or prepared read. It also contains the selector floor
used by the post-outage proof. The frame and the selector are kept in the
same named vocabulary throughout.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedOutageEntry
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## L1: a later frame result is the domain freeze -/

theorem frameG2_eq_freezeRoot_of_later_read
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (ht : domain S.E S.hc r .g2 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g2 ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t w).cache
        (NamedRun.stateBeforeTime S rho t w).st.core.toHealing r).g2 =
      some ((freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2)).map
          (fun B => DecoupledConsensusModel.Protocol.clipGrade B
            (NamedRun.stateBeforeTime S rho t w).st.core.F)) :=
  FrameCompleted.frame_g2_completed S rho core w hw r hr t ht hta hhor


theorem frameG1_eq_freezeRoot_of_later_read
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (ht : domain S.E S.hc r .g1 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g1 ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t w).cache
        (NamedRun.stateBeforeTime S rho t w).st.core.toHealing r).g1 =
      some ((freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g1) (late S.E S.hc r .g1)).map
          (fun B => DecoupledConsensusModel.Protocol.clipGrade B
            (NamedRun.stateBeforeTime S rho t w).st.core.F)) := by
  exact FrameCompleted.frame_phase_completed S rho core w hw r hr .g1 t ht hta hhor

/-! ## Prepared-read forms -/

theorem frameG2_eq_freezeRoot_of_prepared_read
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (ht : domain S.E S.hc r .g2 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g2 ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
        (NamedActionReads.confirmationReadAt S rho w t).cache
        (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing r).g2 =
      some ((freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2)).map
          (fun B => DecoupledConsensusModel.Protocol.clipGrade B
            (NamedRun.stateBeforeTime S rho t w).st.core.F)) := by
  have hbase := frameG2_eq_freezeRoot_of_later_read S rho core w hw r hr t ht hta hhor
  exact NamedOutageClosure.frame_phase_prepared_eq S rho w r .g2 t hround _ hbase

theorem frameG1_eq_freezeRoot_of_prepared_read
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (ht : domain S.E S.hc r .g1 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g1 ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
        (NamedActionReads.confirmationReadAt S rho w t).cache
        (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing r).g1 =
      some ((freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g1) (late S.E S.hc r .g1)).map
          (fun B => DecoupledConsensusModel.Protocol.clipGrade B
            (NamedRun.stateBeforeTime S rho t w).st.core.F)) := by
  have hbase := frameG1_eq_freezeRoot_of_later_read S rho core w hw r hr t ht hta hhor
  exact NamedOutageClosure.frame_phase_prepared_eq S rho w r .g1 t hround _ hbase


/-! ## The frame result carries a protected prefix -/



theorem frameG2_preceq_of_freezeRoot
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (ht : domain S.E S.hc r .g2 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g2 ≤ rho.horizon) {P raw : Block V}
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG)
    (hfreeze : freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw)
    (hPraw : Block.Preceq P raw) :
    ∃ root, (DecoupledConsensusModel.Protocol.readFrame
      (NamedRun.stateBeforeTime S rho t w).cache
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing r).g2 =
      some (some root) ∧ Block.Preceq P root := by
  let n := NamedRun.stateBeforeTime S rho t w
  have hFP : Block.Preceq n.st.core.F P := NamedOutageClosure.q10_filtered_F hPtree
  have hcompat : Block.compatible P n.st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFP
  have hclip : Block.Preceq P (DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F) :=
    (NamedOutageClosure.q10_retained_prefix raw n.st.core.F P hcompat).mpr hPraw
  refine ⟨DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F, ?_, hclip⟩
  have hframe := frameG2_eq_freezeRoot_of_later_read S rho core w hw r hr t ht hta hhor
  rw [hframe, hfreeze]
  rfl

theorem frameG1_preceq_of_freezeRoot
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (ht : domain S.E S.hc r .g1 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g1 ≤ rho.horizon) {P raw : Block V}
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG)
    (hfreeze : freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1) = some raw)
    (hPraw : Block.Preceq P raw) :
    ∃ root, (DecoupledConsensusModel.Protocol.readFrame
      (NamedRun.stateBeforeTime S rho t w).cache
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing r).g1 =
      some (some root) ∧ Block.Preceq P root := by
  let n := NamedRun.stateBeforeTime S rho t w
  have hFP : Block.Preceq n.st.core.F P := NamedOutageClosure.q10_filtered_F hPtree
  have hcompat : Block.compatible P n.st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFP
  have hclip : Block.Preceq P (DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F) :=
    (NamedOutageClosure.q10_retained_prefix raw n.st.core.F P hcompat).mpr hPraw
  refine ⟨DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F, ?_, hclip⟩
  have hframe := frameG1_eq_freezeRoot_of_later_read S rho core w hw r hr t ht hta hhor
  rw [hframe, hfreeze]
  rfl

theorem frameG2_preceq_of_freezeRoot_prepared
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (ht : domain S.E S.hc r .g2 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g2 ≤ rho.horizon) {P raw : Block V}
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing.toFG)
    (hfreeze : freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw)
    (hPraw : Block.Preceq P raw) :
    ∃ root, (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadAt S rho w t).cache
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing r).g2 =
      some (some root) ∧ Block.Preceq P root := by
  let n := NamedActionReads.confirmationReadAt S rho w t
  have hFP : Block.Preceq n.st.core.F P := NamedOutageClosure.q10_filtered_F hPtree
  have hcompat : Block.compatible P n.st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFP
  have hclip : Block.Preceq P (DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F) :=
    (NamedOutageClosure.q10_retained_prefix raw n.st.core.F P hcompat).mpr hPraw
  refine ⟨DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F, ?_, hclip⟩
  have hframe := frameG2_eq_freezeRoot_of_prepared_read S rho core w hw r hr t hround ht hta hhor
  rw [hframe, hfreeze]
  rfl


theorem frameG1_preceq_of_freezeRoot_prepared
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (ht : domain S.E S.hc r .g1 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g1 ≤ rho.horizon) {P raw : Block V}
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing.toFG)
    (hfreeze : freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1) = some raw)
    (hPraw : Block.Preceq P raw) :
    ∃ root, (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadAt S rho w t).cache
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing r).g1 =
      some (some root) ∧ Block.Preceq P root := by
  let n := NamedActionReads.confirmationReadAt S rho w t
  have hFP : Block.Preceq n.st.core.F P := NamedOutageClosure.q10_filtered_F hPtree
  have hcompat : Block.compatible P n.st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFP
  have hclip : Block.Preceq P (DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F) :=
    (NamedOutageClosure.q10_retained_prefix raw n.st.core.F P hcompat).mpr hPraw
  refine ⟨DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F, ?_, hclip⟩
  have hframe := frameG1_eq_freezeRoot_of_prepared_read S rho core w hw r hr t hround ht hta hhor
  rw [hframe, hfreeze]
  rfl

/-! ## L2: the selector anchor keeps the floor -/

theorem anchor_preceq_of_frame_floor
    (S : Setup V) (n : NamedNodeState V) (r : Round) (P : Block V)
    (hPtree : P ∈ Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)
    (hcase :
    (∃ root, (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 =
        some (some root) ∧ Block.Preceq P root) ∨
      Block.Preceq P (Protocol.get_fg_root n.st.core.toHealing.toFG)) :
    Block.Preceq P (nodeAnchor S n r) := by
  change Block.Preceq P
    (DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1)
  rcases hcase with hroot | hfg
  · obtain ⟨root, hframe, hPR⟩ := hroot
    obtain ⟨A, hA, hPA⟩ := NamedOutageClosure.activePrefix_covers hPtree hPR
    rw [hframe]
    simp only [DecoupledConsensusModel.Protocol.anchor, hA, Option.getD_some]
    exact hPA
  · unfold DecoupledConsensusModel.Protocol.anchor
    cases hframe : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 with
    | none => simpa only [hframe, Option.getD_none] using hfg
    | some opt =>
        cases opt with
        | none => simpa only [hframe, Option.getD_none] using hfg
        | some root =>
            cases hactive : DecoupledConsensusModel.Protocol.activePrefix
                (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) root with
            | none => simpa only [hframe, hactive, Option.getD_none] using hfg
            | some A =>
                simp only [hactive, Option.getD_some]
                exact Block.preceq_trans hfg
                  (Proofs.Records.preceq_get_fg_root_of_mem_filtered
                    (NamedProposalParent.activePrefix_mem _ root A hactive))



/-! ## L3: stable output across confirmation writes -/



theorem confirmationReadFrom_get_stable_eq
    (S : Setup V) (before : NamedNodeState V) (t : Time) :
    Protocol.get_stable
        (NamedActionReads.confirmationReadFrom S before t).st.core =
      Protocol.get_stable before.st.core := by
  rfl

theorem voteDutyRead_get_stable_eq
    (S : Setup V) (rho : NamedRun V) (v : V) (s : Slot) :
    Protocol.get_stable (voteDutyRead S rho v s).st.core =
      Protocol.get_stable
        (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) v).st.core := by
  rfl

theorem stable_preceq_of_stable_writes_above_of_compatible
    (S : Setup V) (rho : NamedRun V) (w : V) {P : Block V}
    (i j : Nat) (hij : i ≤ j)
    (hold : Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBefore S rho i w).st.core))
    (hwrites : ∀ (k : Nat) (t : Time), i ≤ k → k < j →
      rho.events[k]? = some (.tick w t) →
      0 < S.E.slotOf t → t = Protocol.support_cutoff S.E (S.E.slotOf t) →
      ∀ G, NamedOutageClosure.dutyStableRoot
          S (NamedActionReads.confirmationReadFrom
          S (NamedRun.stateBefore S rho k w) t) = some G → Block.Preceq P G)
    (hcompat : Block.compatible P
      (NamedRun.stateBefore S rho j w).st.core.F = true) :
    Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBefore S rho j w).st.core) := by
  have hstart : Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.F ∨
      Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.latest_stable := by
    unfold Protocol.get_stable at hold
    split at hold
    · exact Or.inr hold
    · exact Or.inl hold
  have hcases := NamedOutageClosure.stateBefore_stable_covered S rho w i j hij hstart
    (fun k t hk hkj he hpos hcut => by
      by_cases hF : Block.Preceq P
          (NamedRun.stateBefore S rho k w).st.core.F
      · exact Or.inl hF
      · exact Or.inr (fun G hG => hwrites k t hk hkj he hpos hcut G hG))
  rcases hcases with hF | hstable
  · have hFstable : Block.Preceq
        (NamedRun.stateBefore S rho j w).st.core.F
        (Protocol.get_stable (NamedRun.stateBefore S rho j w).st.core) := by
      unfold Protocol.get_stable
      split
      · assumption
      · exact Block.preceq_self _
    exact Block.preceq_trans hF hFstable
  · exact NamedOutageClosure.preceq_get_stable_of_cases _ (Or.inr hstable) hcompat

theorem stable_preceq_of_stable_writes_above_at_time
    (S : Setup V) (rho : NamedRun V) (w : V) {P : Block V}
    {t₀ t₁ : Time} {i j : Nat}
    (h₀ : NamedRun.stateBeforeTime S rho t₀ w = NamedRun.stateBefore S rho i w)
    (h₁ : NamedRun.stateBeforeTime S rho t₁ w = NamedRun.stateBefore S rho j w)
    (hij : i ≤ j)
    (hold : Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho t₀ w).st.core))
    (hwrites : ∀ (k : Nat) (t : Time), i ≤ k → k < j →
      rho.events[k]? = some (.tick w t) →
      0 < S.E.slotOf t → t = Protocol.support_cutoff S.E (S.E.slotOf t) →
      ∀ G, NamedOutageClosure.dutyStableRoot
        S (NamedActionReads.confirmationReadFrom
          S (NamedRun.stateBefore S rho k w) t) = some G → Block.Preceq P G)
    (hcompat : Block.compatible P
      (NamedRun.stateBeforeTime S rho t₁ w).st.core.F = true) :
    Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho t₁ w).st.core) := by
  rw [h₀] at hold
  rw [h₁] at hcompat ⊢
  exact stable_preceq_of_stable_writes_above_of_compatible S rho w i j hij hold hwrites hcompat



#print axioms frameG2_eq_freezeRoot_of_later_read
#print axioms frameG2_eq_freezeRoot_of_prepared_read
#print axioms frameG2_preceq_of_freezeRoot_prepared
#print axioms anchor_preceq_of_frame_floor

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
