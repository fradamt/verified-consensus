module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.Grades.Q31_actionSGBlock_tiers
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapGradePersistence
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationSupport

@[expose] public section

/-!
# SG compatibility before the expiry handover

Compatible previous honest SG emissions suffice under the current execution's
honest action duties. If the FG root extends P, the anchor and SG output also
extend P. If the FG root is below P, the previous SG carriers are compatible
with the finalized block at the grade cutoff and resolve in time for raw G1.

This is a local step for the joint SG/FG/Goldfish induction. The current FG
root and previous SG history remain induction inputs; no synchronized height,
expiry window, grade-existence, or one-third premise is used here.
-/

/-!
# SG compatibility before the expiry handover

Compatible previous honest SG emissions suffice under the current execution's
honest action duties. If the FG root extends P, the anchor and SG output also
extend P. If the FG root is below P, the previous SG carriers are compatible
with the finalized block at the grade cutoff and resolve in time for raw G1.

This is a local step for the joint SG/FG/Goldfish induction. The current FG
root and previous SG history remain induction inputs; no synchronized height,
expiry window, grade-existence, or one-third premise is used here.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem finalized_preceq_fgRoot_at_read
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho) (w : V) (read : Time) :
    Block.Preceq (rho.storeBeforeTime S w read).core.F
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).core.toHealing.toFG) := by
  simpa only [Run.storeBeforeTime] using
    (StoreFinality.finalized_preceq_fgRoot
      (st := (rho.storeBeforeTime S w read).core)
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho read w))
def previousSGWindowHistory
    (S : Setup V) (rho : Run V) (w : V) (n : NamedNodeState V)
    (r : Round) (P : Block V) : Prop :=
  (∀ k ∈ Protocol.latest_window S.hc.η_SG r,
    HonestSGEmissionsCompatibleAtRound S rho k P) ∧
  PhaseGrades.BatchCompatibleAt S.hc
    n.st.core.toHealing.gradeView n.st.core.F rho.honest r
    (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) P ∧
  PhaseGrades.WindowMajorityAt S.E S.hc
    n.st.core.toHealing.gradeView n.st.core.F rho.honest r
    (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) ∧
  (∀ raw, (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 =
      some (some raw) →
    ∀ A, DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw =
      some A →
    PhaseGrades.phaseGrade S.E S.hc n.st.core.toHealing.gradeView
      n.st.core.F r .g1 raw = true) ∧
  PhaseGrades.BatchCompatibleAt S.hc
    (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)
      w).st.core.toHealing.gradeView
    (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)
      w).st.core.F rho.honest r
    (DecoupledConsensusModel.Protocol.late S.E S.hc r .g2) P ∧
  PhaseGrades.WindowMajorityAt S.E S.hc
    (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)
      w).st.core.toHealing.gradeView
    (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)
      w).st.core.F rho.honest r
    (DecoupledConsensusModel.Protocol.late S.E S.hc r .g2)

/-! The action-read form used by the recovery induction. The first three
clauses are local to the prepared action read. The last two clauses are the
same window facts at the G2 domain read of the same round. -/
def PreviousSGReadSideAt
    (S : Setup V) (rho : Run V) (w : V) (r : Round) (P : Block V) : Prop :=
  let n := actionReadAt S rho w r
  PhaseGrades.BatchCompatibleAt S.hc
      n.st.core.toHealing.gradeView n.st.core.F rho.honest r
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) P ∧
  PhaseGrades.WindowMajorityAt S.E S.hc
      n.st.core.toHealing.gradeView n.st.core.F rho.honest r
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) ∧
  (∀ raw, (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 =
      some (some raw) →
    ∀ A, DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw =
      some A →
    PhaseGrades.phaseGrade S.E S.hc n.st.core.toHealing.gradeView
      n.st.core.F r .g1 raw = true) ∧
  PhaseGrades.BatchCompatibleAt S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) w).st.core.F
      rho.honest r (DecoupledConsensusModel.Protocol.late S.E S.hc r .g2) P ∧
  PhaseGrades.WindowMajorityAt S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) w).st.core.F
      rho.honest r (DecoupledConsensusModel.Protocol.late S.E S.hc r .g2)

def RecoverySGWindowInvariant
    (S : Setup V) (rho : Run V) (c : Round) (T : Block V) : Prop :=
  (∀ k : Round, k ≤ c → HonestSGEmissionsCompatibleAtRound S rho k T) ∧
  (∀ r : Round, r ≤ c + 1 → ∀ w ∈ rho.honest,
    PreviousSGReadSideAt S rho w r T)

/-- The SG recovery invariant restricted to the history at or after the
selected recovery source. Pre-settlement rounds are intentionally outside
this package. -/
def RecoverySGWindowInvariantFrom
    (S : Setup V) (rho : Run V) (source c : Round) (T : Block V) : Prop :=
  (∀ k : Round, source ≤ k → k ≤ c →
    HonestSGEmissionsCompatibleAtRound S rho k T) ∧
  (∀ r : Round, source + S.hc.η_SG ≤ r → r ≤ c + 1 → ∀ w ∈ rho.honest,
    PreviousSGReadSideAt S rho w r T)

/-- Assemble the prepared relative window required by the SG selector from the
stronger induction invariant at the next round. -/
theorem previousSGWindowHistory_of_invariant
    (S : Setup V) {rho : Run V} {c : Round} {T : Block V}
    (hinv : RecoverySGWindowInvariant S rho c T)
    {w : V} (hw : w ∈ rho.honest) :
    previousSGWindowHistory S rho w
      (actionReadAt S rho w (c + 1)) (c + 1) T := by
  unfold previousSGWindowHistory
  refine ⟨?_, ?_⟩
  intro k hk
  have hklt : k < c + 1 :=
    mem_latestWindow_lt (etaSG := S.hc.η_SG) (r := c + 1) hk
  exact hinv.1 k (Nat.lt_succ_iff.mp (by
    simpa only [Nat.succ_eq_add_one] using hklt))
  simpa only [PreviousSGReadSideAt] using
    hinv.2 (c + 1) (Nat.le_refl _) w hw

#print axioms previousSGWindowHistory_of_invariant

/-- Assemble the prepared selector window from the source-restricted
invariant once every member of the expiry window is at or after the source. -/
theorem previousSGWindowHistory_of_invariantFrom
    (S : Setup V) {rho : Run V} {source c : Round} {T : Block V}
    (hinv : RecoverySGWindowInvariantFrom S rho source c T)
    (hspan : source + S.hc.η_SG ≤ c + 1)
    {w : V} (hw : w ∈ rho.honest) :
    previousSGWindowHistory S rho w
      (actionReadAt S rho w (c + 1)) (c + 1) T := by
  unfold previousSGWindowHistory
  refine ⟨?_, ?_⟩
  · intro k hk
    have hklt : k < c + 1 :=
      mem_latestWindow_lt (etaSG := S.hc.η_SG) (r := c + 1) hk
    have hsource : source ≤ k := by
      have hlower : c + 1 - S.hc.η_SG ≤ k :=
        WeakSG.mem_latestWindow_lower_bound hk
      exact (Nat.le_sub_of_add_le hspan).trans hlower
    exact hinv.1 k hsource (Nat.lt_succ_iff.mp (by
      simpa only [Nat.succ_eq_add_one] using hklt))
  · simpa only [PreviousSGReadSideAt] using
      hinv.2 (c + 1) hspan (Nat.le_refl _) w hw

#print axioms previousSGWindowHistory_of_invariantFrom

private theorem batchCompatibleAt_of_emittedSGWindow_at_read
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {r : Round} {P : Block V}
    (hhistory : ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      HonestSGEmissionsCompatibleAtRound S rho k P)
    {w : V} (hw : w ∈ rho.honest) (read : Time)
    (p : DecoupledConsensusModel.Protocol.Phase) :
    PhaseGrades.BatchCompatibleAt S.hc
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho read w).st.core.F
      rho.honest r (DecoupledConsensusModel.Protocol.late S.E S.hc r p) P := by
  intro v hv u hu head hconfirmed hfind
  have hraw := (Finset.mem_filter.mp hu).1
  simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hraw
  obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hraw.1
  have hk' : k ∈ Protocol.latest_window S.hc.η_SG r :=
    List.mem_toFinset.mp hk
  have hroot := WeakSG.rootCompatible_of_emittedSGHistory_at_read S adm hw
    (hhistory k hk') huk (hraw.2.1 ▸ hv)
  have hfind' : Block.find? (rho.storeBeforeTime S w read).T head.root =
      some head := by
    simpa only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hfind
  simp only [Proofs.HealingLemmas.rootCompatible, hconfirmed, hfind'] at hroot
  simpa only [Block.compatible, Bool.or_comm] using hroot

set_option maxHeartbeats 400000 in
theorem interpretedInputs_nonempty_at_actionRead_of_domainRead
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {r : Round} {w : V} (hw : w ∈ rho.honest) {P : Block V}
    (hrootAction : Block.compatible
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG)
      P = true)
    {u : V} {k : Round}
    (hcarrier : Block.Preceq (actionSGBlockAt S rho u k) P)
    (htoken : ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
        S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) u,
      y.round = k ∧
      y.confirmed = some (actionSGBlockAt S rho u k).root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T
        (actionSGBlockAt S rho u k).root =
          some (actionSGBlockAt S rho u k)) :
    (DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F
      S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) u).Nonempty := by
  have hread : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ S.a r :=
    FrameForward.domain_le_a S r .g1
  have hFroot : Block.Preceq
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) := by
    exact Proofs.Records.preceq_get_fg_root_of_F
      (st := (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG)
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (S.a r) w)
  obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := htoken
  obtain ⟨hraw, hready⟩ := Finset.mem_filter.mp hy
  have hrawLater := NamedOutageClosure.q10_rawInputs_fwd S rho
    adm.toNamedScheduleWellFormed w hread (le_refl _)
    S.hc.η_SG r u hraw
  have hyLater : y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F
      S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) u := by
    refine Finset.mem_filter.mpr ⟨hrawLater, ?_⟩
    cases hyc : y.confirmed with
    | none =>
        simp only [DecoupledConsensusModel.Protocol.bodyReady, hyc]
    | some root =>
        simp only [DecoupledConsensusModel.Protocol.bodyReady, hyc] at hready ⊢
        have hroot : root = (actionSGBlockAt S rho u k).root :=
          Option.some.inj (hyc.symm.trans hyconfirmed)
        have hfindRoot : Block.find?
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView.T
            root = some (actionSGBlockAt S rho u k) := by
          rw [hroot]
          simpa only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hyfind
        cases hf : Block.find?
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView.T
            root with
        | none =>
            rw [hf] at hready
            exact absurd hready (by simp)
        | some H =>
            rw [hf, Bool.and_eq_true] at hready
            have hfindLater := NamedOutageClosure.q10_find_fwd S rho adm w hw hread hf
            have hHtarget : H = actionSGBlockAt S rho u k :=
              Option.some.inj (hf.symm.trans hfindRoot)
            have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
                (NamedRun.stateBeforeTime S rho
                  (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st :=
              (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
                (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).1.1.1
            have hHmem : H ∈
                (NamedRun.stateBeforeTime S rho
                  (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T := by
              simpa only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
                Proofs.HealingLemmas.find?_mem hf
            rw [hcoh.1] at hHmem
            obtain ⟨Hn, hHn, hHe⟩ := Finset.mem_image.mp hHmem
            obtain ⟨_, hstampeq⟩ := NamedOutageClosure.q10_strict_body_carry
              S rho adm.toNamedScheduleWellFormed w hread hHn
            have hs2 : stampedBefore
                (NamedRun.stateBeforeTime S rho
                  (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.timestamp_block
                (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) Hn.erase = true := by
              simpa only [hHe] using hready.1
            have hs1 : stampedBefore
                (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.timestamp_block
                (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) Hn.erase = true := by
              rw [stampedBefore_eq_occurrenceBefore] at hs2 ⊢
              rw [hstampeq]
              exact hs2
            have hstamp : stampedBefore
                (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.timestamp_block
                (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) H = true := by
              simpa only [hHe] using hs1
            have hPF : Block.compatible P
                (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F = true := by
              have hFP : Block.compatible
                  (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F P = true :=
                Protocol.compatible_of_preceq_of_compatible hFroot hrootAction
              simpa only [Block.compatible, Bool.or_comm] using hFP
            have hHP : Block.Preceq H P := by
              simpa only [hHtarget] using hcarrier
            rw [hfindLater, Bool.and_eq_true]
            exact ⟨hstamp,
              Protocol.compatible_of_preceq_of_compatible hHP hPF⟩
  exact ⟨y, hyLater⟩

#print axioms interpretedInputs_nonempty_at_actionRead_of_domainRead

set_option maxHeartbeats 400000 in
theorem actionReadG1FrameGrade_of_activePrefix
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) :
    ∀ w ∈ rho.honest, ∀ raw,
      (DecoupledConsensusModel.Protocol.readFrame
        (actionReadAt S rho w r).cache
        (actionReadAt S rho w r).st.core.toHealing r).g1 =
          some (some raw) →
      ∀ A, DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree
          (actionReadAt S rho w r).st.core.toHealing.toFG) raw = some A →
      PhaseGrades.phaseGrade S.E S.hc
        (actionReadAt S rho w r).st.core.toHealing.gradeView
        (actionReadAt S rho w r).st.core.F r .g1 raw = true := by
  intro w hw raw hframe A hactive
  have hframe' :
      (DecoupledConsensusModel.Protocol.readFrame
        (NamedActionReads.confirmationReadAt S rho w (S.a r)).cache
        (NamedActionReads.confirmationReadAt S rho w
          (S.a r)).st.core.toHealing r).g1 = some (some raw) := by
    simpa only [actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedDuties.update_confirmation_with,
      Protocol.update_confirmation_with,
      Protocol.NamedStore.setClock] using hframe
  have hdomainGrade := WeakSG.phaseGrade_of_preparedFrame_g1
    S rho adm w hw r hr (S.a r)
      (Proofs.HealingLemmas.round_of_slotOf_a S r)
      (NamedOutageClosure.q10_domain_lt_a S r .g1)
      (FrameForward.a_lt_opening_succ S r).le
      ((FrameForward.domain_le_a S r .g1).trans hhor) hframe'
  have hAdata := Proofs.Engine.deepest?_mem hactive
  have hAmem : A ∈ Protocol.get_filtered_block_tree
      (actionReadAt S rho w r).st.core.toHealing.toFG :=
    (Finset.mem_filter.mp hAdata).1
  have hAraw : Block.Preceq A raw := (Finset.mem_filter.mp hAdata).2
  have hFbelowA : Block.Preceq (actionReadAt S rho w r).st.core.F A :=
    NamedOutageClosure.q10_filtered_F hAmem
  have hFbelowRaw : Block.Preceq (actionReadAt S rho w r).st.core.F raw :=
    Block.preceq_trans hFbelowA hAraw
  have hpersist := WeakSG.phaseGrade_g1_persists_sameReader_of_finalizedBelow
    S adm hw hr (FrameForward.domain_le_a S r .g1)
      (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r)
      (by
        simp only [DecoupledConsensusModel.Protocol.late, DecoupledConsensusModel.Protocol.domain,
          DecoupledConsensusModel.Protocol.Phase.lateOffset,
          DecoupledConsensusModel.Protocol.Phase.domainOffset]
        linarith [S.E.Δ_pos])
      (by
        simpa only [actionReadAt, NamedActionReads.actionReadAt,
          NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedDuties.update_confirmation_with,
          Protocol.update_confirmation_with,
          Protocol.NamedStore.setClock] using hFbelowRaw)
      hdomainGrade
  simpa only [actionReadAt, NamedActionReads.actionReadAt,
    NamedActionReads.actionReadFrom,
    NamedActionReads.confirmationReadFrom,
    Protocol.NamedDuties.update_confirmation_with,
    Protocol.update_confirmation_with,
    Protocol.NamedStore.setClock] using hpersist

#print axioms actionReadG1FrameGrade_of_activePrefix

set_option maxHeartbeats 400000 in
theorem previousSGReadSideAt_of_delivery
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {cap : Time} (hdelivery : NamedHealthyPrefixDelivery S rho cap)
    (hcapHor : cap ≤ rho.horizon)
    (_hmajority : HonestWeightMajority S rho.honest)
    {base r : Round} {P : Block V}
    (hr : 0 < r)
    (hspan : base ≤ r - S.hc.η_SG)
    (hawake : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r)
    (hcarriers : ∀ k, base ≤ k → k < r → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) P)
    (hrootsAction : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho w r).st.core.toHealing.toFG) P)
    (hcapDomain : ∀ p, DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ cap)
    (haHor : S.a r ≤ rho.horizon) :
    ∀ w ∈ rho.honest, PreviousSGReadSideAt S rho w r P := by
  have htoken := WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery
    S adm.toNamedAdmissibleCore hdelivery hcapHor
      (base := base) (r := r) (D := P) hr hspan hawake hcarriers
      hrootsAction
  have hhistory : ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      HonestSGEmissionsCompatibleAtRound S rho k P := by
    intro k hk u hu hemit
    have hklt : k < r := mem_latestWindow_lt hk
    have hkbase : base ≤ k :=
      hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
    have hpre := hcarriers k hkbase hklt u hu hemit
    simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hpre
  intro w hw
  unfold PreviousSGReadSideAt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hbatch := batchCompatibleAt_of_emittedSGWindow_at_read
      S adm.toNamedAdmissibleCore hhistory hw (S.a r) .g1
    simpa only [actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedDuties.update_confirmation_with,
      Protocol.update_confirmation_with,
      Protocol.NamedStore.setClock] using hbatch
  · apply WeakSG.windowMajorityAt_of_awakeWindowMajority S hawake
    intro u hu
    obtain ⟨huHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hu
    have hklt : k < r := mem_latestWindow_lt hk
    have hkbase : base ≤ k :=
      hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
    have hdeadlineG2 : S.a k + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.early S.E S.hc r .g2 :=
      NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
    have hdeadline : S.a k + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 := by
      exact hdeadlineG2.trans (by
        simp only [DecoupledConsensusModel.Protocol.early,
          DecoupledConsensusModel.Protocol.Phase.earlyOffset]
        linarith [S.E.Δ_pos])
    have hearlyDomain : DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 :=
      NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r
    have hactionHor : S.a k ≤ rho.horizon :=
      (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (hdeadline.trans (hearlyDomain.trans
          ((hcapDomain .g1).trans hcapHor)))
    have hemit := honest_emits_exact_actionAttestationAt_of_awake
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed huHon k huk hactionHor
    have hcarrier := hcarriers k hkbase hklt u huHon hemit
    have hroot : Block.compatible
        (Protocol.get_fg_root
          (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG)
        P = true := by
      have hpre := hrootsAction w hw
      rw [actionStoreAt_fgRoot_eq_storeBeforeTime] at hpre
      simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hpre
    obtain ⟨y, hy⟩ := interpretedInputs_nonempty_at_actionRead_of_domainRead
      S adm.toNamedAdmissibleCore hw hroot hcarrier
        (htoken .g1 (hcapDomain .g1) w hw u huHon k hk huk)
    refine ⟨y, ?_⟩
    have hy' := GradeCutoffMono.interpretedInputs_mono
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F
      S.hc.η_SG r (NamedOutageClosure.q10_early_le_late S r .g1) u hy
    simpa only [actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedDuties.update_confirmation_with,
      Protocol.update_confirmation_with,
      Protocol.NamedStore.setClock] using hy'
  · exact actionReadG1FrameGrade_of_activePrefix
      S adm.toNamedAdmissibleCore hr haHor w hw
  · exact batchCompatibleAt_of_emittedSGWindow_at_read
      S adm.toNamedAdmissibleCore hhistory hw
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) .g2
  · apply WeakSG.windowMajorityAt_of_awakeWindowMajority S hawake
    intro u hu
    obtain ⟨huHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hu
    obtain ⟨y, hy, -, -, -⟩ :=
      htoken .g2 (hcapDomain .g2) w hw u huHon k hk huk
    refine ⟨y, ?_⟩
    exact GradeCutoffMono.interpretedInputs_mono
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) w).st.core.F
      S.hc.η_SG r (NamedOutageClosure.q10_early_le_late S r .g2) u hy

#print axioms previousSGReadSideAt_of_delivery

omit [Fintype V] in
private theorem compatible_of_preceq_left {A B P : Block V}
    (hAB : Block.Preceq A B) (hBP : Block.compatible B P = true) :
    Block.compatible A P = true := by
  rcases (show Block.Preceq B P ∨ Block.Preceq P B by
    simpa only [Block.compatible, Bool.or_eq_true] using hBP) with hBP' | hPB
  · simpa only [Block.compatible, Bool.or_eq_true] using
      (Or.inl (Block.preceq_trans hAB hBP'))
  · exact Block.compatible_of_preceq_common hAB hPB

private theorem getSgRoot_compatible_of_activeWindowHistory_at_read
    (S : Setup V) (n : NamedNodeState V) (r : Round) (B : Block V)
    {Hon : Finset V}
    (hbatch : PhaseGrades.BatchCompatibleAt S.hc
      n.st.core.toHealing.gradeView n.st.core.F Hon r
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) B)
    (hmajority : PhaseGrades.WindowMajorityAt S.E S.hc
      n.st.core.toHealing.gradeView n.st.core.F Hon r
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1))
    (hgrade : ∀ raw, (DecoupledConsensusModel.Protocol.readFrame n.cache
      n.st.core.toHealing r).g1 = some (some raw) →
      ∀ A, DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw =
          some A →
      PhaseGrades.phaseGrade S.E S.hc n.st.core.toHealing.gradeView
        n.st.core.F r .g1 raw = true)
    (hroot : Block.compatible
      (Protocol.get_fg_root n.st.core.toHealing.toFG) B = true) :
    Block.compatible
      (Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache)
        S.E S.hc n.st.core.toHealing r) B = true := by
  change Block.compatible
    (DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1) B = true
  cases hframe :
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 with
  | none => exact hroot
  | some opt =>
      cases opt with
      | none => exact hroot
      | some raw =>
          unfold DecoupledConsensusModel.Protocol.anchor
          simp only [Option.getD]
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree
                n.st.core.toHealing.toFG) raw with
          | none => exact hroot
          | some A =>
              have hrawGrade := hgrade raw hframe A hactive
              have hcompat : Block.compatible raw B = true := by
                by_contra hn
                have hconf : Block.conflicts raw B = true := by
                  rw [Bool.not_eq_true] at hn
                  simp only [Block.conflicts, hn, Bool.not_false]
                have hfalse := Proofs.HealingLemmas.q7_grade_eq_false_of_conflicts
                  S.E S.hc n.st.core.toHealing.gradeView n.st.core.F
                  Hon r B raw .g1 hbatch hmajority hconf
                rw [hfalse] at hrawGrade
                cases hrawGrade
              have hpre : Block.Preceq A raw := by
                unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
                exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
              exact compatible_of_preceq_left hpre hcompat

/-- The SG action step before expiry. The compatible live confirmation is
the Goldfish half of the joint invariant, not a grade-existence premise. -/
theorem actionSGBlock_compatible_of_previousSGHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {r : Round} {P : Block V} {w : V}
    (hhistory : previousSGWindowHistory S rho w
      (actionReadAt S rho w (r + 1)) (r + 1) P)
    (hpost : S.E.t_GST ≤ S.a r)
    (hhor : S.a (r + 1) ≤ rho.horizon)
    (hw : w ∈ rho.honest)
    (hroot : Block.compatible
      (Protocol.get_fg_root (actionStoreAt S rho w (r + 1)).toHealing.toFG) P = true)
    (hlive : Block.compatible (actionStoreAt S rho w (r + 1)).live_confirmed P = true) :
    Block.compatible (actionSGBlockAt S rho w (r + 1)) P = true := by
  have _ := adm
  have _ := hmajority
  have _ := hpost
  have _ := hhor
  have _ := hw
  rcases Proofs.HealingLemmas.Rows.q31_actionsgblock_tiers S rho w (r + 1) with
      hclear | hQ | hraw | hanchor
  · exact compatible_of_preceq_left hclear.2.1 hlive
  · obtain ⟨Q, hQ, hSG⟩ := hQ
    rw [hSG]
    have hgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
    apply grade_compatible_of_batchCompatible_of_faulty_lt_m S.E
      hhistory.2.2.2.2.1 hhistory.2.2.2.2.2
    simpa only [PhaseGrades.storeGrade] using hgrade
  · simpa only [hraw.2.2] using hroot
  · rw [hanchor.2.2]
    exact getSgRoot_compatible_of_activeWindowHistory_at_read S
      (actionReadAt S rho w (r + 1)) (r + 1) P
      hhistory.2.1 hhistory.2.2.1 hhistory.2.2.2.1 hroot

/-- The same prepared SG action argument at an arbitrary positive round. -/
theorem actionSGBlock_compatible_of_previousSGHistory_at_round
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V} {w : V}
    (hhistory : previousSGWindowHistory S rho w
      (actionReadAt S rho w r) r P)
    (hhor : S.a r ≤ rho.horizon)
    (hw : w ∈ rho.honest)
    (hroot : Block.compatible
      (Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG) P = true)
    (hlive : Block.compatible
      (actionStoreAt S rho w r).live_confirmed P = true) :
    Block.compatible (actionSGBlockAt S rho w r) P = true := by
  have _ := hhor
  have _ := hw
  rcases Proofs.HealingLemmas.Rows.q31_actionsgblock_tiers S rho w r with
      hclear | hQ | hraw | hanchor
  · exact compatible_of_preceq_left hclear.2.1 hlive
  · obtain ⟨Q, hQ, hSG⟩ := hQ
    rw [hSG]
    have hgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
    apply grade_compatible_of_batchCompatible_of_faulty_lt_m S.E
      hhistory.2.2.2.2.1 hhistory.2.2.2.2.2
    simpa only [PhaseGrades.storeGrade] using hgrade
  · simpa only [hraw.2.2] using hroot
  · rw [hanchor.2.2]
    exact getSgRoot_compatible_of_activeWindowHistory_at_read S
      (actionReadAt S rho w r) r P
      hhistory.2.1 hhistory.2.2.1 hhistory.2.2.2.1 hroot

#print axioms actionSGBlock_compatible_of_previousSGHistory_at_round

/-- The previous SG history and opening Goldfish cone produce the next
actual SG history. Live-confirmation compatibility and raw G1 are derived.
Only current FG-root compatibility remains as the FG induction input. -/
theorem sgEmissionsCompatible_succ_of_previousSGHistory_and_openingVotes
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {r : Round} {P : Block V}
    (hhistory : ∀ w ∈ rho.honest, previousSGWindowHistory S rho w
      (actionReadAt S rho w (r + 1)) (r + 1) P)
    (hgf : NamedHonestVotesCone S rho (S.hc.opening_slot (r + 1))
      (fun X => Block.Preceq P X))
    (hpost : S.E.t_GST ≤ S.a r)
    (hhor : S.a (r + 1) ≤ rho.horizon)
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root (actionStoreAt S rho w (r + 1)).toHealing.toFG) P = true) :
    HonestSGEmissionsCompatibleAtRound S rho (r + 1) P := by
  have hopenPost : S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot (r + 1)) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    exact hpost.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1)).le.trans
          (Γ_0_lt_Γ_1 S.hc S.E.Δ_pos (r + 1)).le)))
  have hconfHor : Protocol.confirmation_time S.E (S.hc.opening_slot (r + 1)) ≤
      rho.horizon := by rwa [opening_confirmation_time_eq_action]
  have hopen : 0 < S.hc.opening_slot (r + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hheads : ∀ x ∈ rho.honest, x ∈ S.E.committee (S.hc.opening_slot (r + 1)) →
      Block.Preceq P (voterHeadAt S rho x (S.hc.opening_slot (r + 1))) := by
    intro x hx hxc
    obtain ⟨X, hPX, hXrun, hXemit⟩ := hgf x hx hxc
    obtain ⟨H, hHerase, hHrun, hHemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits S adm.toNamedAdmissibleCore hx hopen
        hxc ((vote_time_le_confirmation_time S.E _).trans hconfHor)
    have heq := Proofs.Optimistic.emits_gfVote_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hXemit hHemit rfl
    have hroot : X.root = H.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg GoldfishVote.head heq
    have hXH : X = H := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      X H hXrun hHrun X H (Or.inl (Proofs.NamedAncestry.named_self X))
        (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
    rw [← hHerase, ← hXH]
    exact hPX
  intro w hw _
  have hroot := hroots w hw
  apply actionSGBlock_compatible_of_previousSGHistory
    S adm hmajority (hhistory w hw) hpost hhor hw hroot
  rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w (r + 1) with
    ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
  · rw [← hClive]
    simpa only [Block.compatible, Bool.or_comm] using
      (WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
        S adm.toNamedAdmissibleCore hcom hw hopen hopenPost hconfHor hC hheads)
  · rw [← hRlive, hRroot]
    rwa [actionStoreAt_fgRoot_eq_openingConfStore] at hroot

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
