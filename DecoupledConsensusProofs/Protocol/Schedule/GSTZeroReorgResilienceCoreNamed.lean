module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Execution.WeakGenesisCanonicalProposalDutyClosed
public import DecoupledConsensusProofs.Protocol.Grades.WeakProposalPivotNamed
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroActionHead

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Core GST-zero reorganization resilience for named proposal reads -/

namespace DecoupledConsensusModel
namespace Protocol

open Internal Execution Proofs.Optimistic
open Proofs.HealingSurface Statements
open DecoupledConsensusModel.Proofs
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At the source vote read, every honest voter returns the bound named
proposal. -/
theorem voteDutyHead_eq_proposedBlock_gstZero_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {v : V} (hv : v ∈ rho.honest) :
    voterHeadAt S rho v s = B.erase := by
  have hstores := Proofs.HealingSurface.WeakGenesis.honestVoteStoresExtend_positive_of_gstZero
    S h hs hsourceHor hprop hB v hv
  exact voterHeadAt_eq_proposedBlockAt_of_namedVoteStoreExtends S hB hstores

#print axioms voteDutyHead_eq_proposedBlock_gstZero_core

/-- The prepared next-vote anchor is below every current honest voter head.
This is the core-admissible named counterpart used at the final vote-horizon
step. -/
theorem preparedVoterAnchor_preceq_voteDutyHead_of_gstZero_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last d : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1)
    (hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq (voterAnchorAt S rho w (d + 1))
      (voterHeadAt S rho x d) := by
  let s := d + 1
  let t := Protocol.vote_time S.E s
  let read := voteDutyRead S rho w s
  let r := S.hc.round_of s
  have hroundT : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, r, Proofs.Optimistic.slotOf_vote_time]
  have hreadRound : S.hc.round_of read.st.core.s = r := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_vote_time, r, t]
  have hdomain : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 < t := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (proposal_time_mono S.E (Nat.div_mul_le_self s S.hc.R)).trans_lt
      (proposal_time_lt_vote_time S.E s)
  have htop : DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) ≥ t := by
    simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
      (NamedOutageClosure.clockRound_lt_opening_succ S t).le
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon :=
    hdomain.le.trans hvoteHor
  have hfg : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterHeadAt S rho x d) := by
    simpa only [read, t, s, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      voteDutyHead] using
      Proofs.HealingSurface.WeakGenesis.fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
        S h.core h.committees h.gstZero h.windows hhor hd hupper
          (t := t) (le_refl _) hw hx
  rcases voterAnchorAt_cases S rho w s with hanchorFG |
      ⟨raw, A, hframe, hactive, hanchorA⟩
  · rw [show voterAnchorAt S rho w s =
        Protocol.get_fg_root read.st.core.toHealing.toFG by
          simpa only [read] using hanchorFG]
    exact hfg
  · have hanchorA' : voterAnchorAt S rho w s = A := by
      simpa only [read] using hanchorA
    rw [hanchorA']
    have hAraw : Block.Preceq A raw := by
      unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
      exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
    have hframeR := hframe
    change (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
      (S.hc.round_of read.st.core.s)).g1 = some (some raw) at hframeR
    rw [hreadRound] at hframeR
    by_cases hr0 : r = 0
    · have htne : t ≠ DecoupledConsensusModel.Protocol.domain S.E S.hc 0 .g1 := by
        have hdomain0 : DecoupledConsensusModel.Protocol.domain S.E S.hc 0 .g1 < t := by
          simpa only [hr0] using hdomain
        exact ne_of_gt hdomain0
      have hno := Proofs.HealingSurface.WeakGenesis.confirmationRead_g1_round_zero_no_root
        S h.core w t (by simpa only [hr0] using hroundT) htne (root := raw)
      exact False.elim (hno (by
        simpa only [read, voteDutyRead, t, hr0] using hframeR))
    · have hr : 0 < r := Nat.pos_of_ne_zero hr0
      have hgrade := Proofs.HealingSurface.WeakSG.phaseGrade_of_preparedFrame_g1
        S rho h.core w hw r hr t hroundT hdomain htop hdomainHor
          (raw := raw) (by
            simpa only [read, voteDutyRead, t] using hframeR)
      have hpostEarly : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.early S.E S.hc r .g2 := by
        rw [h.gstZero]
        exact (Proofs.HealingLemmas.a_nonneg S (r - 1)).trans
          (le_add_of_nonneg_right S.E.Δ_pos.le) |>.trans
            (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
              (Nat.sub_lt hr (by decide)))
      have hdelivery : TwoCutoffDelivery S rho r :=
        Proofs.HealingSurface.twoCutoffDelivery_of_core S h.core hpostEarly
      have hprevHor : S.a (r - 1) ≤ rho.horizon := by
        have hprev : S.a (r - 1) + S.E.Δ ≤ DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 :=
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
            (Nat.sub_lt hr (by decide))).trans
            (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
        exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (hprev.trans ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
            S r).trans hdomainHor))
      have hcarrier := Proofs.HealingSurface.relativeGradeCarrierAt_of_awakeWindowMajority
        S h.core hr (h.windows r hr hprevHor) (p := .g1) (by
          intro y hy u hu k hk huk
          have hklt : k < r := mem_latestWindow_lt hk
          have hdeadline : S.a k + S.E.Δ ≤ DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 :=
            (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt).trans
              (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
          have hactionTime : S.a k < Protocol.vote_time S.E s :=
            (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
              (hdeadline.trans
                ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                  S r).trans hdomain.le))
          have hAhead :=
            (Proofs.HealingSurface.WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero
              S h.core h.committees h.gstZero h.windows hhor hd hupper hx
                k hactionTime).1 u hu
              (Proofs.HealingSurface.honest_emits_exact_actionAttestationAt_of_awake S
                h.core.toNamedScheduleWellFormed hu k huk (by
                  exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
                    (hdeadline.trans
                      ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                        S r).trans hdomainHor))))
          have hfgY :=
            Proofs.HealingSurface.WeakGenesis.fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
              S h.core h.committees h.gstZero h.windows hhor hd hupper
                (t := DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) hdomain.le hy hx
          have hFJY := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
            S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) y
          have hFrootY : Block.Preceq
              (NamedRun.stateBeforeTime S rho
                (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) y).st.core.F
              (Protocol.get_fg_root
                (NamedRun.stateBeforeTime S rho
                  (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) y).st.core.toHealing.toFG) :=
            Proofs.Records.preceq_get_fg_root_of_F (st :=
              (NamedRun.stateBeforeTime S rho
                (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) y).st.core.toHealing.toFG) hFJY
          have hFheadY : Block.Preceq
              (NamedRun.stateBeforeTime S rho
                (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) y).st.core.F
              (voterHeadAt S rho x d) :=
            Block.preceq_trans hFrootY (by
              simpa only [Run.storeBeforeTime, voteDutyHead] using hfgY)
          exact NamedOutageClosure.honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible
            S rho h.core h.gstZero hdelivery r k .g1 hk y hy hdomainHor hdeadline
              ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mpr
                ⟨hu, actionAttestationAt S rho u k,
                  (Proofs.HealingSurface.actionAttestationAt_shape S rho u k).1,
                  (Proofs.HealingSurface.actionAttestationAt_shape S rho u k).2.1,
                  Proofs.HealingSurface.honest_emits_exact_actionAttestationAt_of_awake S
                    h.core.toNamedScheduleWellFormed hu k huk (by
                      exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
                        (hdeadline.trans
                          ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                            S r).trans hdomainHor)))⟩)
              (Block.compatible_of_preceq_common hFheadY hAhead))
      obtain ⟨k, hk, u, hu, hemit, hraw⟩ := hcarrier w hw raw
        (by simpa only [PhaseGrades.phaseGrade] using hgrade)
      have hklt : k < r := mem_latestWindow_lt hk
      have hactionTime : S.a k < Protocol.vote_time S.E s := by
        calc
          S.a k < S.a k + S.E.Δ := Int.lt_add_of_pos_right _ S.E.Δ_pos
          _ ≤ DecoupledConsensusModel.Protocol.early S.E S.hc r .g2 :=
            NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
          _ ≤ DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 :=
            NamedOutageClosure.q10_early_g2_le_early_g1 S r
          _ ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 :=
            NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r
          _ < t := hdomain
      exact Block.preceq_trans hAraw (Block.preceq_trans hraw
        ((Proofs.HealingSurface.WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero
          S h.core h.committees h.gstZero h.windows hhor hd hupper hx
            k hactionTime).1 u hu hemit))

#print axioms preparedVoterAnchor_preceq_voteDutyHead_of_gstZero_core

/-- A current named honest head is processed at the next prepared vote read
using only the current support-cutoff horizon. -/
theorem honestHead_voterProcessed_at_nextDuty_at_cutoff_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {C H : Block V}
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hH : HonestHead S rho s H)
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    H ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
      (voteDutyRead S rho w (s + 1)).st.core.s := by
  let read := voteDutyRead S rho w (s + 1)
  have havailable :=
    Proofs.HealingSurface.honestHeadsAvailableBefore_of_namedPostHealingCone_core
      S core hw hpost hhor hroot hvotes
  have hslot : read.st.core.s = s + 1 := by
    simpa only [read] using voteDutyRead_slot S rho w (s + 1)
  rcases havailable H hH with hgen | hadmit
  · subst H
    have hgenesis := genesis_mem_and_stamp_storeBeforeTime S
      core.toNamedScheduleWellFormed w (Protocol.vote_time S.E (s + 1))
        (Protocol.view_freeze S.E s)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.Store.toHealing] using hgenesis.1,
      Or.inl (by
        simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          Protocol.Store.toHealing] using hgenesis.2)⟩
  · have hvisible := admittedBefore_mem_and_stamp_at S
      core.toNamedScheduleWellFormed hadmit
      (le_trans (le_of_lt (support_cutoff_lt_view_freeze S.E s))
        (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
    have hstampCut : stampedBefore read.st.core.timestamp_block
        (Protocol.support_cutoff S.E s) H = true := by
      simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hvisible.2
    have hstampFreeze : stampedBefore read.st.core.timestamp_block
        (Protocol.view_freeze S.E s) H = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hstampCut ⊢
      exact occurrenceBefore_mono
        (le_of_lt (support_cutoff_lt_view_freeze S.E s)) hstampCut
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.Store.toHealing] using hvisible.1,
      Or.inl hstampFreeze⟩

#print axioms honestHead_voterProcessed_at_nextDuty_at_cutoff_core

/-- A named run block held at a prepared vote read has its `derive_named`
height in that read. -/
theorem storedHeight_of_runBlock_mem_voteDutyRead_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {X : NamedBlock V}
    (hXrun : RunBlock S rho X)
    (hXmem : X.erase ∈ (voteDutyRead S rho w s).st.core.T) :
    ((voteDutyRead S rho w s).st.core.σ X.erase).h =
      (Protocol.derive_named S.E S.cfg X).h := by
  obtain ⟨X', hX', hX'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E s) w (by
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hXmem)
  have hX'run : RunBlock S rho X' := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      core.toNamedScheduleWellFormed.sorted (Protocol.vote_time S.E s)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
    change X' ∈ (NamedRun.stateBefore S rho i w).st.bodies
    rw [← hi]
    exact hX'
  have hX'eq : X' = X :=
    core.toNamedRootCollisionFree.root_injective X' X hX'run hXrun X' X
      (Or.inl (Proofs.NamedAncestry.named_self X'))
      (Or.inr (Proofs.NamedAncestry.named_self X)) (by
        rw [← Proofs.NamedWire.erase_root X', ← Proofs.NamedWire.erase_root X, hX'erase])
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (Protocol.vote_time S.E s) w X (by
      simpa only [hX'eq] using hX')
  simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock] using congrArg (fun st => st.h) hview

#print axioms storedHeight_of_runBlock_mem_voteDutyRead_core

/-- Core-admissible transport from a later FG-root bound to the finalized
root at an earlier delivery event. -/
theorem finalized_preceq_at_delivery_of_storeBeforeRoot_preceq_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    {Gamma : Time} {v : V} {B : Block V} {X : NamedBlock V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v Gamma).core.toHealing.toFG) B)
    {i : Nat} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block X) t))
    (hlt : t < Gamma) :
    Block.Preceq (rho.stateBefore S i v).st.core.F B := by
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hGamma : Gamma ≤ t :=
      le_time_of_index_ge S core.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := Event.deliver v (Object.block X) t)
        (by simpa only [n] using hni) hi
    exact (not_le_of_gt hlt) hGamma
  have hstore : rho.storeBeforeTime S v Gamma =
      (rho.stateBefore S n v).st := by
    show (NamedRun.stateBeforeTime S rho Gamma v).st = _
    rw [show NamedRun.stateBeforeTime S rho Gamma v =
      NamedRun.stateBefore S rho n v from
        congrFun (stateBeforeTime_eq_take S core.toNamedScheduleWellFormed Gamma) v]
  have hmono : Block.Preceq (rho.stateBefore S i v).st.core.F
      (rho.storeBeforeTime S v Gamma).core.F := by
    rw [hstore]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
  have hFJ : Block.Preceq (rho.storeBeforeTime S v Gamma).core.F
      (rho.storeBeforeTime S v Gamma).core.J := by
    rw [hstore]
    exact Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore S rho n v
  have hFroot : Block.Preceq (rho.storeBeforeTime S v Gamma).core.F
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v Gamma).core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F
      (st := (rho.storeBeforeTime S v Gamma).core.toHealing.toFG) hFJ
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot)

#print axioms finalized_preceq_at_delivery_of_storeBeforeRoot_preceq_core

/-- A named action body below the next vote reader's FG root is processed at
that vote reader under the actual vote horizon. -/
theorem actionBlockProcessedAtNextDuty_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    {u w : V} (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {r : Round} {s : Slot} {T : NamedBlock V}
    (hmem : T ∈ (actionStoreAt S rho u r).st.bodies)
    (haction : S.a r < Protocol.vote_time S.E (s + 1))
    (hpost : S.E.t_GST ≤ Protocol.support_cutoff S.E s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
      T.erase) :
    T.erase ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
      (voteDutyRead S rho w (s + 1)).st.core.s := by
  let action := actionStoreAt S rho u r
  let pre := rho.storeBeforeTime S u (S.a r)
  have hcoherent : Proofs.NamedStore.Coherent S.E S.cfg action.st := by
    have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg action.st := by
      apply Proofs.NamedConfirmationMembership.invariant_update
      exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) u).1
    exact hinv.1.1
  have hactionT : T.erase ∈ action.st.core.T := by
    rw [hcoherent.1]
    exact Finset.mem_image.mpr ⟨T, hmem, rfl⟩
  have hpre : T.erase ∈ pre.core.T := by
    have hactionT' := hactionT
    change T.erase ∈ (actionStoreAt S rho u r).T at hactionT'
    rw [actionStoreAt_T S rho u r] at hactionT'
    simpa only [pre] using hactionT'
  have hopening : S.hc.opening_slot r + 1 ≤ s := by
    change S.hc.a S.E.Δ r < Protocol.vote_time S.E (s + 1) at haction
    rw [Protocol.a_eq_support_cutoff_succ S.hc S.E r] at haction
    by_contra hn
    have hs : s + 1 ≤ S.hc.opening_slot r + 1 :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
    have hvote : Protocol.vote_time S.E (s + 1) <
        Protocol.support_cutoff S.E (s + 1) := by
      rw [← vote_time_add_delta]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    exact (not_lt_of_ge (le_of_lt haction))
      (hvote.trans_le (support_cutoff_mono S.E hs))
  have hcut : S.a r ≤ Protocol.support_cutoff S.E s := by
    change S.hc.a S.E.Δ r ≤ Protocol.support_cutoff S.E s
    rw [Protocol.a_eq_support_cutoff_succ S.hc S.E r]
    exact support_cutoff_mono S.E hopening
  have hfreezeVote : Protocol.view_freeze S.E s ≤
      Protocol.vote_time S.E (s + 1) :=
    (view_freeze_lt_vote_time_succ S.E s).le
  have hrelay : T.erase = Block.genesis ∨
      AdmittedBefore S rho w T.erase (Protocol.view_freeze S.E s) := by
    rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
        core.toNamedScheduleWellFormed u (S.a r) hpre with
      hgen | ⟨D, i, t, hDeq, hacc, ht⟩
    · exact Or.inl hgen
    · right
      have hrootD : Block.Preceq
          (Protocol.get_fg_root
            (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
          D.erase := by
        simpa only [hDeq] using hroot
      have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho w D
          (Protocol.view_freeze S.E s) := by
        intro j hj
        have hjVote := hj.trans (strict_filter_length_mono rho
          (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
        have hroot' : Block.Preceq
            (Protocol.get_fg_root
              (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).toHealing.toFG)
              D.erase := by
          simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
            Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore] using hrootD
        exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
          S rho core.toNamedScheduleWellFormed.sorted hroot' hjVote
      have hadmit := block_admittedBefore_of_accepted_after_cutoff_core
        S core hu hw (by
          rw [← Proofs.NamedWire.erase_slot D]
          exact Nat.zero_lt_of_lt
            (parent_slot_lt_of_acceptsAt_block S hacc))
        hacc (ht.trans_le hcut) hpost
        (support_cutoff_add_delta_eq_view_freeze S.E s)
        (hfreezeVote.trans hhor) hFhist
      simpa only [hDeq] using hadmit
  have hvis : T.erase ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).T ∧
      stampedBefore
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (s + 1))).timestamp_block
        (Protocol.view_freeze S.E s) T.erase = true := by
    rcases hrelay with hgen | hadmit
    · simpa only [hgen] using
        (genesis_mem_and_stamp_storeBeforeTime S
          core.toNamedScheduleWellFormed w
          (Protocol.vote_time S.E (s + 1))
          (Protocol.view_freeze S.E s))
    · exact admittedBefore_mem_and_stamp_at S
        core.toNamedScheduleWellFormed hadmit hfreezeVote
  have hslot : (voteDutyRead S rho w (s + 1)).st.core.s = s + 1 :=
    voteDutyRead_slot S rho w (s + 1)
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
  rw [hslot, Nat.add_sub_cancel]
  exact ⟨by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Protocol.Store.toHealing] using hvis.1,
    Or.inl (by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.Store.toHealing] using hvis.2)⟩

#print axioms actionBlockProcessedAtNextDuty_core

/-- At the actual next-vote horizon, a named protected cone has a processed
descendant in the prepared reader's height band. -/
theorem coneBandDescendant_of_frontierWitnesses_at_vote_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {s : Slot} {C : Block V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hwitnesses : ∀ {C' : NamedBlock V}, C'.erase = C →
      (Protocol.derive_named S.E S.cfg C').h <
        (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C' →
      ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((voteDutyRead S rho w (s + 1)).st.core.h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C'.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    ∃ D : Block V, Block.Preceq C D ∧
      D ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (voteDutyRead S rho w (s + 1)).st.core.s ∧
      (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ D).h := by
  let read := voteDutyRead S rho w (s + 1)
  have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    have hc := hcom s
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  have huHon : u ∈ rho.honest := (Finset.mem_inter.mp hu).2
  have huCommittee : u ∈ S.E.committee s := (Finset.mem_inter.mp hu).1
  obtain ⟨X, hCX, hXrun, hXemit⟩ := hvotes u huHon huCommittee
  obtain ⟨Cn, hCnX, hCnErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hCX
  have hCnrun : RunBlock S rho Cn :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hCnX
  by_cases hband : read.st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg Cn).h
  · have hhead : HonestHead S rho s X.erase :=
      ⟨u, huHon, huCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hprocessed := honestHead_voterProcessed_at_nextDuty_at_cutoff_core
      S core hpost ((support_cutoff_le_vote_time_succ S.E s).trans hhor)
        hvotes hhead hw hroot
    have hXmem : X.erase ∈ read.st.core.T :=
      (Finset.mem_filter.mp hprocessed).1
    have hheight := storedHeight_of_runBlock_mem_voteDutyRead_core
      S core hw (s := s + 1) hXrun hXmem
    have hheightCX := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hCnX
    refine ⟨X.erase, hCX, hprocessed, ?_⟩
    change read.st.core.h_max - 1 ≤ (read.st.core.σ X.erase).h
    rw [hheight]
    exact hband.trans hheightCX
  · have hhighNamed : (Protocol.derive_named S.E S.cfg Cn).h <
        read.st.core.h_max - 1 := Nat.lt_of_not_ge hband
    have hlarge : 1 < (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (s + 1))).core.h_max := by
      by_contra hn
      have hzero : read.st.core.h_max - 1 = 0 := by
        simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hn)
      rw [hzero] at hhighNamed
      exact Nat.not_lt_zero _ hhighNamed
    obtain ⟨a, ta, D, K, ha, hemit, hta, hrow, hselected, hDmem, hKmem,
        hKentry, hKrun, hKheight⟩ :=
      Proofs.HealingSurface.frontier_confirmationWitness_core_entry
        S core hmajority (v := w)
          (time := Protocol.vote_time S.E (s + 1)) hlarge
    have hcompatible : Block.compatible Cn.erase
        (Protocol.derive_named S.E S.cfg K).T_h = true :=
      hwitnesses hCnErase hhighNamed
        hCnrun a ta K ha hemit hta (by
          simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
            using hrow) hselected hKrun
    have hCnK : NamedBlock.Preceq Cn K := by
      have hcases : Block.Preceq Cn.erase K.erase ∨
          Block.Preceq K.erase Cn.erase := by
        simpa only [Block.compatible, Bool.or_eq_true, hKentry] using hcompatible
      rcases hcases with hCK | hKC
      · obtain ⟨Cn', hCn'K, hCn'erase⟩ :=
          Proofs.NamedAncestry.erased_ancestor_lift K hCK
        have hCn'run : RunBlock S rho Cn' :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hKrun hCn'K
        have hCn'eq : Cn' = Cn := by
          apply core.toNamedRootCollisionFree.root_injective
            Cn' Cn hCn'run hCnrun Cn' Cn
              (Or.inl (Proofs.NamedAncestry.named_self Cn'))
              (Or.inr (Proofs.NamedAncestry.named_self Cn))
          rw [← Proofs.NamedWire.erase_root Cn', ← Proofs.NamedWire.erase_root Cn, hCn'erase]
        rw [← hCn'eq]
        exact hCn'K
      · obtain ⟨K', hK'Cn, hK'erase⟩ :=
          Proofs.NamedAncestry.erased_ancestor_lift Cn hKC
        have hK'run : RunBlock S rho K' :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCnrun hK'Cn
        have hK'eq : K' = K := by
          apply core.toNamedRootCollisionFree.root_injective
            K' K hK'run hKrun K' K
              (Or.inl (Proofs.NamedAncestry.named_self K'))
              (Or.inr (Proofs.NamedAncestry.named_self K))
          rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
        have hKCnamed : NamedBlock.Preceq K Cn := by
          rw [← hK'eq]
          exact hK'Cn
        have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKCnamed
        rw [hKheight] at hmono
        have hhighStore : (Protocol.derive_named S.E S.cfg Cn).h <
            (rho.storeBeforeTime S w
              (Protocol.vote_time S.E (s + 1))).core.h_max - 1 := by
          simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
            using hhighNamed
        exact False.elim ((Nat.not_le_of_gt hhighStore) hmono)
    have hpostSupport : S.E.t_GST ≤ Protocol.support_cutoff S.E s := by
      exact hpost.trans (le_of_lt (by
        rw [← vote_time_add_delta]
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos))
    have hprocessed := actionBlockProcessedAtNextDuty_core
      S core ha hw hKmem (by
        simpa only [(emits_attest_shape S hemit).2] using hta)
      hpostSupport hhor (Block.preceq_trans hroot (by
        simpa only [hCnErase, hKentry] using Proofs.NamedWire.erase_preceq hCnK))
    have hKmemRead : K.erase ∈ read.st.core.T :=
      (Finset.mem_filter.mp hprocessed).1
    have hheight := storedHeight_of_runBlock_mem_voteDutyRead_core
      S core hw (s := s + 1) hKrun hKmemRead
    have hbandK : read.st.core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg K).h := by
      have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
          read.st.core.h_max - 1 := by
        simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hKheight
      exact hKheight'.ge
    have hCK : Block.Preceq C K.erase := by
      simpa only [hCnErase] using Proofs.NamedWire.erase_preceq hCnK
    refine ⟨K.erase, hCK, hprocessed, ?_⟩
    change read.st.core.h_max - 1 ≤ (read.st.core.σ K.erase).h
    rw [hheight]
    exact hbandK

#print axioms coneBandDescendant_of_frontierWitnesses_at_vote_core

/-- The prepared voter view contains only committee-valid votes under core
admissibility. -/
theorem voteDutyRead_voteViewValid_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    (v : V) (s : Slot) :
    Protocol.VoteSetValid S.E
      ((voteDutyRead S rho v s).st.core.s - 1)
      (Protocol.voter_view S.E
        (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (voteDutyRead S rho v s).st.core.s) := by
  let t := Protocol.vote_time S.E s
  let read := voteDutyRead S rho v s
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    core.toNamedScheduleWellFormed t
  have hpool := voteSetValid_pool_stateBefore S
    core.toNamedScheduleWellFormed v n (read.st.core.s - 1)
  have hcarried : ∀ B ∈ (rho.stateBefore S n v).st.core.T,
      ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    intro B hB u hu
    exact carriedVote_committee_of_mem_T_core S core v n hB u hu
  have hvalid := voteSetValid_voter_view_of_carried
    (E := S.E) (st := (rho.stateBefore S n v).st.core)
    (s := read.st.core.s) hpool hcarried
  simpa only [read, t, voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock, hn]
    using hvalid

#print axioms voteDutyRead_voteViewValid_core

/-- A protected named vote cone persists through the next actual vote horizon
under weak genesis. -/
theorem protectedVoteSlot_succ_at_vote_of_weakGenesis_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {B : Block V} (hB : ProtectedVoteSlot S rho s B) :
    ProtectedVoteSlot S rho (s + 1) B := by
  have hprevHor : Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))]
    exact (support_cutoff_le_vote_time_succ S.E s).trans hhor
  have hmajority :=
    Proofs.HealingSurface.WeakGenesis.honestWeightMajority_of_finiteWindows
      S h.windows hprevHor
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E s := by
    rw [h.gstZero]
    exact vote_time_nonneg S.E s
  have hupper : s ≤ (s - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))]
  have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    have hc := h.committees s
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  have hxHon : x ∈ rho.honest := (Finset.mem_inter.mp hx).2
  have hrootHeads (w : V) (hw : w ∈ rho.honest) :
      Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
        (voterHeadAt S rho x s) := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      voteDutyHead] using
      (Proofs.HealingSurface.WeakGenesis.fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
        S h.core h.committees h.gstZero h.windows hprevHor
          (d := s) (last := s - 1) (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
          hupper (t := Protocol.vote_time S.E (s + 1)) (le_refl _) hw hxHon)
  have hanchorHeads (w : V) (hw : w ∈ rho.honest) :
      Block.Preceq (voterAnchorAt S rho w (s + 1))
        (voterHeadAt S rho x s) :=
    preparedVoterAnchor_preceq_voteDutyHead_of_gstZero_core
      S h hprevHor (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
        hupper hhor hw hxHon
  have hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) B = true := by
    intro w hw
    exact Block.compatible_of_preceq_common
      (hrootHeads w hw) (hB.heads x hxHon)
  have hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) B = true := by
    intro w hw
    exact Block.compatible_of_preceq_common
      (hanchorHeads w hw) (hB.heads x hxHon)
  have hwitnesses (w : V) (hw : w ∈ rho.honest)
      {C : NamedBlock V} (hCB : C.erase = B)
      (_hheight : (Protocol.derive_named S.E S.cfg C).h <
        (voteDutyRead S rho w (s + 1)).st.core.h_max - 1)
      (_hCrun : RunBlock S rho C)
      (a : NamedAttestation V) (ta : Time) (K : NamedBlock V)
      (ha : a.val_index ∈ rho.honest)
      (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
      (hta : ta < Protocol.vote_time S.E (s + 1))
      (_hrow : a.height_pair.erase.height? =
        some ((voteDutyRead S rho w (s + 1)).st.core.h_max - 1))
      (hselected : fgConfirmationWitness S
        (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h)
      (_hKrun : RunBlock S rho K) :
      Block.compatible C.erase
        (Protocol.derive_named S.E S.cfg K).T_h = true := by
    have htime : S.a a.round < Protocol.vote_time S.E (s + 1) := by
      rw [← (emits_attest_shape S hemit).2]
      exact hta
    have htarget :=
      ((Proofs.HealingSurface.WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero
        S h.core h.committees h.gstZero h.windows hprevHor
          (d := s) (last := s - 1)
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs)) hupper hxHon
          a.round htime).2 a.val_index ha).2 _ hselected
    rw [hCB]
    exact Block.compatible_of_preceq_common (hB.heads x hxHon) htarget
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    have hcases : Block.Preceq
          (Protocol.get_fg_root
            (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) B ∨
        Block.Preceq B
          (Protocol.get_fg_root
            (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) := by
      simpa only [Block.compatible, Bool.or_eq_true] using hroots w hw
    rcases hcases with hroot | habove
    · obtain ⟨D, hBD, hprocessed, hband⟩ :=
        coneBandDescendant_of_frontierWitnesses_at_vote_core
          S h.core h.committees hmajority hpost hhor hB.cone hw
            (hwitnesses w hw) hroot
      have hcandidate :=
        Proofs.HealingSurface.WeakJoint.namedCandidatePath_of_processedBandDescendant_core
          S h.core hw hBD hprocessed hband hroot
      let read := voteDutyRead S rho w (s + 1)
      let st := read.st.core
      let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
      let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
      let tree := voterCandidateTreeAt S rho w (s + 1)
      have hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
        (support_cutoff_le_vote_time_succ S.E s).trans hhor
      have havailable :=
        Proofs.HealingSurface.honestHeadsAvailableBefore_of_namedPostHealingCone_core
          S h.core hw hpost hcutHor hroot hB.cone
      have hresolve0 := headsResolveIn_storeBeforeTime_of_availableBefore_at_core
        S h.core hw s (support_cutoff_le_vote_time_succ S.E s) havailable
      have hresolve : HeadsResolveIn S rho s st.T st.timestamp_block := by
        simpa only [st, read, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hresolve0
      have hbase := canonicalSuffixConeSupportVoterView_core
        S h.core h.committees hs hpost hcutHor hB.cone hw
          (support_cutoff_le_vote_time_succ S.E s)
          (gst := st.toHealing.toFG.toSG.toGoldfishStore) (by rfl) (by rfl) (by rfl)
          (hresolve.of_eq rfl rfl)
      have hslot : st.s = s + 1 := by
        simpa only [st, read] using voteDutyRead_slot S rho w (s + 1)
      have hcone : ConeSupport S.E st.T votes support votes (st.s - 1)
          rho.honest (fun X => Block.Preceq B X) := by
        simpa only [st, read, votes, support, hslot,
          Protocol.Store.toHealing] using hbase
      have hvalid := voteDutyRead_voteViewValid_core S h.core w (s + 1)
      have hmajor : Protocol.voters_count S.E votes (st.s - 1) <
          2 * (Protocol.goldfishSupporters S.E st.T votes support
            (st.s - 1) B).card :=
        supporterMajority_of_cone S.E hcone hvalid
      have hpath : ∀ D : Block V,
          Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
          D ≠ voterAnchorAt S rho w (s + 1) →
          Block.Preceq D B → D ∈ tree := by
        intro D hAD hDne hDB
        by_cases hEq : D = B
        · simpa only [hEq, tree] using hcandidate.1
        · simpa only [tree] using hcandidate.2 D hAD hDne hDB hEq
      have hhead := goldfish_fork_choice_captures_supporter_majority
        S.E st.σ st.h_max st.T tree st.s votes support (st.s - 1)
          (ConeSupport.sub hcone) hmajor (hanchors w hw)
          (fun _ D hAD hDne hDB => hpath D hAD hDne hDB)
      change Block.Preceq B
        (Protocol.get_head_in_tree_with_layer
          (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
          tree votes support (st.s - 1))
      simpa only [get_head_in_tree_eq_voterHeadAt_of_anchor,
        read, st, tree] using hhead
    · exact Block.preceq_trans habove
        (Proofs.HealingSurface.fgRoot_preceq_voterHeadAt S rho w (s + 1))
  refine ⟨hheads, ?_⟩
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    Proofs.HealingSurface.WeakGoldfish.voterHead_runBlock_and_emits
      S h.core hw (Nat.succ_pos s) hcommittee hhor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms protectedVoteSlot_succ_at_vote_of_weakGenesis_core

/-- Every same-or-later honest prepared vote head extends the bound source
proposal at its actual vote horizon. -/
theorem proposedBlock_preceq_futureVoteDutyHead_gstZero_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s k : Slot} (hs : 0 < s) (hsk : s ≤ k)
    (hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (htargetHor : Protocol.vote_time S.E k ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq B.erase (voterHeadAt S rho v k) := by
  have hduty :=
    Proofs.HealingSurface.WeakGenesis.canonicalProposalDuty_positive_of_gstZero_named
      S h hs hsourceHor hprop hB
  have hbase : ProtectedVoteSlot S rho s B.erase := by
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [voteDutyHead_eq_proposedBlock_gstZero_core
        S h hs hsourceHor hprop hB hw]
      exact Block.preceq_self _
    · intro w hw hcommittee
      obtain ⟨X, hXB, hXrun, hXemit⟩ := hduty.votes w hw hcommittee
      exact ⟨X, by rw [hXB]; exact Block.preceq_self _, hXrun, hXemit⟩
  have hfold : ∀ d, s ≤ d → Protocol.vote_time S.E d ≤ rho.horizon →
      ProtectedVoteSlot S rho d B.erase := by
    intro d hsd
    induction d, hsd using Nat.le_induction with
    | base =>
        intro _
        exact hbase
    | succ d hsd ih =>
        intro hdHor
        have hdPrevHor : Protocol.vote_time S.E d ≤ rho.horizon :=
          (vote_time_mono_slots S.E (Nat.le_succ d)).trans hdHor
        exact protectedVoteSlot_succ_at_vote_of_weakGenesis_core
          S h (hs.trans_le hsd) hdHor (ih hdPrevHor)
  exact (hfold k hsk htargetHor).heads v hv

#print axioms proposedBlock_preceq_futureVoteDutyHead_gstZero_core



/-- Every strictly later honest prepared proposal parent extends the bound
source proposal. -/
theorem proposedBlock_preceq_futureProposedParent_gstZero_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s k : Slot} (hs : 0 < s) (hsk : s < k)
    (hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (htargetHor : Protocol.proposal_time S.E k ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    (htargetProp : S.E.proposer k ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    Block.Preceq B.erase (Proofs.HealingSurface.proposedParent S rho k) := by
  have hkpos : 0 < k := hs.trans hsk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hsd : s ≤ d := Nat.le_of_lt_succ hsk
  have hdpos : 0 < d := hs.trans_le hsd
  have hvoteNext : Protocol.vote_time S.E d <
      Protocol.proposal_time S.E (d + 1) := by
    apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ S.E d)
    rw [← vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
    hvoteNext.le.trans htargetHor
  have hheads : ∀ x ∈ rho.honest,
      Block.Preceq B.erase (voterHeadAt S rho x d) := by
    intro x hx
    exact proposedBlock_preceq_futureVoteDutyHead_gstZero_core
      S h hs hsd hsourceHor hvoteHor hprop hB hx
  have hprotected : ProtectedVoteSlot S rho d B.erase := by
    refine ⟨hheads, ?_⟩
    intro x hx hcommittee
    obtain ⟨X, hXe, hXrun, hXemit⟩ :=
      Proofs.HealingSurface.WeakGoldfish.voterHead_runBlock_and_emits
        S h.core hx hdpos hcommittee hvoteHor
    exact ⟨X, by rw [hXe]; exact hheads x hx, hXrun, hXemit⟩
  have hprevHor : Protocol.confirmation_time S.E (d - 1) ≤ rho.horizon := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdpos))]
    exact (support_cutoff_lt_proposal_time_succ S.E d).le.trans htargetHor
  have hupper : d ≤ (d - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdpos))]
  exact Proofs.HealingSurface.WeakGenesis.protected_preceq_proposedParent_of_gstZero_named
    S h hprevHor (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdpos))
      hupper htargetHor htargetProp hprotected

#print axioms proposedBlock_preceq_futureProposedParent_gstZero_core

/-- The proposal and vote call families preserve every bound honest source
proposal under weak genesis. -/
theorem honestProposal_proposalVoteResilience_gstZero_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest) :
    HonestProposalProposalVoteResilience S rho s where
  proposal_calls hsk hhor htargetProp B hB :=
    proposedBlock_preceq_futureProposedParent_gstZero_core
      S h hs hsk hsourceHor hhor hprop htargetProp hB
  vote_calls hsk hhor B hB _ hv :=
    proposedBlock_preceq_futureVoteDutyHead_gstZero_core
      S h hs hsk hsourceHor hhor hprop hB hv

#print axioms honestProposal_proposalVoteResilience_gstZero_core

/-- A prepared confirmation reader's height band is bounded by any protected
later named voter head. -/
theorem confirmationReadBand_le_futureVoterHeadHeight_of_gstZero_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last q d : Slot}
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hqd : q < d) (hupper : d ≤ last + 1)
    {v x : V} (hx : x ∈ rho.honest)
    {X : NamedBlock V} (hX : X.erase = voterHeadAt S rho x d)
    (hXrun : RunBlock S rho X) :
    (confirmationInputRead S rho v q).st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h := by
  let conf := Proofs.Optimistic.confStore S rho v q
  change conf.h_max - 1 ≤ (Protocol.derive_named S.E S.cfg X).h
  by_cases hlarge : 1 < conf.h_max
  · have hmajority :=
      Proofs.HealingSurface.WeakGenesis.honestWeightMajority_of_finiteWindows
        S h.windows hhor
    obtain ⟨a, ta, D, K, ha, hemit, hat, -, hfgK, -, -, hKentry,
        hKrun, hKheight⟩ := Proofs.HealingSurface.frontier_confirmationWitness_core_entry
      S h.core hmajority (v := v) (time := Protocol.confirmation_time S.E q)
        (by simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hlarge)
    have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
    have hconfVote : Protocol.confirmation_time S.E q <
        Protocol.vote_time S.E (d + 1) := by
      have hnext : Protocol.vote_time S.E (d + 1) =
          Protocol.vote_time S.E d + 4 * S.E.Δ := by
        unfold Protocol.vote_time Env.t slotStart
        push_cast
        ring
      rw [← vote_time_succ_add_delta_eq_confirmation_time S.E q, hnext]
      have hle := vote_time_mono_slots S.E (Nat.succ_le_of_lt hqd)
      have harith : ∀ a b z : Int, a ≤ b → 0 < z →
          a + z < b + 4 * z := by
        intro a b z hab hz
        omega
      exact harith _ _ _ hle S.E.Δ_pos
    have hactionTime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
      rw [← htime]
      exact hat.trans hconfVote
    have hsafe : Block.Preceq K.erase (voterHeadAt S rho x d) := by
      have hsource :=
        ((Proofs.HealingSurface.WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero
          S h.core h.committees h.gstZero h.windows hhor
            (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hqd)) hupper hx
            a.round hactionTime).2 a.val_index ha).2 _ hfgK
      rw [← hKentry]
      simpa only [voteDutyHead] using hsource
    have hKX : Block.Preceq K.erase X.erase := by
      rw [hX]
      exact hsafe
    obtain ⟨K', hK'X, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hKX
    have hK'run : RunBlock S rho K' :=
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

#print axioms confirmationReadBand_le_futureVoterHeadHeight_of_gstZero_core

/-- The prepared action anchor is the prepared confirmation anchor at the
round's opening-slot confirmation. -/
theorem actionAnchor_eq_openingConfirmationAnchor_core
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.get_sg_root_with
        (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).toHealing
        (S.hc.round_of (actionStoreAt S rho v r).s) =
      namedConfirmationAnchor S
        (confirmationInputRead S rho v (S.hc.opening_slot r)) := by
  have hcore := Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore
    S rho v r
  have hs : (actionStoreAt S rho v r).st.core.s =
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)).s := by
    rw [hcore]
    rfl
  have hround : S.hc.round_of
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)).s = r := by
    rw [← hs]
    exact Proofs.HealingSurface.actionStoreAt_round S rho v r
  have heq : Internal.PhaseGrades.nodeAnchor S
      (Proofs.HealingSurface.actionReadAt S rho v r) r =
      confAnchorWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)) := by
    show ((NamedProfile.gradeContract (actionStoreAt S rho v r).cache).read
        S.E S.hc (actionStoreAt S rho v r).st.core.toHealing r).anchor = _
    rw [confAnchorWith, Protocol.get_sg_root_with, hround, hcore]
    rfl
  rw [Proofs.HealingSurface.actionStoreAt_round S rho v r]
  change Internal.PhaseGrades.nodeAnchor S
      (Proofs.HealingSurface.actionReadAt S rho v r) r =
    namedConfirmationAnchor S
      (confirmationInputRead S rho v (S.hc.opening_slot r))
  simpa only [Internal.PhaseGrades.nodeAnchor, Internal.PhaseGrades.nodeRead,
    confirmationInputRead, NamedActionReads.confirmationReadAt,
    Proofs.Optimistic.confStore_eq_confirmationInputRead, confAnchorWith,
    Proofs.HealingSurface.opening_confirmation_time_eq_action] using heq

#print axioms actionAnchor_eq_openingConfirmationAnchor_core

/-- Honest slot heads are available before an action cutoff when they extend
the action reader's FG root. -/
theorem honestHeadsAvailableBefore_actionStore_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    {q : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E q)
    (hhor : Protocol.support_cutoff S.E q ≤ rho.horizon)
    {r : Round} (ha : S.a r = Protocol.support_cutoff S.E q)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG) B)
    (hvotes : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq B X)) :
    HonestHeadsAvailableBefore S rho q v
      (Protocol.support_cutoff S.E q) := by
  let pre := rho.storeBeforeTime S v (S.a r)
  have hrootPre : Block.Preceq
      (Protocol.get_fg_root pre.core.toHealing.toFG) B := by
    change Block.Preceq
      (Protocol.get_fg_root pre.core.toHealing.toFG) B at hroot
    exact hroot
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  have hCemit : NamedRun.emits S rho x
      (.gfVote ⟨x, q, C.erase.root⟩) (Protocol.vote_time S.E q) := by
    simpa only [hCX] using hXemit
  have hCmem := voteDutyHead_mem_of_emission_core
    S core hx hCrun hCemit (by rfl)
  have hXmem : X ∈ (voteDutyRead S rho x q).st.core.T := by
    simpa only [hCX] using hCmem
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hx hcommittee
  have hvoteEq : (⟨x, q, X.root⟩ : GoldfishVote V) =
      ⟨x, q, Y.erase.root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S core.toNamedScheduleWellFormed
      hXemit hYemit rfl
  have hrootXY : X.root = Y.erase.root :=
    congrArg GoldfishVote.head hvoteEq
  have hrootNamed : C.root = Y.root := by
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootXY
  have hCY : C = Y :=
    core.toNamedRootCollisionFree.root_injective C Y
      hCrun hYrun C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y)) hrootNamed
  have hBX : Block.Preceq B C.erase := by
    rw [hCY]
    exact hBY
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S core.toNamedScheduleWellFormed (Protocol.vote_time S.E q)
  have hXtime : X ∈
      (rho.storeBeforeTime S x (Protocol.vote_time S.E q)).core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hXmem
  have hXn : X ∈ (rho.stateBefore S n x).st.core.T := by
    rw [← hn]
    exact hXtime
  have hCxn : C.erase ∈ (rho.stateBefore S n x).st.core.T := by
    simpa only [hCX] using hXn
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n x hCxn
  have hDrun := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hx n hDbody)
  have hrootCD : C.root = D.root := by
    calc
      C.root = C.erase.root := (Proofs.NamedWire.erase_root C).symm
      _ = D.erase.root := (congrArg Block.root hDerase).symm
      _ = D.root := Proofs.NamedWire.erase_root D
  have hCD : C = D :=
    core.toNamedRootCollisionFree.root_injective C D
      hCrun hDrun C D (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self D)) hrootCD
  have hCbody : C ∈ (rho.stateBefore S n x).st.bodies := by
    rw [hCD]
    exact hDbody
  have hprocessed : Object.processed (rho.stateBefore S n x).st
      (Object.block C) = true := by
    simpa only [Object.processed, NamedReceipt.processed,
      decide_eq_true_eq] using hCbody
  rcases acceptsAt_block_of_processed S rho x n C hprocessed with
    hgen' | ⟨i, hin, t, hacc⟩
  · have hXgen : X = Block.genesis := by
      rw [← hCX, hgen']
      rfl
    exact False.elim (hgen hXgen)
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have ht : t < Protocol.vote_time S.E q := by
      rw [← het]
      exact hbefore i e hin he
    have hCposErase : 0 < C.erase.slot :=
      Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
    have hCpos : 0 < C.slot := by
      simpa only [Proofs.NamedWire.erase_slot] using hCposErase
    rw [← hCX]
    apply block_admittedBefore_of_accepted_after_cutoff_core
      S core hx hv hCpos hacc ht hpost
        (Proofs.Optimistic.vote_time_add_delta S.E q) hhor
    intro k hk
    rw [← ha] at hk
    exact Block.preceq_trans
      (finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
        S rho core.toNamedScheduleWellFormed.sorted hrootPre hk) hBX

#print axioms honestHeadsAvailableBefore_actionStore_core

/-- The prepared action store resolves all honest heads in its slot under the
core admissibility assumptions. -/
theorem headsResolveIn_actionStore_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    {q : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E q)
    (hhor : Protocol.support_cutoff S.E q ≤ rho.horizon)
    {r : Round} (ha : S.a r = Protocol.support_cutoff S.E q)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG) B)
    (hvotes : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq B X)) :
    HeadsResolveIn S rho q (actionStoreAt S rho v r).T
      (actionStoreAt S rho v r).timestamp_block := by
  have havailable := honestHeadsAvailableBefore_actionStore_core
    S core hv hpost hhor ha hroot hvotes
  have hresolve := headsResolveIn_storeBeforeTime_of_availableBefore_at_core
    S core hv q (Gamma := S.a r) (by rw [ha]) havailable
  exact hresolve.of_eq (actionStoreAt_T S rho v r)
    (actionStoreAt_timestamp_block S rho v r)

#print axioms headsResolveIn_actionStore_core

/-- A common ancestor of the current honest prepared vote heads is below the
actual prepared action head at GST zero. -/
theorem commonAncestor_preceq_actionHead_of_gstZero_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {last : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    {r : Round} (hupper : S.hc.opening_slot r + 1 ≤ last + 1)
    (hactHor : S.a r ≤ rho.horizon) {v : V} (hv : v ∈ rho.honest)
    {B : Block V}
    (hheads : ∀ x ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho x (S.hc.opening_slot r + 1))) :
    Block.Preceq B (actionHeadAt S rho v r) := by
  let p := S.hc.opening_slot r
  let q := p + 1
  let ast := actionStoreAt S rho v r
  let pre := rho.storeBeforeTime S v (S.a r)
  let R := Protocol.get_fg_root ast.toHealing.toFG
  have hqpos : 0 < q := Nat.zero_lt_succ _
  have ha : S.a r = Protocol.support_cutoff S.E q := by
    simpa only [q, p] using Protocol.a_eq_support_cutoff_succ S.hc S.E r
  have hcutHor : Protocol.support_cutoff S.E q ≤ rho.horizon := by
    rw [← ha]
    exact hactHor
  have hvoteHor : Protocol.vote_time S.E q ≤ rho.horizon := by
    have hvoteCut : Protocol.vote_time S.E q ≤
        Protocol.support_cutoff S.E q := by
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
    exact hvoteCut.trans hcutHor
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E q := by
    rw [h.gstZero]
    exact vote_time_nonneg S.E q
  have hqd : p < q := Nat.lt_succ_self p
  have hupper' : q ≤ last + 1 := by simpa only [q, p] using hupper
  have hnextVote : S.a r ≤ Protocol.vote_time S.E (q + 1) := by
    rw [ha]
    exact ((support_cutoff_lt_view_freeze S.E q).trans
      (view_freeze_lt_vote_time_succ S.E q)).le
  have hsg : ∀ x ∈ rho.honest, Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract ast.cache) S.E S.hc ast.toHealing
        (S.hc.round_of ast.s))
      (voterHeadAt S rho x q) := by
    intro x hx
    rw [show Protocol.get_sg_root_with
        (NamedProfile.gradeContract ast.cache) S.E S.hc ast.toHealing
        (S.hc.round_of ast.s) =
      namedConfirmationAnchor S (confirmationInputRead S rho v p) by
        simpa only [ast, p] using
          actionAnchor_eq_openingConfirmationAnchor_core S rho v r]
    exact Proofs.HealingSurface.WeakGenesis.preparedConfirmationAnchor_preceq_voteDutyHead_of_gstZero
        S h hhor hqd hupper' hv hx
  have hrootHeads : ∀ x ∈ rho.honest,
      Block.Preceq R (voterHeadAt S rho x q) := by
    intro x hx
    have hroot :=
      Proofs.HealingSurface.WeakGenesis.fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
        S h.core h.committees h.gstZero h.windows hhor
          (d := q) (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos))
          hupper' (t := S.a r) hnextVote hv hx
    simpa only [R, ast, pre] using hroot
  have hnamesRoot : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq R X) := by
    intro x hx hcommittee
    obtain ⟨X, hXe, hXrun, hXemit⟩ :=
      Proofs.HealingSurface.WeakGoldfish.voterHead_runBlock_and_emits
        S h.core hx hqpos hcommittee hvoteHor
    exact ⟨X, by simpa only [hXe] using hrootHeads x hx, hXrun, hXemit⟩
  have hnames : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq B X) := by
    intro x hx hcommittee
    obtain ⟨X, hXe, hXrun, hXemit⟩ :=
      Proofs.HealingSurface.WeakGoldfish.voterHead_runBlock_and_emits
        S h.core hx hqpos hcommittee hvoteHor
    exact ⟨X, by simpa only [hXe, q, p] using hheads x hx, hXrun, hXemit⟩
  have hresolve := headsResolveIn_actionStore_core
    S h.core hv hpost hcutHor ha (B := R) (Block.preceq_self R) hnamesRoot
  have hcone := coneSupport_actionStoreAt_core
    S h.core h.gstZero h.committees hqpos hcutHor hnames hv ha hresolve
  have hpositive : 0 < ((S.E.committee q) ∩ rho.honest).card := by
    have hc := h.committees q
    omega
  obtain ⟨x, hxq⟩ := Finset.card_pos.mp hpositive
  have hxc : x ∈ S.E.committee q := (Finset.mem_inter.mp hxq).1
  have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxq).2
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    Proofs.HealingSurface.WeakGoldfish.voterHead_runBlock_and_emits
      S h.core hx hqpos hxc hvoteHor
  have hXhead : HonestHead S rho q X.erase :=
    ⟨x, hx, hxc, ⟨X, rfl, hXrun⟩, hXemit⟩
  have hfind : Block.find? ast.T X.erase.root = some X.erase := by
    simpa only [ast] using (hresolve X.erase hXhead).1
  have hXmem : X.erase ∈ ast.T := Proofs.HealingLemmas.find?_mem hfind
  have hXmemPre : X.erase ∈ pre.core.T := by
    have hT : ast.T = (rho.storeBeforeTime S v (S.a r)).T := by
      simpa only [ast] using actionStoreAt_T S rho v r
    rw [hT] at hXmem
    simpa only [pre] using hXmem
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho (S.a r) v hXmemPre
  have hDrun : RunBlock S rho D := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho h.core.toNamedScheduleWellFormed.sorted (S.a r)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDbody
  have hDX : D = X := by
    apply h.core.toNamedRootCollisionFree.root_injective
      D X hDrun hXrun D X (Or.inl (Proofs.NamedAncestry.named_self D))
        (Or.inr (Proofs.NamedAncestry.named_self X))
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root X, hDerase]
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (S.a r) v X (by simpa only [← hDX] using hDbody)
  have hbandNamed :=
    confirmationReadBand_le_futureVoterHeadHeight_of_gstZero_core
      S h hhor hqd hupper' hx hXe hXrun (v := v)
  have hbandPre : pre.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h := by
    simpa only [pre, p, confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.HealingSurface.opening_confirmation_time_eq_action] using hbandNamed
  have hheight : pre.core.h_max - 1 ≤ (pre.core.σ X.erase).h := by
    have hviewHeight : (pre.core.σ X.erase).h =
        (Protocol.derive_named S.E S.cfg X).h := by
      simpa only [pre] using congrArg (fun st => st.h) hview
    rw [hviewHeight]
    exact hbandPre
  have hrootX : Block.Preceq R X.erase := by
    simpa only [hXe] using hrootHeads x hx
  have hFJ : Block.Preceq pre.core.F pre.core.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (S.a r) v
  have hFX : Block.Preceq pre.core.F X.erase := by
    have hFroot : Block.Preceq pre.core.F R :=
      Proofs.Records.preceq_get_fg_root_of_F (st := pre.core.toHealing.toFG) hFJ
    exact Block.preceq_trans hFroot hrootX
  have hcandidate : X.erase ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG := by
    rw [actionStoreAt_filteredTree S rho v r]
    change X.erase ∈ Protocol.get_filtered_block_tree pre.core.toHealing.toFG
    simp only [Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hXmemPre, hFX⟩, X.erase, hXmemPre,
      Block.preceq_self _, hheight⟩, hrootX⟩
  have hBX : Block.Preceq B X.erase := by
    simpa only [hXe, q, p] using hheads x hx
  apply protectedBlock_preceq_actionHead_of_cone_compatible_core
    S h.core ha hcone
      (Block.compatible_of_preceq_common (hsg x hx) (by
        simpa only [q, p] using hheads x hx))
  intro _
  exact actionPath_to_ancestor_of_candidate_core
    S h.core hcandidate hBX

#print axioms commonAncestor_preceq_actionHead_of_gstZero_core



/-- Every same-or-later prepared action call preserves the bound honest source
proposal under weak genesis. -/
theorem honestProposal_actionResilience_gstZero_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest) :
    HonestProposalActionResilience S rho s where
  action_calls B hB q hsq hhor v hv r ha := by
    have hqpos : 0 < q := hs.trans_le hsq
    have hq : q = S.hc.opening_slot r + 1 := by
      have ht := ha.symm.trans (Protocol.a_eq_support_cutoff_succ S.hc S.E r)
      have heq := congrArg S.E.slotOf ht
      simpa only [slotOf_support_cutoff] using heq
    have hprevHor : Protocol.confirmation_time S.E (q - 1) ≤ rho.horizon := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos))]
      exact hhor
    have hvoteHor : Protocol.vote_time S.E q ≤ rho.horizon := by
      have hvoteCut : Protocol.vote_time S.E q ≤
          Protocol.support_cutoff S.E q := by
        rw [← Proofs.Optimistic.vote_time_add_delta]
        exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
      exact hvoteCut.trans hhor
    apply commonAncestor_preceq_actionHead_of_gstZero_core
      S h hprevHor (last := q - 1) (r := r) (by
        rw [← hq, Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos))])
        (ha.trans_le hhor) hv
    intro x hx
    rw [← hq]
    exact proposedBlock_preceq_futureVoteDutyHead_gstZero_core
      S h hs hsq hsourceHor hvoteHor hprop hB hx

#print axioms honestProposal_actionResilience_gstZero_core

/-- An honest prepared proposal remains below every covered proposal, vote,
and action head under weak genesis. -/
theorem honestProposal_reorgResilience_gstZero_core
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest) :
    HonestProposalReorgResilience S rho s where
  toHonestProposalProposalVoteResilience :=
    honestProposal_proposalVoteResilience_gstZero_core
      S h hs hsourceHor hprop
  toHonestProposalActionResilience :=
    honestProposal_actionResilience_gstZero_core
      S h hs hsourceHor hprop

#print axioms honestProposal_reorgResilience_gstZero_core

end Protocol
end DecoupledConsensusModel

end
