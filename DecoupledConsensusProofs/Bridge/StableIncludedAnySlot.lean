module
public import DecoupledConsensusProofs.Bridge.StandardVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.W4GSTZeroStableGrowthLagged
public import DecoupledConsensusProofs.Protocol.Grades.W4StableContinuationClear
public import DecoupledConsensusProofs.Execution.W4StableRecordGrowthPreparedClosed

@[expose] public section

/-! # Stable inclusion of an honest proposal at any slot -/

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Proofs.HealingSurface
open Proofs.HealingSurface.Handover
open Internal.PhaseGrades DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem anySlot_roundLength_formula (S : Setup V) :
    S.a 1 - S.a 0 = 4 * S.E.Δ * (S.hc.R : Int) := by
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
  push_cast
  ring

private theorem anySlot_positive_slot (S : Setup V) {s : Slot}
    (hs : 0 < (legacyInterface S).proposalTime s) : 0 < s := by
  cases s with
  | zero =>
      simp [legacyInterface, Statements.«instance», Protocol.proposal_time,
        Env.t, slotStart] at hs
  | succ k => exact Nat.zero_lt_succ _

private theorem anySlot_opening_before_boundary (S : Setup V)
    {m q : Round} {s : Slot} (hmq : m ≤ q)
    (hs : healingBoundaryTime S q < Protocol.proposal_time S.E s) :
    S.hc.opening_slot m < s := by
  have hm0 : Protocol.proposal_time S.E (S.hc.opening_slot m) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q) :=
    Protocol.proposal_time_mono S.E
      (Nat.mul_le_mul_right S.hc.R hmq)
  have hq : Protocol.proposal_time S.E (S.hc.opening_slot q) ≤
      healingBoundaryTime S q := by
    unfold healingBoundaryTime
    exact (Protocol.proposal_time_lt_vote_time S.E
      (S.hc.opening_slot q)).le.trans
      (Protocol.vote_time_mono_slots S.E
        (Nat.le_add_right (S.hc.opening_slot q) 2))
  have hslot : Protocol.proposal_time S.E (S.hc.opening_slot m) <
      Protocol.proposal_time S.E s := (hm0.trans hq).trans_lt hs
  apply Nat.lt_of_not_ge
  intro hle
  exact (not_lt_of_ge (Protocol.proposal_time_mono S.E hle)) hslot

private theorem slot_before_next_opening (S : Setup V) (s : Slot) :
    s < S.hc.opening_slot (S.hc.round_of s + 1) := by
  have hR : 0 < S.hc.R :=
    lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hmod := Nat.mod_lt s hR
  unfold Protocol.HealConfig.round_of Protocol.HealConfig.opening_slot
  calc
    s = s % S.hc.R + S.hc.R * (s / S.hc.R) :=
      (Nat.mod_add_div s S.hc.R).symm
    _ < S.hc.R + S.hc.R * (s / S.hc.R) := Nat.add_lt_add_right hmod _
    _ = (s / S.hc.R + 1) * S.hc.R := by ring

private theorem confirmation_time_mono_slots (S : Setup V) {a b : Slot}
    (hab : a ≤ b) :
    Protocol.confirmation_time S.E a ≤ Protocol.confirmation_time S.E b := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono S.E (Nat.add_le_add_right hab 1)

/-- The next round and one SG window finish within the pinned delay. -/
theorem nextRoundWrite_before_inclusionDeadline (S : Setup V) (s : Slot) :
    S.a (S.hc.round_of s + 1 + S.hc.η_SG) ≤
      Protocol.proposal_time S.E s + stableInclusionDelay S 1 := by
  have hlow : S.hc.round_of s * S.hc.R ≤ s := by
    have h := Nat.le_add_left (S.hc.R * (s / S.hc.R)) (s % S.hc.R)
    rw [Nat.mod_add_div] at h
    simpa [Protocol.HealConfig.round_of, Nat.mul_comm] using h
  have hlow' : ((S.hc.round_of s * S.hc.R : Nat) : Time) ≤ (s : Time) := by
    exact_mod_cast hlow
  simp only [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot,
    Protocol.proposal_time, Env.t, slotStart, stableInclusionDelay,
    legacyConstants, Statements.ourConstants, anySlot_roundLength_formula]
  push_cast at hlow' ⊢
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  have hscaled := Int.mul_le_mul_of_nonneg_left hlow'
    (show (0 : Time) ≤ 4 * S.E.Δ by nlinarith)
  ring_nf at hlow' hscaled ⊢
  nlinarith

/-- A live-confirmed lower bound passes to an SG vote when the read is clear. -/
theorem actionSGCover_of_liveBound
    (S : Setup V) {rho : Run V} {B : Block V} {k : Round}
    (hlive : ∀ v ∈ rho.honest,
      Block.Preceq B (actionStoreAt S rho v k).st.core.live_confirmed)
    (hclear : ∀ v ∈ rho.honest,
      nodeClear S (actionReadAt S rho v k) k
        (actionStoreAt S rho v k).st.core.live_confirmed = true) :
    ∀ v ∈ rho.honest, Block.Preceq B (actionSGBlockAt S rho v k) := by
  intro v hv
  have hB := hlive v hv
  rcases w4_anchor_preceq_liveConfirmed_or_fgRoot S rho v k with hanch | hroot
  · have hvote : actionSGBlockAt S rho v k =
        (actionStoreAt S rho v k).st.core.live_confirmed :=
      w4_actionSGBlockAt_eq_liveConfirmed S rfl (Block.preceq_self _) rfl
        hanch (hclear v hv)
    rw [hvote]
    exact hB
  · have hBfg : Block.Preceq B
        (Protocol.get_fg_root
          (actionReadAt S rho v k).st.core.toHealing.toFG) := by
      rw [← hroot]
      exact hB
    have hBanchor : Block.Preceq B
        (nodeAnchor S (actionReadAt S rho v k) k) :=
      Block.preceq_trans hBfg
        (w4_fgRoot_preceq_nodeAnchor S (actionReadAt S rho v k) k)
    rcases actionSGBlockAt_tiers S rho v k with
      ⟨hA, -, -⟩ | ⟨Q, hQ, hvote⟩ | ⟨-, -, hvote⟩ | ⟨-, -, hvote⟩
    · exact Block.preceq_trans hBanchor hA
    · rw [hvote]
      exact Block.preceq_trans hBfg
        (Proofs.Records.preceq_get_fg_root_of_mem_filtered
          (actionQ2_mem_filteredTree S rho v k hQ))
    · rw [hvote]
      exact hBfg
    · rw [hvote]
      exact hBanchor

/-- The write step needs a covered SG window and viability at the duty read.
The block need not be an opening proposal. -/
theorem stableWrite_of_windowCover
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (sch : ScheduleWellFormed S rho) {q : Round} {B : NamedBlock V}
    (hq : 0 < q) (hhor : S.a (q + S.hc.η_SG) ≤ rho.horizon)
    (hcover : ∀ j : Round, q ≤ j → j < q + S.hc.η_SG →
      W4StableWrite.W4Cover S rho B j)
    (hdel : W4StableWrite.W4WindowDeliveryAt S rho (q + S.hc.η_SG))
    (hmajority : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG (q + S.hc.η_SG))
    (hviable : ∀ v ∈ rho.honest,
      W4StableWrite.ProposalViableAtDutyRound S rho (q + S.hc.η_SG) B.erase v) :
    ∀ v ∈ rho.honest,
      Block.Preceq B.erase
        (rho.storeAt S v (W4StableWrite.dutyTime S (q + S.hc.η_SG))).latest_stable := by
  have hdpos : 0 < q + S.hc.η_SG :=
    Nat.lt_of_lt_of_le hq (Nat.le_add_right q _)
  have hprev : S.a (q + S.hc.η_SG - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le _ 1)).trans hhor
  have hdom : domain S.E S.hc (q + S.hc.η_SG) .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S _ .g2).trans hhor
  have hgrade := W4StableWrite.w4Grade_of_cover_below S core hdpos
    hprev hdom hmajority hdel (by
      intro j hjlo hjhi
      exact hcover j (by simpa only [Nat.add_sub_cancel_right] using hjlo) hjhi)
  have hduty : W4StableWrite.dutyTime S (q + S.hc.η_SG) ≤ rho.horizon :=
    (W4StableWrite.dutyTime_le_action S _).trans hhor
  apply W4StableWrite.stable_preceq_at_duty_of_dutyCover S core sch hdpos
    (by
      intro v hv
      exact W4StableWrite.dutyCoverAt_of_viable_and_localG2 S
        (hviable v hv) (hgrade v hv)) hduty

#print axioms stableWrite_of_windowCover

/-- A slot-independent stable write. The live bound controls all honest SG
votes in the expiry window; the proposal read safety supplies duty viability. -/
theorem stableWrite_of_liveBound
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (sch : ScheduleWellFormed S rho) {q : Round} {B : NamedBlock V}
    (hq : 0 < q) (hhor : S.a (q + S.hc.η_SG) ≤ rho.horizon)
    (hlive : ∀ j : Round, q ≤ j → j < q + S.hc.η_SG →
      ∀ v ∈ rho.honest,
        Block.Preceq B.erase (actionStoreAt S rho v j).st.core.live_confirmed)
    (hclear : ∀ j : Round, q ≤ j → j < q + S.hc.η_SG →
      ∀ v ∈ rho.honest,
        nodeClear S (actionReadAt S rho v j) j
          (actionStoreAt S rho v j).st.core.live_confirmed = true)
    (hdel : W4StableWrite.W4WindowDeliveryAt S rho (q + S.hc.η_SG))
    (hmajority : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG (q + S.hc.η_SG))
    (hviable : ∀ v ∈ rho.honest,
      W4StableWrite.ProposalViableAtDutyRound S rho (q + S.hc.η_SG) B.erase v) :
    ∀ v ∈ rho.honest,
      Block.Preceq B.erase
        (rho.storeAt S v (W4StableWrite.dutyTime S (q + S.hc.η_SG))).latest_stable := by
  apply stableWrite_of_windowCover S core sch hq hhor ?_ hdel hmajority hviable
  intro j hqj hjd u hu
  have huHon :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u j).mp hu).1
  exact actionSGCover_of_liveBound S (hlive j hqj hjd)
    (hclear j hqj hjd) u huHon

#print axioms stableWrite_of_liveBound

/-- GST-zero duty viability for any block below the reader's preceding vote
head. No opening-proposal identity is used. -/
theorem stableViableAtDuty_gstZero_of_head
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {d : Round} (hd : 0 < d) (hhor : S.a d ≤ rho.horizon)
    {B : Block V}
    (hbelow : ∀ v ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho v (S.hc.opening_slot d - 1))) :
    ∀ v ∈ rho.honest,
      W4StableWrite.ProposalViableAtDutyRound S rho d B v := by
  intro v hv
  have hdEq : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hhead : W4StableWrite.DutyHeadWitness S rho (d - 1) v := by
    change ∃ X : NamedBlock V,
      X ∈ (NamedRun.stateBeforeTime S rho
        (W4StableWrite.dutyTime S (d - 1 + 1)) v).st.bodies ∧
      X.erase = voterHeadAt S rho v (S.hc.opening_slot (d - 1 + 1) - 1) ∧
      RunBlock S rho X
    rw [hdEq]
    simpa only [w4StableDutyTime_eq_dutyTime] using
      (w4_dutyHeadWitness S h.core hd hv)
  have hband : ∀ X : NamedBlock V, NamedRun.blockInRun S rho X →
      X.erase = voterHeadAt S rho v (S.hc.opening_slot (d - 1 + 1) - 1) →
      (NamedActionReads.confirmationReadAt S rho v
        (W4StableWrite.dutyTime S (d - 1 + 1))).st.core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg X).h := by
    intro X hXrun hX
    rw [hdEq] at hX ⊢
    simpa only [w4StableDutyTime_eq_dutyTime] using
      (w4_dutyBand_gstZero S h hd v hv hhor hX hXrun)
  have hopos : 0 < S.hc.opening_slot d := by
    simpa only [Protocol.HealConfig.opening_slot] using
      Nat.mul_pos hd (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hspos : 1 ≤ S.hc.opening_slot d - 1 :=
    Nat.le_sub_of_add_le (w4_openingSlot_two_le S hd)
  have hduty : W4StableWrite.dutyTime S d ≤ rho.horizon :=
    (W4StableWrite.dutyTime_le_action S d).trans hhor
  have hreadHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot d - 1) ≤ rho.horizon := by
    simpa only [Protocol.confirmation_time_eq_support_cutoff_succ,
      Nat.sub_add_cancel hopos, W4StableWrite.dutyTime] using hduty
  have hteq : W4StableWrite.dutyTime S d =
      Protocol.confirmation_time S.E (S.hc.opening_slot d - 1) := by
    simp only [W4StableWrite.dutyTime,
      Protocol.confirmation_time_eq_support_cutoff_succ,
      Nat.sub_add_cancel hopos]
  have hroot := w4_fgRootAtConfirmationRead_preceq_voteDutyHead_of_gstZero
    S h.core h.committees h.gstZero h.windows
    (last := S.hc.opening_slot d - 1)
    (d := S.hc.opening_slot d - 1) hreadHor hspos (Nat.le_succ _)
    (t := W4StableWrite.dutyTime S d) (le_of_eq hteq) hv hv
  have hfg : Block.compatible B (Protocol.get_fg_root
      (NamedActionReads.confirmationReadAt S rho v
        (W4StableWrite.dutyTime S (d - 1 + 1))).st.core.toHealing.toFG) = true := by
    rw [hdEq]
    exact Block.compatible_of_preceq_common (hbelow v hv)
      (by simpa only [NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hroot)
  have hviable := W4StableWrite.proposalViableAtDuty_of_band_and_head S
    hhead hband (by simpa only [hdEq] using hbelow v hv) hfg
  simpa only [W4StableWrite.ProposalViableAtDutyRound,
    W4StableWrite.ProposalViableAtDuty, hdEq] using hviable

#print axioms stableViableAtDuty_gstZero_of_head

/-- The GST-zero write for an honest proposal from any slot before round `q`.
The proposal is already confirmed when round `q` acts. -/
theorem stableWrite_anySlot_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s) (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {q : Round} (hq : 0 < q) (hsq : s < S.hc.opening_slot q)
    (hconfq : Protocol.confirmation_time S.E s ≤ S.a q)
    (hhor : S.a (q + S.hc.η_SG) ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.Preceq B.erase
        (rho.storeAt S v
          (W4StableWrite.dutyTime S (q + S.hc.η_SG))).latest_stable := by
  let d := q + S.hc.η_SG
  have hdpos : 0 < d := Nat.lt_of_lt_of_le hq (Nat.le_add_right q _)
  have hqd : q < d := Nat.lt_add_of_pos_right S.hc.η_SG_ge_one
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right q _)).trans hhor
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon :=
    hconfq.trans hqhor
  have hsafe : GSTZeroGuarantees S rho :=
    gstZeroGuarantees_of_weakGenesis S rho h
  have hreads : HonestProposalReadSafety S rho s :=
    hsafe.proposalReads s hs hconfHor hprop
  have hsource : ∀ v ∈ rho.honest,
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed =
        B.erase := by
    intro v hv
    exact WeakGenesis.honestProposal_liveConfirmed_named_of_gstZero
      S h hs hconfHor hprop hB v hv
  have hlive : ∀ j : Round, q ≤ j → j < d →
      ∀ v ∈ rho.honest,
        Block.Preceq B.erase
          (actionStoreAt S rho v j).st.core.live_confirmed := by
    intro j hqj hjd v hv
    have hjhor : S.a j ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hjd)).trans hhor
    have htj : Protocol.confirmation_time S.E s ≤ S.a j :=
      hconfq.trans (Assembly.a_mono S hqj)
    have hmono := hsafe.liveMonotone v hv
      (Protocol.confirmation_time S.E s) (S.a j) htj
    rw [w4_actionStore_liveConfirmed_eq_storeAt S
      h.core.toNamedScheduleWellFormed hv j hjhor, ← hsource v hv]
    exact hmono
  have hclear : ∀ j : Round, q ≤ j → j < d →
      ∀ v ∈ rho.honest,
        nodeClear S (actionReadAt S rho v j) j
          (actionStoreAt S rho v j).st.core.live_confirmed = true := by
    intro j hqj hjd v hv
    have hjpos : 0 < j := Nat.lt_of_lt_of_le hq hqj
    have hjhor : S.a j ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hjd)).trans hhor
    have hnextslot : S.hc.opening_slot j + 1 ≤
        S.hc.opening_slot (j + 1) := by
      simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left
        ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two)
        (j * S.hc.R)
    have hnext : Protocol.confirmation_time S.E
        (S.hc.opening_slot j + 1) ≤ rho.horizon :=
      (confirmation_time_mono_slots S hnextslot).trans (by
        simpa only [opening_confirmation_time_eq_action] using
          (Assembly.a_mono S (Nat.succ_le_of_lt hjd)).trans hhor)
    exact w4_nodeClear_liveConfirmed_gstZero S h hjpos hv hjhor hnext
  have hcover : ∀ j : Round, q ≤ j → j < d → 0 < j →
      S.a j ≤ rho.horizon →
      Protocol.confirmation_time S.E (S.hc.opening_slot j + 1) ≤
        rho.horizon →
      ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho j,
        Block.Preceq B.erase (actionSGBlockAt S rho u j) := by
    intro j hqj hjd _ _ _ u hu
    have huHon :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u j).mp hu).1
    exact actionSGCover_of_liveBound S (hlive j hqj hjd)
      (hclear j hqj hjd) u huHon
  have hwindow := w4_gstZeroWindowCarrier_and_ready S h hq hdpos
    (by simpa only [d, Nat.add_sub_cancel] using (Nat.le_refl q))
    hcover hhor
  have hdel : W4StableWrite.W4WindowDeliveryAt S rho d := by
    refine ⟨?_, hwindow.2⟩
    intro w hw j hjlo hjhi u hu
    exact (hwindow.1 w hw j hjlo hjhi u hu).2
  have hprev : S.a (d - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le _ 1)).trans hhor
  have hmajority : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG d := h.windows d hdpos hprev
  have hslotDuty : s ≤ S.hc.opening_slot d - 1 := by
    have hopen : S.hc.opening_slot q < S.hc.opening_slot d :=
      Nat.mul_lt_mul_of_pos_right hqd
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    exact Nat.le_sub_one_of_lt (hsq.trans hopen)
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot d - 1) ≤ rho.horizon := by
    exact (Protocol.vote_time_mono_slots S.E (Nat.sub_le _ 1)).trans
      ((Protocol.vote_time_le_confirmation_time S.E _).trans
        (by simpa only [opening_confirmation_time_eq_action] using hhor))
  have hbelow : ∀ v ∈ rho.honest,
      Block.Preceq B.erase
        (voterHeadAt S rho v (S.hc.opening_slot d - 1)) := by
    intro v hv
    exact hreads.vote B hB _ hslotDuty hvoteHor v hv
  have hviable := stableViableAtDuty_gstZero_of_head S h hdpos hhor hbelow
  exact stableWrite_of_liveBound S h.core h.core.toNamedScheduleWellFormed
    hq hhor hlive hclear hdel hmajority hviable

#print axioms stableWrite_anySlot_gstZero

/-- The prepared continuation writes a confirmed honest proposal from any
slot before `q`. The selected opening is used only to locate the SG window. -/
theorem stableWrite_anySlot_afterGST
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    (hphase : PhaseShiftSafety S rho (base + S.hc.η_SG) start Pseed.erase)
    {s : Slot} (hstarts : start < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {q : Round} (hsq : s < S.hc.opening_slot q)
    (hconfq : Protocol.confirmation_time S.E s ≤ S.a q)
    (hhor : S.a (q + S.hc.η_SG) ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.Preceq B.erase
        (rho.storeAt S v
          (W4StableWrite.dutyTime S (q + S.hc.η_SG))).latest_stable := by
  let d := q + S.hc.η_SG
  have hqpos : 0 < q := by
    by_contra hn
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hn
    simp [hq0, Protocol.HealConfig.opening_slot] at hsq
  have hdpos : 0 < d := Nat.lt_of_lt_of_le hqpos (Nat.le_add_right q _)
  have hqd : q < d := Nat.lt_add_of_pos_right S.hc.η_SG_ge_one
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right q _)).trans hhor
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon :=
    hconfq.trans hqhor
  have hreads := hphase.honestProposalReads s hstarts hconfHor hprop
  obtain ⟨B', hB', hsource⟩ :=
    hphase.honestProposalLive s hstarts hconfHor hprop
  have hBB' : B' = B := Option.some.inj (hB'.symm.trans hB)
  subst B'
  have hstartConf : Protocol.confirmation_time S.E start ≤
      Protocol.confirmation_time S.E s :=
    confirmation_time_mono_slots S hstarts.le
  have hlive : ∀ j : Round, q ≤ j → j < d →
      ∀ v ∈ rho.honest,
        Block.Preceq B.erase
          (actionStoreAt S rho v j).st.core.live_confirmed := by
    intro j hqj hjd v hv
    have hjhor : S.a j ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hjd)).trans hhor
    have htj : Protocol.confirmation_time S.E s ≤ S.a j :=
      hconfq.trans (Assembly.a_mono S hqj)
    have hmono := hphase.liveMonotone v hv
      (Protocol.confirmation_time S.E s) (S.a j) hstartConf htj
    rw [w4_actionStore_liveConfirmed_eq_storeAt S
      core.toNamedScheduleWellFormed hv j hjhor]
    rw [hsource v hv] at hmono
    exact hmono
  have hstartq : start < S.hc.opening_slot q := hstarts.trans hsq
  have hcutq : base + S.hc.η_SG < q :=
    Nat.lt_of_mul_lt_mul_right (hboot.settled.trans_lt hstartq)
  have hclear : ∀ j : Round, q ≤ j → j < d →
      ∀ v ∈ rho.honest,
        nodeClear S (actionReadAt S rho v j) j
          (actionStoreAt S rho v j).st.core.live_confirmed = true := by
    intro j hqj hjd v hv
    have hjhor : S.a j ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hjd)).trans hhor
    have hcutj : base + S.hc.η_SG ≤ j := (Nat.le_of_lt hcutq).trans hqj
    have hstartj : start ≤ S.hc.opening_slot j + 1 :=
      (hstartq.le.trans (Nat.mul_le_mul_right S.hc.R hqj)).trans
        (Nat.le_succ _)
    have hnextslot : S.hc.opening_slot j + 1 ≤
        S.hc.opening_slot (j + 1) := by
      simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left
        ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two)
        (j * S.hc.R)
    have hnext : Protocol.confirmation_time S.E
        (S.hc.opening_slot j + 1) ≤ rho.horizon :=
      (confirmation_time_mono_slots S hnextslot).trans (by
        simpa only [opening_confirmation_time_eq_action] using
          (Assembly.a_mono S (Nat.succ_le_of_lt hjd)).trans hhor)
    exact W4StableWrite.w4_preparedNodeClear_liveConfirmed S core hcom
      hboot hawake hfinality hcutj hstartj hjhor hnext hv
  have hdel := W4StableWrite.w4_preparedWindowDelivery_at_selectedDuty
    S core hcom hboot hawake hfinality hstartq hhor
  have hprev : S.a (d - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le _ 1)).trans hhor
  have hmajority : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG d :=
    hawake d ((Nat.le_of_lt hcutq).trans (Nat.le_add_right q _)) hprev
  have hslotPrev : s ≤ S.hc.opening_slot d - 1 := by
    have hopen : S.hc.opening_slot q < S.hc.opening_slot d :=
      Nat.mul_lt_mul_of_pos_right hqd
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    exact Nat.le_sub_one_of_lt (hsq.trans hopen)
  have hslotOpen : s ≤ S.hc.opening_slot d :=
    hsq.le.trans (Nat.mul_le_mul_right S.hc.R (Nat.le_of_lt hqd))
  have hdutyHor : W4StableWrite.dutyTime S d ≤ rho.horizon :=
    (W4StableWrite.dutyTime_le_action S d).trans hhor
  have hopenHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot d) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action] using hhor
  have hvotePrev : Protocol.vote_time S.E
      (S.hc.opening_slot d - 1) ≤ rho.horizon :=
    (W4StableWrite.voteTime_le_supportCutoff_mono S (Nat.sub_le _ 1)).trans hdutyHor
  have hvoteOpen : Protocol.vote_time S.E
      (S.hc.opening_slot d) ≤ rho.horizon :=
    (W4StableWrite.voteTime_le_supportCutoff_mono S (Nat.le_refl _)).trans hdutyHor
  have hviable : ∀ v ∈ rho.honest,
      W4StableWrite.ProposalViableAtDutyRound S rho d B.erase v := by
    intro v hv
    have hdEq : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
    have hs : start < S.hc.opening_slot (d - 1 + 1) := by
      rw [hdEq]
      exact hstartq.trans (Nat.mul_lt_mul_of_pos_right hqd
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two))
    have hhead : W4StableWrite.DutyHeadWitness S rho (d - 1) v := by
      rw [W4StableWrite.DutyHeadWitness, hdEq]
      exact W4StableWrite.dutyHeadWitnessAll_closed S rho core d hdpos v hv
    have hp := W4StableWrite.proposalViableAtDuty_of_package_and_head
      S core hcom hboot hawake hfinality hs
      (by simpa only [hdEq] using hdutyHor)
      (by simpa only [hdEq] using hopenHor) hv hhead
      (by simpa only [hdEq] using hreads.vote B hB _ hslotPrev hvotePrev v hv)
      (by simpa only [hdEq] using hreads.vote B hB _ hslotOpen hvoteOpen v hv)
    simpa only [W4StableWrite.ProposalViableAtDutyRound,
      W4StableWrite.ProposalViableAtDuty, hdEq] using hp
  exact stableWrite_of_liveBound S core core.toNamedScheduleWellFormed
    hqpos hhor hlive hclear hdel hmajority hviable

#print axioms stableWrite_anySlot_afterGST

/-- Every honest proposal, including one outside an opening slot, reaches
the stable output without a proposer recurrence premise. -/
theorem available_stableIncluded_any (S : Setup V) :
    ∀ rho t₀, SleepyRegime S (legacyInterface S) (legacyConstants S) rho t₀ →
      RecoveredBy S (legacyInterface S) (legacyConstants S) rho t₀ →
        Included S (legacyInterface S) rho (legacyInterface S).stable t₀
          (stableInclusionDelay S 1) := by
  intro rho t₀ hsleep hrecovered s hs hprop hdeadline
  let q : Round := S.hc.round_of s + 1
  let d : Round := q + S.hc.η_SG
  let T : Time := Protocol.proposal_time S.E s + stableInclusionDelay S 1
  have hqpos : 0 < q := Nat.zero_lt_succ _
  have hqd : q < d := Nat.lt_add_of_pos_right S.hc.η_SG_ge_one
  have hsq : s < S.hc.opening_slot q := slot_before_next_opening S s
  have hconfq : Protocol.confirmation_time S.E s ≤ S.a q := by
    exact (confirmation_time_mono_slots S hsq.le).trans
      (by rw [opening_confirmation_time_eq_action])
  have hwriteTime : S.a d ≤ T :=
    nextRoundWrite_before_inclusionDeadline S s
  have hhor : S.a d ≤ rho.horizon :=
    hwriteTime.trans (by simpa only [T, legacyInterface] using hdeadline)
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right q _)).trans hhor
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon :=
    hconfq.trans hqhor
  have hconfirmedHor : (legacyInterface S).proposalTime s +
      (legacyConstants S).confirmationDelay ≤ rho.horizon := by
    simpa [legacyInterface, legacyConstants, Statements.ourConstants,
      Protocol.confirmation_time, Protocol.proposal_time] using hconfHor
  obtain ⟨B, hHon, _⟩ := available_confirmedIncluded S rho t₀
    hsleep hrecovered s hs hprop hconfirmedHor
  have hB : proposedBlockAt S rho s = some B := hHon.2
  have hdutyToT : W4StableWrite.dutyTime S d ≤ T :=
    (W4StableWrite.dutyTime_le_action S d).trans hwriteTime
  refine ⟨B, hHon, ?_⟩
  intro v hv
  cases hrecovered with
  | genesis =>
      have hweak : WeakGenesis S rho := weakGenesis_of_sleepy S hsleep
      have hwrite := stableWrite_anySlot_gstZero S hweak
        (by
          exact anySlot_positive_slot S
            (by simpa [legacyInterface] using hs))
        hprop hB hqpos hsq hconfq hhor
      have hcanon : StableRecordCanonicalFrom S rho 0 :=
        Handover.stableRecordSafety_gstZero_clean S rho hweak
      have hduty0 : (0 : Time) ≤ W4StableWrite.dutyTime S d :=
        (Proofs.HealingLemmas.a_nonneg S q).trans
          ((W4StableWrite.action_le_nextDuty S q).trans
            (W4StableWrite.dutyTime_mono S hqd))
      have hret := W4StableWrite.stable_retained_of_duty_from S hcanon
        hduty0 hwrite hdutyToT
        (by simpa only [T, legacyInterface] using hdeadline) v hv
      simpa [T, legacyInterface, Statements.«instance», Internal.readAt,
        Internal.stableOutputAt] using hret.2
  | @recovered source tPrefix gap extra hrec hcont hslash =>
      obtain ⟨rGST, n, hstrong, hsum⟩ := strongRecovery_of_recovery S hrec
      have hweak := weakContinuation_of_sleepy_recovered S hrec hstrong
        hsum hcont hsleep hslash
      obtain ⟨m, _hmn, hmhi, hpack⟩ :=
        W4StableWrite.continuationV4Package S
          (W4StableWrite.preparedV4AwakeWindows_closed S)
          source rGST gap extra n hstrong
      obtain ⟨fresh, base, Pseed, cap, hphase, hboot, hfinality,
        hawake, _hstartHor, hlatest⟩ := hpack rho hweak
      have hrecover : (legacyConstants S).recoveryEnd tPrefix gap extra =
          healingBoundaryTime S (n + gap) := by
        simpa [legacyConstants, Statements.ourConstants, recoveryRound, hsum]
      have hstarts : S.hc.opening_slot m < s :=
        anySlot_opening_before_boundary S hmhi
          (by simpa [hrecover, legacyInterface] using hs)
      have hwrite := stableWrite_anySlot_afterGST S hweak.core
        hweak.committees hboot hawake hfinality hphase hstarts
        hprop hB hsq hconfq hhor
      have sch : ScheduleWellFormed S rho := hweak.core.toNamedScheduleWellFormed
      have hcanon : StableRecordCanonicalFrom S rho
          (Protocol.confirmation_time S.E (S.hc.opening_slot m)) :=
        Handover.stableRecordCanonicalFrom_of_phaseShift_latestFinality
          S sch hphase hlatest
      have hmq : m < q :=
        Nat.lt_of_mul_lt_mul_right (hstarts.trans hsq)
      have hdutyStart : Protocol.confirmation_time S.E
          (S.hc.opening_slot m) ≤ W4StableWrite.dutyTime S d := by
        rw [opening_confirmation_time_eq_action]
        exact (Assembly.a_mono S hmq.le).trans
          ((W4StableWrite.action_le_nextDuty S q).trans
            (W4StableWrite.dutyTime_mono S hqd))
      have hret := W4StableWrite.stable_retained_of_duty_from S hcanon
        hdutyStart hwrite hdutyToT
        (by simpa only [T, legacyInterface] using hdeadline) v hv
      simpa [T, legacyInterface, Statements.«instance», Internal.readAt,
        Internal.stableOutputAt] using hret.2

#print axioms available_stableIncluded_any

end Proofs
end DecoupledConsensusModel

end
