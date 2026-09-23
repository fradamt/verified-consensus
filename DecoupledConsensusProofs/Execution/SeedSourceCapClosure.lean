module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.FreshFGSourceCapture
public import DecoupledConsensusProofs.Execution.FrontierWitnessRelay
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Closure of the gate-off seed source-height input

The full seed frame supplies source activity and prepared-anchor compatibility
at the next opening. The cached named derivation gives the height in the
source validator's own action store.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

omit [Fintype V] in
private theorem seedSourceCap_namedParent_preceq (P : NamedBlock V) :
    NamedBlock.Preceq P.parent P := by
  cases P with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

private theorem seedSourceCap_action_le_nextEarly (S : Setup V) (q : Round) :
    S.a q + S.E.Δ ≤
      DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g2 := by
  have hRcast : (3 : Time) ≤ (S.hc.R : Time) := by
    exact_mod_cast S.hc.R_ge_three
  have hmul : 12 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Time) := by
    have h := Int.mul_le_mul_of_nonneg_left hRcast
      (Int.mul_nonneg (show (0 : Time) ≤ 4 by norm_num) S.E.Δ_pos.le)
    calc
      12 * S.E.Δ = (4 * S.E.Δ) * 3 := by ring
      _ ≤ 4 * S.E.Δ * (S.hc.R : Time) := h
  have hrest : S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Time) - 11 * S.E.Δ := by
    calc
      S.E.Δ = 12 * S.E.Δ + -(11 * S.E.Δ) := by ring
      _ ≤ 4 * S.E.Δ * (S.hc.R : Time) + -(11 * S.E.Δ) :=
        Int.add_le_add_right hmul _
      _ = _ := by ring
  have heq : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g2 =
      S.a q + 4 * S.E.Δ * (S.hc.R : Time) - 11 * S.E.Δ := by
    unfold DecoupledConsensusModel.Protocol.early DecoupledConsensusModel.Protocol.opening
      DecoupledConsensusModel.Protocol.Phase.earlyOffset Protocol.proposal_time Env.t Setup.a
      Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
    push_cast
    ring
  calc
    S.a q + S.E.Δ ≤
        S.a q + (4 * S.E.Δ * (S.hc.R : Time) - 11 * S.E.Δ) :=
      Int.add_le_add_left hrest _
    _ = DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g2 := by rw [heq]; ring

private theorem seedSourceCap_nextProposal_frame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    {C : Block V} {Cn : NamedBlock V} (hCerase : Cn.erase = C)
    (hCrun : RunBlock S rho Cn)
    (hCband : M - 1 ≤ (Protocol.derive_named S.E S.cfg Cn).h) :
    let o := S.hc.opening_slot (c + 1)
    let p := S.E.proposer o
    p ∈ rho.honest →
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S p (Protocol.proposal_time S.E o)).toHealing.toFG) C ∧
      (rho.storeBeforeTime S p (Protocol.proposal_time S.E o)).h_max = M ∧
      (rho.storeBeforeTime S p (Protocol.proposal_time S.E o)).h_j + 2 ≤ M := by
  dsimp only
  intro hp
  have hpredC : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have hdelay : S.a c + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) :=
    action_add_delta_le_openingProposal_of_round_lt S (Nat.lt_succ_self c)
  have hreadHi : Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) ≤
      S.a (c + 1) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  have hfr := hframe (Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)))
    (hpredC.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay))
    hreadHi (S.E.proposer (S.hc.opening_slot (c + 1))) hp
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot (c + 1)))
          (Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)))).toHealing.toFG) C := by
    rw [fgRoot_eq_F_of_frame hfr.1 hfr.2]
    simpa only [hCerase] using finalizedRoot_preceq_of_band S adm hfb hp hfr.1 hCrun hCband
  exact ⟨hroot, hfr.2, hfr.1⟩

/-- A fresh source is active in the next honest opening proposal read. -/
private theorem seedSourceCap_active_nextOpeningProposal
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v c) c = some C)
    {Cn : NamedBlock V} (hCbody : Cn ∈ (actionStoreAt S rho v c).st.bodies)
    (hCerase : Cn.erase = C) (hCrun : RunBlock S rho Cn)
    (hCband : M - 1 ≤ (Protocol.derive_named S.E S.cfg Cn).h)
    (hprop : S.E.proposer (S.hc.opening_slot (c + 1)) ∈ rho.honest) :
    C ∈ Protocol.get_filtered_block_tree
      (proposerDutyStore S rho (S.hc.opening_slot (c + 1))).toHealing.toFG := by
  have hsb := slashableBound_of_admissible_belowOneThird S adm hfb
  have hpostC : S.E.t_GST ≤ S.a c :=
    hpost.trans (Assembly.a_mono S (Nat.sub_le c 1))
  have hdelay : S.a c + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) :=
    action_add_delta_le_openingProposal_of_round_lt S (Nat.lt_succ_self c)
  have hreadHi : Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) ≤
      S.a (c + 1) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  have hreadHor := hreadHi.trans hhor
  have hframeData := seedSourceCap_nextProposal_frame S adm hfb hc hframe hpost hhor
    hCerase hCrun hCband hprop
  obtain ⟨hroot, hmax, hgate⟩ := hframeData
  have hvis := actionConeWitness_visibleAtReader_after_gst S adm hv hprop hCbody
    (by rw [hCerase]; exact Block.preceq_self C) hCband hpostC hdelay hreadHor hroot
  have hCT : C ∈ (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot (c + 1)))
      (Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)))).T := by
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)))
      (S.E.proposer (S.hc.opening_slot (c + 1)))).1.1.1
    have himage : Cn.erase ∈ (NamedRun.stateBeforeTime S rho
        (Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)))
        (S.E.proposer (S.hc.opening_slot (c + 1)))).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image.mpr ⟨Cn, hvis.1, rfl⟩
    simpa only [Run.storeBeforeTime, hCerase] using himage
  have hM : 1 ≤ M :=
    (Nat.succ_le_succ (Nat.zero_le 1)).trans
      ((Nat.le_add_left 2 _).trans hgate)
  have hfiltered := frontierBlock_filtered_of_gateOff S adm hsb hprop hreadHor
    hCT hCerase hCrun hCband hM hmax hgate
  simpa only [proposerDutyStore, proposerReadAt,
    NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock] using hfiltered

omit [Fintype V] in
private theorem seedSourceCap_compatible_ancestor_left {A K C : Block V}
    (hAK : Block.Preceq A K) (hKC : Block.compatible K C = true) :
    Block.compatible A C = true := by
  rcases (show Block.Preceq K C ∨ Block.Preceq C K by
    simpa only [Block.compatible, Bool.or_eq_true] using hKC) with hKC | hCK
  · simpa only [Block.compatible, Bool.or_eq_true] using
      Or.inl (Block.preceq_trans hAK hKC)
  · exact Block.compatible_of_preceq_common hAK hCK

private theorem seedSourceCap_carrier_compatible_at_secondSlot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {c : Round} {K C : Block V}
    (hKcone : NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
      (fun X => Block.Preceq K X))
    (hCcone : NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
      (fun X => Block.Preceq C X)) :
    Block.compatible K C = true := by
  have hpositive : 0 < ((S.E.committee (S.hc.opening_slot c + 1)) ∩
      rho.honest).card := by
    have h := hcom (S.hc.opening_slot c + 1)
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  have hxCommittee := (Finset.mem_inter.mp hx).1
  have hxHonest := (Finset.mem_inter.mp hx).2
  obtain ⟨HK, hKHK, hHKrun, hKem⟩ := hKcone x hxHonest hxCommittee
  obtain ⟨HC, hCHC, hHCrun, hCem⟩ := hCcone x hxHonest hxCommittee
  have hemit := Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed
    hKem hCem rfl
  have hroot : HK.erase.root = HC.erase.root := congrArg GoldfishVote.head hemit
  have heq := runBlock_eq_of_root_eq adm.toNamedRootCollisionFree hHKrun hHCrun hroot
  rw [heq] at hKHK
  exact Block.compatible_of_preceq_common hKHK hCHC

/-- The next opening proposal's prepared anchor is compatible with the fresh
source. Its active G1 branch is below a previous honest carrier, and the two
second-slot cones make that carrier compatible with the source. -/
private theorem seedSourceCap_compatible_nextOpeningProposalAnchor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    (ready : GradeRoundReady S rho c)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v c) c = some C)
    {Cn : NamedBlock V} (hCerase : Cn.erase = C) (hCrun : RunBlock S rho Cn)
    (hCband : M - 1 ≤ (Protocol.derive_named S.E S.cfg Cn).h)
    (hprop : S.E.proposer (S.hc.opening_slot (c + 1)) ∈ rho.honest) :
    Block.compatible
      (nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot (c + 1)))
        (S.hc.round_of
          (Internal.NamedRecoveryRead.proposalDutyRead S rho
            (S.hc.opening_slot (c + 1))).st.core.s)) C = true := by
  let o := S.hc.opening_slot (c + 1)
  have hround : S.hc.round_of o = c + 1 :=
    round_of_opening_slot_eq_schedule S.hc (c + 1)
  have hroundSt : S.hc.round_of
      (Internal.NamedRecoveryRead.proposalDutyRead S rho o).st.core.s = c + 1 := by
    simpa only [Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.slotOf_proposal_time] using hround
  have hrootC : Block.Preceq
      (Protocol.get_fg_root (proposerReadAt S rho o).st.core.toHealing.toFG) C := by
    simpa only [o, proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      (seedSourceCap_nextProposal_frame S adm hfb hc hframe hpost hhor
        hCerase hCrun hCband hprop).1
  rw [hroundSt]
  rcases proposalAnchor_cases S rho o with hfg | ⟨root, A, hframeA, hactive, hanchor⟩
  · rw [hroundSt] at hfg
    rw [hfg]
    simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hrootC
  · have hanchor' : nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho o) (c + 1) = A := by
      simpa only [hroundSt] using hanchor
    rw [hanchor']
    have hopen : domain S.E S.hc (c + 1) .g1 = Protocol.proposal_time S.E o := by
      rw [NamedOutageClosure.domain_g1_eq_opening]
      rfl
    have hproposalHor : Protocol.proposal_time S.E o ≤ rho.horizon := by
      exact (Protocol.proposal_time_le_confirmation_time S.E o).trans
        (by simpa only [o, Setup.a, Protocol.a_eq_confirmation_time] using hhor)
    have hroundTime : S.hc.round_of (S.E.slotOf (Protocol.proposal_time S.E o)) = c + 1 := by
      simpa only [Proofs.Optimistic.slotOf_proposal_time] using hround
    have hframeStore := preparedFrame_g1_eq_storeRoot_at_opening S rho
      adm.toNamedAdmissibleCore (S.E.proposer o) hprop (c + 1) (Nat.succ_pos c)
      (Protocol.proposal_time S.E o) hroundTime hopen (by rw [hopen]; exact hproposalHor)
    have hframeA' := hframeA
    rw [hroundSt] at hframeA'
    have hframeA'' :
        (DecoupledConsensusModel.Protocol.readFrame (proposerReadAt S rho o).cache
          (proposerReadAt S rho o).st.core.toHealing (c + 1)).g1 =
          some (some root) := by
      simpa only [Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt] using hframeA'
    let read := PhaseGrades.readAt S rho (domain S.E S.hc (c + 1) .g1)
      (S.E.proposer o)
    have hframeRead :
        (DecoupledConsensusModel.Protocol.readFrame (proposerReadAt S rho o).cache
          (proposerReadAt S rho o).st.core.toHealing (c + 1)).g1 =
          some ((storeRoot S.E S.hc read.st (c + 1) .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              (proposerReadAt S rho o).st.core.F)) := by
      simpa only [read, Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hframeStore
    cases hstore : storeRoot S.E S.hc read.st (c + 1) .g1 with
    | none =>
        simp only [hstore, Option.map_none] at hframeRead
        rw [hframeA''] at hframeRead
        cases hframeRead
    | some raw =>
        have hrootEq : root = DecoupledConsensusModel.Protocol.clipGrade raw
            (proposerReadAt S rho o).st.core.F := by
          have hopt : some (some root) = some
              (some (DecoupledConsensusModel.Protocol.clipGrade raw
                (proposerReadAt S rho o).st.core.F)) :=
            hframeA''.symm.trans (by simpa only [hstore, Option.map_some] using hframeRead)
          exact Option.some.inj (Option.some.inj hopt)
        have hAroot : Block.Preceq A root := by
          unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
          exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
        have hAraw : Block.Preceq A raw := by
          rw [hrootEq] at hAroot
          exact Block.preceq_trans hAroot
            (NamedOutageClosure.q10_clip_preceq raw (proposerReadAt S rho o).st.core.F)
        have hrawData := Proofs.Engine.deepest?_mem hstore
        have hrawGrade : phaseGrade S.E S.hc read.st.core.toHealing.gradeView
            read.st.core.F (c + 1) .g1 raw = true :=
          (Finset.mem_filter.mp hrawData).2
        have hAGrade := confirmation_phaseGrade_mono S.E S.hc _ _ (c + 1) .g1
          hAraw hrawGrade
        have hprev : ∀ u ∈ rho.honest,
            (rho.storeBeforeTime S u (S.a c)).h_max = M := by
          intro u hu
          exact (hframe _ (Assembly.a_mono S (Nat.sub_le c 1))
            (Assembly.a_mono S (Nat.le_succ c)) u hu).2
        have hfrontier : ∀ u ∈ rho.honest,
            (rho.storeBeforeTime S u (S.a (c + 1))).h_max = M := by
          intro u hu
          exact (hframe _ ((Assembly.a_mono S (Nat.sub_le c 1)).trans
            (Assembly.a_mono S (Nat.le_succ c))) le_rfl u hu).2
        have hgate : ∀ u ∈ rho.honest,
            (rho.storeBeforeTime S u (S.a (c + 1))).h_j + 2 ≤ M := by
          intro u hu
          exact (hframe _ ((Assembly.a_mono S (Nat.sub_le c 1)).trans
            (Assembly.a_mono S (Nat.le_succ c))) le_rfl u hu).1
        have hpostC : S.E.t_GST ≤ S.a c :=
          hpost.trans (Assembly.a_mono S (Nat.sub_le c 1))
        have hwindow : RelativeCarrierWindowAt S rho c .g1 :=
          relativeCarrierWindowAt_of_gateOff S adm hfb (Nat.succ_pos c) hpostC
            hprev hfrontier hgate (by
              rw [hopen]
              exact hproposalHor)
        have hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho (c + 1) :=
          gradeFormingMajority_of_admissible_belowOneThird S adm hfb (Nat.succ_pos c)
            ((NamedOutageClosure.q10_domain_g2_lt_domain_g1 S (c + 1)).le.trans (by
              rw [hopen]
              exact hproposalHor))
        obtain ⟨u, huRound, hAK⟩ := relativeGrade_has_roundCarrier S
          adm.toNamedAdmissibleCore hwindow hmajority hprop hAGrade
        have hu : u ∈ rho.honest :=
          ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u c).mp huRound).1
        have hdis := seedRoundDischarge_of_canonicity S adm hcom hfb hc hpost hhor
          hframe ready
        have hCcone := freshFGSource_secondSlotCone S adm hcom hfb hc hframe hpost
          hhor ready (fun d hlo hhi w hw =>
            voteDutyHead_band_at_duty S adm hfb hc hframe hpost hhor hw hlo hhi
              (seedEntryRoundOf' S hlo hhi)) hv hsource ⟨Cn, hCerase, hCrun⟩
        exact seedSourceCap_compatible_ancestor_left hAK
          (seedSourceCap_carrier_compatible_at_secondSlot S adm hcom
            (hdis.claim1 u hu) hCcone)

/-- All local inputs required to capture a fresh source in the next opening
proposal parent follow from the gate-off seed window. -/
private theorem seedSourceCap_preceq_nextOpeningParent_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    (ready : GradeRoundReady S rho c)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v c) c = some C)
    {Cn : NamedBlock V} (hCbody : Cn ∈ (actionStoreAt S rho v c).st.bodies)
    (hCerase : Cn.erase = C) (hCrun : RunBlock S rho Cn)
    (hCband : M - 1 ≤ (Protocol.derive_named S.E S.cfg Cn).h)
    (hprop : S.E.proposer (S.hc.opening_slot (c + 1)) ∈ rho.honest) :
    Block.Preceq C (proposedParent S rho (S.hc.opening_slot (c + 1))) := by
  exact freshFGSource_preceq_nextOpeningParent S adm hcom hfb hc hframe hpost hhor
    ready hv hsource hCerase hCrun hCband hprop
      (seedSourceCap_active_nextOpeningProposal S adm hfb hc hframe hpost hhor hv
        hsource hCbody hCerase hCrun hCband hprop)
      (seedSourceCap_compatible_nextOpeningProposalAnchor S adm hcom hfb hc hframe
        hpost hhor ready hv hsource hCerase hCrun hCband hprop)

/-- The gate-off seed context supplies the source-height cap needed by the
`M - 1` promotion closer. The source is read at the round immediately before
the later opening. -/
theorem seedPredPromotionInputs_of_public
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    (_hdelay : TimeoutDelayBound S delayExtra)
    {gap : Round} (_hrec : MultiProposerRecurrence S rho gap) :
    SeedPredPromotionInputs S rho delayExtra := by
  intro M q q' C C' B B' hM hgraded hcarrier hceiling hwindow hpred hspace
    hcarrier' hceiling' hwindow' hpost hhor hframe hBrun hforms hretained
  refine { sourceHeightLeNextOpeningParent := ?_ }
  have hq2 : 2 ≤ q' :=
    (Nat.le_add_left 2 q).trans
      ((Nat.le_add_right (q + 2) delayExtra).trans hspace)
  have hcOne : 1 ≤ q' - 1 := by
    apply Nat.le_sub_of_add_le
    exact hq2
  have hcPred : (q' - 1) - 1 = q' - 2 := by
    rw [Nat.sub_sub]
  have hcSucc : (q' - 1) + 1 = q' := by
    exact Nat.sub_add_cancel (Nat.le_trans (by decide) hq2)
  have hpredSucc : q' - 2 + 1 = q' - 1 := by
    simpa only [hcPred] using Nat.sub_add_cancel hcOne
  have hpostC : S.E.t_GST ≤ S.a ((q' - 1) - 1) := by
    simpa only [hcPred] using hpost
  have hhorC : S.a ((q' - 1) + 1) ≤ rho.horizon := by
    simpa only [hcSucc] using hhor
  have hcHor : S.a (q' - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le q' 1)).trans hhor
  have hready : GradeRoundReady S rho (q' - 1) := by
    constructor
    · have hdeadline := seedSourceCap_action_le_nextEarly S (q' - 2)
      have hdeadline' : S.a (q' - 2) + S.E.Δ ≤
          DecoupledConsensusModel.Protocol.early S.E S.hc (q' - 1) .g2 := by
        simpa only [hpredSucc] using hdeadline
      exact hpost.trans
        ((le_add_of_nonneg_right S.E.Δ_pos.le).trans hdeadline')
    · rw [domain_g0_eq_Γ_1]
      have hΓ12 : S.hc.Γ_1 S.E.Δ (q' - 1) ≤
          S.hc.Γ_2 S.E.Δ (q' - 1) := by
        have h := Γ_1_add_Δ S.hc S.E.Δ (q' - 1)
        linarith [S.E.Δ_pos]
      exact hΓ12.trans ((Γ_2_le_a S.hc S.E.Δ_pos (q' - 1)).trans hcHor)
  have hframeC : GateOffFrameAt S rho M ((q' - 1) - 1) ((q' - 1) + 1) := by
    intro read hlo hhi w hw
    rw [hcPred] at hlo
    rw [hcSucc] at hhi
    exact hframe read hlo hhi w hw
  have hparentWitness := proposedBlockAt_parent S rho
    (S.hc.opening_slot q') hwindow'.proposal
  obtain ⟨Parent, hParent?, hParentErase⟩ := hparentWitness
  have hB'parent : B'.parent = Parent := by
    cases B' with
    | genesis => cases hParent?
    | node parent slot root votes support rows proposer =>
        exact Option.some.inj hParent?
  have hs'pos : 0 < S.hc.opening_slot q' := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hwindow'.roundPositive
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hproposalHor' : Protocol.proposal_time S.E
      (S.hc.opening_slot q') ≤ rho.horizon := by
    exact (Protocol.proposal_time_le_confirmation_time S.E _).trans
      (by simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hhor)
  have hB'run : RunBlock S rho B' :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot q') hs'pos hcarrier'.1 hproposalHor' hwindow'.proposal
  have hParentRun : RunBlock S rho B'.parent := by
    exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hB'run
      (by simpa only [hB'parent] using
        (seedSourceCap_namedParent_preceq B'))
  intro v hv Q hsource
  obtain ⟨D, hDbody, hDerase, hDrun, hσ⟩ :=
    seedFresh_namedSource_witness S adm hv hsource
  have hactive : B.erase ∈
      PhaseGrades.filteredTree (actionReadAt S rho v (q' - 1)) :=
    namedGradeFormsAt_actionStore_of_window S hforms hv (hretained v hv)
  have hBQ : Block.Preceq B.erase Q :=
    namedGradeFormsAt_preceq_actionSource S adm.toNamedAdmissibleCore
      hcOne hcHor hforms hv hactive hsource
  have hBDerase : Block.Preceq B.erase D.erase := by
    rw [hDerase]
    exact hBQ
  have hBD : NamedBlock.Preceq B D :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hBrun hDrun hBDerase
  have hDband : M - 1 ≤ (Protocol.derive_named S.E S.cfg D).h := by
    have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hBD
    rw [hpred] at hmono
    exact hmono
  have hsourceParent := seedSourceCap_preceq_nextOpeningParent_of_gateOff
    S adm hcom hfb hcOne hframeC hpostC hhorC hready hv hsource hDbody
      hDerase hDrun hDband (by simpa only [hcSucc] using hcarrier'.1)
  have hsourceParent' : Block.Preceq Q
      (proposedParent S rho (S.hc.opening_slot q')) := by
    simpa only [hcSucc] using hsourceParent
  have hDParentErase : Block.Preceq D.erase B'.parent.erase := by
    rw [hDerase, hB'parent, hParentErase]
    exact hsourceParent'
  have hDParent : NamedBlock.Preceq D B'.parent :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hDrun hParentRun
      hDParentErase
  have hσheight :
      ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h =
        (Protocol.derive_named S.E S.cfg D).h :=
    congrArg (fun X : Protocol.ChainState V => X.h) hσ
  calc
    ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h =
        (Protocol.derive_named S.E S.cfg D).h := hσheight
    _ ≤ (Protocol.derive_named S.E S.cfg B'.parent).h :=
      Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hDParent

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
