module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FreshFGSourceCone

@[expose] public section

/-! # Capture of a fresh FG source

An exact source selected at a seed action enters the honest Goldfish vote cone,
persists to the round boundary, and is therefore available to the next opening
proposal capture step.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem confirmation_time_mono_fresh (E : Env V) {a b : Slot}
    (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time E a,
    ← Protocol.vote_time_succ_add_delta_eq_confirmation_time E b]
  exact Int.add_le_add_right
    (Protocol.vote_time_mono_slots E (Nat.succ_le_succ hab)) _

/-- A clear exact FG source seeds the vote cone one slot after the opening. -/
theorem secondSlotCone_of_clearFGSource
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hbandO : ∀ u ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho u (S.hc.opening_slot c) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    (hband1 : ∀ w ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (S.hc.opening_slot c + 1) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hCrun : ∃ Cn : NamedBlock V, Cn.erase = C ∧ RunBlock S rho Cn)
    (hanchor : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (S.hc.opening_slot c + 1)) C = true)
    (hclear : Block.Preceq C (actionStoreAt S rho v c).live_confirmed) :
    NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
      (fun X => Block.Preceq C X) := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hoPos : 0 < S.hc.opening_slot c := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hc (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hoo' : S.hc.opening_slot c + 2 ≤ S.hc.opening_slot (c + 1) := by
    unfold Protocol.HealConfig.opening_slot
    rw [Nat.succ_mul]
    exact Nat.add_le_add_left S.hc.R_ge_two _
  have hSc : S.a c = Protocol.confirmation_time S.E (S.hc.opening_slot c) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
  have hpredLe : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have hpredLt : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hhorC : S.a c ≤ rho.horizon := haCSucc.trans hhor
  have hframeC : GateOffFrameAt S rho M (c - 1) c :=
    fun read hlo hhi w hw => hframe read hlo (hhi.trans haCSucc) w hw
  have hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot c) := by
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact hpost.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1)
  have hpredProp : S.a (c - 1) ≤ Protocol.proposal_time S.E (S.hc.opening_slot c) := by
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
  have hvoteO_le : Protocol.vote_time S.E (S.hc.opening_slot c) ≤ S.a c := by
    rw [hSc]
    exact Protocol.vote_time_le_confirmation_time S.E _
  have hpredVoteO : S.a (c - 1) ≤ Protocol.vote_time S.E (S.hc.opening_slot c) :=
    hpredProp.trans (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))
  have hvoteOHor : Protocol.vote_time S.E (S.hc.opening_slot c) ≤ rho.horizon :=
    hvoteO_le.trans hhorC
  have hpostVoteO : S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot c) :=
    hpost.trans hpredVoteO
  have hvote1Action : Protocol.vote_time S.E (S.hc.opening_slot c + 1) ≤ S.a c :=
    by
      have h := Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E
        (S.hc.opening_slot c)
      rw [Setup.a, Protocol.a_eq_confirmation_time, ← h]
      exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hpredVote1 : S.a (c - 1) ≤ Protocol.vote_time S.E (S.hc.opening_slot c + 1) :=
    hpredVoteO.trans (Protocol.vote_time_mono_slots S.E (Nat.le_succ _))
  have hconf1 : Protocol.confirmation_time S.E (S.hc.opening_slot c + 1) ≤
      S.a (c + 1) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact confirmation_time_mono_fresh S.E ((Nat.le_succ _).trans hoo')
  have hconfOHor : Protocol.confirmation_time S.E (S.hc.opening_slot c) ≤
      rho.horizon := by rw [← hSc]; exact hhorC
  have hframeV1 : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).h_j + 2 ≤ M ∧
      (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).h_max = M :=
    fun w hw => hframe _ hpredVote1 (hvote1Action.trans haCSucc) w hw
  rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v c with
    ⟨D, hgen, hDeq⟩ | ⟨R, hReq, hRlive⟩
  · rw [← hDeq] at hclear
    obtain ⟨x, hx, hxCommittee, hDx⟩ :=
      genuineConfirmation_exists_honestVoteSupporter_ceiling
        S adm hcom hv hoPos hpostVoteO hconfOHor hgen
    obtain ⟨Hx, hHxErase, hHxRun, hHxBand⟩ := hbandO x hx
    have hsupp : ∃ u ∈ rho.honest, ∃ Hn : NamedBlock V,
        Hn.erase = voterHeadAt S rho u (S.hc.opening_slot c) ∧ RunBlock S rho Hn ∧
          Block.Preceq D Hn.erase ∧
          M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h :=
      ⟨x, hx, Hx, hHxErase, hHxRun, by rw [hHxErase]; exact hDx, hHxBand⟩
    have hframe1 : ∀ w ∈ rho.honest,
        (voteDutyStore S rho w (S.hc.opening_slot c + 1)).h_max = M ∧
        (voteDutyStore S rho w (S.hc.opening_slot c + 1)).h_j + 2 ≤ M ∧
        (Block.Preceq (Protocol.get_fg_root
            (voteDutyStore S rho w (S.hc.opening_slot c + 1)).toHealing.toFG) C ∨
          Block.Preceq C (Protocol.get_fg_root
            (voteDutyStore S rho w (S.hc.opening_slot c + 1)).toHealing.toFG)) := by
      intro w hw
      have hcmp := fgRoot_comparable_of_bandWitness S adm hfb hw
        (hframeV1 w hw).1 (hframeV1 w hw).2 hHxRun
        (Block.preceq_trans hclear (by rw [hHxErase]; exact hDx)) hHxBand
      exact ⟨by simpa only [voteDutyStore, voteStore, tickStore] using (hframeV1 w hw).2,
        by simpa only [voteDutyStore, voteStore, tickStore] using (hframeV1 w hw).1,
        by simpa only [voteDutyStore, voteStore, tickStore] using hcmp⟩
    exact baseCone_succ_of_genuineSupporter_rootComparable S adm hcom hfb hv
      hpostProp (hconf1.trans hhor) hgen hclear hCrun hframe1 hsupp hanchor
  · rw [← hRlive] at hclear
    have hfr := hframe (S.a c) hpredLe haCSucc v hv
    refine secondSlotCone_of_rootBelow' S adm hfb hhorC hframeC hband1 hv ?_
    have hR' : R = (rho.storeBeforeTime S v (S.a c)).core.F := by
      have h := fgRoot_eq_F_of_frame hfr.1 hfr.2
      rw [hReq, hSc]
      rw [hSc] at h
      simpa only [confStore, tickStore] using h
    rw [← hR']
    exact hclear

/-- The exact FG source seeds the honest vote cone at the second slot. -/
theorem freshFGSource_secondSlotCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    (ready : GradeRoundReady S rho c)
    (hband : ∀ d : Slot, S.hc.opening_slot c ≤ d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v c) c = some C)
    (hCrun : ∃ Cn : NamedBlock V, Cn.erase = C ∧ RunBlock S rho Cn) :
    NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
      (fun X => Block.Preceq C X) := by
  have hb : S.hc.opening_slot c + 1 ≤ S.hc.opening_slot (c + 1) - 1 := by
    unfold Protocol.HealConfig.opening_slot
    have hR := S.hc.R_ge_two
    apply Nat.le_sub_of_add_le
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  have hbandO := fun u hu => hband _ le_rfl ((Nat.le_succ _).trans hb) u hu
  have hband1 := fun w hw => hband _ (Nat.le_succ _) hb w hw
  cases hQ : nodeQ2 S (actionReadAt S rho v c) c with
  | none =>
      have hbad := hsource
      simp only [nodeFGSource, nodeQ2, nodeRead] at hbad hQ
      unfold Protocol.grade2_block_with at hbad
      rw [hQ] at hbad
      simp [Protocol.fg_source_with] at hbad
  | some Q =>
      have hsource' := hsource
      rw [nodeFGSource, Protocol.fg_source_with.eq_def] at hsource'
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v c).cache)
          S.E S.hc (actionReadAt S rho v c).st.core.toHealing c = some Q := hQ
      rw [hQ'] at hsource'
      cases hwalk : Protocol.deepest_clear (some Q)
          (actionReadAt S rho v c).st.core.toHealing.live_confirmed
          ((NamedProfile.gradeContract (actionReadAt S rho v c).cache).read
            S.E S.hc (actionReadAt S rho v c).st.core.toHealing c).clear with
      | none =>
          simp only [hwalk] at hsource'
          have hCQ : C = Q := (Option.some_inj.mp hsource').symm
          subst C
          have haCSucc := Assembly.a_mono S (Nat.le_succ c)
          exact secondSlotCone_of_grade2' S adm hfb hc hpost (haCSucc.trans hhor)
            (fun read hlo hhi w hw => hframe read hlo (hhi.trans haCSucc) w hw)
            ready hv hQ
      | some B =>
          simp only [hwalk] at hsource'
          have hCB : C = B := (Option.some_inj.mp hsource').symm
          subst B
          have hclear : Block.Preceq C (actionStoreAt S rho v c).live_confirmed :=
            Proofs.Engine.deepest_clear_preceq hwalk
          exact secondSlotCone_of_clearFGSource S adm hcom hfb hc hpost hhor hframe
            hbandO hband1 hv hCrun
            (fun w hw => preparedAnchor_compatible_freshFGSource_of_gateOff_relative
              S adm hfb hc hframe hpost hhor ready hw hv (Nat.le_refl _)
                hb (seedEntryRoundOf S le_rfl hb) hsource)
            hclear

/-- A fresh source cone persists to the last vote of its seed round. The
source's named lower-band witness is local: callers can obtain it from the
persisted opening block below the source. -/
theorem freshFGSource_boundaryCone
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
    (hCband : M - 1 ≤ (Protocol.derive_named S.E S.cfg Cn).h) :
    NamedHonestVotesCone S rho (seedRoundLastSlot S c)
      (fun X => Block.Preceq C X) := by
  have hb : S.hc.opening_slot c + 1 ≤ seedRoundLastSlot S c := by
    unfold seedRoundLastSlot Protocol.HealConfig.opening_slot
    have hR := S.hc.R_ge_two
    apply Nat.le_sub_of_add_le
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  have hband : ∀ d : Slot, S.hc.opening_slot c ≤ d →
      d ≤ seedRoundLastSlot S c → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h := by
    intro d hlo hhi w hw
    exact voteDutyHead_band_at_duty S adm hfb hc hframe hpost hhor hw hlo hhi
      (seedEntryRoundOf' S hlo hhi)
  have hbaseCone := freshFGSource_secondSlotCone S adm hcom hfb hc hframe hpost
    hhor ready hband hv hsource ⟨Cn, hCerase, hCrun⟩
  have hbaseThin : ThinHonestHeadAt S rho M (S.hc.opening_slot c + 1) C := by
    simpa only [hCerase] using
      thinHonestHeadAt_of_thin_endpoint S adm hcom hCrun hCband (by
        simpa only [hCerase] using hbaseCone)
  have hframe' : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
      d ≤ seedRoundLastSlot S c → VoteDutyFrameAt' S rho M d C := by
    intro d hdlo hdhi w hw
    have hlo : S.hc.opening_slot c ≤ d :=
      (Nat.le_succ _).trans (Nat.le_of_lt hdlo)
    have hvoteLo : S.a (c - 1) ≤ Protocol.vote_time S.E d := by
      have hpredLt : c - 1 < c := Nat.sub_lt (Nat.succ_le_iff.mp hc) Nat.one_pos
      have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
      exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
        ((Protocol.proposal_time_mono S.E hlo).trans
          (le_of_lt (Protocol.proposal_time_lt_vote_time S.E d)))
    have hvoteHi : Protocol.vote_time S.E d ≤ S.a (c + 1) := by
      have hdNext : d ≤ S.hc.opening_slot (c + 1) :=
        hdhi.trans (by unfold seedRoundLastSlot; exact Nat.sub_le _ _)
      refine (Protocol.vote_time_le_confirmation_time S.E d).trans ?_
      have hm := confirmation_time_mono_fresh S.E hdNext
      exact hm.trans (by rw [Setup.a, Protocol.a_eq_confirmation_time])
    have hfr := hframe _ hvoteLo hvoteHi w hw
    have hcmp := fgRoot_comparable_of_bandWitness S adm hfb hw hfr.1 hfr.2
      hCrun (by rw [hCerase]; exact Block.preceq_self C) hCband
    exact ⟨by simpa only [voteDutyStore, voteStore, tickStore] using hfr.2,
      by simpa only [voteDutyStore, voteStore, tickStore] using hfr.1,
      by simpa only [voteDutyStore, voteStore, tickStore] using hcmp⟩
  have hanchor : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
      d ≤ seedRoundLastSlot S c → ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w d) C = true := by
    intro d hdlo hdhi w hw
    exact preparedAnchor_compatible_freshFGSource_of_gateOff_relative
      S adm hfb hc hframe hpost hhor ready hw hv (Nat.le_of_lt hdlo) hdhi
        (seedEntryRoundOf S (Nat.le_of_lt hdlo) hdhi) hsource
  have hband' : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
      d ≤ seedRoundLastSlot S c → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w d).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg Hn).h := by
    intro d hdlo hdhi w hw
    obtain ⟨H, he, hr, hh⟩ := hband d
      ((Nat.le_succ _).trans (Nat.le_of_lt hdlo)) hdhi w hw
    have hvoteLo : S.a (c - 1) ≤ Protocol.vote_time S.E d := by
      have hpredLt : c - 1 < c := Nat.sub_lt (Nat.succ_le_iff.mp hc) Nat.one_pos
      have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
      exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
        ((Protocol.proposal_time_mono S.E
          ((Nat.le_succ _).trans (Nat.le_of_lt hdlo))).trans
            (le_of_lt (Protocol.proposal_time_lt_vote_time S.E d)))
    have hvoteHi : Protocol.vote_time S.E d ≤ S.a (c + 1) := by
      refine (Protocol.vote_time_le_confirmation_time S.E d).trans ?_
      exact (confirmation_time_mono_fresh S.E
        (hdhi.trans (by unfold seedRoundLastSlot; exact Nat.sub_le _ _))).trans
          (by rw [Setup.a, Protocol.a_eq_confirmation_time])
    have hmax := (hframe _ hvoteLo hvoteHi w hw).2
    refine ⟨H, he, hr, ?_⟩
    simpa only [voteDutyStore, voteStore, tickStore, hmax] using hh
  have hpostVote : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot c + 1) := by
    have hpredLt : c - 1 < c := Nat.sub_lt (Nat.succ_le_iff.mp hc) Nat.one_pos
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact hpost.trans (((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((Protocol.proposal_time_mono S.E (Nat.le_succ _)).trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))))
  exact (boundaryConeAndThin_of_baseCone' S adm hcom hfb hpostVote hhor
    ⟨hbaseCone, hbaseThin⟩ hframe' hanchor hband').1

/-- The fresh source is below the next honest opening proposal parent. The
two final local premises are exactly the proposal-capture interface: source
activity and compatibility with that proposal read's prepared anchor. -/
theorem freshFGSource_preceq_nextOpeningParent
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
    (hprop : S.E.proposer (S.hc.opening_slot (c + 1)) ∈ rho.honest)
    (hactive : C ∈ Protocol.get_filtered_block_tree
      (proposerDutyStore S rho (S.hc.opening_slot (c + 1))).toHealing.toFG)
    (hcompat : Block.compatible
      (nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot (c + 1)))
        (S.hc.round_of
          (Internal.NamedRecoveryRead.proposalDutyRead S rho
            (S.hc.opening_slot (c + 1))).st.core.s)) C = true) :
    Block.Preceq C (proposedParent S rho (S.hc.opening_slot (c + 1))) := by
  have hcone := freshFGSource_boundaryCone S adm hcom hfb hc hframe hpost hhor
    ready hv hsource hCerase hCrun hCband
  have hlastPos : 0 < seedRoundLastSlot S c := by
    have hopenPos : 0 < S.hc.opening_slot c := by
      unfold Protocol.HealConfig.opening_slot
      exact Nat.mul_pos hc (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    exact lt_of_lt_of_le hopenPos (by
      unfold seedRoundLastSlot Protocol.HealConfig.opening_slot
      have hR := S.hc.R_ge_two
      apply Nat.le_sub_of_add_le
      rw [Nat.add_mul]
      simp only [Nat.one_mul]
      omega)
  have hlastSucc : seedRoundLastSlot S c + 1 = S.hc.opening_slot (c + 1) := by
    unfold seedRoundLastSlot Protocol.HealConfig.opening_slot
    have hpos : 0 < (c + 1) * S.hc.R :=
      Nat.mul_pos (Nat.succ_pos c)
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
  have hpostLast : S.E.t_GST ≤ Protocol.vote_time S.E (seedRoundLastSlot S c) := by
    have hlo : S.hc.opening_slot c ≤ seedRoundLastSlot S c := by
      unfold seedRoundLastSlot Protocol.HealConfig.opening_slot
      have hR := S.hc.R_ge_two
      apply Nat.le_sub_of_add_le
      rw [Nat.add_mul]
      simp only [Nat.one_mul]
      omega
    have hpredLt : c - 1 < c := Nat.sub_lt (Nat.succ_le_iff.mp hc) Nat.one_pos
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact hpost.trans (((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
      ((Protocol.proposal_time_mono S.E hlo).trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))))
  have hsupportHor : Protocol.support_cutoff S.E (seedRoundLastSlot S c) ≤
      rho.horizon := by
    exact (Protocol.support_cutoff_le_confirmation_time S.E _).trans
      ((confirmation_time_mono_fresh S.E
        (by unfold seedRoundLastSlot; exact Nat.sub_le _ _)).trans
          (by simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hhor))
  have hout := coneTarget_preceq_nextProposedParent_named S adm hcom hlastPos
    hpostLast hsupportHor (by simpa only [hlastSucc] using hprop) hcone
    (by simpa only [hlastSucc] using hactive)
    (by simpa only [hlastSucc] using hcompat)
  simpa only [hlastSucc] using hout

#print axioms secondSlotCone_of_clearFGSource
#print axioms freshFGSource_secondSlotCone
#print axioms freshFGSource_boundaryCone
#print axioms freshFGSource_preceq_nextOpeningParent

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
