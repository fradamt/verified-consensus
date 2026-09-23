module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootGradeBootstrap
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot

@[expose] public section

/-! # Fixed-height root Claim-1 closure
A bounded recurrent honest proposer window either exposes a public frontier
rise, or supplies one predecessor-round common grade. Under the no-rise branch,
every relevant action and vote read has the previous exact FG root and fixed
frontier. The fixed-root Claim-1 producer and certified-prefix lock then close
the opening cone result.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-
/-- A bounded proposer recurrence turns a fixed-height root interference into
an opening Claim-1 cone-root lock at the predecessor round, unless the public
honest frontier has risen by the recurrence endpoint. -/
theorem fixedHeightJustificationRoot_boundedOpeningConeRootLock_of_proposerRecurrence_of_faultBound
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time}
    (h: FixedHeightJustificationRootAtRead S rho H w read)
    {r gap: Round}
    (hpost: S.E.t_GST ≤ read) (hreadAction: read ≤ S.a r)
    (hrecurrence: MultiProposerRecurrence S rho gap)
    (hendHor: S.a (r + 4 + gap) ≤ rho.horizon):
    H < honestHMaxAt S rho (S.a (r + 4 + gap)) ∨
      ∃ q: Round,
        r + 3 ≤ q ∧ q ≤ r + 3 + gap ∧
          ProposerCarrierAt S rho q ∧
            GradeFormsAt S rho (q - 1)
              (rho.storeBeforeTime S w read).J ∧
              SGTargetOpeningConeRootLock S rho H (q - 1)
                (S.hc.opening_slot q - 1):= by
  by_cases hrise: H < honestHMaxAt S rho (S.a (r + 4 + gap))
  · exact Or.inl hrise
  · have hcapEnd: honestHMaxAt S rho (S.a (r + 4 + gap)) ≤ H:=
      Nat.le_of_not_gt hrise
    rcases
        fixedHeightJustificationRoot_boundedGradeFormsAt_of_proposerRecurrence_of_faultBound
          S adm hfb h hpost hreadAction hrecurrence hendHor with
      hcontrary | ⟨q, hqlo, hqhi, hcarrier, hforms⟩
    · exact False.elim (hrise hcontrary)
    · right
      refine ⟨q, hqlo, hqhi, hcarrier, hforms, ?_⟩
      have hqlo': r + 1 + 2 ≤ q:= by
        simpa only [Nat.add_assoc] using hqlo
      have hqTwo: 2 ≤ q:=
        (Nat.le_add_left 2 (r + 1)).trans hqlo'
      have hqOne: 1 ≤ q:=
        (by decide: 1 ≤ 2).trans hqTwo
      have hqPos: 0 < q:=
        (by decide: 0 < 2).trans_le hqTwo
      have hqPredPos: 0 < q - 1:=
        Nat.sub_pos_of_lt (show 1 < q from hqTwo)
      have hqActionLower: r + 1 ≤ q - 2:=
        Nat.le_sub_of_add_le hqlo'
      have hqActionSucc: q - 2 ≤ q - 1:=
        Nat.sub_le_sub_left (by decide: 1 ≤ 2) q
      have hqReadyLower: r + 1 ≤ q - 1:=
        hqActionLower.trans hqActionSucc
      have hqPred: q - 2 + 1 = q - 1:= by
        have hqEq: q - 2 + 2 = q:= Nat.sub_add_cancel hqTwo
        rw [← hqEq]
        simp
      have hqPredAdd: q - 1 + 1 = q:=
        Nat.sub_add_cancel hqOne
      have hbaseEnd: r + 3 ≤ r + 4:=
        Nat.add_le_add_left (Nat.le_succ 3) r
      have hqEnd: q ≤ r + 4 + gap:=
        hqhi.trans (Nat.add_le_add_right hbaseEnd gap)
      have hqActionEnd: q - 2 ≤ r + 4 + gap:=
        (Nat.sub_le q 2).trans hqEnd
      have hqNextEnd: q - 1 ≤ r + 4 + gap:=
        (Nat.sub_le q 1).trans hqEnd
      have hactionAtEnd: S.a (q - 2) ≤ S.a (r + 4 + gap):=
        Assembly.a_mono S hqActionEnd
      have hnextAtEnd: S.a (q - 1) ≤ S.a (r + 4 + gap):=
        Assembly.a_mono S hqNextEnd
      have hqAtEnd: S.a q ≤ S.a (r + 4 + gap):=
        Assembly.a_mono S hqEnd
      have hdelayAction: read + S.E.Δ ≤ S.a (q - 2):= by
        calc
          read + S.E.Δ ≤ S.a r + S.E.Δ:=
            Int.add_le_add_right hreadAction S.E.Δ
          _ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1):=
            action_add_delta_le_next_Γ_neg1 S r
          _ ≤ S.a (r + 1):=
            le_of_lt (next_Γ_neg1_lt_action S r)
          _ ≤ S.a (q - 2):= Assembly.a_mono S hqActionLower
      have hdelayNext: read + S.E.Δ ≤ S.a (q - 1):=
        hdelayAction.trans (Assembly.a_mono S hqActionSucc)
      have hnextHor: S.a (q - 1) ≤ rho.horizon:=
        hnextAtEnd.trans hendHor
      have hnextCap: honestHMaxAt S rho (S.a (q - 1)) ≤ H:=
        (honestHMaxAt_mono S adm.toScheduleWellFormed hnextAtEnd).trans hcapEnd
      have hready: GradeRoundReady S rho (q - 1):=
        gradeRoundReady_of_action_horizon S
          (gst_le_Γ_neg1_succ S r (hpost.trans hreadAction))
          hqReadyLower hnextHor
      obtain ⟨hslo, hshi, hsucc⟩:=
        lastInteriorSlot_before_opening S.hc hqPos
      have hslotPrev: S.hc.opening_slot (q - 2) + 2 ≤
          S.hc.opening_slot (q - 1):= by
        calc
          S.hc.opening_slot (q - 2) + 2 ≤
              S.hc.opening_slot (q - 2) + S.hc.R:=
            Nat.add_le_add_left S.hc.R_ge_two _
          _ = S.hc.opening_slot ((q - 2) + 1):=
            (opening_slot_succ_eq S.hc (q - 2)).symm
          _ = S.hc.opening_slot (q - 1):=
            congrArg S.hc.opening_slot hqPred
      have hHone: 1 ≤ H:=
        Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
      have htargetHeight:
          (derived_state S.E S.cfg (rho.storeBeforeTime S w read).J).h = H - 1:=
        h.targetDerivedHeight
      have htargetHeightSucc:
          (derived_state S.E S.cfg (rho.storeBeforeTime S w read).J).h + 1 = H:= by
        rw [htargetHeight]
        exact Nat.sub_add_cancel hHone
      have htargetHeightLt:
          (derived_state S.E S.cfg (rho.storeBeforeTime S w read).J).h < H:= by
        rw [htargetHeight]
        exact Nat.sub_lt
          (Nat.zero_lt_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive))
          (by decide: 0 < 1)
      have hsb: SlashableBound S rho:=
        slashableBound_of_admissible_belowOneThird S adm hfb
      have hactionExact: ∀ v ∈ rho.honest,
          Protocol.get_fg_root
              (actionStoreAt S rho v (q - 1)).toHealing.toFG =
            (rho.storeBeforeTime S w read).J ∧
          (actionStoreAt S rho v (q - 1)).h_max = H:= by
        intro v hv
        obtain ⟨hroot, hmax⟩:=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb h hv hpost hdelayNext hnextHor hnextCap
        refine ⟨?_, ?_⟩
        · rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho v (q - 1)]
          exact hroot
        · have hbridge: (actionStoreAt S rho v (q - 1)).h_max =
              (rho.storeBeforeTime S v (S.a (q - 1))).h_max:= by
            rfl
          exact hbridge.trans hmax
      have hactionRoot: ∀ v ∈ rho.honest,
          Protocol.get_fg_root
              (actionStoreAt S rho v (q - 1)).toHealing.toFG =
            (rho.storeBeforeTime S w read).J:= by
        intro v hv
        exact (hactionExact v hv).1
      have hactionCap: ∀ v ∈ rho.honest,
          (actionStoreAt S rho v (q - 1)).h_max ≤
            (derived_state S.E S.cfg (rho.storeBeforeTime S w read).J).h + 1:= by
        intro v hv
        exact le_of_eq ((hactionExact v hv).2.trans htargetHeightSucc.symm)
      have hvoteDelay: ∀ d: Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          read + S.E.Δ ≤ Protocol.vote_time S.E d:= by
        intro d hdlo _
        have hprevOpeningLe: S.hc.opening_slot (q - 1) ≤ d:=
          (Nat.le_succ _).trans hdlo
        have hslot: S.hc.opening_slot (q - 2) + 2 ≤ d:=
          hslotPrev.trans hprevOpeningLe
        exact hdelayAction.trans
          ((le_of_lt (Protocol.action_lt_vote_time_two_after S (q - 2))).trans
            (Protocol.vote_time_mono_slots S.E hslot))
      have hvoteLeActionQ: ∀ d: Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          Protocol.vote_time S.E d ≤ S.a q:= by
        intro d _ hdhi
        have hdhiQ: d < S.hc.opening_slot q:= by
          simpa only [hqPredAdd] using hdhi
        exact (Protocol.vote_time_mono_slots S.E (Nat.le_of_lt hdhiQ)).trans
          (le_of_lt (Protocol.opening_vote_time_lt_action S q))
      have hvoteExact: ∀ d: Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          ∀ v ∈ rho.honest,
            Protocol.get_fg_root
                (Proofs.Optimistic.voteDutyStore S rho v d).toHealing.toFG =
              (rho.storeBeforeTime S w read).J ∧
            (Proofs.Optimistic.voteDutyStore S rho v d).h_max = H:= by
        intro d hdlo hdhi v hv
        have hvoteEnd: Protocol.vote_time S.E d ≤ S.a (r + 4 + gap):=
          (hvoteLeActionQ d hdlo hdhi).trans hqAtEnd
        have hvoteHor: Protocol.vote_time S.E d ≤ rho.horizon:=
          hvoteEnd.trans hendHor
        have hvoteCap: honestHMaxAt S rho (Protocol.vote_time S.E d) ≤ H:=
          (honestHMaxAt_mono S adm.toScheduleWellFormed hvoteEnd).trans hcapEnd
        obtain ⟨hroot, hmax⟩:=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb h hv hpost (hvoteDelay d hdlo hdhi) hvoteHor hvoteCap
        refine ⟨?_, ?_⟩
        · change Protocol.get_fg_root
              (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).toHealing.toFG =
            (rho.storeBeforeTime S w read).J
          exact hroot
        · change (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).h_max = H
          exact hmax
      have hvoteRoot: ∀ d: Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          ∀ v ∈ rho.honest,
            Protocol.get_fg_root
                (Proofs.Optimistic.voteDutyStore S rho v d).toHealing.toFG =
              (rho.storeBeforeTime S w read).J:= by
        intro d hdlo hdhi v hv
        exact (hvoteExact d hdlo hdhi v hv).1
      have hvoteCap: ∀ d: Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          ∀ v ∈ rho.honest,
            (Proofs.Optimistic.voteDutyStore S rho v d).h_max ≤
              (derived_state S.E S.cfg (rho.storeBeforeTime S w read).J).h + 1:= by
        intro d hdlo hdhi v hv
        exact le_of_eq
          ((hvoteExact d hdlo hdhi v hv).2.trans htargetHeightSucc.symm)
      have hslotHor: Protocol.vote_time S.E (S.hc.opening_slot q - 1) ≤
          rho.horizon:= by
        exact ((hvoteLeActionQ (S.hc.opening_slot q - 1) hslo hshi).trans
          hqAtEnd).trans hendHor
      have hcanonical: SGTargetConeCanonicality S rho (q - 1)
          (S.hc.opening_slot q - 1):=
        sgTargetConeCanonicality_of_gradeFormsAt_exactFGRoot_heightCap
          S adm hcom hfb hqPredPos hready hforms hslo hshi hnextHor hslotHor
            hactionRoot hactionCap hvoteRoot hvoteCap
      have hrq: r < q:=
        (Nat.lt_succ_self r).trans_le
          (hqActionLower.trans (Nat.sub_le q 2))
      have hopenDelay: read + S.E.Δ ≤
          Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1):= by
        rw [hsucc]
        exact ((Int.add_le_add_right hreadAction S.E.Δ).trans
          (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hrq)).trans
            (le_of_lt (Protocol.proposal_time_lt_vote_time S.E
              (S.hc.opening_slot q)))
      have hopenEnd: Protocol.vote_time S.E
          ((S.hc.opening_slot q - 1) + 1) ≤ S.a (r + 4 + gap):= by
        rw [hsucc]
        exact (le_of_lt (Protocol.opening_vote_time_lt_action S q)).trans
          hqAtEnd
      have hopenHor: Protocol.vote_time S.E
          ((S.hc.opening_slot q - 1) + 1) ≤ rho.horizon:=
        hopenEnd.trans hendHor
      have hopenCap: honestHMaxAt S rho
          (Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1)) ≤ H:=
        (honestHMaxAt_mono S adm.toScheduleWellFormed hopenEnd).trans hcapEnd
      have hopenExact: ∀ v ∈ rho.honest,
          Protocol.get_fg_root
              (Proofs.Optimistic.voteDutyStore S rho v
                ((S.hc.opening_slot q - 1) + 1)).toHealing.toFG =
            (rho.storeBeforeTime S w read).J ∧
          (Proofs.Optimistic.voteDutyStore S rho v
            ((S.hc.opening_slot q - 1) + 1)).h_max = H:= by
        intro v hv
        obtain ⟨hroot, hmax⟩:=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb h hv hpost hopenDelay hopenHor hopenCap
        refine ⟨?_, ?_⟩
        · change Protocol.get_fg_root
              (rho.storeBeforeTime S v
                (Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1))).toHealing.toFG =
            (rho.storeBeforeTime S w read).J
          exact hroot
        · change (rho.storeBeforeTime S v
              (Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1))).h_max = H
          exact hmax
      have hpostSlot: S.E.t_GST ≤
          Protocol.vote_time S.E (S.hc.opening_slot q - 1):= by
        have hreadDelay: read ≤ read + S.E.Δ:=
          le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
        exact hpost.trans (hreadDelay.trans
          (hvoteDelay (S.hc.opening_slot q - 1) hslo hshi))
      exact sgTargetOpeningConeRootLock_of_fixedFrontier_certifiedPrefix
        S adm hcom hfb hcanonical h.fixedTarget.targetBlock
          h.fixedTarget.certificate htargetHeightLt
          (fun u hu => preceq_actionSGBlockAt_of_gradeFormsAt S hforms hu)
          hpostSlot hopenHor (fun v hv => (hopenExact v hv).2)

/-- Compatibility corollary for the original strict-read interference record. -/
theorem fixedHeightRootTarget_boundedOpeningConeRootLock_of_proposerRecurrence_of_faultBound
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time} {P: Block V}
    (h: FixedHeightRootInterferenceAtRead S rho H w read P)
    {r gap: Round}
    (hpost: S.E.t_GST ≤ read) (hreadAction: read ≤ S.a r)
    (hrecurrence: MultiProposerRecurrence S rho gap)
    (hendHor: S.a (r + 4 + gap) ≤ rho.horizon):
    H < honestHMaxAt S rho (S.a (r + 4 + gap)) ∨
      ∃ q: Round,
        r + 3 ≤ q ∧ q ≤ r + 3 + gap ∧
          ProposerCarrierAt S rho q ∧
            GradeFormsAt S rho (q - 1)
              (rho.storeBeforeTime S w read).J ∧
              SGTargetOpeningConeRootLock S rho H (q - 1)
                (S.hc.opening_slot q - 1):=
  fixedHeightJustificationRoot_boundedOpeningConeRootLock_of_proposerRecurrence_of_faultBound
    S adm hcom hfb h.toJustificationRootAtRead hpost hreadAction
      hrecurrence hendHor

-/

private theorem claimOne_fixedHeightJustificationRoot_target_named
    (S : Setup V) {rho : Run V} {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read) :
    ∃ J : NamedBlock V,
      J.erase = (rho.storeBeforeTime S w read).J ∧
        RunBlock S rho J ∧
          (Protocol.derive_named S.E S.cfg J).h = H - 1 := by
  obtain ⟨D, _hDbody, hDrun, hjust⟩ := h.carrierExists
  have hhj : (Protocol.derive_named S.E S.cfg D).h_j = H - 1 := by
    exact hjust.2.trans (by simpa only using h.fixedTarget.justificationHeight)
  have hhjNe : (Protocol.derive_named S.E S.cfg D).h_j ≠ 0 := by
    rw [hhj]
    exact Nat.ne_of_gt h.targetHeightPositive
  obtain ⟨J, hJD, hJerase, hJheight⟩ :=
    (NamedCheckpointHeights.justified_ancestor_height S.E S.cfg D).resolve_left hhjNe
  refine ⟨J, hJerase.trans hjust.1, ?_, ?_⟩
  · exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDrun hJD
  · rw [hJheight, hhj]

private theorem claimOne_runBlock_of_body_at_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {read : Time} {B : NamedBlock V}
    (hB : B ∈ (rho.storeBeforeTime S w read).bodies) :
    RunBlock S rho B := by
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted read
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
  have hB' := hB
  change B ∈ (NamedRun.stateBeforeTime S rho read w).st.bodies at hB'
  rw [congrFun hi w] at hB'
  exact hB'

private theorem claimOne_named_run_eq_of_erase
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A B : NamedBlock V} (hA : RunBlock S rho A) (hB : RunBlock S rho B)
    (herase : A.erase = B.erase) : A = B :=
  adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective A B hA hB A B
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self B))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])

private theorem claimOne_namedGradeProcessedAtAction
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {C : Block V} (hforms : NamedGradeFormsAt S rho r C)
    {v : V} (hv : v ∈ rho.honest) :
    C ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
  have hsource : C ∈ (rho.storeBeforeTime S v
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.T := by
    have hfiltered := (hforms v hv).1
    have htree := Proofs.Records.get_filtered_block_tree_subset _ hfiltered
    simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
      Run.storeBeforeTime] using htree
  rw [storeBeforeTime_eq_storeAt_sub_one_recovery] at hsource ⊢
  apply StoreFinality.stateAt_T_subset
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
      (Int.sub_le_sub_right (FrameForward.domain_le_a S r .g2) 1) hsource

/-- A bounded proposer recurrence turns a fixed-height root interference into
an opening Claim-1 cone-root lock at the predecessor round, unless the public
honest frontier has risen by the recurrence endpoint. -/
theorem fixedHeightJustificationRoot_boundedOpeningConeRootLock_of_proposerRecurrence_of_faultBound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read)
    {r gap : Round}
    (hpost : S.E.t_GST ≤ read) (hreadAction : read ≤ S.a r)
    (hrecurrence : MultiProposerRecurrence S rho gap)
    (hendHor : S.a (r + 4 + gap) ≤ rho.horizon) :
    H < honestHMaxAt S rho (S.a (r + 4 + gap)) ∨
      ∃ q : Round,
        r + 3 ≤ q ∧ q ≤ r + 3 + gap ∧
          ProposerCarrierAt S rho q ∧
            NamedGradeFormsAt S rho (q - 1)
              (rho.storeBeforeTime S w read).J ∧
              SGTargetOpeningConeRootLock S rho H (q - 1)
                (S.hc.opening_slot q - 1) := by
  by_cases hrise : H < honestHMaxAt S rho (S.a (r + 4 + gap))
  · exact Or.inl hrise
  · have hcapEnd : honestHMaxAt S rho (S.a (r + 4 + gap)) ≤ H :=
      Nat.le_of_not_gt hrise
    rcases
        fixedHeightJustificationRoot_boundedGradeFormsAt_of_proposerRecurrence_of_faultBound
          S adm hfb h hpost hreadAction hrecurrence hendHor with
      hcontrary | ⟨q, hqlo, hqhi, hcarrier, hforms⟩
    · exact False.elim (hrise hcontrary)
    · right
      refine ⟨q, hqlo, hqhi, hcarrier, hforms, ?_⟩
      obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
        claimOne_fixedHeightJustificationRoot_target_named S h
      have hformsNamed : NamedGradeFormsAt S rho (q - 1) Jn.erase := by
        simpa only [hJnErase] using hforms
      have hqlo' : r + 1 + 2 ≤ q := by
        simpa only [Nat.add_assoc] using hqlo
      have hqTwo : 2 ≤ q :=
        (Nat.le_add_left 2 (r + 1)).trans hqlo'
      have hqOne : 1 ≤ q :=
        (by decide : 1 ≤ 2).trans hqTwo
      have hqPos : 0 < q :=
        (by decide : 0 < 2).trans_le hqTwo
      have hqPredPos : 0 < q - 1 :=
        Nat.sub_pos_of_lt (show 1 < q from hqTwo)
      have hqActionLower : r + 1 ≤ q - 2 :=
        Nat.le_sub_of_add_le hqlo'
      have hqActionSucc : q - 2 ≤ q - 1 :=
        Nat.sub_le_sub_left (by decide : 1 ≤ 2) q
      have hqReadyLower : r + 1 ≤ q - 1 :=
        hqActionLower.trans hqActionSucc
      have hqPred : q - 2 + 1 = q - 1 := by
        have hqEq : q - 2 + 2 = q := Nat.sub_add_cancel hqTwo
        rw [← hqEq]
        simp
      have hqPredAdd : q - 1 + 1 = q :=
        Nat.sub_add_cancel hqOne
      have hbaseEnd : r + 3 ≤ r + 4 :=
        Nat.add_le_add_left (Nat.le_succ 3) r
      have hqEnd : q ≤ r + 4 + gap :=
        hqhi.trans (Nat.add_le_add_right hbaseEnd gap)
      have hqActionEnd : q - 2 ≤ r + 4 + gap :=
        (Nat.sub_le q 2).trans hqEnd
      have hqNextEnd : q - 1 ≤ r + 4 + gap :=
        (Nat.sub_le q 1).trans hqEnd
      have hactionAtEnd : S.a (q - 2) ≤ S.a (r + 4 + gap) :=
        Assembly.a_mono S hqActionEnd
      have hnextAtEnd : S.a (q - 1) ≤ S.a (r + 4 + gap) :=
        Assembly.a_mono S hqNextEnd
      have hqAtEnd : S.a q ≤ S.a (r + 4 + gap) :=
        Assembly.a_mono S hqEnd
      have hdelayAction : read + S.E.Δ ≤ S.a (q - 2) := by
        calc
          read + S.E.Δ ≤ S.a r + S.E.Δ :=
            Int.add_le_add_right hreadAction S.E.Δ
          _ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) :=
            action_add_delta_le_next_Γ_neg1 S r
          _ ≤ S.a (r + 1) :=
            le_of_lt (next_Γ_neg1_lt_action S r)
          _ ≤ S.a (q - 2) := Assembly.a_mono S hqActionLower
      have hdelayNext : read + S.E.Δ ≤ S.a (q - 1) :=
        hdelayAction.trans (Assembly.a_mono S hqActionSucc)
      have hnextHor : S.a (q - 1) ≤ rho.horizon :=
        hnextAtEnd.trans hendHor
      have hnextCap : honestHMaxAt S rho (S.a (q - 1)) ≤ H :=
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hnextAtEnd).trans hcapEnd
      have hready : GradeRoundReady S rho (q - 1) :=
        ⟨(gst_le_Γ_neg1_succ S r (hpost.trans hreadAction)).trans
            (by
              have hnextRound : r + 2 ≤ q - 1 := by
                simpa only [hqPred] using Nat.add_le_add_right hqActionLower 1
              have hmono := Γ_neg1_mono S.hc S.E.Δ_pos hnextRound
              have hround := Γ_neg1_add_rounds S.hc S.E.Δ (r + 1) 1
              have hR : (1 : Time) ≤ (S.hc.R : Nat) := by
                exact_mod_cast (le_trans (by decide : 1 ≤ 2) S.hc.R_ge_two)
              have hshift : 4 * S.E.Δ ≤
                  4 * S.E.Δ * (S.hc.R * 1 : Nat) := by
                calc
                  4 * S.E.Δ = 4 * S.E.Δ * 1 := by ring
                  _ ≤ 4 * S.E.Δ * (S.hc.R * 1 : Nat) :=
                    mul_le_mul_of_nonneg_left
                      (by simpa only [Nat.mul_one] using hR)
                      (by linarith [S.E.Δ_pos])
              have hbase : S.hc.Γ_neg1 S.E.Δ (r + 1) + 4 * S.E.Δ ≤
                  S.hc.Γ_neg1 S.E.Δ (r + 2) := by
                rw [hround]
                linarith
              have hsub : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤
                  S.hc.Γ_neg1 S.E.Δ (r + 2) - 4 * S.E.Δ := by
                exact (le_sub_iff_add_le).2 hbase
              have hsub' := sub_le_sub_right hmono (4 * S.E.Δ)
              rw [early_g2_eq_Γ_neg1_sub]
              exact hsub.trans hsub'),
          (by
            rw [domain_g0_eq_Γ_1]
            have hΓ12 : S.hc.Γ_1 S.E.Δ (q - 1) ≤
                S.hc.Γ_2 S.E.Δ (q - 1) := by
              have h := Γ_1_add_Δ S.hc S.E.Δ (q - 1)
              linarith [S.E.Δ_pos]
            exact hΓ12.trans ((Γ_2_le_a S.hc S.E.Δ_pos (q - 1)).trans hnextHor))⟩
      obtain ⟨hslo, hshi, hsucc⟩ :=
        lastInteriorSlot_before_opening S.hc hqPos
      have hslotPrev : S.hc.opening_slot (q - 2) + 2 ≤
          S.hc.opening_slot (q - 1) := by
        calc
          S.hc.opening_slot (q - 2) + 2 ≤
              S.hc.opening_slot (q - 2) + S.hc.R :=
            Nat.add_le_add_left S.hc.R_ge_two _
          _ = S.hc.opening_slot ((q - 2) + 1) :=
            (opening_slot_succ_eq S.hc (q - 2)).symm
          _ = S.hc.opening_slot (q - 1) :=
            congrArg S.hc.opening_slot hqPred
      have hHone : 1 ≤ H :=
        Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
      have htargetHeightSucc :
          (Protocol.derive_named S.E S.cfg Jn).h + 1 = H := by
        rw [hJnHeight]
        exact Nat.sub_add_cancel hHone
      have htargetHeightLt :
          (Protocol.derive_named S.E S.cfg Jn).h < H := by
        rw [hJnHeight]
        exact Nat.sub_lt
          (Nat.zero_lt_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive))
          (by decide : 0 < 1)
      have hsb : SlashableBound S rho :=
        slashableBound_of_admissible_belowOneThird S adm hfb
      have hactionExact : ∀ v ∈ rho.honest,
          Protocol.get_fg_root
              (actionStoreAt S rho v (q - 1)).toHealing.toFG =
            (rho.storeBeforeTime S w read).J ∧
          (actionStoreAt S rho v (q - 1)).h_max = H := by
        intro v hv
        obtain ⟨hroot, hmax⟩ :=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb h hv hpost hdelayNext hnextHor hnextCap
        refine ⟨?_, ?_⟩
        · rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho v (q - 1)]
          exact hroot
        · have hbridge : (actionStoreAt S rho v (q - 1)).h_max =
              (rho.storeBeforeTime S v (S.a (q - 1))).h_max := by
            rfl
          exact hbridge.trans hmax
      have hactionRoot : ∀ v ∈ rho.honest,
          Protocol.get_fg_root
              (actionStoreAt S rho v (q - 1)).toHealing.toFG = Jn.erase := by
        intro v hv
        exact (hactionExact v hv).1.trans hJnErase.symm
      have hactionCap : ∀ v ∈ rho.honest,
          (actionStoreAt S rho v (q - 1)).h_max ≤
            (Protocol.derive_named S.E S.cfg Jn).h + 1 := by
        intro v hv
        exact le_of_eq ((hactionExact v hv).2.trans htargetHeightSucc.symm)
      have hvoteDelay : ∀ d : Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          read + S.E.Δ ≤ Protocol.vote_time S.E d := by
        intro d hdlo _
        have hprevOpeningLe : S.hc.opening_slot (q - 1) ≤ d :=
          (Nat.le_succ _).trans hdlo
        have hslot : S.hc.opening_slot (q - 2) + 2 ≤ d :=
          hslotPrev.trans hprevOpeningLe
        exact hdelayAction.trans
          ((le_of_lt (Protocol.action_lt_vote_time_two_after S (q - 2))).trans
            (Protocol.vote_time_mono_slots S.E hslot))
      have hvoteLeActionQ : ∀ d : Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          Protocol.vote_time S.E d ≤ S.a q := by
        intro d _ hdhi
        have hdhiQ : d < S.hc.opening_slot q := by
          simpa only [hqPredAdd] using hdhi
        exact (Protocol.vote_time_mono_slots S.E (Nat.le_of_lt hdhiQ)).trans
          (le_of_lt (Protocol.opening_vote_time_lt_action S q))
      have hvoteExact : ∀ d : Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          ∀ v ∈ rho.honest,
            Protocol.get_fg_root
                (Proofs.Optimistic.voteDutyStore S rho v d).toHealing.toFG =
              (rho.storeBeforeTime S w read).J ∧
            (Proofs.Optimistic.voteDutyStore S rho v d).h_max = H := by
        intro d hdlo hdhi v hv
        have hvoteEnd : Protocol.vote_time S.E d ≤ S.a (r + 4 + gap) :=
          (hvoteLeActionQ d hdlo hdhi).trans hqAtEnd
        have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
          hvoteEnd.trans hendHor
        have hvoteCap : honestHMaxAt S rho (Protocol.vote_time S.E d) ≤ H :=
          (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hvoteEnd).trans hcapEnd
        obtain ⟨hroot, hmax⟩ :=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb h hv hpost (hvoteDelay d hdlo hdhi) hvoteHor hvoteCap
        refine ⟨?_, ?_⟩
        · change Protocol.get_fg_root
              (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).toHealing.toFG =
            (rho.storeBeforeTime S w read).J
          exact hroot
        · change (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).h_max = H
          exact hmax
      have hvoteRoot : ∀ d : Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          ∀ v ∈ rho.honest,
            Protocol.get_fg_root
                (Proofs.Optimistic.voteDutyStore S rho v d).toHealing.toFG = Jn.erase := by
        intro d hdlo hdhi v hv
        exact (hvoteExact d hdlo hdhi v hv).1.trans hJnErase.symm
      have hvoteCap : ∀ d : Slot,
          S.hc.opening_slot (q - 1) + 1 ≤ d →
          d < S.hc.opening_slot ((q - 1) + 1) →
          ∀ v ∈ rho.honest,
            (Proofs.Optimistic.voteDutyStore S rho v d).h_max ≤
              (Protocol.derive_named S.E S.cfg Jn).h + 1 := by
        intro d hdlo hdhi v hv
        exact le_of_eq
          ((hvoteExact d hdlo hdhi v hv).2.trans htargetHeightSucc.symm)
      have hslotHor : Protocol.vote_time S.E (S.hc.opening_slot q - 1) ≤
          rho.horizon := by
        exact ((hvoteLeActionQ (S.hc.opening_slot q - 1) hslo hshi).trans
          hqAtEnd).trans hendHor
      have hcanonical : SGTargetConeCanonicality S rho (q - 1)
          (S.hc.opening_slot q - 1) :=
        sgTargetConeCanonicality_of_gradeFormsAt_exactFGRoot_heightCap
          S adm hcom hfb hqPredPos hready hJnRun hformsNamed hslo hshi hnextHor hslotHor
            hactionRoot hactionCap hvoteRoot hvoteCap
      have hJtarget : ∀ u ∈ rho.honest,
          Block.Preceq Jn.erase (actionSGBlockAt S rho u (q - 1)) := by
        intro u hu
        have hJraw := claimOne_namedGradeProcessedAtAction S adm hformsNamed hu
        obtain ⟨J', hJ'body, hJ'erase⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
            S rho (S.a (q - 1)) u hJraw
        have hJ'run := claimOne_runBlock_of_body_at_read S adm hu hJ'body
        have hJ'eq := claimOne_named_run_eq_of_erase adm hJ'run hJnRun
          (hJ'erase.trans rfl)
        have hJbody : Jn ∈
            (rho.storeBeforeTime S u (S.a (q - 1))).bodies := by
          simpa only [hJ'eq] using hJ'body
        have hJactive : Jn.erase ∈ PhaseGrades.filteredTree
            (actionReadAt S rho u (q - 1)) := by
          have hfiltered := mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
            S rho u (S.a (q - 1)) hJbody rfl (hactionRoot u hu)
              (Block.preceq_self Jn.erase) (hactionCap u hu)
          simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt, actionReadAt,
            NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
            NamedActionReads.confirmationReadFrom,
            NamedActionReads.preparedCache] using hfiltered
        exact preceq_actionSGBlockAt_of_namedGradeFormsAt
          S adm.toNamedAdmissibleCore hqPredPos hnextHor hformsNamed hu hJactive
      have hrq : r < q :=
        (Nat.lt_succ_self r).trans_le
          (hqActionLower.trans (Nat.sub_le q 2))
      have hopenDelay : read + S.E.Δ ≤
          Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1) := by
        rw [hsucc]
        exact ((Int.add_le_add_right hreadAction S.E.Δ).trans
          (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hrq)).trans
            (le_of_lt (Protocol.proposal_time_lt_vote_time S.E
              (S.hc.opening_slot q)))
      have hopenEnd : Protocol.vote_time S.E
          ((S.hc.opening_slot q - 1) + 1) ≤ S.a (r + 4 + gap) := by
        rw [hsucc]
        exact (le_of_lt (Protocol.opening_vote_time_lt_action S q)).trans
          hqAtEnd
      have hopenHor : Protocol.vote_time S.E
          ((S.hc.opening_slot q - 1) + 1) ≤ rho.horizon :=
        hopenEnd.trans hendHor
      have hopenCap : honestHMaxAt S rho
          (Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1)) ≤ H :=
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hopenEnd).trans hcapEnd
      have hopenExact : ∀ v ∈ rho.honest,
          Protocol.get_fg_root
              (Proofs.Optimistic.voteDutyStore S rho v
                ((S.hc.opening_slot q - 1) + 1)).toHealing.toFG =
            (rho.storeBeforeTime S w read).J ∧
          (Proofs.Optimistic.voteDutyStore S rho v
            ((S.hc.opening_slot q - 1) + 1)).h_max = H := by
        intro v hv
        obtain ⟨hroot, hmax⟩ :=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb h hv hpost hopenDelay hopenHor hopenCap
        refine ⟨?_, ?_⟩
        · change Protocol.get_fg_root
              (rho.storeBeforeTime S v
                (Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1))).toHealing.toFG =
            (rho.storeBeforeTime S w read).J
          exact hroot
        · change (rho.storeBeforeTime S v
              (Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1))).h_max = H
          exact hmax
      have hpostSlot : S.E.t_GST ≤
          Protocol.vote_time S.E (S.hc.opening_slot q - 1) := by
        have hreadDelay : read ≤ read + S.E.Δ :=
          le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
        exact hpost.trans (hreadDelay.trans
          (hvoteDelay (S.hc.opening_slot q - 1) hslo hshi))
      have hcertNamed : Certificate S rho (H - 1) Jn.root := by
        have hroot : Jn.root = (rho.storeBeforeTime S w read).J.root := by
          rw [← Proofs.NamedWire.erase_root Jn, hJnErase]
        rw [hroot]
        exact h.fixedTarget.certificate
      exact sgTargetOpeningConeRootLock_of_fixedFrontier_certifiedPrefix
        S adm hcom hfb hcanonical hJnRun hcertNamed htargetHeightLt
          hJtarget hpostSlot hopenHor (fun v hv => (hopenExact v hv).2)

#print axioms
  fixedHeightJustificationRoot_boundedOpeningConeRootLock_of_proposerRecurrence_of_faultBound

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
