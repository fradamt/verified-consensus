module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoverySelectedG2SGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3
public import DecoupledConsensusProofs.Generic.SGSafetyWindow
public import DecoupledConsensusProofs.Objects.SGTargetCompatibility

@[expose] public section

/-!
# Delayed recovery-source SG seed

The recovery proof selects its exact source after one settled gate-off
predecessor round. Relative source-round grades then have honest carriers in
that predecessor round, and the source cone compares those carriers with the
exact checkpoint.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem delayedSource_compatible_ancestor_left
    {A B C : Block V} (hAB : Block.Preceq A B)
    (hBC : Block.compatible B C = true) : Block.compatible A C = true := by
  rcases (show Block.Preceq B C ∨ Block.Preceq C B by
    simpa only [Block.compatible, Bool.or_eq_true] using hBC) with hBC | hCB
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hAB hBC)
  · exact Block.compatible_of_preceq_common hAB hCB



private theorem delayedSource_cone_mono
    {S : Setup V} {rho : Run V} {s : Slot} {A B : Block V}
    (hAB : Block.Preceq A B)
    (hcone : NamedHonestVotesCone S rho s (fun X => Block.Preceq B X)) :
    NamedHonestVotesCone S rho s (fun X => Block.Preceq A X) := by
  intro w hw hcommittee
  obtain ⟨X, hBX, hXrun, hXemit⟩ := hcone w hw hcommittee
  exact ⟨X, Block.preceq_trans hAB hBX, hXrun, hXemit⟩
private theorem delayedSource_opening_le_lastSlot
    (x R : Nat) (hR : 2 ≤ R) : x ≤ x + R - 1 := by
  omega

private theorem delayedSource_secondSlot_le_lastSlot
    (x R : Nat) (hR : 2 ≤ R) : x + 1 ≤ x + R - 1 := by
  omega

/-- One settled gate-off predecessor round makes the exact recovery source's
actual SG emissions compatible with its derived checkpoint. -/
theorem PrefixFGSelectorConeAt.sgEmissionsCompatible_sourceRound_of_relativeGateOffPredecessor_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 M : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hpred : 1 ≤ a.round)
    (hpost : S.E.t_GST ≤ S.a (a.round - 2))
    (hhor : S.a (a.round + 2) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (a.round - 2) (a.round + 2))
    (hwindowG2 : RelativeCarrierWindowAt S rho (a.round - 1) .g2)
    (hwindowG1 : RelativeCarrierWindowAt S rho (a.round - 1) .g1)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho a.round) :
    HonestSGEmissionsCompatibleAtRound S rho a.round T := by
  have hroundPos : 0 < a.round := Nat.zero_lt_of_lt hpred
  have hpredSucc : a.round - 1 + 1 = a.round := Nat.sub_add_cancel hpred
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg Cfg
  have hbefore :=
    hseed.actionPrefix_lt adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hrootT : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho w a.round).st.core.toHealing.toFG) T := by
    intro w hw
    have hread := (hseed.checkpointFiltered_at_read_beforeFirst_k6free
      adm hbelow hfirst hcap hrec ready (le_refl _) hbefore hw).2.1
    rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
    exact hread
  have hsourceQ2 : ∃ Q : Block V,
      nodeQ2 S (actionReadAt S rho a.val_index a.round) a.round = some Q := by
    cases hQ : nodeQ2 S (actionReadAt S rho a.val_index a.round) a.round with
    | none =>
        have hsource := hseed.exactFGSource
        unfold actionFGSource at hsource
        dsimp only at hsource
        have hround : S.hc.round_of
            (actionStoreAt S rho a.val_index a.round).st.core.toHealing.s =
              a.round := by
          simpa only [Protocol.Store.toHealing] using
            actionStoreAt_round S rho a.val_index a.round
        rw [hround] at hsource
        change Protocol.grade2_block_with
          (NamedProfile.gradeContract
            (actionReadAt S rho a.val_index a.round).cache)
          S.E S.hc
          (actionReadAt S rho a.val_index a.round).st.core.toHealing
          a.round = none at hQ
        simp only [actionStoreAt] at hsource
        rw [Protocol.fg_source_with.eq_def, hQ] at hsource
        cases hsource
    | some Q => exact ⟨Q, rfl⟩
  obtain ⟨Qsource, hQsource⟩ := hsourceQ2
  have hsourceCase := actionFGSource_genuineClear_or_selectedG2_named
    S rho a.val_index a.round hQsource hseed.exactFGSource
  have hcarrierCompatible : ∀ u ∈
      Internal.NamedOutageEntry.honestRoundVoters S rho (a.round - 1),
      Block.compatible (actionSGBlockAt S rho u (a.round - 1)) T = true := by
    by_cases htwo : 2 ≤ a.round
    · have hprevPos : 1 ≤ a.round - 1 := by
        exact Nat.le_sub_of_add_le (by simpa only [one_add_one_eq_two] using htwo)
      have hreadyPrev : GradeRoundReady S rho (a.round - 1) := by
        apply gradeRoundReady_of_previousAction S
        · exact Nat.zero_lt_of_lt hprevPos
        · simpa only [Nat.sub_sub] using hpost
        · exact (Assembly.a_mono S (Nat.sub_le a.round 1)).trans
            ((Assembly.a_mono S (Nat.le_add_right a.round 2)).trans hhor)
      have hcarrierCone : ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters
          S rho (a.round - 1),
          ∀ s, (s = S.hc.opening_slot a.round ∨
              s = S.hc.opening_slot a.round + 1) →
            NamedHonestVotesCone S rho s
              (fun X => Block.Preceq (actionSGBlockAt S rho u (a.round - 1)) X) := by
        intro u hu s hs
        have huHon : u ∈ rho.honest :=
          ((Proofs.NamedOutageInputs.honestRoundVoters_iff
            S rho u (a.round - 1)).mp hu).1
        have hcone := sgVotesCone_laterRounds_of_gateOffWindow
          S adm hcom hbelow hprevPos (by rw [hpredSucc])
          hpost hhor (by
            intro read hlo hhi w hw
            exact hframe read
              ((Assembly.a_mono S
                (by rw [Nat.sub_sub])).trans hlo)
              hhi w hw) hreadyPrev u huHon a.round
                (by rw [hpredSucc]) (le_refl _)
        rcases hs with rfl | rfl
        · exact hcone (S.hc.opening_slot a.round) (le_refl _)
            (by
              unfold seedRoundLastSlot
              rw [opening_slot_succ_eq S.hc a.round]
              exact delayedSource_opening_le_lastSlot _ _ S.hc.R_ge_two)
        · exact hcone (S.hc.opening_slot a.round + 1) (Nat.le_succ _)
            (by
              unfold seedRoundLastSlot
              rw [opening_slot_succ_eq S.hc a.round]
              exact delayedSource_secondSlot_le_lastSlot _ _ S.hc.R_ge_two)
      intro u hu
      rcases hseed.cone with hcone | hcone
      · exact sgTargetCompatible_of_honestVotesCone S hcom
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
          adm.toNamedAdmissibleCore.toNamedRootCollisionFree
          (hcarrierCone u hu _ (Or.inl rfl))
          (delayedSource_cone_mono hTCfg hcone)
      · exact sgTargetCompatible_of_honestVotesCone S hcom
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
          adm.toNamedAdmissibleCore.toNamedRootCollisionFree
          (hcarrierCone u hu _ (Or.inr rfl))
          (delayedSource_cone_mono hTCfg hcone)
    · have hone : a.round = 1 :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge htwo)) hpred
      intro u hu
      have huHon : u ∈ rho.honest :=
        ((Proofs.NamedOutageInputs.honestRoundVoters_iff
          S rho u (a.round - 1)).mp hu).1
      rw [hone]
      simp only [Nat.reduceSubDiff]
      rw [WeakGenesis.actionSGBlock_eq_genesis_zero S
        adm.toNamedAdmissibleCore
        (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow) huHon]
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (Protocol.preceq_genesis T)
  have hgradeCompatible : ∀ (p : Phase),
      RelativeCarrierWindowAt S rho (a.round - 1) p →
      ∀ (w : V), w ∈ rho.honest →
      ∀ B : Block V,
      storeGrade S.E S.hc
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc a.round p) w).st
        a.round p B = true → Block.compatible B T = true := by
    intro p hwindow w hw B hgrade
    have hgrade' : DecoupledConsensusModel.Protocol.gradeBool S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (a.round - 1 + 1) p) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (a.round - 1 + 1) p) w).st.core.F
        S.hc.η_SG (a.round - 1 + 1)
        (early S.E S.hc (a.round - 1 + 1) p)
        (late S.E S.hc (a.round - 1 + 1) p) B = true := by
      simpa only [storeGrade, phaseGrade, hpredSucc] using hgrade
    obtain ⟨u, hu, hBu⟩ := relativeGrade_has_roundCarrier S
      adm.toNamedAdmissibleCore hwindow
      (by simpa only [hpredSucc] using hmajority) hw hgrade'
    exact delayedSource_compatible_ancestor_left hBu (hcarrierCompatible u hu)
  have hhorAction : S.a a.round ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right a.round 2)).trans hhor
  have hpostPrev : S.E.t_GST ≤ S.a (a.round - 1) :=
    hpost.trans (Assembly.a_mono S
      (Nat.sub_le_sub_left (by decide : 1 ≤ 2) a.round))
  have hloPred : S.a (a.round - 2) ≤ S.a (a.round - 1) :=
    Assembly.a_mono S (Nat.sub_le_sub_left (by decide : 1 ≤ 2) a.round)
  have hhiPred : S.a (a.round - 1) ≤ S.a (a.round + 2) :=
    Assembly.a_mono S ((Nat.sub_le a.round 1).trans
      (Nat.le_add_right a.round 2))
  have hloAction : S.a (a.round - 2) ≤ S.a a.round :=
    Assembly.a_mono S (Nat.sub_le a.round 2)
  have hhiAction : S.a a.round ≤ S.a (a.round + 2) :=
    Assembly.a_mono S (Nat.le_add_right a.round 2)
  have hraw : ∀ w ∈ rho.honest,
      nodeRawG2 S (actionReadAt S rho w a.round) a.round := by
    intro w hw
    refine nodeRawG2_of_gateOffFrame (M := M)
      S adm hbelow hroundPos hhorAction hpostPrev
      ?_ ?_ ?_ w hw
    · intro u hu
      exact (hframe _ hloPred hhiPred u hu).2
    · intro u hu
      exact (hframe _ hloAction hhiAction u hu).2
    · intro u hu
      exact (hframe _ hloAction hhiAction u hu).1
  intro w hw _
  have hroot : Block.compatible
      (Protocol.get_fg_root
        (actionStoreAt S rho w a.round).st.core.toHealing.toFG) T = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (hrootT w hw)
  have hlive : Block.compatible
      (actionStoreAt S rho w a.round).live_confirmed T = true := by
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w a.round with
      ⟨C, hgenuine, hC⟩ | ⟨R, hRroot, hRlive⟩
    · rw [← hC]
      rcases hsourceCase with
        ⟨Csource, hgenuineSource, _, _, _, hCfgC⟩ | hsourceSelected
      · have hpostOpening : S.E.t_GST ≤ Protocol.proposal_time S.E
            (S.hc.opening_slot a.round) := ready.1.trans
          (early_g2_lt_Γ_0 S a.round).le
        have hcompatible := Protocol.sameSlot_genuine_compatible_after_gst
          S adm hseed.signerHonest hw hpostOpening
            (by rwa [opening_confirmation_time_eq_action]) hgenuineSource hgenuine
        have hsourceC : Block.compatible Csource C = true := by
          simpa only [Block.compatible, Bool.or_comm] using hcompatible
        have hTC := delayedSource_compatible_ancestor_left
          (Block.preceq_trans hTCfg hCfgC) hsourceC
        simpa only [Block.compatible, Bool.or_comm] using hTC
      · have hCfgQ : Cfg.erase = Qsource := hsourceSelected
        have hselected : nodeQ2
            S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase := by
          simpa only [hCfgQ] using hQsource
        have hQC := selectedG2_compatible_genuineOpening_of_recoveryPrefix
          S adm hcom hbelow ready hseed.signerHonest hw hselected hseed.sourceMem
            (by
              simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
                opening_confirmation_time_eq_action] using hgenuine)
            (honestPrefixFinalityCap_of_le S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hbefore.le hcap)
            hrec hseed.sourceDerivedHeight (Nat.le_refl _)
            ((hfirst.before _ hbefore).trans_lt
              (Nat.lt_succ_self (blocked + 1))) hhorAction
        have hTC := delayedSource_compatible_ancestor_left hTCfg
          (by simpa only [Block.compatible, Bool.or_comm] using hQC)
        simpa only [Block.compatible, Bool.or_comm] using hTC
    · rw [← hRlive, hRroot]
      exact hroot
  rcases actionSGBlockAt_tiers_of_rawG2 S rho w a.round (hraw w hw) with
    hwalk | ⟨Q, hQ, hsg⟩ | hsg
  · exact delayedSource_compatible_ancestor_left hwalk.2.1 hlive
  · rw [hsg]
    exact hgradeCompatible .g2 hwindowG2 w hw Q
      (selectedQ2_storeGrade_at_g2Domain S adm hQ)
  · rw [hsg]
    exact hroot

#print axioms PrefixFGSelectorConeAt.sgEmissionsCompatible_sourceRound_of_relativeGateOffPredecessor_named

/-- Caller-facing delayed-source wrapper. The recovery regime chooses the
exact source only after the gate-off predecessor has settled; this wrapper
builds the two relative carrier windows and the grade-majority fact locally. -/
theorem PrefixFGSelectorConeAt.sgEmissionsCompatible_sourceRound_of_gateOffPredecessor_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 M : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hpred : 1 ≤ a.round)
    (hpost : S.E.t_GST ≤ S.a (a.round - 2))
    (hhor : S.a (a.round + 2) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (a.round - 2) (a.round + 2)) :
    HonestSGEmissionsCompatibleAtRound S rho a.round T := by
  have hroundPos : 0 < a.round := Nat.zero_lt_of_lt hpred
  have hloPred : S.a (a.round - 2) ≤ S.a (a.round - 1) :=
    Assembly.a_mono S (Nat.sub_le_sub_left (by decide : 1 ≤ 2) a.round)
  have hhiPred : S.a (a.round - 1) ≤ S.a (a.round + 2) :=
    Assembly.a_mono S ((Nat.sub_le a.round 1).trans
      (Nat.le_add_right a.round 2))
  have hloAction : S.a (a.round - 2) ≤ S.a a.round :=
    Assembly.a_mono S (Nat.sub_le a.round 2)
  have hhiAction : S.a a.round ≤ S.a (a.round + 2) :=
    Assembly.a_mono S (Nat.le_add_right a.round 2)
  have hpostPrev : S.E.t_GST ≤ S.a (a.round - 1) := hpost.trans hloPred
  have hhorAction : S.a a.round ≤ rho.horizon := hhiAction.trans hhor
  have hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (a.round - 1))).h_max = M := by
    intro u hu
    exact (hframe _ hloPred hhiPred u hu).2
  have hfrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a a.round)).h_max = M := by
    intro u hu
    exact (hframe _ hloAction hhiAction u hu).2
  have hgate : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a a.round)).h_j + 2 ≤ M := by
    intro u hu
    exact (hframe _ hloAction hhiAction u hu).1
  have hwindowG2 : RelativeCarrierWindowAt S rho (a.round - 1) .g2 :=
    relativeCarrierWindowAt_of_gateOff S adm hbelow hroundPos hpostPrev
      hprev hfrontier hgate
      ((FrameForward.domain_le_a S a.round .g2).trans hhorAction)
  have hwindowG1 : RelativeCarrierWindowAt S rho (a.round - 1) .g1 :=
    relativeCarrierWindowAt_of_gateOff S adm hbelow hroundPos hpostPrev
      hprev hfrontier hgate
      ((FrameForward.domain_le_a S a.round .g1).trans hhorAction)
  have hmajority : Internal.NamedOutageEntry.GradeFormingMajority
      S rho a.round :=
    gradeFormingMajority_of_admissible_belowOneThird S adm hbelow hroundPos
      ((FrameForward.domain_le_a S a.round .g2).trans hhorAction) (by assumption)
  exact hseed.sgEmissionsCompatible_sourceRound_of_relativeGateOffPredecessor_named
    adm hcom hbelow hfirst hcap hrec ready hpred hpost hhor hframe
      hwindowG2 hwindowG1 hmajority

#print axioms PrefixFGSelectorConeAt.sgEmissionsCompatible_sourceRound_of_gateOffPredecessor_named




/-- Internal  delivery and participation inputs for prepared action reads
after the source's SG expiry window. -/
structure RecoverySGReadSidePackage
    (S : Setup V) (rho : Run V) (source last : Round) (T : Block V) where
  cap : Time
  delivery : NamedHealthyPrefixDelivery S rho cap
  capHorizon : cap ≤ rho.horizon
  awake : ∀ r, source + S.hc.η_SG ≤ r → r ≤ last + 1 →
    AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r
  carriers : ∀ r, source + S.hc.η_SG ≤ r → r ≤ last + 1 →
    ∀ k, source ≤ k → k < r → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) T
  roots : ∀ r, source + S.hc.η_SG ≤ r → r ≤ last + 1 →
    ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho w r).st.core.toHealing.toFG) T
  domains : ∀ r, source + S.hc.η_SG ≤ r → r ≤ last + 1 →
    ∀ p, DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ cap
  actions : ∀ r, source + S.hc.η_SG ≤ r → r ≤ last + 1 →
    S.a r ≤ rho.horizon

/-- Producer 1 supplies every read-side field in the exact range used by the
source-restricted invariant. -/
theorem RecoverySGReadSidePackage.previousSGReadSideAt
    {S : Setup V} {rho : Run V} {source last : Round} {T : Block V}
    (hpkg : RecoverySGReadSidePackage S rho source last T)
    (adm : Admissible S rho) (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hsource : source + S.hc.η_SG ≤ r)
    (hlast : r ≤ last + 1) :
    ∀ w ∈ rho.honest, PreviousSGReadSideAt S rho w r T := by
  have hr : 0 < r := by
    exact (Nat.add_pos_right source
      (Nat.zero_lt_of_lt S.hc.η_SG_ge_one)).trans_le hsource
  have hspan : source ≤ r - S.hc.η_SG :=
    Nat.le_sub_of_add_le hsource
  exact previousSGReadSideAt_of_delivery S adm hpkg.delivery hpkg.capHorizon
    (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
    hr hspan (hpkg.awake r hsource hlast)
    (hpkg.carriers r hsource hlast) (hpkg.roots r hsource hlast)
    (hpkg.domains r hsource hlast) (hpkg.actions r hsource hlast)

private theorem delayedSource_honestRoundVoter_emits_exactAction
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {u : V} {k : Round}
    (hu : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho k) :
    u ∈ rho.honest ∧
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) := by
  obtain ⟨huHon, a, _, haround, hemit⟩ :=
    (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mp hu
  have hawake : (S.node u).awake k = true := by
    simpa only [haround] using Proofs.Optimistic.emits_attest_awake S hemit
  obtain ⟨i, hi, _⟩ := hemit
  have hhor : S.a k ≤ rho.horizon := by
    have h := core.toNamedScheduleWellFormed.in_horizon
      (Event.tick u (S.a k)) (List.mem_of_getElem? hi)
    simpa only [NamedEvent.time] using h.2
  exact ⟨huHon, honest_emits_exact_actionAttestationAt_of_awake
    S core.toNamedScheduleWellFormed huHon k hawake hhor⟩





/-- A prepared vote anchor in the first expiry-window rounds is compatible
with the protected target because its relative G1 lies below an emitted
honest carrier from the immediately preceding round. -/
theorem voterAnchorAt_compatible_of_previousRelativeCarrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {d : Slot} (hround : S.hc.round_of d = q + 1)
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hwindow : RelativeCarrierWindowAt S rho q .g1)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho (q + 1))
    {T : Block V}
    (hprev : HonestSGEmissionsCompatibleAtRound S rho q T)
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) T) :
    Block.compatible (voterAnchorAt S rho w d) T = true := by
  rcases voterAnchorAt_cases S rho w d with hfg | hactive
  · rw [hfg]
    simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hroot
  · obtain ⟨root, A, hframe, hactive, hanchor⟩ := hactive
    rw [hanchor]
    have hslo : S.hc.opening_slot (q + 1) ≤ d := by
      rw [← hround]
      exact Nat.div_mul_le_self d S.hc.R
    have hshi : d < S.hc.opening_slot ((q + 1) + 1) := by
      rw [← hround]
      apply (Nat.div_lt_iff_lt_mul
        (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      exact Nat.lt_succ_self (d / S.hc.R)
    have hnext : Protocol.vote_time S.E d ≤
        DecoupledConsensusModel.Protocol.opening S.E S.hc ((q + 1) + 1) := by
      have hvoteNext : Protocol.vote_time S.E d <
          Protocol.proposal_time S.E (d + 1) := by
        apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ S.E d)
        rw [← Proofs.Optimistic.vote_time_add_delta]
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos
      exact hvoteNext.le.trans (by
        simpa only [DecoupledConsensusModel.Protocol.opening] using
          proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
    have hframe' : (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing
        (q + 1)).g1 = some (some root) := by
      have hslot :
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.s = d :=
        Proofs.Optimistic.voteDutyRead_slot S rho w d
      simpa only [hslot, hround] using hframe
    obtain ⟨_, hAGrade⟩ := fixedRoot_activeVoterAnchor_g1_data
      S adm (Nat.succ_pos q) hslo hround hnext hvoteHor hw hframe' hactive
    have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q + 1) .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q + 1) .g1) w).st.core.F
        S.hc.η_SG (q + 1) (early S.E S.hc (q + 1) .g1)
        (late S.E S.hc (q + 1) .g1) A = true := by
      simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
        PhaseGrades.readAt] using hAGrade
    obtain ⟨u, hu, hAu⟩ := relativeGrade_has_roundCarrier
      S adm.toNamedAdmissibleCore hwindow hmajority hw hgrade
    obtain ⟨huHon, hemit⟩ := delayedSource_honestRoundVoter_emits_exactAction
      S adm.toNamedAdmissibleCore hu
    exact delayedSource_compatible_ancestor_left hAu (hprev u huHon hemit)

#print axioms voterAnchorAt_compatible_of_previousRelativeCarrier

/-- K6-free named Goldfish canonicality step for the delayed recovery source. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_beforeFirst_k6free
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread : S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hbefore : strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) T = true) :
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X) := by
  obtain ⟨K, _, hKT, hKh, _, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT' : K.erase = T := hKT.trans hseed.checkpointDerived.symm
  have hKheight :
      (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKh.trans hseed.sourceDerivedHeight
  have hreads := fun w hw => hseed.checkpointFiltered_at_read_beforeFirst_k6free
    adm hbelow hfirst hcap hrec ready hread hbefore (w := w) hw
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq T (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    have hmax : (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max = blocked + 1 := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
        (hreads w hw).1
    have hroot : Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) T := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
        (hreads w hw).2.1
    have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
      have hc := hcom s
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
    have huCommittee : u ∈ S.E.committee s := (Finset.mem_inter.mp hu).1
    have huHonest : u ∈ rho.honest := (Finset.mem_inter.mp hu).2
    obtain ⟨X, hTX, hXrun, hXemit⟩ := hvotes u huHonest huCommittee
    have hXhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
      ⟨u, huHonest, huCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hrootDuty : Block.Preceq
        (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) T := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hroot
    have hprocessed := honestHead_voterProcessed_at_nextDuty_of_postHealingCone
      S adm hpost hhor hvotes hXhead hw hrootDuty
    obtain ⟨K', hK'X, hK'erase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift X hTX
    have hK'run : RunBlock S rho K' :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
    have hK'eq : K' = K := by
      apply adm.toNamedRootCollisionFree.root_injective
        K' K hK'run hKrun K' K
        (Or.inl (Proofs.NamedAncestry.named_self K'))
        (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root K', hK'erase, ← hKT', Proofs.NamedWire.erase_root]
    have hKXheight :
        (Protocol.derive_named S.E S.cfg K).h ≤
          (Protocol.derive_named S.E S.cfg X).h := by
      rw [← hK'eq]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hK'X
    have hXmem : X.erase ∈
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.T := by
      have hmem := (Finset.mem_filter.mp hprocessed).1
      simpa only [Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hmem
    have hstored := WeakJoint.storedHeight_of_runBlock_mem_voteDutyRead
      S adm hw hXrun hXmem
    have hband :
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.σ X.erase).h := by
      rw [hKheight] at hKXheight
      rw [hstored, hmax]
      exact (Nat.sub_le (blocked + 1) 1).trans hKXheight
    have hpath := WeakJoint.namedCandidatePath_of_processedBandDescendant
      S adm hw hTX hprocessed hband hroot
    apply goldfishCone_step' S adm hcom hs hpost hhor hvotes hw
    exact { rootSide := Or.inl ⟨hroot, hpath⟩, anchor := hanchors w hw }
  refine ⟨hheads, ?_⟩
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    named_voter_head_emits S adm hw (Nat.succ_pos s) hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_beforeFirst_k6free

/-- A round ceiling protects both every honest reader head and every honest
committee vote throughout its round. -/
private theorem delayedSource_roundCeiling_heads_and_votesThrough
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C) {d : Slot}
    (hdlo : S.hc.opening_slot q ≤ d)
    (hdhi : d ≤ seedRoundLastSlot S q) :
    (∀ w ∈ rho.honest, Block.Preceq C.erase (voterHeadAt S rho w d)) ∧
      NamedHonestVotesCone S rho d (fun X => Block.Preceq C.erase X) := by
  have hdpos : 0 < d := by
    exact (Nat.mul_pos h.roundPositive
      (Nat.zero_lt_of_lt S.hc.R_ge_two)).trans_le hdlo
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)
  have hprevLo : S.hc.opening_slot q - 1 ≤ d - 1 :=
    Nat.sub_le_sub_right hdlo 1
  have hprevHi : d - 1 ≤ seedRoundLastSlot S q - 1 :=
    Nat.sub_le_sub_right hdhi 1
  have hprevCone : NamedHonestVotesCone S rho (d - 1)
      (fun X => Block.Preceq C.erase X) := by
    by_cases heq : d = S.hc.opening_slot q
    · subst d
      exact h.lastVotes
    · have hlt : S.hc.opening_slot q < d := lt_of_le_of_ne hdlo (Ne.symm heq)
      exact roundCeiling_votesThrough S adm hcom h (d - 1)
        (Nat.le_pred_of_lt hlt) (hprevHi.trans (Nat.sub_le _ _))
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E (d - 1) :=
    h.postPreviousVote.trans (vote_time_mono_slots S.E hprevLo)
  have hconfHor : Protocol.confirmation_time S.E (d - 1) ≤ rho.horizon := by
    have hmono : Protocol.confirmation_time S.E (d - 1) ≤
        Protocol.confirmation_time S.E (seedRoundLastSlot S q - 1) := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact Proofs.Optimistic.support_cutoff_mono S.E
        (Nat.add_le_add_right hprevHi 1)
    exact hmono.trans h.roundConfirmationInHorizon
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq C.erase (voterHeadAt S rho w d) := by
    intro w hw
    have hpredPos : 0 < d - 1 := by
      have hopenTwo : 2 ≤ S.hc.opening_slot q := by
        exact S.hc.R_ge_two.trans
          (Nat.le_mul_of_pos_left S.hc.R h.roundPositive)
      exact Nat.sub_pos_of_lt
        (Nat.lt_of_succ_le (hopenTwo.trans hdlo))
    have hhead := goldfishCone_step S adm hcom
      hpredPos hpost hconfHor hprevCone hw
        (roundCeiling_voteInputs S h hdlo hdhi hw)
    simpa only [hpred] using hhead
  exact ⟨hheads, roundCeiling_votesThrough S adm hcom h d hdlo hdhi⟩
/-- Compatibility-only form of the pre-expiry relative-G2 successor. -/
theorem sgEmissionsCompatible_succ_of_relativeGateOff_compatible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} (hr : 0 < r) {T : Block V}
    (hwindow : RelativeCarrierWindowAt S rho (r - 1) .g2)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho r)
    (hraw : ∀ w ∈ rho.honest,
      PhaseGrades.nodeRawG2 S (actionReadAt S rho w r) r)
    (hcarriers : ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u (r - 1))) (S.a (r - 1)) →
      Block.compatible (actionSGBlockAt S rho u (r - 1)) T = true)
    (hgf : NamedHonestVotesCone S rho (S.hc.opening_slot r)
      (fun X => Block.Preceq T X))
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r))
    (hhor : S.a r ≤ rho.horizon)
    (hroots : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho w r).st.core.toHealing.toFG) T) :
    HonestSGEmissionsCompatibleAtRound S rho r T := by
  have hopen : 0 < S.hc.opening_slot r :=
    Nat.mul_pos hr (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hconfHor :
      Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤ rho.horizon := by
    rwa [opening_confirmation_time_eq_action]
  have hheads : ∀ x ∈ rho.honest,
      x ∈ S.E.committee (S.hc.opening_slot r) →
      Block.Preceq T (voterHeadAt S rho x (S.hc.opening_slot r)) := by
    intro x hx hxc
    obtain ⟨X, hTX, hXrun, hXemit⟩ := hgf x hx hxc
    obtain ⟨H, hHerase, hHrun, hHemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits S adm.toNamedAdmissibleCore hx
        hopen hxc ((vote_time_le_confirmation_time S.E _).trans hconfHor)
    have heq := Proofs.Optimistic.emits_gfVote_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hXemit hHemit rfl
    have hroot : X.root = H.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg GoldfishVote.head heq
    have hXH : X = H :=
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
        X H hXrun hHrun X H (Or.inl (Proofs.NamedAncestry.named_self X))
          (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
    rw [← hHerase, ← hXH]
    exact hTX
  intro w hw _
  have hlive : Block.compatible
      (actionStoreAt S rho w r).live_confirmed T = true := by
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w r with
      ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
    · rw [← hClive]
      simpa only [Block.compatible, Bool.or_comm] using
        (WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
          S adm.toNamedAdmissibleCore hcom hw hopen hpost hconfHor hC hheads)
    · rw [← hRlive, hRroot]
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (hroots w hw)
  rcases actionSGBlockAt_tiers_of_rawG2 S rho w r (hraw w hw) with
    hwalk | ⟨Q, hQ, hsg⟩ | hsg
  · exact delayedSource_compatible_ancestor_left hwalk.2.1 hlive
  · rw [hsg]
    have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r - 1 + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r - 1 + 1) .g2) w).st.core.F
        S.hc.η_SG (r - 1 + 1) (early S.E S.hc (r - 1 + 1) .g2)
        (late S.E S.hc (r - 1 + 1) .g2) Q = true := by
      have hpred' : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
      simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade, hpred'] using
        selectedQ2_storeGrade_at_g2Domain S adm hQ
    have hmajority' : Internal.NamedOutageEntry.GradeFormingMajority
        S rho (r - 1 + 1) := by
      simpa only [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)] using hmajority
    obtain ⟨u, hu, hQu⟩ := relativeGrade_has_roundCarrier
      S adm.toNamedAdmissibleCore hwindow hmajority' hw hgrade
    obtain ⟨huHon, hemit⟩ := delayedSource_honestRoundVoter_emits_exactAction
      S adm.toNamedAdmissibleCore hu
    exact delayedSource_compatible_ancestor_left hQu (hcarriers u huHon hemit)
  · rw [hsg]
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (hroots w hw)
private theorem delayedSource_lastSlot_nat (x b : Nat) (hb : 2 ≤ b) :
    (x ≤ x + b - 1 ∧ x + b - 1 < x + b) ∧ 0 < x + b - 1 := by
  omega

private theorem delayedSource_le_succ_of_sub_one_le (x n : Nat)
    (h : x - 1 ≤ n) : x ≤ n + 1 := by
  omega

private theorem delayedSource_round_of_between_openings
    (hc : Protocol.HealConfig) {r d : Nat}
    (hlo : hc.opening_slot r ≤ d) (hhi : d < hc.opening_slot (r + 1)) :
    hc.round_of d = r := by
  rcases eq_or_lt_of_le hlo with h | h
  · rw [← h]
    exact round_of_opening_slot_eq_schedule hc r
  · exact round_of_eq_of_opening_succ_le_of_lt_next_opening hc h hhi

private theorem delayedSource_action_le_next_opening_vote
    (S : Setup V) (r : Round) :
    S.a r ≤ Protocol.vote_time S.E (S.hc.opening_slot (r + 1)) := by
  rw [← Protocol.Γ_1_eq_vote_time]
  exact (a_le_Γ_neg1_succ S.hc S.E.Δ_pos r).trans
    ((le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans
      (le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos (r + 1))))

/-- The delayed source's selected relative G2 is below an honest predecessor
carrier. The gate-off round ceiling puts that carrier below every honest
source-round head and vote. -/
theorem PrefixFGSelectorConeAt.selectedG2ActiveRead_heads_and_cone_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 M : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T Q : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (_hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (_hcap : HonestPrefixFinalityCap S rho first hF0)
    (_hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hpred : 1 ≤ a.round)
    (hpost : S.E.t_GST ≤ S.a (a.round - 2))
    (hhor : S.a (a.round + 2) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (a.round - 2) (a.round + 2))
    (hwindow : RelativeCarrierWindowAt S rho (a.round - 1) .g2)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho a.round)
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Q)
    (hTQ : Block.Preceq T Q)
    {d : Slot} (hround : S.hc.round_of d = a.round) :
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w d)) ∧
      NamedHonestVotesCone S rho d (fun X => Block.Preceq T X) := by
  have hroundPos : 0 < a.round := Nat.zero_lt_of_lt hpred
  have hpredSucc : a.round - 1 + 1 = a.round := Nat.sub_add_cancel hpred
  have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (a.round - 1 + 1) .g2)
        a.val_index).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (a.round - 1 + 1) .g2)
        a.val_index).st.core.F
      S.hc.η_SG (a.round - 1 + 1)
      (early S.E S.hc (a.round - 1 + 1) .g2)
      (late S.E S.hc (a.round - 1 + 1) .g2) Q = true := by
    simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade, hpredSucc] using
      selectedQ2_storeGrade_at_g2Domain S adm hselected
  have hmajority' : Internal.NamedOutageEntry.GradeFormingMajority
      S rho (a.round - 1 + 1) := by
    simpa only [hpredSucc] using hmajority
  obtain ⟨u, hu, hQu⟩ := relativeGrade_has_roundCarrier
    S adm.toNamedAdmissibleCore hwindow hmajority' hseed.signerHonest hgrade
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff
      S rho u (a.round - 1)).mp hu).1
  have hTcarrier : Block.Preceq T
      (actionSGBlockAt S rho u (a.round - 1)) :=
    Block.preceq_trans hTQ hQu
  have hdlo : S.hc.opening_slot a.round ≤ d := by
    rw [← hround]
    exact Nat.div_mul_le_self d S.hc.R
  have hdhi : d ≤ seedRoundLastSlot S a.round := by
    unfold seedRoundLastSlot
    have hlt : d < S.hc.opening_slot (a.round + 1) := by
      rw [← hround]
      apply (Nat.div_lt_iff_lt_mul
        (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      exact Nat.lt_succ_self (d / S.hc.R)
    exact Nat.le_sub_one_of_lt hlt
  by_cases htwo : 2 ≤ a.round
  · have hprevPos : 1 ≤ a.round - 1 := by
      exact Nat.le_sub_of_add_le (by simpa only [one_add_one_eq_two] using htwo)
    have hreadyPrev : GradeRoundReady S rho (a.round - 1) := by
      apply gradeRoundReady_of_previousAction S
      · exact Nat.zero_lt_of_lt hprevPos
      · simpa only [Nat.sub_sub] using hpost
      · exact (Assembly.a_mono S (Nat.sub_le a.round 1)).trans
          ((Assembly.a_mono S (Nat.le_add_right a.round 2)).trans hhor)
    have hhorPrevSucc : S.a (a.round - 1 + 1) ≤ rho.horizon :=
      (Assembly.a_mono S (by
        rw [hpredSucc]
        exact Nat.le_add_right a.round 2)).trans hhor
    have hframePrevSucc : GateOffFrameAt S rho M
        (a.round - 1 - 1) (a.round - 1 + 1) := by
      intro read hlo hhi w hw
      exact hframe read (by simpa only [Nat.sub_sub] using hlo)
        (hhi.trans (Assembly.a_mono S (by
          rw [hpredSucc]
          exact Nat.le_add_right a.round 2))) w hw
    have hdis := seedRoundDischarge_of_canonicity
      S adm hcom hbelow hprevPos hpost hhorPrevSucc hframePrevSucc hreadyPrev
    have hhorPrevTwo : S.a (a.round - 1 + 2) ≤ rho.horizon :=
      (Assembly.a_mono S
        (Nat.add_le_add_right (Nat.sub_le a.round 1) 2)).trans hhor
    have hframePrevTwo : GateOffFrameAt S rho M
        (a.round - 1 - 1) (a.round - 1 + 2) := by
        intro read hlo hhi w hw
        exact hframe read (by simpa only [Nat.sub_sub] using hlo)
          (hhi.trans (Assembly.a_mono S
            (Nat.add_le_add_right (Nat.sub_le a.round 1) 2))) w hw
    obtain ⟨_, C, hC⟩ := seedBoundaryAdoption_of_discharge
      S adm hcom hbelow hprevPos hpost hhorPrevTwo hframePrevTwo hdis
    have hprotected := delayedSource_roundCeiling_heads_and_votesThrough
      S adm hcom hC (by simpa only [hpredSucc] using hdlo)
        (by simpa only [hpredSucc] using hdhi)
    refine ⟨?_, ?_⟩
    · intro w hw
      exact Block.preceq_trans hTcarrier
        (Block.preceq_trans (by
          simpa only [hpredSucc] using hC.previousCarriers u huHon)
          (hprotected.1 w hw))
    · exact delayedSource_cone_mono
        (Block.preceq_trans hTcarrier (by
          simpa only [hpredSucc] using hC.previousCarriers u huHon))
        hprotected.2
  · have hone : a.round = 1 :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge htwo)) hpred
    have hcarrierGenesis :
        actionSGBlockAt S rho u (a.round - 1) = Block.genesis := by
      rw [hone]
      simp only [Nat.reduceSubDiff]
      exact WeakGenesis.actionSGBlock_eq_genesis_zero S
        adm.toNamedAdmissibleCore
        (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow) huHon
    have hTgenesis : Block.Preceq T Block.genesis := by
      simpa only [hcarrierGenesis] using hTcarrier
    have hTany : ∀ X : Block V, Block.Preceq T X := by
      intro X
      exact Block.preceq_trans hTgenesis (Protocol.preceq_genesis X)
    refine ⟨?_, ?_⟩
    · intro w hw
      exact hTany _
    · have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon := by
        have hdnext : d ≤ S.hc.opening_slot (a.round + 1) :=
          hdhi.trans (by unfold seedRoundLastSlot; exact Nat.sub_le _ _)
        have hconf : Protocol.confirmation_time S.E d ≤
            Protocol.confirmation_time S.E (S.hc.opening_slot (a.round + 1)) := by
          rw [Protocol.confirmation_time_eq_support_cutoff_succ,
            Protocol.confirmation_time_eq_support_cutoff_succ]
          exact Proofs.Optimistic.support_cutoff_mono S.E
            (Nat.add_le_add_right hdnext 1)
        have hopenConf : Protocol.confirmation_time S.E
            (S.hc.opening_slot (a.round + 1)) = S.a (a.round + 1) := by
          rw [opening_confirmation_time_eq_action]
        exact (vote_time_le_confirmation_time S.E d).trans
          (hconf.trans (hopenConf.le.trans
            ((Assembly.a_mono S (Nat.le_succ (a.round + 1))).trans hhor)))
      intro w hw hcommittee
      obtain ⟨X, hXe, hXrun, hXemit⟩ :=
        named_voter_head_emits S adm hw
          ((Nat.mul_pos hroundPos
            (Nat.zero_lt_of_lt S.hc.R_ge_two)).trans_le hdlo)
          hcommittee hvoteHor
      exact ⟨X, hTany X.erase, hXrun, hXemit⟩

#print axioms PrefixFGSelectorConeAt.selectedG2ActiveRead_heads_and_cone_named






/-- A delayed named recovery source protects every vote head in the current
round and carries the source-restricted SG invariant through that round. -/
theorem PrefixFGSelectorConeAt.checkpointProtection_and_SGHistory_beforeFirst_of_G2_cover_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 M : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T Q : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Q)
    (hTQ : Block.Preceq T Q)
    (hpred : 1 ≤ a.round)
    (hpost : S.E.t_GST ≤ S.a (a.round - 2))
    {c : Round} (hc : a.round ≤ c)
    (hhor : S.a (c + 2) ≤ rho.horizon)
    (hbefore : strictEventIndex rho (S.a (c + 2)) < first)
    (hframe : GateOffFrameAt S rho M (a.round - 2) (c + 2))
    (hpkg : RecoverySGReadSidePackage S rho a.round c T) :
    (∀ d, S.hc.opening_slot c ≤ d → d < S.hc.opening_slot (c + 1) →
      Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon →
      strictEventIndex rho (Protocol.vote_time S.E d) < first →
      (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w d)) ∧
        NamedHonestVotesCone S rho d (fun X => Block.Preceq T X)) ∧
    RecoverySGWindowInvariantFrom S rho a.round c T := by
  have hR := S.hc.R_ge_two
  have sourceWindow (p : Phase) :
      RelativeCarrierWindowAt S rho (a.round - 1) p := by
    have hroundPos : 0 < a.round := Nat.zero_lt_of_lt hpred
    have hloPred : S.a (a.round - 2) ≤ S.a (a.round - 1) :=
      Assembly.a_mono S (Nat.sub_le_sub_left (by decide : 1 ≤ 2) a.round)
    have hhiPred : S.a (a.round - 1) ≤ S.a (c + 2) :=
      Assembly.a_mono S ((Nat.sub_le a.round 1).trans
        (hc.trans (Nat.le_add_right c 2)))
    have hloAction : S.a (a.round - 2) ≤ S.a a.round :=
      Assembly.a_mono S (Nat.sub_le a.round 2)
    have hhiAction : S.a a.round ≤ S.a (c + 2) :=
      Assembly.a_mono S (hc.trans (Nat.le_add_right c 2))
    apply relativeCarrierWindowAt_of_gateOff S adm hbelow hroundPos
      (hpost.trans hloPred)
    · intro u hu
      exact (hframe _ hloPred hhiPred u hu).2
    · intro u hu
      exact (hframe _ hloAction hhiAction u hu).2
    · intro u hu
      exact (hframe _ hloAction hhiAction u hu).1
    · exact (FrameForward.domain_le_a S a.round p).trans
        (hhiAction.trans hhor)
  have sourceMajority : Internal.NamedOutageEntry.GradeFormingMajority
      S rho a.round :=
    gradeFormingMajority_of_admissible_belowOneThird S adm hbelow
      (Nat.zero_lt_of_lt hpred)
      ((FrameForward.domain_le_a S a.round .g2).trans
        ((Assembly.a_mono S (hc.trans (Nat.le_add_right c 2))).trans hhor))
      (hpost.trans (Assembly.a_mono S
        (Nat.sub_le_sub_left (by decide : 1 ≤ 2) a.round)))
  have hsourceVotes : ∀ d,
      S.hc.opening_slot a.round ≤ d →
      d < S.hc.opening_slot (a.round + 1) →
      Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon →
      strictEventIndex rho (Protocol.vote_time S.E d) < first →
      (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w d)) ∧
        NamedHonestVotesCone S rho d (fun X => Block.Preceq T X) := by
    intro d hdlo hdhi _ _
    apply hseed.selectedG2ActiveRead_heads_and_cone_named
      adm hcom hbelow hfirst hcap hrec ready hpred hpost
      ((Assembly.a_mono S ((Nat.add_le_add_right hc 2))).trans hhor)
      (by
        intro read hlo hhi w hw
        exact hframe read hlo
          (hhi.trans (Assembly.a_mono S (Nat.add_le_add_right hc 2))) w hw)
      (sourceWindow .g2) sourceMajority hselected hTQ
    exact delayedSource_round_of_between_openings S.hc hdlo hdhi
  have hsourceSG : HonestSGEmissionsCompatibleAtRound S rho a.round T := by
    apply hseed.sgEmissionsCompatible_sourceRound_of_gateOffPredecessor_named
      adm hcom hbelow hfirst hcap hrec ready hpred hpost
      ((Assembly.a_mono S (Nat.add_le_add_right hc 2)).trans hhor)
    intro read hlo hhi w hw
    exact hframe read hlo
      (hhi.trans (Assembly.a_mono S (Nat.add_le_add_right hc 2))) w hw
  induction c, hc using Nat.le_induction with
  | base =>
      refine ⟨hsourceVotes, ?_⟩
      constructor
      · intro k hklo hkhi
        have hk : k = a.round := Nat.le_antisymm hkhi hklo
        simpa only [hk] using hsourceSG
      · intro r hrlo hrhi
        exact hpkg.previousSGReadSideAt adm hbelow hrlo hrhi
  | succ r hr ih =>
      have hrEnd : r + 2 ≤ r + 1 + 2 := by omega
      have hnextEnd : r + 1 ≤ r + 1 + 2 := Nat.le_add_right _ 2
      have hhorR : S.a (r + 2) ≤ rho.horizon :=
        (Assembly.a_mono S hrEnd).trans hhor
      have hbeforeR : strictEventIndex rho (S.a (r + 2)) < first :=
        (strictEventIndex_mono rho (Assembly.a_mono S hrEnd)).trans_lt
          hbefore
      have hframeR : GateOffFrameAt S rho M (a.round - 2) (r + 2) := by
        intro read hlo hhi w hw
        exact hframe read hlo
          (hhi.trans (Assembly.a_mono S hrEnd)) w hw
      let hpkgR : RecoverySGReadSidePackage S rho a.round r T :=
        { cap := hpkg.cap
          delivery := hpkg.delivery
          capHorizon := hpkg.capHorizon
          awake := fun q hlo hhi => hpkg.awake q hlo
            (hhi.trans (Nat.le_succ (r + 1)))
          carriers := fun q hlo hhi => hpkg.carriers q hlo
            (hhi.trans (Nat.le_succ (r + 1)))
          roots := fun q hlo hhi => hpkg.roots q hlo
            (hhi.trans (Nat.le_succ (r + 1)))
          domains := fun q hlo hhi => hpkg.domains q hlo
            (hhi.trans (Nat.le_succ (r + 1)))
          actions := fun q hlo hhi => hpkg.actions q hlo
            (hhi.trans (Nat.le_succ (r + 1))) }
      have ih' := ih hhorR hbeforeR hframeR hpkgR
      have hlastBounds : S.hc.opening_slot r ≤
          S.hc.opening_slot (r + 1) - 1 ∧
          S.hc.opening_slot (r + 1) - 1 < S.hc.opening_slot (r + 1) := by
        rw [opening_slot_succ_eq S.hc r]
        exact (delayedSource_lastSlot_nat
          (S.hc.opening_slot r) S.hc.R hR).1
      have hlastPos : 0 < S.hc.opening_slot (r + 1) - 1 := by
        rw [opening_slot_succ_eq S.hc r]
        exact (delayedSource_lastSlot_nat
          (S.hc.opening_slot r) S.hc.R hR).2
      have hprevSG : HonestSGEmissionsCompatibleAtRound S rho r T :=
        ih'.2.1 r hr (Nat.le_refl _)
      have hnextWindow (p : Phase) : RelativeCarrierWindowAt S rho r p := by
        have hrPos : 0 < r + 1 := Nat.succ_pos r
        have hloPrev : S.a (a.round - 2) ≤ S.a r :=
          Assembly.a_mono S ((Nat.sub_le a.round 2).trans hr)
        have hhiPrev : S.a r ≤ S.a (r + 1 + 2) :=
          Assembly.a_mono S (Nat.le_add_right r 3)
        have hloNext : S.a (a.round - 2) ≤ S.a (r + 1) :=
          Assembly.a_mono S ((Nat.sub_le a.round 2).trans
            (hr.trans (Nat.le_succ r)))
        have hhiPrev : S.a r ≤ S.a (r + 1 + 2) :=
          Assembly.a_mono S (Nat.le_add_right r 3)
        have hhiNext : S.a (r + 1) ≤ S.a (r + 1 + 2) :=
          Assembly.a_mono S hnextEnd
        apply relativeCarrierWindowAt_of_gateOff S adm hbelow hrPos
          (hpost.trans hloPrev)
        · intro u hu
          exact (hframe _ hloPrev hhiPrev u hu).2
        · intro u hu
          exact (hframe _ hloNext hhiNext u hu).2
        · intro u hu
          exact (hframe _ hloNext hhiNext u hu).1
        · exact (FrameForward.domain_le_a S (r + 1) p).trans
            (hhiNext.trans hhor)
      have hnextMajority : Internal.NamedOutageEntry.GradeFormingMajority
          S rho (r + 1) :=
        gradeFormingMajority_of_admissible_belowOneThird S adm hbelow
          (Nat.succ_pos r)
          ((FrameForward.domain_le_a S (r + 1) .g2).trans
            ((Assembly.a_mono S hnextEnd).trans hhor))
          (by simpa only [Nat.add_sub_cancel] using
            hpost.trans (Assembly.a_mono S
              ((Nat.sub_le a.round 2).trans hr)))
      have hnextRaw : ∀ w ∈ rho.honest,
          PhaseGrades.nodeRawG2 S (actionReadAt S rho w (r + 1)) (r + 1) := by
        intro w hw
        have hloPrev : S.a (a.round - 2) ≤ S.a r :=
          Assembly.a_mono S ((Nat.sub_le a.round 2).trans hr)
        have hloNext : S.a (a.round - 2) ≤ S.a (r + 1) :=
          Assembly.a_mono S ((Nat.sub_le a.round 2).trans
            (hr.trans (Nat.le_succ r)))
        have hhiPrev : S.a r ≤ S.a (r + 1 + 2) :=
          Assembly.a_mono S (Nat.le_add_right r 3)
        have hhiNext : S.a (r + 1) ≤ S.a (r + 1 + 2) :=
          Assembly.a_mono S hnextEnd
        refine nodeRawG2_of_gateOffFrame (M := M) S adm hbelow
          (Nat.succ_pos r) (hhiNext.trans hhor) (hpost.trans hloPrev)
          ?_ ?_ ?_ w hw
        · intro u hu
          exact (hframe _ hloPrev hhiPrev u hu).2
        · intro u hu
          exact (hframe _ hloNext hhiNext u hu).2
        · intro u hu
          exact (hframe _ hloNext hhiNext u hu).1
      have hnextVotes : ∀ d, S.hc.opening_slot (r + 1) ≤ d →
          d < S.hc.opening_slot (r + 1 + 1) →
          Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon →
          strictEventIndex rho (Protocol.vote_time S.E d) < first →
          (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w d)) ∧
            NamedHonestVotesCone S rho d (fun X => Block.Preceq T X) := by
        intro d hdlo hdhi hdhor hdbefore
        have hlastLe : S.hc.opening_slot (r + 1) - 1 ≤ d :=
          hlastBounds.2.le.trans hdlo
        have hlastRead := vote_time_mono_slots S.E hlastLe
        have hlastCone := ih'.1 _ hlastBounds.1 hlastBounds.2
          ((add_le_add hlastRead (le_refl S.E.Δ)).trans hdhor)
          ((strictEventIndex_mono rho hlastRead).trans_lt hdbefore)
        have hfold : ∀ n, S.hc.opening_slot (r + 1) - 1 ≤ n → n ≤ d →
            (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w n)) ∧
              NamedHonestVotesCone S rho n (fun X => Block.Preceq T X) := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => intro _; exact hlastCone
          | succ n hn ihSlot =>
              intro hntop
              have hprev := ihSlot (Nat.le_of_succ_le hntop)
              have hnlo : S.hc.opening_slot (r + 1) ≤ n + 1 :=
                delayedSource_le_succ_of_sub_one_le _ _ hn
              have hnhi : n + 1 < S.hc.opening_slot (r + 1 + 1) :=
                hntop.trans_lt hdhi
              have hroundN := delayedSource_round_of_between_openings
                S.hc hnlo hnhi
              have hnRead := vote_time_mono_slots S.E hntop
              have hnHor : Protocol.confirmation_time S.E n ≤ rho.horizon := by
                rw [← vote_time_succ_add_delta_eq_confirmation_time S.E n]
                exact (add_le_add hnRead (le_refl S.E.Δ)).trans hdhor
              have hnPost : S.E.t_GST ≤ Protocol.vote_time S.E n := by
                have hsourceOpen : S.hc.opening_slot a.round ≤
                    S.hc.opening_slot r := Nat.mul_le_mul_right S.hc.R hr
                have hopenPost : S.E.t_GST ≤
                    Protocol.vote_time S.E (S.hc.opening_slot a.round) := by
                  rw [← Protocol.Γ_1_eq_vote_time]
                  exact ready.1.trans
                    ((early_g2_lt_Γ_0 S a.round).le.trans
                      ((Γ_0_lt_Γ_1 S.hc S.E.Δ_pos a.round).le))
                exact hopenPost.trans (vote_time_mono_slots S.E
                  (hsourceOpen.trans (hlastBounds.1.trans hn)))
              have hnSourceRead : S.a a.round ≤
                  Protocol.vote_time S.E (n + 1) :=
                (Assembly.a_mono S hr).trans
                  ((delayedSource_action_le_next_opening_vote S r).trans
                    (vote_time_mono_slots S.E hnlo))
              have hroot : ∀ w ∈ rho.honest,
                  Block.Preceq
                    (Protocol.get_fg_root
                      (Internal.NamedRecoveryRead.voteDutyRead S rho w
                        (n + 1)).st.core.toHealing.toFG) T := by
                intro w hw
                have hb := (hseed.checkpointFiltered_at_read_beforeFirst_k6free
                  adm hbelow hfirst hcap hrec ready hnSourceRead
                    ((strictEventIndex_mono rho hnRead).trans_lt hdbefore) hw).2.1
                simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                  NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom,
                  Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
                  Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hb
              apply hseed.checkpointVoteStep_beforeFirst_k6free
                adm hcom hbelow hfirst hcap hrec ready
                (hlastPos.trans_le hn) hnPost hnHor hnSourceRead
                ((strictEventIndex_mono rho hnRead).trans_lt hdbefore) hprev.2
              intro w hw
              exact voterAnchorAt_compatible_of_previousRelativeCarrier
                S adm hroundN
                (hnRead.trans
                  ((le_add_of_nonneg_right S.E.Δ_pos.le).trans hdhor))
                (hnextWindow .g1) hnextMajority hprevSG hw (hroot w hw)
        exact hfold d hlastLe (Nat.le_refl d)
      have hnextSG : HonestSGEmissionsCompatibleAtRound S rho (r + 1) T := by
        by_cases hspan : a.round + S.hc.η_SG ≤ r + 1
        · have hopenHi : S.hc.opening_slot (r + 1) <
              S.hc.opening_slot (r + 1 + 1) := by
              rw [opening_slot_succ_eq S.hc (r + 1)]
              exact Nat.lt_add_of_pos_right
                (Nat.zero_lt_of_lt S.hc.R_ge_two)
          have hopenAction : Protocol.vote_time S.E
                (S.hc.opening_slot (r + 1)) + S.E.Δ ≤ S.a (r + 1) := by
              rw [← opening_confirmation_time_eq_action,
                ← vote_time_succ_add_delta_eq_confirmation_time]
              exact add_le_add (vote_time_mono_slots S.E (Nat.le_succ _))
                (le_refl S.E.Δ)
          have hopenCone := (hnextVotes _ (Nat.le_refl _) hopenHi
            (hopenAction.trans ((Assembly.a_mono S hnextEnd).trans hhor))
            ((strictEventIndex_mono rho
              (((le_add_of_nonneg_right S.E.Δ_pos.le).trans hopenAction).trans
                (Assembly.a_mono S hnextEnd))).trans_lt hbefore)).2
          have hroot : ∀ w ∈ rho.honest, Block.compatible
              (Protocol.get_fg_root
                (actionStoreAt S rho w (r + 1)).toHealing.toFG) T = true := by
            intro w hw
            have hb := (hseed.checkpointFiltered_at_read_beforeFirst_k6free
              adm hbelow hfirst hcap hrec ready
              (Assembly.a_mono S (hr.trans (Nat.le_succ r)))
              ((strictEventIndex_mono rho (Assembly.a_mono S hnextEnd)).trans_lt
                hbefore) hw).2.1
            rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inl hb
          apply sgEmissionsCompatible_succ_of_previousSGHistory_and_openingVotes
            S adm hcom
              (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
          · intro w hw
            exact previousSGWindowHistory_of_invariantFrom S ih'.2 hspan hw
          · exact hopenCone
          · exact hpost.trans (Assembly.a_mono S
              ((Nat.sub_le a.round 2).trans hr))
          · exact (Assembly.a_mono S hnextEnd).trans hhor
          · exact hroot
        · have hopenHi : S.hc.opening_slot (r + 1) <
              S.hc.opening_slot (r + 1 + 1) := by
              rw [opening_slot_succ_eq S.hc (r + 1)]
              exact Nat.lt_add_of_pos_right
                (Nat.zero_lt_of_lt S.hc.R_ge_two)
          have hopenAction : Protocol.vote_time S.E
                (S.hc.opening_slot (r + 1)) + S.E.Δ ≤ S.a (r + 1) := by
              rw [← opening_confirmation_time_eq_action,
                ← vote_time_succ_add_delta_eq_confirmation_time]
              exact add_le_add (vote_time_mono_slots S.E (Nat.le_succ _))
                (le_refl S.E.Δ)
          have hopenCone := (hnextVotes _ (Nat.le_refl _) hopenHi
            (hopenAction.trans ((Assembly.a_mono S hnextEnd).trans hhor))
            ((strictEventIndex_mono rho
              (((le_add_of_nonneg_right S.E.Δ_pos.le).trans hopenAction).trans
                (Assembly.a_mono S hnextEnd))).trans_lt
              hbefore)).2
          have hroot : ∀ w ∈ rho.honest,
              Block.Preceq
                (Protocol.get_fg_root
                  (actionStoreAt S rho w (r + 1)).st.core.toHealing.toFG) T := by
            intro w hw
            have hb := (hseed.checkpointFiltered_at_read_beforeFirst_k6free
              adm hbelow hfirst hcap hrec ready
              (Assembly.a_mono S (hr.trans (Nat.le_succ r)))
              ((strictEventIndex_mono rho (Assembly.a_mono S
                hnextEnd)).trans_lt
                hbefore) hw).2.1
            rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
            exact hb
          apply sgEmissionsCompatible_succ_of_relativeGateOff_compatible
            S adm hcom (Nat.succ_pos r) (hnextWindow .g2) hnextMajority
              hnextRaw
          · intro u hu hemit
            exact hprevSG u hu hemit
          · exact hopenCone
          · rw [← Protocol.Γ_1_eq_vote_time]
            exact (hpost.trans (Assembly.a_mono S
              ((Nat.sub_le a.round 2).trans hr))).trans
                ((a_le_Γ_neg1_succ S.hc S.E.Δ_pos r).trans
                  ((Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1)).le.trans
                    (Γ_0_lt_Γ_1 S.hc S.E.Δ_pos (r + 1)).le))
          · exact (Assembly.a_mono S hnextEnd).trans hhor
          · exact hroot
      refine ⟨hnextVotes, ?_⟩
      constructor
      · intro k hklo hkhi
        rcases Nat.eq_or_lt_of_le hkhi with rfl | hklt
        · exact hnextSG
        · exact ih'.2.1 k hklo (Nat.le_of_lt_succ hklt)
      · intro q hqlo hqhi
        exact hpkg.previousSGReadSideAt adm hbelow hqlo hqhi

#print axioms PrefixFGSelectorConeAt.checkpointProtection_and_SGHistory_beforeFirst_of_G2_cover_named

private theorem delayedSource_actionBody_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) : RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨j, hj, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hDj : D ∈ (rho.stateBefore S j v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho j v).st.bodies
    rw [← hj]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv j hDj)

/-- Every honest source-height row at or after the delayed source has the
source checkpoint as its exact confirmation witness. -/
theorem PrefixFGSelectorConeAt.confirmationWitness_beforeFirst_of_G2_cover_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 M : Height}
    {i : Nat} {a b : NamedAttestation V} {ta tb : Time}
    {Cfg : NamedBlock V} {T Q : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Q)
    (hTQ : Block.Preceq T Q)
    (hpred : 1 ≤ a.round)
    (hpost : S.E.t_GST ≤ S.a (a.round - 2))
    (hhor : S.a (b.round + 2) ≤ rho.horizon)
    (hbeforeFrame : strictEventIndex rho (S.a (b.round + 2)) < first)
    (hframe : GateOffFrameAt S rho M (a.round - 2) (b.round + 2))
    (hpkg : RecoverySGReadSidePackage S rho a.round b.round T)
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1))
    (hround : a.round ≤ b.round)
    (_hbefore : strictEventIndex rho (S.a b.round) < first) :
    fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T := by
  rcases eq_or_lt_of_le hround with heq | hlt
  · exact hseed.confirmationWitness_of_sameRound_honestHeightRow
      adm hcom hbelow hfirst hcap hrec ready hb hemit hrow heq
  have hhistory :=
    hseed.checkpointProtection_and_SGHistory_beforeFirst_of_G2_cover_named
      adm hcom hbelow hfirst hcap hrec ready hselected hTQ hpred hpost
        hround hhor hbeforeFrame hframe hpkg
  let r := b.round - 1
  have hr : a.round ≤ r := Nat.le_sub_one_of_lt hlt
  have hsucc : r + 1 = b.round := Nat.sub_add_cancel
    ((Nat.succ_le_succ (Nat.zero_le a.round)).trans hlt)
  have hrPos : 0 < b.round := Nat.zero_lt_of_lt (hpred.trans_lt hlt)
  have hopenHi : S.hc.opening_slot b.round <
      S.hc.opening_slot (b.round + 1) := by
    rw [opening_slot_succ_eq S.hc b.round]
    exact Nat.lt_add_of_pos_right (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hopenAction : Protocol.vote_time S.E
        (S.hc.opening_slot b.round) + S.E.Δ ≤ S.a b.round := by
    rw [← opening_confirmation_time_eq_action,
      ← vote_time_succ_add_delta_eq_confirmation_time]
    exact add_le_add (vote_time_mono_slots S.E (Nat.le_succ _))
      (le_refl S.E.Δ)
  have hactionHor : S.a b.round ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right b.round 2)).trans hhor
  have hactionBefore : strictEventIndex rho (S.a b.round) < first :=
    (strictEventIndex_mono rho
      (Assembly.a_mono S (Nat.le_add_right b.round 2))).trans_lt hbeforeFrame
  have hopenRead : Protocol.vote_time S.E (S.hc.opening_slot b.round) ≤
      S.a b.round := (le_add_of_nonneg_right S.E.Δ_pos.le).trans hopenAction
  have hgf := (hhistory.1 _ (Nat.le_refl _) hopenHi
    (hopenAction.trans hactionHor)
    ((strictEventIndex_mono rho hopenRead).trans_lt hactionBefore)).2
  have hpostOpen : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot b.round) := by
    rw [← hsucc, ← Protocol.Γ_1_eq_vote_time]
    exact (hpost.trans (Assembly.a_mono S
      ((Nat.sub_le a.round 2).trans hr))).trans
        ((a_le_Γ_neg1_succ S.hc S.E.Δ_pos r).trans
          ((Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1)).le.trans
            (Γ_0_lt_Γ_1 S.hc S.E.Δ_pos (r + 1)).le))
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot b.round) ≤ rho.horizon := by
    rw [opening_confirmation_time_eq_action]
    exact hactionHor
  obtain ⟨D, Kb, hW, hDmem, hDsource, hDheight, hKbmem,
      hKbErase, hKbheight, hKbD, _⟩ :=
    honestHeightRow_confirmationWitness S adm hb hemit hrow
  have hnodeSource : PhaseGrades.nodeFGSource S
      (actionReadAt S rho b.val_index b.round) b.round = some D.erase := by
    unfold actionFGSource at hDsource
    dsimp only at hDsource
    have hroundStore : S.hc.round_of
        (actionStoreAt S rho b.val_index b.round).st.core.toHealing.s =
          b.round := by
      simpa only [Protocol.Store.toHealing] using
        actionStoreAt_round S rho b.val_index b.round
    rw [hroundStore] at hDsource
    simpa only [PhaseGrades.nodeFGSource, PhaseGrades.nodeRead,
      actionStoreAt] using hDsource
  have hnodeQ2 : ∃ R, PhaseGrades.nodeQ2 S
      (actionReadAt S rho b.val_index b.round) b.round = some R := by
    cases hq : PhaseGrades.nodeQ2 S
        (actionReadAt S rho b.val_index b.round) b.round with
    | none =>
        have hbad := hnodeSource
        simp only [PhaseGrades.nodeFGSource, PhaseGrades.nodeQ2,
          PhaseGrades.nodeRead] at hbad hq
        unfold Protocol.fg_source_with Protocol.grade2_block_with at hbad
        rw [hq] at hbad
        simp only [Protocol.fg_source_with.eq_def] at hbad
        cases hbad
    | some R => exact ⟨R, rfl⟩
  obtain ⟨R, hR⟩ := hnodeQ2
  have hsourceCompat : Block.compatible D.erase T = true := by
    rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho b.val_index b.round hR hDsource with hclear | hselectedD
    · obtain ⟨C, hC, _, _, _, hDC⟩ := hclear
      have hCT : Block.compatible C T = true := by
        simpa only [Block.compatible, Bool.or_comm] using
          (WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
            S adm.toNamedAdmissibleCore hcom hb
              (Nat.mul_pos hrPos (Nat.zero_lt_of_lt S.hc.R_ge_two))
              hpostOpen hconfHor hC (fun w hw _ => hhistory.1
                (S.hc.opening_slot b.round) (Nat.le_refl _) hopenHi
                  (hopenAction.trans hactionHor)
                  ((strictEventIndex_mono rho hopenRead).trans_lt
                    hactionBefore) |>.1 w hw))
      exact delayedSource_compatible_ancestor_left hDC hCT
    · have hprevPost : S.E.t_GST ≤ S.a (b.round - 1) :=
        hpost.trans (Assembly.a_mono S
          ((Nat.sub_le a.round 2).trans hr))
      have hloPrev : S.a (a.round - 2) ≤ S.a (b.round - 1) :=
        Assembly.a_mono S
          ((Nat.sub_le a.round 2).trans hr)
      have hloAction : S.a (a.round - 2) ≤ S.a b.round :=
        Assembly.a_mono S ((Nat.sub_le a.round 2).trans hround)
      have hhiAction : S.a b.round ≤ S.a (b.round + 2) :=
        Assembly.a_mono S (Nat.le_add_right b.round 2)
      have hhiPrev : S.a (b.round - 1) ≤ S.a (b.round + 2) :=
        Assembly.a_mono S ((Nat.sub_le b.round 1).trans
          (Nat.le_add_right b.round 2))
      have hwindow : RelativeCarrierWindowAt S rho (b.round - 1) .g2 := by
        apply relativeCarrierWindowAt_of_gateOff S adm hbelow hrPos hprevPost
        · intro u hu
          exact (hframe _ hloPrev hhiPrev u hu).2
        · intro u hu
          exact (hframe _ hloAction hhiAction u hu).2
        · intro u hu
          exact (hframe _ hloAction hhiAction u hu).1
        · exact (FrameForward.domain_le_a S b.round .g2).trans hactionHor
      have hmajority : Internal.NamedOutageEntry.GradeFormingMajority
          S rho b.round :=
        gradeFormingMajority_of_admissible_belowOneThird S adm hbelow
          hrPos ((FrameForward.domain_le_a S b.round .g2).trans hactionHor)
          hprevPost
      have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (b.round - 1 + 1) .g2)
            b.val_index).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (b.round - 1 + 1) .g2)
            b.val_index).st.core.F
          S.hc.η_SG (b.round - 1 + 1)
          (early S.E S.hc (b.round - 1 + 1) .g2)
          (late S.E S.hc (b.round - 1 + 1) .g2) R = true := by
        simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
          Nat.sub_add_cancel (Nat.succ_le_iff.mpr hrPos)] using
            selectedQ2_storeGrade_at_g2Domain S adm hR
      have hmajority' : Internal.NamedOutageEntry.GradeFormingMajority
          S rho (b.round - 1 + 1) := by
        simpa only [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hrPos)] using hmajority
      obtain ⟨u, hu, hRu⟩ := relativeGrade_has_roundCarrier
        S adm.toNamedAdmissibleCore hwindow hmajority' hb hgrade
      obtain ⟨huHon, huEmit⟩ := delayedSource_honestRoundVoter_emits_exactAction
        S adm.toNamedAdmissibleCore hu
      have hprevSG := hhistory.2.1 (b.round - 1)
        (Nat.le_sub_one_of_lt hlt) (Nat.sub_le b.round 1)
      rw [hselectedD]
      exact delayedSource_compatible_ancestor_left hRu
        (hprevSG u huHon huEmit)
  obtain ⟨K, _, hKT, hKh, hKCfg, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKerase : K.erase = T := hKT.trans hseed.checkpointDerived.symm
  have hDrun : RunBlock S rho D :=
    delayedSource_actionBody_runBlock S adm hb hDmem
  have hnamedCompat : NamedBlock.compatible K D = true := by
    simp only [Block.compatible, Bool.or_eq_true] at hsourceCompat
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    rcases hsourceCompat with hDK | hKD
    · exact Or.inr (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hDrun hKrun (by simpa only [hKerase] using hDK))
    · exact Or.inl (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hKrun hDrun (by simpa only [hKerase] using hKD))
  have hKheight : (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKh.trans hseed.sourceDerivedHeight
  have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = T :=
    (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKCfg hKh).trans
      hseed.checkpointDerived.symm
  have heq : T = (Protocol.derive_named S.E S.cfg D).T_h := by
    apply fgConfirmationWitness_eq_of_compatible_of_height_eq S
      hnamedCompat (hKheight.trans hDheight.symm)
    · exact hKtarget.symm
    · rfl
  have hKbtarget : (Protocol.derive_named S.E S.cfg Kb).T_h = Kb.erase :=
    (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg
      (Protocol.namedPreceq_of_runBlock_erase_preceq adm
        (delayedSource_actionBody_runBlock S adm hb hKbmem) hDrun hKbD)
      (hKbheight.trans hDheight.symm)).trans hKbErase.symm
  rw [hW, hKbtarget, hKbErase, ← heq]

#print axioms PrefixFGSelectorConeAt.confirmationWitness_beforeFirst_of_G2_cover_named









end HealingSurface
end Proofs
end DecoupledConsensusModel

end
