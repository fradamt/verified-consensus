module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFGSourceFrame
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleBootstrap
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBoundaryConeLead
public import DecoupledConsensusProofs.Protocol.Grades.SeedFinalizedCanonical
public import DecoupledConsensusProofs.Execution.SeedGradeExistence
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapGradePersistence
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.Grades.Q31_actionSGBlock_tiers

@[expose] public section

/-!
# Recovery anchors from the previous SG history

After the source round, the recovery prefix supplies the two reads needed
for a raw grade-one block. The relative-majority branch is therefore absent
during this strong bootstrap. Compatible prior SG emissions constrain fresh
anchors, and the derived FG-root bound constrains the root fallback.

This supplies the anchor part of the shared Goldfish canonicality step.
There is no fixed-height window through a future action. Initial compatible
SG history and protection across the crossing remain separate obligations.
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
/-- In a later round before the first crossing, the previous honest SG
history supplies actual anchor compatibility. The named recovery prefix
supplies raw G1 and the FG-root bound without a future-action height window. -/
theorem PrefixFGSelectorConeAt.sgAnchor_compatible_laterRound_beforeFirst
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked hF0: Height}
    {i: Nat} {a: NamedAttestation V} {ta: Time}
    {Cfg: NamedBlock V} {T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap: HonestPrefixFinalityCap S rho first hF0)
    (hrec: NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready: GradeRoundReady S rho a.round)
    (hK6Q2: Internal.PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear: Internal.PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {c: Round} (hc: a.round + 1 ≤ c)
    (hsg: HonestSGEmissionsCompatibleAtRound S rho (c - 1) T)
    {d: Slot} (hround: S.hc.round_of d = c)
    (hhor: Protocol.vote_time S.E d ≤ rho.horizon)
    (hbefore: strictEventIndex rho (Protocol.vote_time S.E d) < first)
    {w: V} (hw: w ∈ rho.honest):
    Block.compatible (Proofs.Optimistic.healAnchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho w d).toHealing) T = true:= by
  have hcpos: 1 ≤ c:= (Nat.succ_le_succ (Nat.zero_le a.round)).trans hc
  have hpred: c - 1 + 1 = c:= Nat.sub_add_cancel hcpos
  have hcutRead:= Γ_0_le_vote_time_of_round_eq S hround
  have hsourceRead: S.a a.round ≤ Protocol.vote_time S.E d:=
    ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (action_add_delta_le_next_Γ_neg1 S a.round)).trans
        ((Γ_neg1_mono S.hc S.E.Δ_pos hc).trans
          ((le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos c)).trans hcutRead))
  have hraw:= hseed.rawG1_at_laterRoundRead_beforeFirst
    adm hbelow hfirst hcap hrec ready hK6Q2 hK6Clear hc hcutRead hhor hbefore hw
  have hbatch:= batchCompatible_at_read_of_emittedSGHistory S adm hw
    (time:= Protocol.vote_time S.E d) hsg
  rw [hpred] at hbatch
  have hrootBound:= (hseed.checkpointFiltered_at_read_beforeFirst
    adm hbelow hfirst hcap hrec ready hK6Q2 hK6Clear hsourceRead hbefore hw).2.1
  have hroot: Block.compatible (Protocol.get_fg_root
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing.toFG) T = true:= by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl hrootBound
  have hanchor:= getSgRoot_compatible_of_batch_and_rawG1 S.E
    (HonestWeightMajority.faulty_lt
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)) hbatch hraw hroot
  rw [Proofs.Optimistic.healAnchor_eq_get_sg_root,
    show (Proofs.Optimistic.voteDutyStore S rho w d).toHealing.s = d from
      Proofs.Optimistic.voteDutyStore_slot S rho w d, hround]
  exact hanchor

#print axioms PrefixFGSelectorConeAt.sgAnchor_compatible_laterRound_beforeFirst

-/





/-
/-- In a later round before the first crossing, the previous honest SG
history supplies actual anchor compatibility. The prefix supplies raw G1
and the FG-root bound without a future-action height window. -/
theorem PrefixFGSelectorConeAt.sgAnchor_compatible_laterRound_beforeFirst
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked hF0: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap: HonestPrefixFinalityCap S rho first hF0)
    (hrec: NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready: GradeRoundReady S rho a.round)
    {c: Round} (hc: a.round + 1 ≤ c)
    (hsg: HonestSGEmissionsCompatibleAtRound S rho (c - 1) T)
    {d: Slot} (hround: S.hc.round_of d = c)
    (hhor: Protocol.vote_time S.E d ≤ rho.horizon)
    (hbefore: strictEventIndex rho (Protocol.vote_time S.E d) < first)
    {w: V} (hw: w ∈ rho.honest):
    Block.compatible (Proofs.Optimistic.healAnchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho w d).toHealing) T = true:= by
  have hcpos: 1 ≤ c:= (Nat.succ_le_succ (Nat.zero_le a.round)).trans hc
  have hpred: c - 1 + 1 = c:= Nat.sub_add_cancel hcpos
  have hcutRead:= Γ_0_le_vote_time_of_round_eq S hround
  have hsourceRead: S.a a.round ≤ Protocol.vote_time S.E d:=
    ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (action_add_delta_le_next_Γ_neg1 S a.round)).trans
        ((Γ_neg1_mono S.hc S.E.Δ_pos hc).trans
          ((le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos c)).trans hcutRead))
  have hraw:= hseed.rawG1_at_laterRoundRead_beforeFirst
    adm hbelow hfirst hcap hrec ready hc hcutRead hhor hbefore hw
  have hbatch:= batchCompatible_at_read_of_emittedSGHistory S adm hw
    (time:= Protocol.vote_time S.E d) hsg
  rw [hpred] at hbatch
  have hrootBound:= (hseed.checkpointFiltered_at_read_beforeFirst
    adm hbelow hfirst hcap hrec ready hsourceRead hbefore hw).2.1
  have hroot: Block.compatible (Protocol.get_fg_root
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing.toFG) T = true:= by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl hrootBound
  have hanchor:= getSgRoot_compatible_of_batch_and_rawG1 S.E
    (HonestWeightMajority.faulty_lt_m
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)) hbatch hraw hroot
  rw [Proofs.Optimistic.healAnchor_eq_get_sg_root,
    show (Proofs.Optimistic.voteDutyStore S rho w d).toHealing.s = d from
      Proofs.Optimistic.voteDutyStore_slot S rho w d, hround]
  exact hanchor

/-- The later-round recovery step now consumes only the prior Goldfish cone
and prior honest SG history. The prefix derives anchor, root, filter, and
local-height facts at the actual next vote read. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_previousSGHistory_beforeFirst
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest) (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked hF0: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap: HonestPrefixFinalityCap S rho first hF0)
    (hrec: NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready: GradeRoundReady S rho a.round)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread: S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hbefore: strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hc: a.round + 1 ≤ S.hc.round_of (s + 1))
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hsg: HonestSGEmissionsCompatibleAtRound S rho (S.hc.round_of (s + 1) - 1) T):
    (∀ w ∈ rho.honest, Block.Preceq T (voteDutyHead S rho w (s + 1))) ∧
      Proofs.Optimistic.HonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X):= by
  have hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon:= by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  apply hseed.checkpointVoteStep_beforeFirst adm hcom hbelow hfirst hcap hrec ready
    hs hpost hhor hread hbefore hvotes
  intro w hw
  exact hseed.sgAnchor_compatible_laterRound_beforeFirst adm hbelow hfirst hcap hrec ready
    hc hsg rfl hvoteHor hbefore hw

/-- Raw grade 1 at later-round reads before the first crossing, from the
regime frame. -/
theorem PrefixFGSelectorConeAt.rawG1_at_laterRoundRead_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready: GradeRoundReady S rho a.round)
    {c: Round} (hc: a.round + 1 ≤ c)
    (hsg: HonestSGEmissionsCompatibleAtRound S rho (c - 1) T)
    {read: Time} (hread: S.hc.Γ_0 S.E.Δ c ≤ read)
    (hhor: read ≤ rho.horizon)
    (hbefore: strictEventIndex rho read < first)
    {w: V} (hw: w ∈ rho.honest):
    ((rho.storeBeforeTime S w read).T.filter (fun B => Protocol.G1 S.E
      (rho.storeBeforeTime S w read).toHealing.gradeView S.hc c B = true)).Nonempty:= by
  have hcpos: 1 ≤ c:= (Nat.succ_le_succ (Nat.zero_le a.round)).trans hc
  have hpred: c - 1 + 1 = c:= Nat.sub_add_cancel hcpos
  have hsourcePred: a.round ≤ c - 1:= Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hc)
  have hsourceTime: S.a a.round ≤ S.a (c - 1):= Assembly.a_mono S hsourcePred
  have hpredCut: S.a (c - 1) ≤ S.hc.Γ_neg1 S.E.Δ c:= by
    have h:= (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (action_add_delta_le_next_Γ_neg1 S (c - 1))
    simpa only [hpred] using h
  have hcutRead: S.hc.Γ_neg1 S.E.Δ c ≤ read:=
    (le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos c)).trans hread
  have hcutBefore: strictEventIndex rho (S.hc.Γ_neg1 S.E.Δ c) < first:=
    (strictEventIndex_mono rho hcutRead).trans_lt hbefore
  have hpost: S.E.t_GST ≤ S.a (c - 1):=
    ready.1.trans ((le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos a.round)).trans
      (((le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos a.round)).trans
        ((le_of_lt (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos a.round)).trans
          (Γ_2_le_a S.hc S.E.Δ_pos a.round))).trans hsourceTime))
  have hTCfg: Block.Preceq T Cfg:= by
    rw [hseed.checkpointDerived]
    exact Proofs.Records.derived_state_T_h_preceq S.E S.cfg Cfg
  have hTrun: RunBlock S rho T:=
    (actionSourceAncestor_mem_and_runBlock S adm hseed.signerHonest hseed.sourceMem hTCfg).2
  have hTh: (derived_state S.E S.cfg T).h = blocked + 1:= by
    rw [hseed.checkpointDerived, Protocol.derived_target_height, hseed.sourceDerivedHeight]
  have hFT: Block.Preceq (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ c)).F T:= by
    rw [storeBeforeTime_eq_stateBefore_strictEventIndex S adm.toScheduleWellFormed w]
    exact hframe.floor w hw _ (Nat.le_sub_one_of_lt hcutBefore) T hTrun (hTh ▸ Nat.le_succ blocked)
      (hseed.prev_preceq_checkpoint_of_frame adm hframe)
  apply g1_exists_at_read_of_previousSGFinalizedCompatibility S adm
    (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
    hcpos hpost (hcutRead.trans hhor) hw _ hread
  intro v hv
  have hemit:= honest_emits_exact_actionAttestationAt S adm hv (c - 1)
    (hpredCut.trans (hcutRead.trans hhor))
  have hcompat:= hsg v hv hemit
  rcases (show Block.Preceq (actionSGBlockAt S rho v (c - 1)) T ∨
      Block.Preceq T (actionSGBlockAt S rho v (c - 1)) by
        simpa only [Block.compatible, Bool.or_eq_true] using hcompat) with hVT | hTV
  · rcases Block.preceq_linear hVT hFT with hVF | hFV
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hVF
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl hFV
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hFT hTV)

/-- Later-round anchor compatibility before the first crossing, from the
regime frame. -/
theorem PrefixFGSelectorConeAt.sgAnchor_compatible_laterRound_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready: GradeRoundReady S rho a.round)
    {c: Round} (hc: a.round + 1 ≤ c)
    (hsg: HonestSGEmissionsCompatibleAtRound S rho (c - 1) T)
    {d: Slot} (hround: S.hc.round_of d = c)
    (hhor: Protocol.vote_time S.E d ≤ rho.horizon)
    (hbefore: strictEventIndex rho (Protocol.vote_time S.E d) < first)
    {w: V} (hw: w ∈ rho.honest):
    Block.compatible (Proofs.Optimistic.healAnchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho w d).toHealing) T = true:= by
  have hcpos: 1 ≤ c:= (Nat.succ_le_succ (Nat.zero_le a.round)).trans hc
  have hpred: c - 1 + 1 = c:= Nat.sub_add_cancel hcpos
  have hcutRead:= Γ_0_le_vote_time_of_round_eq S hround
  have hsourceRead: S.a a.round ≤ Protocol.vote_time S.E d:=
    ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (action_add_delta_le_next_Γ_neg1 S a.round)).trans
        ((Γ_neg1_mono S.hc S.E.Δ_pos hc).trans
          ((le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos c)).trans hcutRead))
  have hraw:= hseed.rawG1_at_laterRoundRead_of_frame
    adm hbelow hframe ready hc hsg hcutRead hhor hbefore hw
  have hbatch:= batchCompatible_at_read_of_emittedSGHistory S adm hw
    (time:= Protocol.vote_time S.E d) hsg
  rw [hpred] at hbatch
  have hrootBound:= (hseed.checkpointFiltered_at_read_of_frame
    adm hfirst hframe ready hsourceRead hbefore hw).2.1
  have hroot: Block.compatible (Protocol.get_fg_root
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing.toFG) T = true:= by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl hrootBound
  have hanchor:= getSgRoot_compatible_of_batch_and_rawG1 S.E
    (HonestWeightMajority.faulty_lt_m
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)) hbatch hraw hroot
  rw [Proofs.Optimistic.healAnchor_eq_get_sg_root,
    show (Proofs.Optimistic.voteDutyStore S rho w d).toHealing.s = d from
      Proofs.Optimistic.voteDutyStore_slot S rho w d, hround]
  exact hanchor

/-- The later-round vote step from the previous SG history, from the regime
frame. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_previousSGHistory_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest) (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready: GradeRoundReady S rho a.round)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread: S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hbefore: strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hc: a.round + 1 ≤ S.hc.round_of (s + 1))
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hsg: HonestSGEmissionsCompatibleAtRound S rho (S.hc.round_of (s + 1) - 1) T):
    (∀ w ∈ rho.honest, Block.Preceq T (voteDutyHead S rho w (s + 1))) ∧
      Proofs.Optimistic.HonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X):= by
  have hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon:= by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  apply hseed.checkpointVoteStep_of_frame adm hcom hbelow hfirst hframe ready
    hs hpost hhor hread hbefore hvotes
  intro w hw
  exact hseed.sgAnchor_compatible_laterRound_of_frame adm hbelow hfirst hframe ready
    hc hsg rfl hvoteHor hbefore hw
-/

/-- The later-round named vote step consumes the complete prepared SG window
at the next vote read. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_previousSGHistory_beforeFirst_named
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
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread : S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hbefore : strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hc : a.round + 1 ≤ S.hc.round_of (s + 1))
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hhistory : ∀ w ∈ rho.honest,
      previousSGWindowHistory S rho w
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1))
        (S.hc.round_of (s + 1)) T) :
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X) := by
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  apply hseed.checkpointVoteStep_beforeFirst adm hcom hbelow hfirst hcap hrec
    ready hK6Q2 hK6Clear hs hpost hhor hread hbefore hvotes
  intro w hw
  let r := S.hc.round_of (s + 1)
  have hr : 0 < r := Nat.zero_lt_of_lt
    ((Nat.succ_le_succ (Nat.zero_le a.round)).trans hc)
  have hRpos : 0 < S.hc.R := Nat.zero_lt_of_lt S.hc.R_ge_two
  have hslot : s + 1 < S.hc.opening_slot (r + 1) := by
    apply (Nat.div_lt_iff_lt_mul hRpos).mp
    exact Nat.lt_succ_self r
  have hnext : Protocol.vote_time S.E (s + 1) ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) := by
    have hvoteNext : Protocol.vote_time S.E (s + 1) <
        Protocol.proposal_time S.E (s + 1 + 1) := by
      apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ S.E (s + 1))
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    exact hvoteNext.le.trans (by
      simpa only [DecoupledConsensusModel.Protocol.opening] using
        proposal_time_mono S.E (Nat.succ_le_iff.mpr hslot))
  have hrootBound := (hseed.checkpointFiltered_at_read_beforeFirst
    adm hbelow hfirst hcap hrec ready hK6Q2 hK6Clear hread hbefore hw).2.1
  have hroot : Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
      T = true := by
    have hpre : Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
        T := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hrootBound
    simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hpre
  have hanchor := WeakSG.getSgRoot_compatible_of_windowHistory_at_voteDuty
    S adm.toNamedAdmissibleCore (Eq.refl r) hr hnext hvoteHor hw
      (hhistory w hw).2.1 (hhistory w hw).2.2.1 hroot
  have hslot :
      (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.s = s + 1 :=
    Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  simpa only [voterAnchorAt, PhaseGrades.nodeAnchor,
    PhaseGrades.nodeRead, Protocol.get_sg_root_with, hslot, r] using hanchor

#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_of_previousSGHistory_beforeFirst_named

/-- The later-round named vote step from an additive named regime frame. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_previousSGHistory_of_frameN
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread : S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hbefore : strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hc : a.round + 1 ≤ S.hc.round_of (s + 1))
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hhistory : ∀ w ∈ rho.honest,
      previousSGWindowHistory S rho w
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1))
        (S.hc.round_of (s + 1)) T) :
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X) := by
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  apply hseed.checkpointVoteStep_of_frame adm hcom hbelow hfirst hframe ready
    hK6Q2 hK6Clear hs hpost hhor hread hbefore hvotes
  intro w hw
  let r := S.hc.round_of (s + 1)
  have hr : 0 < r := Nat.zero_lt_of_lt
    ((Nat.succ_le_succ (Nat.zero_le a.round)).trans hc)
  have hRpos : 0 < S.hc.R := Nat.zero_lt_of_lt S.hc.R_ge_two
  have hslot : s + 1 < S.hc.opening_slot (r + 1) := by
    apply (Nat.div_lt_iff_lt_mul hRpos).mp
    exact Nat.lt_succ_self r
  have hnext : Protocol.vote_time S.E (s + 1) ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) := by
    have hvoteNext : Protocol.vote_time S.E (s + 1) <
        Protocol.proposal_time S.E (s + 1 + 1) := by
      apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ S.E (s + 1))
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    exact hvoteNext.le.trans (by
      simpa only [DecoupledConsensusModel.Protocol.opening] using
        proposal_time_mono S.E (Nat.succ_le_iff.mpr hslot))
  have hrootBound := (hseed.checkpointFiltered_at_read_of_frameN
    adm hfirst hframe ready hK6Q2 hK6Clear hread hbefore hw).2.1
  have hroot : Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
      T = true := by
    have hpre : Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
        T := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hrootBound
    simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hpre
  have hanchor := WeakSG.getSgRoot_compatible_of_windowHistory_at_voteDuty
    S adm.toNamedAdmissibleCore (Eq.refl r) hr hnext hvoteHor hw
      (hhistory w hw).2.1 (hhistory w hw).2.2.1 hroot
  have hslotRead :
      (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.s = s + 1 :=
    Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  simpa only [voterAnchorAt, PhaseGrades.nodeAnchor,
    PhaseGrades.nodeRead, Protocol.get_sg_root_with, hslotRead, r] using hanchor

#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_of_previousSGHistory_of_frameN

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
