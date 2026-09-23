module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierTimeoutGate
public import DecoupledConsensusProofs.Protocol.ValidatorClient.MigrationResiduals
public import DecoupledConsensusProofs.Protocol.ChainState.RowFreshness
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Canonical-regime finality producer

This file closes the Rule-B lock-alignment part of the canonical carrier
producer. A lock at the carrier height comes from an earlier finality pair.
That pair has an earlier honest target row at the same height. Once the carrier
height is above the boundary frontier, the row belongs to the canonical action
history. Its exact source is therefore on the carrier opening chain, and
same-height target stability identifies its target with the carrier target.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- An honest emitted attestation is the exact action attestation for its
recorded round. -/
theorem emittedHonestAttestation_eq_actionAttestationAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hemit : rho.emits S v (.attest a) t) :
    a = actionAttestationAt S rho v a.round := by
  have htick : t = S.a a.round :=
    (Proofs.Optimistic.emits_attest_shape S hemit).2
  subst t
  exact ((NamedActionSources.action_run_emission S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v a.round a).mp hemit).2.2

omit [Fintype V] in
/- Two named ancestors of one block are comparable. -/
private theorem preceq_or_preceq_of_common_producer
    {A B C : NamedBlock V} (hA : NamedBlock.Preceq A C)
    (hB : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A B ∨ NamedBlock.Preceq B A := by
  induction C with
  | genesis =>
      have hgen : A = .genesis := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hA
      have hBgen : B = .genesis := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hB
      subst A
      subst B
      exact Or.inl (by rfl)
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hA
      rcases hA with rfl | hA
      · exact Or.inr hB
      · simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
          decide_eq_true_eq] at hB
        rcases hB with rfl | hB
        · exact Or.inl (by
            simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
            exact Or.inr hA)
        · exact ih hA hB

private theorem actionBody_runBlock_producer
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) : RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

/-- A finality-pair target emitted no later than the carrier action names the
carrier chain's target at that height, provided the height is above the
boundary frontier and has a canonical witness below the carrier opening. -/
theorem finalityPairTarget_eq_canonicalTarget
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfinality : FinalityTargetHeightSource S rho)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    {H : Height} {P W : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P)
    (hW : NamedBlock.Preceq W P)
    (hWheight : (Protocol.derive_named S.E S.cfg W).h = H)
    (habove : honestHMaxAt S rho (S.a q0) < H)
    {a : NamedAttestation V} {ta : Time} {target : BlockId}
    (haHonest : a.val_index ∈ rho.honest)
    (haEmit : rho.emits S a.val_index (.attest a) ta)
    (hta : ta ≤ S.a r)
    (hpair : a.finality_pair = some ⟨H, target⟩) :
    target = (Protocol.derive_named S.E S.cfg W).T_h.root := by
  obtain ⟨b, tb, hbHonest, hbEmit, htb, hbPair⟩ :=
    hfinality a ta haHonest haEmit _ target hpair
  have hbEq : b = actionAttestationAt S rho b.val_index b.round :=
    emittedHonestAttestation_eq_actionAttestationAt S adm hbEmit
  have hbPairAction :
      (actionAttestationAt S rho b.val_index b.round).height_pair =
        NamedHeightPair.vote H target false := by
    rw [← hbEq]
    exact hbPair
  have hbHeight :
      (actionAttestationAt S rho b.val_index b.round).height_pair.erase.height? =
        some H := by
    rw [hbPairAction]
    rfl
  have hq0b : q0 < b.round :=
    honestRow_after_frontier S adm hbHonest habove hbHeight
  have htbShape : tb = S.a b.round :=
    (Proofs.Optimistic.emits_attest_shape S hbEmit).2
  have hbBefore : S.a b.round < S.a r := by
    rw [← htbShape]
    exact htb.trans_le hta
  have hbr : b.round < r :=
    (action_strictMono S).lt_iff_lt.mp hbBefore
  obtain ⟨Q, hsource, hQrun, hQP0, hQheight⟩ :=
    hround.heightHistory P hP b.round (Nat.le_of_lt hq0b) hbr
      b.val_index hbHonest _ hbHeight
  obtain ⟨Cfg, hCfg, hCfgHeight, hCfgTarget⟩ :=
    NamedActionSources.action_source S rho b.val_index b.round H target false
      hbPairAction
  obtain ⟨D, hDbody, hDerase, hDderive, -⟩ :=
    NamedActionSources.action_witness S rho b.val_index b.round Cfg hCfg
  have hsourceCfg : Q.erase = Cfg :=
    Option.some.inj (hsource.symm.trans hCfg)
  have hDQerase : D.erase = Q.erase :=
    hDerase.trans hsourceCfg.symm
  have hDrun : RunBlock S rho D :=
    actionBody_runBlock_producer S adm hbHonest (by simpa only [actionStoreAt] using hDbody)
  have hDQroot : D.root = Q.root := by
    calc
      D.root = D.erase.root := (Proofs.NamedWire.erase_root D).symm
      _ = Q.erase.root := congrArg Block.root hDQerase
      _ = Q.root := Proofs.NamedWire.erase_root Q
  have hDQ : D = Q :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective D Q hDrun hQrun D Q
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self Q)) hDQroot
  have hDheight : (Protocol.derive_named S.E S.cfg D).h = H := by
    simpa only [hDderive] using hCfgHeight
  have hDtarget : (Protocol.derive_named S.E S.cfg D).T_h.root = target := by
    simpa only [hDderive] using hCfgTarget
  have hDP : NamedBlock.Preceq D P := by
    simpa only [hDQ] using hQP0
  have hsame : (Protocol.derive_named S.E S.cfg D).T_h =
      (Protocol.derive_named S.E S.cfg W).T_h := by
    rcases preceq_or_preceq_of_common_producer hDP hW with hDW | hWD
    · exact Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hDW
        (hDheight.trans hWheight.symm)
    · exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hWD
        (hWheight.trans hDheight.symm)).symm
  calc
    target = (Protocol.derive_named S.E S.cfg D).T_h.root := hDtarget.symm
    _ = (Protocol.derive_named S.E S.cfg W).T_h.root := congrArg Block.root hsame


/-
/-- At every canonical height above the boundary frontier, every stored lock
and every same-action finality pair uses that height's canonical target. -/
theorem CanonicalRegimeRoundAt.successorTargetLockAlignment_of_canonicalHeight
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hfb: BelowOneThird S rho.honest)
    {q0 r: Round} (hround: CanonicalRegimeRoundAt S rho q0 r)
    {H: Height} {W: Block V}
    (hW: Block.Preceq W (proposedBlock S rho (S.hc.opening_slot r)))
    (hWheight: (derived_state S.E S.cfg W).h = H)
    (habove: honestHMaxAt S rho (S.a q0) < H):
    ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt
        (rho.stateBeforeTime S (S.a r) v).Λ
        (actionAttestationAt S rho v r).finality_pair
        H (derived_state S.E S.cfg W).T_h.root:= by
  have hfinality: FinalityTargetHeightSource S rho:=
    finalityTargetHeightSource_of_admissible S adm hfb
  intro v hv
  constructor
  · intro X hlock
    obtain ⟨n, hn, hbefore⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toScheduleWellFormed (S.a r)
    have hlockN: (rho.stateBefore S n v).Λ.lock H = some X:= by
      rw [← hn]
      exact hlock
    obtain ⟨i, hi, ta, a, hevent, hemitted, hpair⟩:=
      recordLock_finalityEmission_before S rho v n hlockN
    have haEmit: rho.emits S v (.attest a) ta:=
      ⟨i, hevent, hemitted⟩
    have haHonest: a.val_index ∈ rho.honest:= by
      rw [(Proofs.Optimistic.emits_attest_shape S haEmit).1]
      exact hv
    exact finalityPairTarget_eq_canonicalTarget
      S adm hfinality hround hW hWheight habove haHonest
        (by simpa only [(Proofs.Optimistic.emits_attest_shape S haEmit).1] using haEmit)
        (le_of_lt (hbefore i _ hi hevent)) hpair
  · intro p hfp hpHeight
    have hactionHor: S.a r ≤ rho.horizon:= by
      have hmono: Protocol.confirmation_time S.E
          (S.hc.opening_slot r) ≤ Protocol.confirmation_time S.E
            (S.hc.opening_slot r + 2):=
        confirmation_time_mono_producer S.E (Nat.le_add_right _ 2)
      have ha: S.a r ≤ Protocol.confirmation_time S.E
          (S.hc.opening_slot r + 2):= by
        simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hmono
      exact ha.trans hround.inHorizon
    have haEmit:= honest_emits_exact_actionAttestationAt
      S adm hv r hactionHor
    rcases p with ⟨height, target⟩
    change height = H at hpHeight
    subst height
    have haHonest:
        (actionAttestationAt S rho v r).val_index ∈ rho.honest:= by
      rw [(actionAttestationAt_shape S rho v r).1]
      exact hv
    have haEmit': rho.emits S
        (actionAttestationAt S rho v r).val_index
        (.attest (actionAttestationAt S rho v r)) (S.a r):= by
      rw [(actionAttestationAt_shape S rho v r).1]
      exact haEmit
    exact finalityPairTarget_eq_canonicalTarget
      S adm hfinality hround hW hWheight habove
        (a:= actionAttestationAt S rho v r) (ta:= S.a r)
        (target:= target) haHonest haEmit'
        (show S.a r ≤ S.a r from le_rfl) hfp

/-- The carrier-opening instance of the canonical-height lock alignment. -/
theorem CanonicalRegimeRoundAt.successorTargetLockAlignment_of_aboveBoundary
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hfb: BelowOneThird S rho.honest)
    {q0 r: Round} (hround: CanonicalRegimeRoundAt S rho q0 r)
    (habove: honestHMaxAt S rho (S.a q0) <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).h):
    ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt
        (rho.stateBeforeTime S (S.a r) v).Λ
        (actionAttestationAt S rho v r).finality_pair
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).T_h.root:=
  CanonicalRegimeRoundAt.successorTargetLockAlignment_of_canonicalHeight
      S adm hfb hround
      (Block.preceq_self (proposedBlock S rho (S.hc.opening_slot r)))
      rfl habove
-/

#print axioms finalityPairTarget_eq_canonicalTarget

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
