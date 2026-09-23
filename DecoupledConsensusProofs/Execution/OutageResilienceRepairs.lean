module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.MutualInduction
public import DecoupledConsensusProofs.Protocol.Grades.Stage2
public import DecoupledConsensusProofs.Protocol.Grades.BoundedChainPrebuild
public import DecoupledConsensusProofs.Protocol.Grades.OutageEnvEmitted
public import DecoupledConsensusProofs.Protocol.Grades.GateOffWindowCone

@[expose] public section

/-!
# Proof-layer repairs for stable-chain outage resilience

The declarations in this module are additive. They do not change the frozen
public statement.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry.History
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem noHonestConflictAbove_of_carrierFloor
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P)
    (hfloor : ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho s,
      Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho u s)) :
    NoHonestConflictAbove S rho b0 P := by
  have hroundOne : DecoupledConsensusModel.Protocol.domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before S rho b0 b1 hexec hcom hsleep hroundOne
  have hconf := namedConfirmationIdxQueryEmitted_of_healthyPrefix_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1
  obtain ⟨C, hhistory⟩ :=
    NamedOutageHistory.OutageEnv.layerA_joint_history_idx_emitted_of_outage
      S rho b0 b1 s hexec hsleep hmargin hcom hconf
      (boundaryIdx rho b0) (le_refl _)
  obtain ⟨Pn, _, hPe, hPnrun⟩ :=
    Proofs.NamedIntrinsicEntry.stable_full_prefix_scoped S rho hexec.core.sorted
      v hv s P hstable
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hs1Hor : S.a (s + 1) ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans (hmargin.trans hcap)
  have hcovered : RoundCovered S rho (s + 1) :=
    Or.inl ⟨Proofs.HealingLemmas.a_nonneg S (s + 1), hs1Hor⟩
  have hmajority : GradeFormingMajority S rho (s + 1) :=
    hforming (s + 1) (Nat.succ_pos s) hcovered
  have hvoters : (honestRoundVoters S rho s).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    have hlt := hmajority
    unfold GradeFormingMajority at hlt
    rw [Nat.add_sub_cancel, hempty] at hlt
    exact Nat.not_lt_zero _ (by
      simpa only [Electorate.weightOf, Finset.sum_empty] using hlt)
  obtain ⟨u, hu⟩ := hvoters
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u s).mp hu).1
  obtain ⟨a, haround, _, hemit⟩ := honestRoundVoter_emits S rho hu
  have hsHor : S.a s ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ s)).trans hs1Hor
  have haconfirmed := honest_emitted_round_confirmed S rho hexec.core
    u huHon s hsHor haround hemit
  obtain ⟨i, hi, himem⟩ := hemit
  have hasb0 : S.a s < b0 := by
    exact (NamedOutageHistory.JointHistoryGapsTime.setup_a_strictMono S
      (Nat.lt_succ_self s)).trans_le
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hibound : i < boundaryIdx rho b0 :=
    tick_index_lt_boundaryIdx rho hexec.core.sorted hi
      (by simpa only [NamedEvent.time] using hasb0)
  obtain ⟨K, hKrun, _, hKroot, hKC⟩ :=
    hhistory.1.2.1 i u (S.a s) a huHon hi himem hibound
      (Proofs.HealingSurface.actionSGBlockAt S rho u s).root haconfirmed
  have hcarrierMem : Proofs.HealingSurface.actionSGBlockAt S rho u s ∈
      (NamedRun.stateBeforeTime S rho (S.a s) u).st.core.T :=
    Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime S rho u s
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a s) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    hexec.core.sorted (S.a s)
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hDrun : NamedRun.blockInRun S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hDprefix
  have hDKroot : D.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact hKroot.symm
  have hDK : D = K :=
    hexec.core.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hKe : K.erase = Proofs.HealingSurface.actionSGBlockAt S rho u s := by
    rw [← hDK, hDerase]
  have hPnKraw : Block.Preceq Pn.erase K.erase := by
    rw [hPe, hKe]
    exact hfloor u hu
  have hPnK : NamedBlock.Preceq Pn K :=
    NamedOutageHistory.JointHistoryProducersTime.named_of_erase_preceq
      S rho hexec.core hPnrun hKrun hPnKraw
  have hPnC : NamedBlock.Preceq Pn C :=
    NamedOutageHistory.IdxDriverHelpers.named_preceq_trans hPnK hKC
  have hno := NamedOutageHistory.OutageEnv.noHonestConflictAbove_of_layerA
    S rho b0 hexec.core C Pn hhistory.1 hPnrun hPnC
  simpa only [hPe] using hno

/-- Public additive export of the existing carrier-floor prefix-safety proof.
The private theorem is retained unchanged for its existing consumers. -/
theorem noHonestConflictAbove_of_carrierFloor_export
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P)
    (hfloor : ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho s,
      Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho u s)) :
    NoHonestConflictAbove S rho b0 P :=
  noHonestConflictAbove_of_carrierFloor S rho b0 b1 v s P
    hexec hcom hsleep hforming hv hmargin hstable hfloor

theorem honestConfirmedAtOrAbove_exactRound_of_carrierFloor
    (S : Setup V) (rho : NamedRun V) (s : Round) (P : Block V)
    (core : NamedAdmissibleCore S rho)
    (hfloor : ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho s,
      Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho u s))
    (a : NamedAttestation V) (t : Time)
    (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) t)
    (haround : a.round = s)
    (key : BlockId) (hkey : a.confirmed = some key)
    (K : NamedBlock V) (hKrun : NamedRun.blockInRun S rho K)
    (hKroot : K.root = key) :
    Block.Preceq P K.erase := by
  obtain ⟨i, hi, _, _, _, _, ht, _⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hem
  have hemAction : NamedRun.emits S rho a.val_index (.attest a) (S.a s) := by
    simpa only [ht, haround] using hem
  have hvoter : a.val_index ∈ honestRoundVoters S rho s := by
    apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho a.val_index s).mpr
    exact ⟨ha, a, rfl, haround, hemAction⟩
  have hcarrierMem : Proofs.HealingSurface.actionSGBlockAt S rho a.val_index s ∈
      (NamedRun.stateBeforeTime S rho (S.a s) a.val_index).st.core.T :=
    Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime S rho a.val_index s
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a s) a.val_index hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    core.sorted (S.a s)
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n a.val_index).st.bodies := by
    rw [← hn]
    exact hDbody
  have hDrun : NamedRun.blockInRun S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S ha hDprefix
  have hsHor : S.a s ≤ rho.horizon := by
    have hmem : NamedEvent.tick a.val_index (S.a s) ∈ rho.events := by
      apply List.mem_iff_getElem?.mpr
      exact ⟨i, by simpa only [ht, haround] using hi⟩
    exact (core.toNamedScheduleWellFormed.in_horizon _ hmem).2
  have hconfirmed := honest_emitted_round_confirmed S rho core
    a.val_index ha s hsHor haround hemAction
  have hDKroot : D.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase, hKroot]
    exact Option.some.inj (hconfirmed.symm.trans hkey)
  have hDK : D = K :=
    core.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  rw [← hDK, hDerase]
  exact hfloor a.val_index hvoter

#print axioms noHonestConflictAbove_of_carrierFloor
#print axioms noHonestConflictAbove_of_carrierFloor_export
#print axioms honestConfirmedAtOrAbove_exactRound_of_carrierFloor
















end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
