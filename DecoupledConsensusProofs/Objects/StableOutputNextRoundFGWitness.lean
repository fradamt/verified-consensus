module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Execution.OutageInputs

@[expose] public section

/-!
# T_out, step 1: FG-root provenance under a faulty-weight quorum bound

The ordinary FG-root witness theorem uses `HonestWeightMajority`. The outage
boundary already gives the weaker fact needed here: a finality quorum cannot
be entirely faulty. This leaf keeps that distinction explicit and exports
the same exact honest action witness for the later carrier proof.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/- The following three helpers are local copies of private helpers in
`Proofs.HealingSurface.FGRootWitnessRun`; the names stay local to this clean leaf. -/

private theorem w4_namedAncestorBodyMem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) :
    A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

private theorem w4_actionStore_coherent
    (S : Setup V) {rho : Run V} (v : V) (r : Round) :
    Proofs.NamedStore.Coherent S.E S.cfg (actionStoreAt S rho v r).st := by
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  exact hinv.1.1

private theorem w4_actionBody_runBlock
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

private theorem w4_quorum_honest_member (S : Setup V) (rho : NamedRun V)
    (Q : Finset V) (hQ : S.E.electorate.IsQuorum Q)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    ∃ signer ∈ Q, signer ∈ rho.honest := by
  by_contra hn
  have hsub : Q ⊆ Finset.univ \ rho.honest := by
    intro signer hs
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hh => hn ⟨signer, hs, hh⟩⟩
  have hm := S.E.electorate.weightOf_mono hsub
  have hq : S.E.q ≤ S.E.electorate.weightOf Q := hQ
  omega

/- The proof follows `Proofs.HealingSurface.processedJustification_confirmationWitness`,
but obtains the honest signer from `hbad` and uses the public named action
source/witness projections instead of its private selector helper. -/
theorem fgRoot_confirmationWitness_at_read_of_faulty_lt_quorum
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    {v : V} (hv : v ∈ rho.honest) (time : Time) :
    let R := Protocol.get_fg_root
      (rho.storeBeforeTime S v time).toHealing.toFG
    R = Block.genesis ∨ ∃ (C : NamedBlock V),
      C ∈ (rho.storeBeforeTime S v time).bodies ∧
      (Protocol.derive_named S.E S.cfg C).J = R ∧
      ∃ (a : NamedAttestation V) (ta : Time),
      a.val_index ∈ rho.honest ∧
      NamedRun.emits S rho a.val_index (Object.attest a) ta ∧ ta < time ∧
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root ∧
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R := by
  dsimp only
  obtain ⟨C, hC, hCJ⟩ := Proofs.HealingSurface.fgRoot_justificationSource_at_read
    S adm v time
  by_cases hz : (Protocol.derive_named S.E S.cfg C).h_j = 0
  · exact Or.inl (hCJ.symm.trans
      (NamedJustificationCertificates.justified_zero_is_genesis
        S.E S.cfg C hz))
  · obtain ⟨Jcert, hJcert, hJcertErase, Q, hQ, hrows⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg C hz
    obtain ⟨signer, hsignerQ, hsignerHon⟩ := w4_quorum_honest_member
      S rho Q hQ hbad
    obtain ⟨carrier, a, hcarrier, hrowMem, hai, hap⟩ := hrows signer hsignerQ
    have haHon : a.val_index ∈ rho.honest := by
      rw [hai]
      exact hsignerHon
    have sch : ScheduleWellFormed S rho := adm.toNamedScheduleWellFormed
    obtain ⟨n, hn, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      sch.sorted time
    have hCpre : C ∈ (rho.stateBefore S n v).st.bodies := by
      change C ∈ (NamedRun.stateBefore S rho n v).st.bodies
      have hstate := congrFun hn v
      rw [← hstate]
      exact hC
    have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1.1.1
    have hcarrierBody : carrier ∈ (rho.stateBefore S n v).st.bodies :=
      w4_namedAncestorBodyMem hcoh.2.2.1 hCpre hcarrier
    rcases Proofs.Bridges.processes_block_of_mem_T S rho v n carrier hcarrierBody with
      hgen | ⟨j, e, hj, hje, hproc⟩
    · simp only [hgen, NamedBlock.attestations, List.not_mem_nil] at hrowMem
    · obtain ⟨hround, hemit⟩ := Proofs.Bridges.carriedArePastEmissions_of_processes
        S rho adm.toNamedUnforgeable hproc hrowMem haHon
      have hta : S.a a.round < time :=
        lt_of_le_of_lt hround (hbefore j e hj hje)
      have hJcertRoot : Jcert.root =
          (Protocol.derive_named S.E S.cfg C).J.root := by
        simpa only [Proofs.NamedWire.erase_root] using congrArg Block.root hJcertErase
      have hpair : a.height_pair.erase = HeightPair.target
          (Protocol.derive_named S.E S.cfg C).h_j
          (Protocol.derive_named S.E S.cfg C).J.root := by
        rw [hap]
        simp [NamedHeightPair.erase, hJcertRoot]
      have haEq : a = actionAttestationAt S rho a.val_index a.round := by
        exact (NamedActionSources.action_run_emission S rho sch
          a.val_index a.round a).mp hemit |>.2.2
      have hrowAction :
          (actionAttestationAt S rho a.val_index a.round).height_pair =
            NamedHeightPair.vote
              (Protocol.derive_named S.E S.cfg C).h_j Jcert.root false := by
        rw [← haEq]
        exact hap
      obtain ⟨Cfg, hCfg, hCfgHeight, hCfgRoot⟩ :=
        NamedActionSources.action_source S rho a.val_index a.round
          (Protocol.derive_named S.E S.cfg C).h_j Jcert.root false hrowAction
      obtain ⟨D, hD, hDerase, hDderive, hfg⟩ :=
        NamedActionSources.action_witness S rho a.val_index a.round Cfg hCfg
      have hCfg' : actionFGSource S (actionStoreAt S rho a.val_index a.round) =
          some Cfg := by simpa only [actionStoreAt] using hCfg
      have hD' : D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies := by
        simpa only [actionStoreAt] using hD
      have hDderive' :
          (actionStoreAt S rho a.val_index a.round).st.core.σ Cfg =
            Protocol.derive_named S.E S.cfg D := by
        simpa only [actionStoreAt] using hDderive
      have hfg' : fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
            some (Protocol.derive_named S.E S.cfg D).T_h := by
        simpa only [actionStoreAt] using hfg
      obtain ⟨K, hKD, hKentry, hKheight⟩ :=
        Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg D
      have hcohAction := w4_actionStore_coherent (rho := rho) S a.val_index a.round
      have hK : K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies :=
        w4_namedAncestorBodyMem hcohAction.2.2.1 hD' hKD
      have hKrun := w4_actionBody_runBlock S adm haHon hK
      have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase :=
        (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKD hKheight).trans
          hKentry.symm
      have hCmemCore : C.erase ∈
          (rho.storeBeforeTime S v time).core.T := by
        have hcohTime :=
          (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time v).1.1.1
        change C.erase ∈ (NamedRun.stateBeforeTime S rho time v).st.core.T
        rw [hcohTime.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hC
      have hJmem : (Protocol.derive_named S.E S.cfg C).J ∈
          (rho.storeBeforeTime S v time).core.T := by
        have hcohTime :=
          (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time v).1.1.1
        apply NamedDerivationGeometry.core_ancestor_mem S.E S.cfg
          (rho.storeBeforeTime S v time) hcohTime hCmemCore
        exact (NamedDerivationGeometry.derive_named_anchors_preceq
          S.E S.cfg C).2
      obtain ⟨J, hJerase, hJrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          sch hv time hJmem
      have hKroot : K.root = J.root := by
        calc
          K.root = K.erase.root := (Proofs.NamedWire.erase_root K).symm
          _ = (Protocol.derive_named S.E S.cfg D).T_h.root := by
            rw [hKentry]
          _ = ((actionStoreAt S rho a.val_index a.round).st.core.σ Cfg).T_h.root := by
            rw [hDderive']
          _ = Jcert.root := hCfgRoot
          _ = Jcert.erase.root := (Proofs.NamedWire.erase_root Jcert).symm
          _ = (Protocol.derive_named S.E S.cfg C).J.root := by
            rw [hJcertErase]
          _ = J.erase.root := by rw [hJerase]
          _ = J.root := Proofs.NamedWire.erase_root J
      have hEq : K = J :=
        adm.toNamedRootCollisionFree.root_injective K J hKrun hJrun K J
          (Or.inl (Proofs.NamedAncestry.named_self K))
          (Or.inr (Proofs.NamedAncestry.named_self J)) hKroot
      have hW : (Protocol.derive_named S.E S.cfg K).T_h =
          (Protocol.derive_named S.E S.cfg C).J := by
        exact hKtarget.trans (hEq ▸ hJerase)
      have hfgK : fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
            some (Protocol.derive_named S.E S.cfg K).T_h := by
        rw [hfg']
        congr 1
        exact (hKtarget.trans hKentry).symm
      refine Or.inr ⟨C, hC, hCJ, a, S.a a.round, haHon, hemit, hta, hpair, ?_⟩
      rw [hfgK, hW, hCJ]

theorem fgRoot_confirmationWitness_at_read_of_healthyPrefix
    (S : Setup V) (rho : Run V) (b0 b1 : Time) (s : Round)
    (hout : OutageExecution S rho b0 b1)
    (hsleep : OutageSleepyThroughout S rho)
    (hmargin : FormationMargin S s b0)
    {v : V} (hv : v ∈ rho.honest) (time : Time) :
    let R := Protocol.get_fg_root
      (rho.storeBeforeTime S v time).toHealing.toFG
    R = Block.genesis ∨ ∃ (C : NamedBlock V),
      C ∈ (rho.storeBeforeTime S v time).bodies ∧
      (Protocol.derive_named S.E S.cfg C).J = R ∧
      ∃ (a : NamedAttestation V) (ta : Time),
      a.val_index ∈ rho.honest ∧
      NamedRun.emits S rho a.val_index (Object.attest a) ta ∧ ta < time ∧
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root ∧
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R := by
  have hbad := Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s hout
    hmargin hsleep
  exact fgRoot_confirmationWitness_at_read_of_faulty_lt_quorum S
    (rho := rho) hout.core hbad hv time

#print axioms fgRoot_confirmationWitness_at_read_of_faulty_lt_quorum
#print axioms fgRoot_confirmationWitness_at_read_of_healthyPrefix

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
