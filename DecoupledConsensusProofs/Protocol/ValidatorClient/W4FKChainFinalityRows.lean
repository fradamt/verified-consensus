module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The emission lemma -/

/-- Named twin of earlier's `round_action_finality_pair_of_record_guard`
(`RecurringFinalityRun.lean:1333`). Rule B permits an empty target record, so
the complete empty-or-matching target and lock guards are sufficient for the
round action to emit the current head checkpoint. -/
theorem namedRoundAction_finality_pair_of_record_guard
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.HealingStore V) (record : Protocol.NamedRecord)
    {h : Height} {J : BlockId}
    (htarget : record.legacy.target h = none ∨ record.legacy.target h = some J)
    (htimeout : record.legacy.timeout h = false)
    (hlock : record.legacy.lock h = none ∨ record.legacy.lock h = some J)
    (hhj : (st.σ (actionHeadWith contract E hc st)).h_j = h)
    (hJ : (st.σ (actionHeadWith contract E hc st)).J.root = J)
    (hF : (st.σ (actionHeadWith contract E hc st)).h_F < h) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.finality_pair =
      some ⟨h, J⟩ := by
  obtain ⟨Hd, hHd, heq⟩ :=
    _root_.DecoupledConsensusModel.Proofs.round_action_finality_pair
      contract E hc nd st record
  have hHdEq : Hd = actionHeadWith contract E hc st := hHd
  subst hHdEq
  rw [heq, hhj, hJ]
  have hguard :
      (record.legacy.target h = none ∨ record.legacy.target h = some J) ∧
        record.legacy.timeout h = false ∧
        (record.legacy.lock h = none ∨ record.legacy.lock h = some J) :=
    ⟨htarget, htimeout, hlock⟩
  simp only [Protocol.finality_pair, if_pos hF, if_pos hguard]

#print axioms namedRoundAction_finality_pair_of_record_guard

/-! ## 2. The honest action row -/

/-- Copied from the private `MovingChainRoundReadRun.lean:318`
(`mem_bodies_of_mem_T`): a run block whose erasure is in an honest reader's
tree is itself one of that reader's named bodies. -/
private theorem w4frMemBodies_of_memT
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {B : NamedBlock V}
    (hBrun : RunBlock S rho B)
    (hmem : B.erase ∈ (rho.storeBeforeTime S v t).core.T) :
    B ∈ (rho.storeBeforeTime S v t).bodies := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed t
  have hmemN : B.erase ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Run.storeBeforeTime, hn] using hmem
  obtain ⟨D, hDmem, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hmemN
  have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDmem
  have hDB : D = B :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D B hDrun hBrun D B
      (Or.inl (Proofs.NamedAncestry.named_self D)) (Or.inr (Proofs.NamedAncestry.named_self B))
      (by rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root B, hDerase])
  have hBmem : B ∈ (rho.stateBefore S n v).st.bodies := hDB ▸ hDmem
  simpa only [Run.storeBeforeTime, hn] using hBmem

/-- The action head of an honest reader, when it is the erasure of a run block,
is a named body of that reader's own action store. -/
theorem actionHead_namedBody_of_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {P : NamedBlock V}
    (hPrun : RunBlock S rho P)
    (hhead : actionHeadAt S rho v r = P.erase) :
    P ∈ (actionStoreAt S rho v r).st.bodies := by
  have hheadMem :
      actionHeadWith (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
          S.E S.hc (actionStoreAt S rho v r).st.core.toHealing ∈
        (rho.storeBeforeTime S v (S.a r)).T :=
    actionHeadWith_mem_storeBeforeTime S v r
  have hheadEq : actionHeadAt S rho v r =
      actionHeadWith (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).st.core.toHealing := rfl
  have hPmem : P.erase ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
    rw [← hhead, hheadEq]
    exact hheadMem
  have hbodies := w4frMemBodies_of_memT S adm hv hPrun hPmem
  simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
    NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, NamedRun.stateBeforeTime,
    Run.storeBeforeTime] using hbodies

/-- Named twin of the `hrows` block of
`canonicalCarrier_commonFinalized_of_justifiedPrefix`
(`FinalityFromJustifiedPrefixRun.lean:70-98`): an honest round action whose head
is the named block `P` emits `P`'s live justification as its finality pair,
given the three record guards at that height. -/
theorem actionAttestation_finality_pair_of_recordGuard
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {P : NamedBlock V}
    (hPrun : RunBlock S rho P)
    (hhead : actionHeadAt S rho v r = P.erase)
    {hJ : Height} {J : Block V}
    (hhj : (derive_named S.E S.cfg P).h_j = hJ)
    (hJeq : (derive_named S.E S.cfg P).J = J)
    (hdebt : (derive_named S.E S.cfg P).h_F < hJ)
    (htarget : (rho.stateBeforeTime S (S.a r) v).Λ.target hJ = none ∨
      (rho.stateBeforeTime S (S.a r) v).Λ.target hJ = some J.root)
    (htimeout : (rho.stateBeforeTime S (S.a r) v).Λ.timeout hJ = false)
    (hlock : (rho.stateBeforeTime S (S.a r) v).Λ.lock hJ = none ∨
      (rho.stateBeforeTime S (S.a r) v).Λ.lock hJ = some J.root) :
    (actionAttestationAt S rho v r).finality_pair = some ⟨hJ, J.root⟩ := by
  have hbody := actionHead_namedBody_of_runBlock S adm hv hPrun hhead
  have hagree := derivedStateAgrees_actionStoreAt S adm v r P hbody
  have hheadEq : actionHeadAt S rho v r =
      actionHeadWith (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).st.core.toHealing := rfl
  have hsigma : (actionStoreAt S rho v r).st.core.toHealing.σ
      (actionHeadWith (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).st.core.toHealing) =
      derive_named S.E S.cfg P := by
    rw [← hheadEq, hhead]
    exact hagree
  have hrecord : (actionStoreAt S rho v r).record =
      (rho.stateBeforeTime S (S.a r) v).Λ := rfl
  exact namedRoundAction_finality_pair_of_record_guard
    (NamedProfile.gradeContract (actionStoreAt S rho v r).cache) S.E S.hc
    (S.node v) (actionStoreAt S rho v r).st.core.toHealing
    (actionStoreAt S rho v r).record
    (by rw [hrecord]; exact htarget)
    (by rw [hrecord]; exact htimeout)
    (by rw [hrecord]; exact hlock)
    (by rw [hsigma]; exact hhj)
    (by rw [hsigma, hJeq])
    (by rw [hsigma]; exact hdebt)

#print axioms actionHead_namedBody_of_runBlock
#print axioms actionAttestation_finality_pair_of_recordGuard

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
