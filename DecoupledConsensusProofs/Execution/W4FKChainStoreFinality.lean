module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainSecondCheckpoint
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainCheckpointLift
public import DecoupledConsensusProofs.Execution.W4FinalityProjection
public import DecoupledConsensusProofs.Execution.StoreFinalityRun

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # W4 branches fk-chain: `W4CommonFinalityAtConfirmationPin`

Named proof of earlier's `commonFinalityAtConfirmation_of_proposedBlockCandidate`
(`RecurringFinalityRun.lean:1476`). earlier's route is

1. the lifecycle makes the honest proposal the reader's live confirmation at
   the slot's confirmation duty, so the proposal is in the reader's tree;
2. the reader therefore PROCESSED the proposal, and `on_block`'s finality write
   carries the proposal's own candidate checkpoint into the reader's `F`
   (`acceptedBlock_candidateFinality_preceq`);
3. a non-genesis checkpoint below the reader's `F` bounds the reader's
   `finalized_height` (`finalized_height_ge_of_checkpoint_preceq`, through
   `derived_height_le_finalized_height_of_preceq`).

Steps 1 and 3 are restated here. Step 1 is wave A3's available
`proposedBlock_emitted_and_liveConfirmed_of_canonicalSuffixExecution`
(`W4FinalityProjectionRun.lean:259`) followed by
`Proofs.NamedStoreBridge.liveConfirmed_mem_stateAt` and the store's coherence, which
turns the tree membership into NAMED body membership. Step 3 is
`namedHeight_le_finalizedHeight_of_preceq` below: earlier reads
`finalized_height` off `DerivedStateAgrees` at a `DepReachableStore`, and the
named store carries the same agreement as the `DerivedView` component of
`Proofs.NamedStore.Coherent`, so the reader's finalized height is the NAMED height of
the named body behind its `F`.

Step 2 is the residual, isolated as `W4ProcessedFinalityAdvancePin`. It is the
only fact this pin still lacks, and it is a handler-level statement, not a
carrier-level one: see the Open at the end of this file.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Residual pin: an honest reader's own finalized block dominates the
finalized checkpoint of every named body the reader holds. This is the
invariant earlier establishes at each acceptance step through
`acceptedBlock_candidateFinality_preceq` (`AcceptedFinalityRun.lean`, blocked
class d) and `Protocol.stateBefore_F_mono`. -/
def W4ProcessedFinalityAdvancePin (S : Setup V) (rho : Run V) : Prop :=
  ∀ v ∈ rho.honest, ∀ (t : Time) (B : NamedBlock V),
    B ∈ (rho.storeAt S v t).bodies →
    Block.Preceq (derive_named S.E S.cfg B).F (rho.storeAt S v t).core.F

/-! ## 1. Named bodies of an honest reader -/

/-- Copied from the private `StoreFinalityRun.lean:149` (`run_bodies_stateAt`). -/
private theorem w4sfRunBodies_storeAt (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {v : V} (hv : v ∈ rho.honest) (t : Time) :
    ∀ D ∈ (rho.storeAt S v t).bodies, RunBlock S rho D := by
  obtain ⟨n, hn⟩ := Proofs.Bridges.stateAt_eq_stateBefore S sch t
  intro D hD
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
  simpa only [Run.storeAt, hn] using hD

private theorem w4sfRunBlockUnique
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- A run block whose erasure an honest reader holds in its tree is one of that
reader's named bodies. -/
theorem namedBody_of_mem_storeAt_T
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {B : NamedBlock V}
    (hBrun : RunBlock S rho B)
    (hmem : B.erase ∈ (rho.storeAt S v t).core.T) :
    B ∈ (rho.storeAt S v t).bodies := by
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.storeAt S v t) :=
    (Proofs.NamedRuntime.readAt_invariants S rho t v).1.1.1
  have himg : B.erase ∈ (rho.storeAt S v t).bodies.image NamedBlock.erase := by
    rw [← hcoh.1]
    exact hmem
  obtain ⟨D, hDb, hDe⟩ := Finset.mem_image.mp himg
  have hDrun : RunBlock S rho D :=
    w4sfRunBodies_storeAt S adm.toNamedScheduleWellFormed hv t D hDb
  have hDB : D = B := w4sfRunBlockUnique adm hDrun hBrun hDe
  exact hDB ▸ hDb

/-! ## 2. The reader's finalized height -/


/-- Named twin of `derived_height_le_finalized_height_of_preceq`
(`AcceptedFinalityRun.lean:367`, blocked class d). earlier reads the store's
finalized height through `DerivedStateAgrees` at a `DepReachableStore`; the
named store carries the same agreement as the `DerivedView` component of its
coherence, so the height is the NAMED height of the named body behind `F`. -/
theorem namedHeight_le_finalizedHeight_of_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {P : NamedBlock V}
    (hPrun : RunBlock S rho P)
    (hPne : P.erase ≠ Block.genesis)
    (hPF : Block.Preceq P.erase (rho.storeAt S v t).core.F) :
    (derive_named S.E S.cfg P).h ≤
      (rho.storeAt S v t).core.finalized_height := by
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.storeAt S v t) :=
    (Proofs.NamedRuntime.readAt_invariants S rho t v).1.1.1
  have hFmem : (rho.storeAt S v t).core.F ∈ (rho.storeAt S v t).core.T :=
    Proofs.NamedStoreBridge.finalizedInTree_readAt S rho t v
  have hFne : (rho.storeAt S v t).core.F ≠ Block.genesis := by
    intro hgenesis
    apply hPne
    apply Block.preceq_antisymm
    · simpa only [hgenesis] using hPF
    · exact Protocol.preceq_genesis P.erase
  have himg : (rho.storeAt S v t).core.F ∈
      (rho.storeAt S v t).bodies.image NamedBlock.erase := by
    rw [← hcoh.1]
    exact hFmem
  obtain ⟨FN, hFNb, hFNe⟩ := Finset.mem_image.mp himg
  have hFNrun : RunBlock S rho FN :=
    w4sfRunBodies_storeAt S adm.toNamedScheduleWellFormed hv t FN hFNb
  have hsigma : (rho.storeAt S v t).core.σ (rho.storeAt S v t).core.F =
      derive_named S.E S.cfg FN := by
    rw [← hFNe]
    exact hcoh.2.2.2.2 FN hFNb
  have hnamed : NamedBlock.Preceq P FN :=
    (namedPreceq_iff_erase_preceq S rho
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree hPrun hFNrun).mpr
      (by rw [hFNe]; exact hPF)
  unfold Protocol.Store.finalized_height
  rw [if_neg hFne, hsigma]
  exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed

/-! ## 3. The pin -/

/-- earlier's `commonFinalityAtConfirmation_of_proposedBlockCandidate`
(`RecurringFinalityRun.lean:1476`) in named form, over the one residual
handler-level advance. -/
theorem w4CommonFinalityAtConfirmationPin_of_duty
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {q0 : Round}
    (hduty : ∀ s : Slot, 0 < s →
      healingBoundaryTime S q0 < Protocol.proposal_time S.E s →
      S.E.proposer s ∈ rho.honest →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
        Protocol.CanonicalProposalDutyAt S rho s B)
    (hadvance : W4ProcessedFinalityAdvancePin S rho) :
    W4CommonFinalityAtConfirmationPin S rho q0 := by
  intro s B T h hs hafter hprop hhor hB hfin hpos hTne v hv
  have hlive : (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed =
      B.erase :=
    Protocol.storeAt_liveConfirmed_eq_proposedBlock_of_dutyExecution
      S adm hcom hhor (hduty s hs hafter hprop hhor B hB) hv
  have hmemT : B.erase ∈
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).core.T := by
    rw [← hlive]
    exact Proofs.NamedStoreBridge.liveConfirmed_mem_readAt S rho
      (Protocol.confirmation_time S.E s) v
  have hBrun : RunBlock S rho B :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore s hs hprop
      ((Protocol.proposal_time_le_confirmation_time S.E s).trans hhor) hB
  have hBbodies : B ∈ (rho.storeAt S v (Protocol.confirmation_time S.E s)).bodies :=
    namedBody_of_mem_storeAt_T S adm hv hBrun hmemT
  have hTF : Block.Preceq T
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).core.F := by
    rw [← hfin.1]
    exact hadvance v hv (Protocol.confirmation_time S.E s) B hBbodies
  refine ⟨hTF, ?_⟩
  obtain ⟨cp, hcpLe, hcpErase, hcpHeight⟩ :=
    namedCheckpoint_of_namedFinalizedAt S.E S.cfg hfin hpos
  have hcpRun : RunBlock S rho cp :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hcpLe
  have hcpNe : cp.erase ≠ Block.genesis := by
    rw [hcpErase]
    exact hTne
  have hcpF : Block.Preceq cp.erase
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).core.F := by
    rw [hcpErase]
    exact hTF
  have hle := namedHeight_le_finalizedHeight_of_preceq S adm hv hcpRun hcpNe hcpF
  rw [hcpHeight] at hle
  exact hle

#print axioms namedBody_of_mem_storeAt_T
#print axioms namedHeight_le_finalizedHeight_of_preceq

#print axioms w4CommonFinalityAtConfirmationPin_of_duty



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
