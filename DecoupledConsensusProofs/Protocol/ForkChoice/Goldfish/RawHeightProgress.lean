module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.GSTZero
public import DecoupledConsensusProofs.Objects.BlockVisibilityCore
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotoneCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Objects.FixedHeightRootCore
public import DecoupledConsensusProofs.Execution.RawHeightAdapters
public import DecoupledConsensusProofs.Protocol.ChainState.RecoveryCrossingCore

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Raw height progress from an arbitrary honest frontier

design note (proof 1659): `RunBlock` and the height
derivation of a processed carrier now live only over named bodies
(`NamedBlock`), never the retired `derived_state`/`DepReachableStore` route.
`HonestHMaxCarrierAt`'s `runBlock` and `exactHeight` fields merge into one
`namedWitness` existential naming that body, since both need the same witness
to state at all (statement change, ledger row `HonestHMaxCarrierAt`).

The private
`exactHeightCarrier_finalizedCompatibleAtEarlierEvent` and the four public
`HonestHMaxCarrierAt` relay producers are available below. They use the named
twin `NamedFinalizationBridge.named_no_off_can_finalization` and the named
state-before-time store producers. Their old goals are kept below as comments,
verbatim except for mechanical renames that do not change the proof route.

`commonFinalizedFloor_preceq_honestProposalParent` has no cone consumer (only
an off-cone one, `RecoveryCrossingHealingRun`) and cannot be mechanically
restated: its conclusion names the retired `Internal.proposedBlock`, and
`DecoupledConsensusProofs/Availability/ProposalCoreRun.lean` documents that
bridging the ordinary composed head this proof actually establishes
(`Protocol.proposedParent`, ungraded `Protocol.get_head`) to the real
`proposedBlockAt`'s parent (grade-contract based) is "a genuine new
equivalence claim, not a mechanical restatement" — retired there under,
Open class d, not guessed at. Under  it is moved byte-exact to
`the compatibility layer`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Internal.HealingSurface
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- A processed run block that attains the exact public honest maximum at one
honest inclusive read.

design note: the run witness is a `NamedBlock`, since `RunBlock` and the height
derivation now live only over named bodies; the prior `runBlock` and
`exactHeight` fields merge into one existential `namedWitness` naming that
body (ledger row: statement change). -/
structure HonestHMaxCarrierAt
    (S : Setup V) (rho : Run V) (t : Time) (H : Height)
    (holder : V) (carrier : Block V) : Prop where
  holderHonest : holder ∈ rho.honest
  processed : carrier ∈ (rho.storeAt S holder t).T
  namedWitness : ∃ D : NamedBlock V, D.erase = carrier ∧ RunBlock S rho D ∧
    (Protocol.derive_named S.E S.cfg D).h = H

/-- Every named derivation has height at least one: genesis derives the initial
chain state, and each node either keeps its parent's height or advances it.
Reproved here (short private induction, same pattern as
`Protocol.one_le_derive_named_h`) so a single-file compile of this module
does not need that file's own import chain. -/
private theorem one_le_derive_named_h
    (E : Env V) (cfg : Protocol.HeightConfig) :
    ∀ B : NamedBlock V, 1 ≤ (Protocol.derive_named E cfg B).h := by
  intro B
  induction B with
  | genesis => exact Nat.le_refl 1
  | node p sl r gv sup rows pr ih =>
      rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p sl r gv sup rows pr with
        hstay | hup
      · rw [hstay]; exact ih
      · rw [hup]; exact le_trans ih (Nat.le_succ _)


/-- The finite honest supremum is attained by a processed block at its exact
height. The positivity argument uses an arbitrary honest reachable store, whose
processed maximum witness has protocol height at least one.

design note: the carrier is a `NamedBlock` read from
`Proofs.NamedStoreBridge.maximum_carrier_stateBefore` and
`exists_honest_exactHMaxCarrierAtPrefix`, never through the retired
`DepReachableStore`/`hMaxInTree_depReachable`/`derivedStateAgrees_depReachable`
route. -/
theorem honestHMaxCarrierAt_of_eq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {t : Time} {H : Height}
    (hH : honestHMaxAt S rho t = H) :
    ∃ holder carrier, HonestHMaxCarrierAt S rho t H holder carrier := by
  let n := inclusiveEventIndex rho t
  have hprefix : honestHMaxBeforeIndex S rho n = H := by
    rw [← honestHMaxAt_eq_honestHMaxBeforeIndex
      S adm.toNamedScheduleWellFormed t]
    exact hH
  obtain ⟨u, hu⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  obtain ⟨W, _hWmem, hWheight⟩ := Proofs.NamedStoreBridge.maximum_carrier_stateBefore S rho n u
  have hHpos : 1 ≤ H := by
    calc
      1 ≤ (Protocol.derive_named S.E S.cfg W).h :=
        one_le_derive_named_h S.E S.cfg W
      _ = (rho.stateBefore S n u).st.h_max := hWheight
      _ ≤ honestHMaxBeforeIndex S rho n :=
        localHMax_le_honestHMaxBeforeIndex S rho n hu
      _ = H := hprefix
  have hpred : H - 1 + 1 = H := Nat.sub_add_cancel hHpos
  have hprefixSucc : honestHMaxBeforeIndex S rho n = H - 1 + 1 := by
    rw [hprefix, hpred]
  obtain ⟨v, hv, carrier, hcarrier, hrun, hheight⟩ :=
    exists_honest_exactHMaxCarrierAtPrefix S adm n (H - 1) hprefixSucc
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.stateBefore S n v).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1.1.1
  have hcarrierT : carrier.erase ∈ (rho.stateBefore S n v).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem _ hcarrier
  refine ⟨v, carrier.erase, hv, ?_,
    ⟨carrier, rfl, hrun, by simpa only [hpred] using hheight⟩⟩
  rw [storeAt_eq_stateBefore_inclusiveEventIndex
    S adm.toNamedScheduleWellFormed v t]
  exact hcarrierT

/-! The complete earlier goals for the available cluster remain below. The
comparison step is supplied by
`NamedFinalizationBridge.named_no_off_can_finalization`; every other ingredient
is supplied by the named state-before-time producers:
`Proofs.Bridges.storeFinalizationOnChain_stateBefore` supplies the named finalization
carrier together with its `h_F < h_max` bound directly (folding what was
a a separate `NoHighJustifications`/`JustificationBelowMax` chain into one
call), `RunBlock`/`derive_named` read at the named carrier, and
`adm.toNamedRootCollisionFree.root_injective` gives run-wide uniqueness of a
named body by its erasure (transports a global named witness into a
store-local `.bodies` reader). -/



/-! ## Named finalization compatibility -/

/-- Two `RunBlock` witnesses that erase to the same public block are the same
named body. -/
private theorem runBlock_unique_of_erase_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])



/-- An earlier honest finalization is below an exact-height named body. -/
private theorem exactHeightCarrier_finalizedBelowAtPrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {H : Height} {D : NamedBlock V}
    (hcarrierRun : RunBlock S rho D)
    (hcarrierHeight : (Protocol.derive_named S.E S.cfg D).h = H)
    {w : V} (hw : w ∈ rho.honest)
    {i : Nat} {cutoff : Time}
    (hi : i ≤ (rho.events.filter
      (fun e => decide (e.time < cutoff))).length)
    (hcap : (rho.storeBeforeTime S w cutoff).h_max ≤ H) :
    Block.Preceq (rho.stateBefore S i w).st.core.F D.erase := by
  let n := strictEventIndex rho cutoff
  have hiN : i ≤ n := by simpa only [strictEventIndex] using hi
  have hstore : rho.storeBeforeTime S w cutoff =
      (rho.stateBefore S n w).st := by
    rw [storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed w cutoff]
  have hpreCap : (rho.stateBefore S i w).st.core.h_max ≤ H :=
    (stateBefore_hMax_mono S rho w hiN).trans (by
      rw [← hstore]
      exact hcap)
  obtain ⟨C, hC, hCF, hCheight⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho i w
  have hCrun : RunBlock S rho C :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hw hC
  have hcrossed : (Protocol.derive_named S.E S.cfg C).h_F <
      (Protocol.derive_named S.E S.cfg D).h := by
    calc
      (Protocol.derive_named S.E S.cfg C).h_F <
          (rho.stateBefore S i w).st.core.h_max := hCheight
      _ ≤ H := hpreCap
      _ = (Protocol.derive_named S.E S.cfg D).h := hcarrierHeight.symm
  have hpreceq := NamedFinalizationBridge.finalized_preceq_of_height_lt
    S rho D C hsb adm.toNamedRootCollisionFree hcarrierRun hCrun hcrossed
  simpa only [hCF] using hpreceq

/-- A bounded relay makes a carrier visible at any honest reader whose local
frontier has not passed its height. -/
theorem HonestHMaxCarrierAt.visibleAtReader_after_oneDelay_of_localCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {t read : Time} {H : Height} {holder : V} {carrier : Block V}
    (hcarrier : HonestHMaxCarrierAt S rho t H holder carrier)
    (hpost : S.E.t_GST ≤ t)
    (hdelay : t + 1 + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    (hcap : (rho.storeBeforeTime S w read).h_max ≤ H) :
    carrier ∈ (rho.storeBeforeTime S w read).T := by
  obtain ⟨D, hDerase, hDrun, hDheight⟩ := hcarrier.namedWitness
  let sourceRead := t + 1
  let relayCut := sourceRead + S.E.Δ
  have hsource : carrier ∈ (rho.storeBeforeTime S holder sourceRead).T := by
    have hstate := stateBeforeTime_eq_stateAt_pred
      S adm.toNamedScheduleWellFormed sourceRead
    have hpred : sourceRead - 1 = t := by
      simp [sourceRead]
    change carrier ∈ (NamedRun.stateBeforeTime S rho sourceRead holder).st.core.T
    rw [congrFun hstate holder, hpred]
    exact hcarrier.processed
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed sourceRead
  have hsourceN : carrier ∈ (rho.stateBefore S n holder).st.core.T := by
    simpa only [Run.storeBeforeTime, hn] using hsource
  obtain hgen | ⟨D', hD'erase, i, hi, ta, hacc⟩ :=
    Protocol.acceptsAt_block_of_processed_erased S rho holder n hsourceN
  · simpa only [hgen] using (Protocol.genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedScheduleWellFormed w read read).1
  · have hD'body : D' ∈ (rho.stateBefore S (i + 1) holder).st.bodies := by
      simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
    have hD'run : RunBlock S rho D' :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hcarrier.holderHonest hD'body
    have hEq : D' = D :=
      runBlock_unique_of_erase_eq adm hD'run hDrun
        (hD'erase.trans hDerase.symm)
    have hD'height : (Protocol.derive_named S.E S.cfg D').h = H := by
      simpa only [hEq] using hDheight
    have hta : ta < sourceRead := by
      obtain ⟨_, ⟨e, he, _, het⟩⟩ := hacc.1
      simpa only [het] using hbefore i e hi he
    have hD'pos : 0 < D'.slot := by
      rw [← Proofs.NamedWire.erase_slot]
      exact Nat.zero_lt_of_lt
        (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
    have hrelayRead : relayCut ≤ read := by
      simpa only [relayCut, sourceRead, add_assoc] using hdelay
    have hrelayHor : relayCut ≤ rho.horizon := hrelayRead.trans hreadHor
    have hFhist : Protocol.BlockFinalizedBelowAtDeliveriesBefore
        S rho w D' relayCut := by
      intro j hj
      exact exactHeightCarrier_finalizedBelowAtPrefix
        S adm hsb hD'run hD'height hw
        (hj.trans (strict_filter_length_mono rho hrelayRead)) hcap
    have hadmit : Protocol.AdmittedBefore
        S rho w D'.erase relayCut :=
      Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hcarrier.holderHonest hw hD'pos hacc hta
          (hpost.trans (by simp [sourceRead])) rfl hrelayHor hFhist
    have hvisible := Protocol.admittedBefore_mem_and_stamp_at
      S adm.toNamedScheduleWellFormed hadmit hrelayRead
    simpa only [hD'erase] using hvisible.1

/-- Preserve the public no-rise interface as a reader-local relay wrapper. -/
theorem HonestHMaxCarrierAt.visibleToAll_after_oneDelay_of_noRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {t read : Time} {H : Height} {holder : V} {carrier : Block V}
    (hcarrier : HonestHMaxCarrierAt S rho t H holder carrier)
    (hpost : S.E.t_GST ≤ t)
    (hdelay : t + 1 + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon)
    (hcap : honestHMaxAt S rho read ≤ H) :
    ∀ w ∈ rho.honest,
      carrier ∈ (rho.storeBeforeTime S w read).T := by
  intro w hw
  exact hcarrier.visibleAtReader_after_oneDelay_of_localCap S adm hsb
    hpost hdelay hreadHor hw
    (((storeBeforeTime_hMax_le_storeAt
        S adm.toNamedScheduleWellFormed w read).trans
      (localHMax_le_honestHMaxAt S rho read hw)).trans hcap)

/-- Every honest reader reaches a relayed carrier's height. -/
theorem HonestHMaxCarrierAt.localFrontier_ge_after_oneDelay
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {t read : Time} {H : Height} {holder : V} {carrier : Block V}
    (hcarrier : HonestHMaxCarrierAt S rho t H holder carrier)
    (hpost : S.E.t_GST ≤ t)
    (hdelay : t + 1 + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon) :
    ∀ w ∈ rho.honest, H ≤ (rho.storeBeforeTime S w read).h_max := by
  intro w hw
  by_cases hbound : H ≤ (rho.storeBeforeTime S w read).h_max
  · exact hbound
  have hmem := hcarrier.visibleAtReader_after_oneDelay_of_localCap S adm hsb
    hpost hdelay hreadHor hw (Nat.le_of_lt (Nat.lt_of_not_ge hbound))
  obtain ⟨D, hDmem, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho read w hmem
  obtain ⟨D', hD'erase, hD'run⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime
      S adm.toNamedScheduleWellFormed hw read hmem
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed read
  have hDmemN : D ∈ (rho.stateBefore S n w).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hDmem
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hw hDmemN
  have hEq : D = D' :=
    runBlock_unique_of_erase_eq adm hDrun hD'run
      (hDerase.trans hD'erase.symm)
  obtain ⟨Dcarrier, hDcarrierErase, hDcarrierRun, hDcarrierHeight⟩ :=
    hcarrier.namedWitness
  have hEqCarrier : D' = Dcarrier :=
    runBlock_unique_of_erase_eq adm hD'run hDcarrierRun
      (hD'erase.trans hDcarrierErase.symm)
  have hheight : (Protocol.derive_named S.E S.cfg D').h = H := by
    simpa only [hEqCarrier] using hDcarrierHeight
  have hmax := Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime S rho read w D hDmem
  rw [hEq, hheight] at hmax
  exact hmax

/-- After one full carrier delay and under a public no-rise cap, every honest
strict store contains the exact carrier and has local frontier exactly `H`. -/
theorem HonestHMaxCarrierAt.visibleWithExactFrontier_after_oneDelay_of_noRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {t read : Time} {H : Height} {holder : V} {carrier : Block V}
    (hcarrier : HonestHMaxCarrierAt S rho t H holder carrier)
    (hpost : S.E.t_GST ≤ t)
    (hdelay : t + 1 + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon)
    (hcap : honestHMaxAt S rho read ≤ H) :
    ∀ w ∈ rho.honest,
      carrier ∈ (rho.storeBeforeTime S w read).T ∧
        (rho.storeBeforeTime S w read).h_max = H := by
  intro w hw
  have hmem := hcarrier.visibleToAll_after_oneDelay_of_noRise
    S adm hsb hpost hdelay hreadHor hcap w hw
  refine ⟨hmem, ?_⟩
  have hlower := hcarrier.localFrontier_ge_after_oneDelay S adm hsb
    hpost hdelay hreadHor w hw
  have hupper : (rho.storeBeforeTime S w read).h_max ≤ H :=
    ((storeBeforeTime_hMax_le_storeAt
        S adm.toNamedScheduleWellFormed w read).trans
      (localHMax_le_honestHMaxAt S rho read hw)).trans hcap
  exact Nat.le_antisymm hupper hlower





/-- The confirmation update immediately before an action preserves the exact
finality-gadget root read by that action. -/
private theorem actionStoreAt_fgRoot_eq_healStoreAt
    (S : Setup V) (rho : Run V) (w : V) (r : Round) :
    Protocol.get_fg_root
        (actionStoreAt S rho w r).toHealing.toFG =
      Protocol.get_fg_root (healStoreAt S rho w r).toFG := by
  simpa only [healStoreAt] using
    actionStoreAt_fgRoot_eq_storeBeforeTime S rho w r

/-- The exact root-side obstruction at an action read. -/
def FixedHeightActionRootObstructionAt
    (S : Setup V) (rho : Run V) (H : Height) (w : V) (r : Round)
    (carrier : Block V) : Prop :=
  (Block.Preceq carrier
      (Protocol.get_fg_root
        (actionStoreAt S rho w r).toHealing.toFG) ∧
    carrier ∉ Protocol.get_filtered_block_tree
      (actionStoreAt S rho w r).toHealing.toFG) ∨
  FixedHeightRootInterferenceAtRead S rho H w (S.a r) carrier

private theorem runBlock_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {w : V} (hw : w ∈ rho.honest) {t : Time} {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S w t).bodies) : RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch t
  have hD' : D ∈ (rho.stateBefore S n w).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hw hD'

private theorem namedWitness_at_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {t : Time} {carrier : Block V} {H : Height}
    {D : NamedBlock V} (hDerase : D.erase = carrier) (hDrun : RunBlock S rho D)
    (hDheight : (Protocol.derive_named S.E S.cfg D).h = H)
    (hmem : carrier ∈ (rho.storeBeforeTime S w t).T) :
    ∃ D' : NamedBlock V, D' ∈ (rho.storeBeforeTime S w t).bodies ∧
      D'.erase = carrier ∧ (Protocol.derive_named S.E S.cfg D').h = H := by
  obtain ⟨D', hD'mem, hD'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t w hmem
  have hD'run : RunBlock S rho D' :=
    runBlock_of_mem_storeBeforeTime S adm.toNamedScheduleWellFormed hw hD'mem
  have hEq : D = D' :=
    runBlock_unique_of_erase_eq adm hDrun hD'run (hDerase.trans hD'erase.symm)
  exact ⟨D', hD'mem, hD'erase, hEq ▸ hDheight⟩


/-- At an exact-height honest action read, the carrier is active, the exact
root-side obstruction is exposed, or the public raw frontier has risen.

design note: `hcarrier.namedWitness` supplies the global named body directly to
`fixedHeightRootInterferenceAtRead_of_interference` (no store-local membership
needed there); `heightFilterInterference_lt_honestHMaxAt` does need a body
retained at this exact read, so `namedWitness_at_storeBeforeTime` transports
the same witness there via run-wide erasure uniqueness. -/
theorem HonestHMaxCarrierAt.filteredAtAction_or_rootObstruction_or_hMaxRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    (hsb : SlashableBound S rho)
    {t : Time} {H : Height} {holder : V} {carrier : Block V}
    (hcarrier : HonestHMaxCarrierAt S rho t H holder carrier)
    {w : V} (hw : w ∈ rho.honest) {r : Round}
    (hreadHor : S.a r ≤ rho.horizon)
    (hmem : carrier ∈ (rho.storeBeforeTime S w (S.a r)).T)
    (hfrontier : (rho.storeBeforeTime S w (S.a r)).h_max = H) :
    carrier ∈ Protocol.get_filtered_block_tree
        (actionStoreAt S rho w r).toHealing.toFG ∨
      FixedHeightActionRootObstructionAt S rho H w r carrier ∨
      H < honestHMaxAt S rho (S.a r) := by
  obtain ⟨D, hDerase, hDrun, hDheight⟩ := hcarrier.namedWitness
  by_cases hfiltered : carrier ∈ Protocol.get_filtered_block_tree
      (actionStoreAt S rho w r).toHealing.toFG
  · exact Or.inl hfiltered
  by_cases hrebase : Block.Preceq carrier
      (Protocol.get_fg_root
        (actionStoreAt S rho w r).toHealing.toFG)
  · exact Or.inr (Or.inl (Or.inl ⟨hrebase, hfiltered⟩))
  have hnotQuiet :
      ¬ FinalityFilterNoninterferenceAtRead
        S rho w (S.a r) carrier := by
    intro hquiet
    rcases hquiet with hroot | hactive
    · apply hrebase
      rw [actionStoreAt_fgRoot_eq_healStoreAt S rho w r]
      simpa only [healStoreAt] using hroot
    · apply hfiltered
      rw [actionStoreAt_filteredTree S rho w r]
      simpa only [healStoreAt] using hactive
  rcases (not_finalityFilterNoninterferenceAtRead_iff
      S rho w (S.a r) carrier).mp hnotQuiet with hroot | hheight
  · exact Or.inr (Or.inl (Or.inr
      (fixedHeightRootInterferenceAtRead_of_interference
        S adm hfb hsb hw hreadHor hmem hDerase hDrun
          (le_of_eq hDheight.symm) hfrontier hroot)))
  · obtain ⟨D', hD'mem, hD'erase, hD'height⟩ :=
      namedWitness_at_storeBeforeTime S adm hw hDerase hDrun hDheight hmem
    exact Or.inr (Or.inr
      (heightFilterInterference_lt_honestHMaxAt
        S adm hw hD'mem (le_of_eq hD'height.symm)
          (by rw [hD'erase]; exact hheight)))




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
