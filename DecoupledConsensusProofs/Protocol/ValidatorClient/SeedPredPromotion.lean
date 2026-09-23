module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.SeedActionQ2
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedOpeningWindow
public import DecoupledConsensusProofs.Protocol.Grades.LifecycleActionSource
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierFirst
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeiling
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedAdoption
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawExactHeightSeed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The `M - 1` opening case of the gate-off seed (named runtime)

When the opening proposal of a carrier round sits one height below the public
frontier, the round's own action rows carry the missing height to the *next*
carrier round's opening proposal.

The route deliberately never names an interior block. The rows of round `q`
are emitted at the round action, which is the opening slot's confirmation
instant; the block they name is the round's opening proposal `B`, at height
`M - 1`. Those same rows are still resolved at the opening proposal of a later
carrier round `q'`, because `B` is below every honest round-`q` action carrier
and each honest action attestation travels with its carrier. If the selected
parent at `q'` is still at height `M - 1`, the coverage forces the proposal at
`q'` to height `M`; if the parent has already reached `M`, the proposal is at
`M` under the public no-rise branch. Either way the opening of `q'` is at the
exact frontier height, which is what the seed's third outcome consumes.

Two hypotheses of the existing lifecycle-row chain are weakened here. The
grade of the row round is only ever serves to know that *some* grade-2 block is
selected at each honest action read, so `SeedRoundGradedAt.selected` replaces
the common grade; and the coverage step uses the carrier form, whose ancestry
input is the lifecycle's own `ActionCarriersCover`.

## The named restatement (design note)

Every proposal is a bound named witness `proposedBlockAt … = some B`, heights
are `Protocol.derive_named`, the action read is the prepared
`actionReadAt`, its selected grade is `PhaseGrades.nodeQ2`, its source is
`PhaseGrades.nodeFGSource`, and the emitted row is a `NamedHeightPair.vote`
whose boolean is the timeout bit. the prior `CarrierRetryRun` import is dropped:
that module still reads the retired total `Internal.proposedBlock` and the erased
`CombinedAttestation` row, so its compiled artefact is stale and its coverage
theorem cannot be consumed at the named row type.

## Pinned producers (PRE-BUILDING)

Seven producers of this route have no live named declaration: they survive only
inside the  earlier comments of `SeedPromotionRun`, `SeedCeilingRun`,
`SeedFlushRun` and `RawHeightCoverageRun`. Each is taken here as an `_of_…`
hypothesis stating exactly the named fact its producer will supply, so the
route is complete the moment those land:

* (closed) the round's selected grade-2 block at the action store is the
  prepared read's own frozen candidate;
* `_of_selectedActionQ2_namedG1` — that candidate carries the round's G1 grade
  at the G1 domain read (the named twin of `G2_imp_G1` across the two reads);
* `_of_actionRead_namedDerivation` — the prepared action read derives the
  opening proposal exactly as `derive_named` does;
* `_of_gateOff_actionOwnLock_at_pred_none` — the gate-off own lock at `M - 1`
  is empty (retired `gateOff_actionOwnLock_at_pred_none`);
* `_of_gateOff_sgProposalLifecyclePacket_of_roundCeiling` — Claim 4 at the
  selected opening (retired `gateOff_sgProposalLifecyclePacket_of_roundCeiling`);
* `_of_openingProposal_preceq_nextOpeningParent` — the persisted grade, the
  action-carrier cover and the opening alignment put the round-`q` proposal
  below the round-`q'` opening parent as *named* blocks (retired
  `gradeFormsAt_persists_through_gateOffActionWindow`,
  `actionCarriersCover_of_gradeFormsAt`, `openingAnchorsAligned_of_roundCeiling`);
* `_of_actionRowsOnNextOpeningParentChain` — exact action-row
  coverage at the later opening read lifts the proposal one height above its
  parent (retired `HonestActionProposalCoverageAt`,
  `actionAttestationAt_coveredAtProposal_of_carrier` and
  `proposedBlock_height_eq_succ_of_actionCoverage`).
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (HeightConfig)
open Protocol (own_lock)
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- **Record-lock provenance over the named runtime.** A lock recorded at a
height traces back to an earlier honest tick whose emitted attestation carries
the finality pair at that height.

Re-homed here from `MigrationResidualsRun`: importing that module from this one
closes an import cycle through `CarrierRetryRun` and back into the seed cone.
The proof is its own, byte for byte. -/
private theorem recordLock_finalityEmission_before_migration
    (S : Setup V) (rho : Run V) (v : V) :
    ∀ (n : Nat) {H : Height} {T : BlockId},
      (rho.stateBefore S n v).record.legacy.lock H = some T →
        ∃ (i : Nat), i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
          rho.events[i]? = some (Event.tick v t) ∧
            Object.attest a ∈
              (on_tick_emit S v (rho.stateBefore S i v) t).2 ∧
            a.finality_pair = some ⟨H, T⟩ := by
  intro n
  induction n with
  | zero =>
      intro H T hlock
      exact absurd hlock (by
        simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
          NamedNode.initial, Protocol.NamedRecord.initial,
          Protocol.Record.initial])
  | succ n ih =>
      intro H T hlock
      change (NamedRun.stateBefore S rho (n + 1) v).record.legacy.lock H =
        some T at hlock
      cases hpre : (rho.stateBefore S n v).record.legacy.lock H with
      | some X =>
          have hmono :
              (rho.stateBefore S (n + 1) v).record.legacy.lock H = some X :=
            stateBefore_lock_mono S rho v (n + 1) (Nat.le_succ n) hpre
          have hXT : X = T := by
            rw [hlock] at hmono
            exact (Option.some.inj hmono).symm
          subst X
          obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ := ih hpre
          exact ⟨i, Nat.lt_succ_of_lt hi, t, a, hevent, hemitted, hpair⟩
      | none =>
          change (NamedRun.stateBefore S rho n v).record.legacy.lock H =
            none at hpre
          have hstep := congrFun (Proofs.NamedRuntime.stateBefore_succ S rho n) v
          cases hevent : rho.events[n]? with
          | none =>
              rw [hstep, hevent] at hlock
              simp only [Option.toList, List.foldl_nil] at hlock
              exact absurd hlock (by rw [hpre]; simp)
          | some e =>
              cases e with
              | tick u t =>
                  by_cases huv : u = v
                  · subst u
                    have hpost :
                        (on_tick_emit S v (rho.stateBefore S n v) t).1.record.legacy.lock H =
                          some T := by
                      rw [← stateBefore_succ_record S rho hevent]
                      exact hlock
                    obtain ⟨a, hemitted, hpair⟩ :=
                      Protocol.on_tick_emit_lock_introduced
                        S v (rho.stateBefore S n v) t hpre hpost
                    exact ⟨n, Nat.lt_succ_self n, t, a, hevent,
                      hemitted, hpair⟩
                  · rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_of_ne (Ne.symm huv)] at hlock
                    exact absurd hlock (by rw [hpre]; simp)
              | deliver u o t =>
                  by_cases huv : u = v
                  · subst u
                    rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_self] at hlock
                    change (NamedNode.process S
                      (NamedRun.stateBefore S rho n v) o).record.legacy.lock H =
                        some T at hlock
                    rw [NamedNode.process_record_eq] at hlock
                    exact absurd hlock (by rw [hpre]; simp)
                  · rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_of_ne (Ne.symm huv)] at hlock
                    exact absurd hlock (by rw [hpre]; simp)

/-! ## Named parent steps -/

/-- A retained named parent precedes the erased proposal it belongs to. -/
private theorem seedPredParent_preceq_proposedBlockAt
    (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B) :
    Block.Preceq (proposedParent S rho s) B.erase := by
  obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho s hB
  cases B with
  | genesis => cases hp
  | node parent slot root votes support rows proposer =>
      have hparent : parent = p := Option.some.inj hp
      subst p
      apply Protocol.preceq_of_parent?
      change some parent.erase = some (proposedParent S rho s)
      exact congrArg some hpe


/-! ## The lifecycle action source from a selected grade alone -/

/-- **The lifecycle proposal is the height-pair source of every honest action
of its round.** This is the named `lifecycleAction_fgSource_eq_block` with the
round's grade weakened to what the proof actually consumes: at the reader's own
prepared action read some grade-2 block is selected. A grade that forms at
every honest read is one way to get that; the seed's producer obligation gives
it directly. -/
theorem seedLifecycleAction_fgSource_eq_block_of_selected
    (S : Setup V) {rho : Run V}
    {q : Round} (hq : 0 < q) {P : NamedBlock V} {v : V} (hv : v ∈ rho.honest)
    {Q2 : Block V}
    (hQ2 : nodeQ2 S (actionReadAt S rho v q) q = some Q2)
    (_of_selectedActionQ2_namedG1 : namedG1At S rho v q Q2)
    (hpacket : NamedSGProposalLifecyclePacket S rho (q - 1)
      (S.hc.opening_slot q - 1) P) :
    nodeFGSource S (actionReadAt S rho v q) q = some P.erase := by
  have hqPred : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))
  have hQ2G1 : namedG1At S rho v (q - 1 + 1) Q2 := by
    simpa only [hqPred] using _of_selectedActionQ2_namedG1
  have hQ2parent : Block.Preceq Q2
      (proposedParent S rho (S.hc.opening_slot q)) := by
    simpa only [hqPred] using hpacket.liveG1Parent v hv Q2 hQ2G1
  have hproposal : proposedBlockAt S rho (S.hc.opening_slot q) = some P := by
    simpa only [hqPred] using hpacket.proposal
  have hparentBlock : Block.Preceq
      (proposedParent S rho (S.hc.opening_slot q)) P.erase :=
    seedPredParent_preceq_proposedBlockAt S rho _ hproposal
  have hQ2P : Block.Preceq Q2 P.erase :=
    Block.preceq_trans hQ2parent hparentBlock
  have hLive : (actionReadAt S rho v q).st.core.live_confirmed = P.erase := by
    simpa only [hqPred] using hpacket.lifecycle.liveConfirmed v hv
  have hLiveHealing :
      (actionReadAt S rho v q).st.core.toHealing.live_confirmed = P.erase := by
    change (actionReadAt S rho v q).st.core.live_confirmed = P.erase
    exact hLive
  have hclear : nodeClear S (actionReadAt S rho v q) q P.erase = true := by
    simpa only [hqPred] using hpacket.g0ClearAtAction v hv
  have hQ2' : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionReadAt S rho v q).cache) S.E S.hc
      (actionReadAt S rho v q).st.core.toHealing q = some Q2 := hQ2
  have hwalk : Protocol.deepest_clear (some Q2) P.erase
      ((NamedProfile.gradeContract (actionReadAt S rho v q).cache).read S.E S.hc
        (actionReadAt S rho v q).st.core.toHealing q).clear = some P.erase :=
    deepest_clear_eq_tip (floor := some Q2) (C := P.erase)
      (by simpa using hQ2P) hclear
  rw [nodeFGSource, Protocol.fg_source_with.eq_def, hQ2', hLiveHealing]
  simp only [hwalk]


/-! ## The `M - 1` opening pushes the next carrier's opening to height `M` -/



/-! ## The action's own lock at the predecessor height -/

/-- The height carried by the action's own finality pair is at or below the
reader's own justified height at the action read.

earlier's route over the named store: the pair's height is the justified height of
a block the action read has processed, that block lifts to a retained named
body, and the named justification bound caps it. -/
private theorem seedActionFinalityPair_height_le_preJustification
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho)
    (v : V) (r : Round) {H : Height} {T : BlockId}
    (hpair : (actionAttestationAt S rho v r).finality_pair = some ⟨H, T⟩) :
    H ≤ (rho.storeBeforeTime S v (S.a r)).h_j := by
  have hJ : (rho.stateBeforeTime S (S.a r) v).st.core.J ∈
      (rho.stateBeforeTime S (S.a r) v).st.core.T :=
    Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho (S.a r) v
  have hF : (rho.stateBeforeTime S (S.a r) v).st.core.F ∈
      (rho.stateBeforeTime S (S.a r) v).st.core.T :=
    Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime S rho (S.a r) v
  obtain ⟨Hd, hHd, hHdHeight⟩ :=
    round_action_head_mem_frame (actionReadAt S rho v r).cache
      S.E S.hc (S.node v) (actionReadAt S rho v r).st.core
      (actionReadAt S rho v r).record hJ hF hpair
  obtain ⟨Hn, hHnbody, hHnerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) v hHd
  have hsigma : (rho.stateBeforeTime S (S.a r) v).st.core.σ Hn.erase =
      Protocol.derive_named S.E S.cfg Hn :=
    Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho (S.a r) v Hn hHnbody
  have hnoHigh : Internal.NamedNoHighJustifications S.E S.cfg
      (rho.stateBeforeTime S (S.a r) v).st :=
    NamedJustificationBound.noHighJustifications_stateBeforeTime S rho (S.a r) v
  have hHeight : (Protocol.derive_named S.E S.cfg Hn).h_j = H := by
    rw [← hsigma, hHnerase]
    exact hHdHeight
  rw [← hHeight]
  exact hnoHigh Hn hHnbody

/-- An emitted attestation's finality-pair height is at or below the emitter's
justified height just before the emitting tick. -/
private theorem seedFinalityEmissionHeight_le_stateBeforeIndex
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i : Nat} {v : V} {t : Time} {a : NamedAttestation V}
    {H : Height} {T : BlockId}
    (hi : rho.events[i]? = some (Event.tick v t))
    (hmem : Object.attest a ∈
      (on_tick_emit S v (rho.stateBefore S i v) t).2)
    (hpair : a.finality_pair = some ⟨H, T⟩) :
    H ≤ (rho.stateBefore S i v).st.h_j := by
  have hemit : NamedRun.emits S rho v (Object.attest a) t := ⟨i, hi, hmem⟩
  have htime : t = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
  subst t
  have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi
  obtain ⟨j, hj, hact⟩ := Proofs.Optimistic.attest_eq_of_mem_on_tick_emit S hemit
  have hbeforeJ : NamedRun.stateBefore S rho j v =
      NamedRun.stateBeforeTime S rho (S.a a.round) v :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj
  rw [hbeforeJ] at hact
  have hown : actionAttestationAt S rho v a.round = a := hact
  have hle := seedActionFinalityPair_height_le_preJustification S adm v a.round
    (by rw [hown]; exact hpair)
  rw [hbefore]
  exact hle

/-- A lock recorded at a height traces to an earlier emission at that height,
so the height is at or below the reader's own justified height now. -/
private theorem seedRecordLock_height_le_preJustification
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) {H : Height} {T : BlockId}
    (hlock : (rho.stateBeforeTime S (S.a r) v).record.legacy.lock H = some T) :
    H ≤ (rho.storeBeforeTime S v (S.a r)).h_j := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  have hlockN : (rho.stateBefore S n v).record.legacy.lock H = some T := by
    rw [← hn]
    exact hlock
  obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ :=
    recordLock_finalityEmission_before_migration S rho v n hlockN
  have hle : H ≤ (rho.stateBefore S i v).st.h_j :=
    seedFinalityEmissionHeight_le_stateBeforeIndex S adm hevent hemitted hpair
  have hmono := stateBefore_h_j_mono S rho v (Nat.le_of_lt hi)
  have hleN : H ≤ (rho.stateBefore S n v).st.h_j := hle.trans hmono
  rw [← hn] at hleN
  exact hleN

/-- Either source of the validator's own lock at a height is capped by its own
justified height at the action read. -/
private theorem seedActionOwnLock_height_le_preJustification
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) {H : Height} {T : BlockId}
    (hlock : Protocol.own_lock
      (rho.stateBeforeTime S (S.a r) v).record.legacy H
      (actionAttestationAt S rho v r).finality_pair = some T) :
    H ≤ (rho.storeBeforeTime S v (S.a r)).h_j := by
  cases hfp : (actionAttestationAt S rho v r).finality_pair with
  | none =>
      have hrecord :
          (rho.stateBeforeTime S (S.a r) v).record.legacy.lock H = some T := by
        simpa only [Protocol.own_lock, hfp] using hlock
      exact seedRecordLock_height_le_preJustification S adm v r hrecord
  | some p =>
      rcases p with ⟨h, target⟩
      by_cases hh : h = H
      · subst h
        have htarget : target = T := by
          apply Option.some.inj
          simpa only [Protocol.own_lock, hfp, ↓reduceIte] using hlock
        subst target
        exact seedActionFinalityPair_height_le_preJustification S adm v r hfp
      · have hrecord :
            (rho.stateBeforeTime S (S.a r) v).record.legacy.lock H = some T := by
          simpa only [Protocol.own_lock, hfp, hh, ↓reduceIte] using hlock
        exact seedRecordLock_height_le_preJustification S adm v r hrecord

/-- **At a gate-off action read the validator's own lock at the predecessor
height is absent.** A current or persisted lock traces to a finality-pair
emission at that height, which contradicts the gate-off justification bound. -/
theorem gateOff_actionOwnLock_at_pred_none
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) {M : Height}
    (hgateOff : (rho.storeBeforeTime S v (S.a r)).h_j + 2 ≤ M) :
    Protocol.own_lock (actionReadAt S rho v r).record.legacy (M - 1)
      (actionAttestationAt S rho v r).finality_pair = none := by
  cases hlock : Protocol.own_lock (actionReadAt S rho v r).record.legacy
      (M - 1) (actionAttestationAt S rho v r).finality_pair with
  | none => rfl
  | some T =>
      exfalso
      have hle : M - 1 ≤ (rho.storeBeforeTime S v (S.a r)).h_j :=
        seedActionOwnLock_height_le_preJustification S adm v r hlock
      have key : ∀ a b : Nat, a + 2 ≤ b → b - 1 ≤ a → False := by
        intro a b h1 h2; omega
      exact key _ _ hgateOff hle



#print axioms seedPredParent_preceq_proposedBlockAt
#print axioms seedLifecycleAction_fgSource_eq_block_of_selected

end HealingSurface
end Proofs
end DecoupledConsensusModel

end

