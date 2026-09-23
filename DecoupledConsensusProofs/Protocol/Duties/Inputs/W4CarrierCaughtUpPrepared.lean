module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.W4CarrierQuietPrepared
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainJustification

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Named high branch at a selected carrier

The high case compares the named height of the actual previous honest
opening with the named height of this carrier's opening. The previous
opening is a named ancestor of the new opening's parent. No erased
height comparison is used.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the previous honest opening is already at the carrier opening's
named height, the intervening parent and the previous opening are both on
that same height plateau. The ancestry input is the selected-carrier fact
`w4cr_previousOpening_namedPreceq_openingParent`. -/
theorem w4_caughtUp_previousAndParent_flatHeight
    (S : Setup V) {Pprev P0 : NamedBlock V}
    (hPrevParent : NamedBlock.Preceq Pprev P0.parent)
    (hHigh : (Protocol.derive_named S.E S.cfg P0).h ≤
      (Protocol.derive_named S.E S.cfg Pprev).h) :
    (Protocol.derive_named S.E S.cfg Pprev).h =
        (Protocol.derive_named S.E S.cfg P0).h ∧
      (Protocol.derive_named S.E S.cfg P0.parent).h =
        (Protocol.derive_named S.E S.cfg P0).h := by
  have hParentP0 : NamedBlock.Preceq P0.parent P0 := by
    cases P0 with
    | genesis => exact Proofs.NamedAncestry.named_self _
    | node parent slot root votes support rows proposer =>
        exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (Proofs.NamedAncestry.named_self parent)
  have hPrevParentHeight :=
    Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hPrevParent
  have hParentP0Height :=
    Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hParentP0
  constructor
  · exact Nat.le_antisymm
      (hPrevParentHeight.trans hParentP0Height) hHigh
  · exact Nat.le_antisymm hParentP0Height
      (hHigh.trans hPrevParentHeight)

#print axioms w4_caughtUp_previousAndParent_flatHeight

/-- If the carrier's own named proposal raises its parent's height, it is
already the height entry. This closes the recent-entry goal before any
timeout-maturity argument is considered. -/
theorem w4_caughtUp_recentEntry_of_parentRise
    (S : Setup V) (rho : Run V) (r : Round) {P0 : NamedBlock V}
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (hRise : (Protocol.derive_named S.E S.cfg P0.parent).h <
      (Protocol.derive_named S.E S.cfg P0).h) :
    CarrierRecentHeightEntryAt S rho r := by
  have hentry : (Protocol.derive_named S.E S.cfg P0).T_h = P0.erase := by
    cases P0 with
    | genesis =>
        simp only [NamedBlock.parent] at hRise
        exact False.elim ((Nat.lt_irrefl _) hRise)
    | node parent slot root votes support rows proposer =>
        have htrans : Protocol.derive_named S.E S.cfg
            (.node parent slot root votes support rows proposer) =
            Protocol.named_transition S.E S.cfg
              (Protocol.derive_named S.E S.cfg parent)
                (.node parent slot root votes support rows proposer) := rfl
        rcases Proofs.NamedEntryHeight.transition_height_entry_cases S.E S.cfg
          (Protocol.derive_named S.E S.cfg parent)
            (.node parent slot root votes support rows proposer) with
          ⟨hsame, -⟩ | ⟨-, hnew⟩
        · have hflat : (Protocol.derive_named S.E S.cfg
                (.node parent slot root votes support rows proposer)).h =
              (Protocol.derive_named S.E S.cfg parent).h := by
            rw [htrans]
            exact hsame
          rw [hflat] at hRise
          exact False.elim ((Nat.lt_irrefl _) hRise)
        · rw [htrans]
          exact hnew
  have hcanon : P0 = canonicalProposal S rho (S.hc.opening_slot r) := by
    have hspec := canonicalProposal_spec S rho (S.hc.opening_slot r)
    rw [hP0] at hspec
    exact Option.some.inj hspec
  rw [hcanon] at hentry
  exact carrierRecentHeightEntryAt_of_target_eq_opening S rho hentry

#print axioms w4_caughtUp_recentEntry_of_parentRise



/-- On the named height plateau, the predecessor's target and timeout
histories give the exact successor-target record at the previous action
read. This is earlier's `hrecord`, with named ancestry and the prepared record;
the same-height `nj` fact is the existing
`namedNj_eq_of_preceq_sameHeight`. -/
theorem w4_caughtUp_successorRecord_of_previousHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} {Pprev P0 : NamedBlock V}
    (hPrevParent : NamedBlock.Preceq Pprev P0.parent)
    (hHigh : (Protocol.derive_named S.E S.cfg P0).h ≤
      (Protocol.derive_named S.E S.cfg Pprev).h)
    (hP0nj : (Protocol.derive_named S.E S.cfg P0).nj = false)
    (hhistPrev : CanonicalHeightSourceHistoryAt S rho q0 (r - 1) Pprev)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h) :
    ∀ v ∈ rho.honest,
      SuccessorTargetRecordAt
        (rho.stateBeforeTime S (S.a (r - 1)) v).Λ
        (Protocol.derive_named S.E S.cfg P0).h
        (Protocol.derive_named S.E S.cfg P0.parent).T_h.root := by
  obtain ⟨hPrevHeight, hParentHeight⟩ :=
    w4_caughtUp_previousAndParent_flatHeight S hPrevParent hHigh
  have hPrevParentHeight : (Protocol.derive_named S.E S.cfg Pprev).h =
      (Protocol.derive_named S.E S.cfg P0.parent).h :=
    hPrevHeight.trans hParentHeight.symm
  have hPrevTarget := Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg
    hPrevParent hPrevParentHeight
  have hParentP0 : NamedBlock.Preceq P0.parent P0 := by
    cases P0 with
    | genesis => exact Proofs.NamedAncestry.named_self _
    | node parent slot root votes support rows proposer =>
        exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (Proofs.NamedAncestry.named_self parent)
  have hParentNj := NamedCheckpointAlgebra.namedNj_eq_of_preceq_sameHeight S.E S.cfg
    hParentP0 hParentHeight.symm
  have hPrevNj := NamedCheckpointAlgebra.namedNj_eq_of_preceq_sameHeight S.E S.cfg
    hPrevParent hPrevParentHeight.symm
  have hPrevNjFalse : (Protocol.derive_named S.E S.cfg Pprev).nj = false := by
    rw [← hPrevNj, ← hParentNj]
    exact hP0nj
  have htargetHistory := w4cr_targetHistory_of_heightHistory S adm hhistPrev
  have htimeoutHistory := w4cr_timeoutHistory_of_heightHistory S adm hhistPrev
  intro v hv
  constructor
  · rcases Option.eq_none_or_eq_some
        ((rho.stateBeforeTime S (S.a (r - 1)) v).Λ.legacy.target
          (Protocol.derive_named S.E S.cfg P0).h) with
      hnone | ⟨X, hX⟩
    · exact Or.inl hnone
    · obtain ⟨Q, -, hQPrev, hQHeight, hQTarget⟩ :=
        htargetHistory v hv _ X habove hX
      have hQsame : (Protocol.derive_named S.E S.cfg Q).h =
          (Protocol.derive_named S.E S.cfg Pprev).h :=
        hQHeight.trans hPrevHeight.symm
      have hentry := Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg
        hQPrev hQsame
      have hXT : X =
          (Protocol.derive_named S.E S.cfg P0.parent).T_h.root := by
        rw [← hQTarget, hentry, hPrevTarget]
      exact Or.inr (by rw [hXT] at hX; exact hX)
  · by_contra hnot
    have htrue : (rho.stateBeforeTime S (S.a (r - 1)) v).Λ.legacy.timeout
        (Protocol.derive_named S.E S.cfg P0).h = true := by
      simpa only [Bool.not_eq_false] using hnot
    obtain ⟨Q, -, hQPrev, hQHeight, hQnj⟩ :=
      htimeoutHistory v hv _ habove htrue
    have hQsame : (Protocol.derive_named S.E S.cfg Pprev).h =
        (Protocol.derive_named S.E S.cfg Q).h :=
      hPrevHeight.trans hQHeight.symm
    have hNjSame := NamedCheckpointAlgebra.namedNj_eq_of_preceq_sameHeight S.E S.cfg
      hQPrev hQsame
    rw [hPrevNjFalse, hQnj] at hNjSame
    exact Bool.noConfusion hNjSame

#print axioms w4_caughtUp_successorRecord_of_previousHistory

/-- A finality pair emitted by the predecessor action's time uses the
height-`H` target of the named previous honest opening. This is the
history-only part of `finalityPairTarget_eq_canonicalTarget`, whose existing
proof reads `CanonicalRegimeRoundAt.heightHistory` at a carrier; here the
predecessor is not assumed to be a carrier. -/
theorem w4_caughtUp_finalityPairTarget_of_previousHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {q0 m : Round} {Pprev : NamedBlock V} {H : Height}
    (hhistPrev : CanonicalHeightSourceHistoryAt S rho q0 m Pprev)
    (hPrevHeight : (Protocol.derive_named S.E S.cfg Pprev).h = H)
    (habove : honestHMaxAt S rho (S.a q0) < H)
    {a : NamedAttestation V} {ta : Time} {target : BlockId}
    (haHonest : a.val_index ∈ rho.honest)
    (haEmit : rho.emits S a.val_index (.attest a) ta)
    (hta : ta ≤ S.a m)
    (hpair : a.finality_pair = some ⟨H, target⟩) :
    target = (Protocol.derive_named S.E S.cfg Pprev).T_h.root := by
  have hfinality : FinalityTargetHeightSource S rho :=
    finalityTargetHeightSource_of_admissible S adm hbelow
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
  have hbBefore : S.a b.round < S.a m := by
    rw [← htbShape]
    exact htb.trans_le hta
  have hbm : b.round < m := (action_strictMono S).lt_iff_lt.mp hbBefore
  obtain ⟨Q, hsource, hQrun, hQPrev, hQheight⟩ :=
    hhistPrev b.round (Nat.le_of_lt hq0b) hbm
      b.val_index hbHonest _ hbHeight
  obtain ⟨Cfg, hCfg, hCfgHeight, hCfgTarget⟩ :=
    NamedActionSources.action_source S rho b.val_index b.round H target false
      hbPairAction
  obtain ⟨D, hDbody, hDerase, hDderive, -⟩ :=
    NamedActionSources.action_witness S rho b.val_index b.round Cfg hCfg
  have hsourceCfg : Q.erase = Cfg :=
    Option.some.inj (hsource.symm.trans hCfg)
  have hDQerase : D.erase = Q.erase := hDerase.trans hsourceCfg.symm
  have hDbodyPre : D ∈ (rho.stateBeforeTime S (S.a b.round) b.val_index).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hDbody
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a b.round)
  have hDrun : RunBlock S rho D := by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hbHonest (i := i)
    simpa only [hi] using hDbodyPre
  have hDQroot : D.root = Q.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root Q, hDQerase]
  have hDQ : D = Q :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D Q hDrun hQrun D Q
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self Q)) hDQroot
  have hQtarget : (Protocol.derive_named S.E S.cfg Q).T_h.root = target := by
    rw [← hDQ, ← hDderive]
    exact hCfgTarget
  have hsame := Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hQPrev
    (hQheight.trans hPrevHeight.symm)
  calc
    target = (Protocol.derive_named S.E S.cfg Q).T_h.root := hQtarget.symm
    _ = (Protocol.derive_named S.E S.cfg Pprev).T_h.root :=
      congrArg Block.root hsame

#print axioms w4_caughtUp_finalityPairTarget_of_previousHistory

/-- A stored lock and a same-action finality pair at the honest
predecessor's height both name its canonical target. The predecessor needs
only named height history, not a full carrier-round record. -/
theorem w4_caughtUp_lockAlignment_of_previousHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {q0 m : Round} {Pprev : NamedBlock V} {H : Height}
    (hhistPrev : CanonicalHeightSourceHistoryAt S rho q0 m Pprev)
    (hPrevHeight : (Protocol.derive_named S.E S.cfg Pprev).h = H)
    (habove : honestHMaxAt S rho (S.a q0) < H)
    (hpost : S.E.t_GST ≤ S.a m)
    (hhor : S.a m ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt
        (rho.stateBeforeTime S (S.a m) v).Λ
        (actionAttestationAt S rho v m).finality_pair
        H (Protocol.derive_named S.E S.cfg Pprev).T_h.root := by
  intro v hv
  constructor
  · intro X hlock
    obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a m)
    have hlockN : (rho.stateBefore S n v).record.legacy.lock H = some X := by
      rw [← hn]
      exact hlock
    obtain ⟨i, hi, ta, a, hevent, hemitted, hpair⟩ :=
      recordLock_finalityEmission_before_migration S rho v n hlockN
    have haEmit : rho.emits S v (.attest a) ta :=
      ⟨i, hevent, hemitted⟩
    have haHonest : a.val_index ∈ rho.honest := by
      rw [(Proofs.Optimistic.emits_attest_shape S haEmit).1]
      exact hv
    exact w4_caughtUp_finalityPairTarget_of_previousHistory S adm hbelow
      hhistPrev hPrevHeight habove haHonest
      (by simpa only [(Proofs.Optimistic.emits_attest_shape S haEmit).1] using haEmit)
      (le_of_lt (hbefore i _ hi hevent)) hpair
  · intro p hfp hpHeight
    have haEmit := honest_emits_exact_actionAttestationAt S adm hv m hhor hpost
    rcases p with ⟨height, target⟩
    change height = H at hpHeight
    subst height
    have haHonest :
        (actionAttestationAt S rho v m).val_index ∈ rho.honest := by
      rw [(actionAttestationAt_shape S rho v m).1]
      exact hv
    have haEmit' : rho.emits S
        (actionAttestationAt S rho v m).val_index
        (.attest (actionAttestationAt S rho v m)) (S.a m) := by
      rw [(actionAttestationAt_shape S rho v m).1]
      exact haEmit
    exact w4_caughtUp_finalityPairTarget_of_previousHistory S adm hbelow
      hhistPrev hPrevHeight habove haHonest haEmit'
      (show S.a m ≤ S.a m from le_rfl) hfp

#print axioms w4_caughtUp_lockAlignment_of_previousHistory

private theorem w4cu_actionBodyRun
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) : RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

/-! ### The opening duty's fresh predecessor row

earlier does not put the predecessor row on the opening parent's chain. It uses
the opening proposal's selected row source. The named duty selects
`poolAndCarried`; its pool half needs only exact processing and the SG window.
The two private helpers below are local, `w4cu_`-prefixed copies of the
corresponding bodies in `RawHeightCoverageRun` and
`SeedActionRowCarriageRun`. -/

private theorem w4cu_fgSource_mem_actionStore
    (S : Setup V) {rho : Run V} (v : V) (r : Round) {Q : Block V}
    (hsource : actionFGSource S (actionReadAt S rho v r) = some Q) :
    Q ∈ (actionStoreAt S rho v r).st.core.T := by
  let n := actionReadAt S rho v r
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  have hround : S.hc.round_of n.st.core.s = r := by
    simpa only [n] using actionStoreAt_round S rho v r
  change Protocol.fg_source_with (NamedProfile.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing (S.hc.round_of n.st.core.s)
    (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc
      n.st.core.toHealing (S.hc.round_of n.st.core.s)) = some Q at hsource
  rw [hround] at hsource
  simpa only [n] using
    (NamedActionSources.frame_fg_source_mem S n.cache n.st r hinv hsource)

private theorem w4cu_exactActionRow_mem_namedProcessed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {a : NamedAttestation V}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) (S.a a.round))
    (hprocessed : a.erase ∈
      (Protocol.proposerDutyStore S rho s).processed_attestations S.hc) :
    a ∈ Protocol.NamedProposalRows.processedRows S.hc
      (proposerReadAt S rho s).st := by
  let st := (proposerReadAt S rho s).st
  have hPool : NamedStore.PoolView st := by
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (Protocol.proposal_time S.E s)
          (S.E.proposer s)).1.1.1.2.2.2.1
  have hmap := NamedProposalRows.processed_rows_erasure S.hc st hPool
  have hmemMap : a.erase ∈
      (Protocol.NamedProposalRows.processedRows S.hc st).map
        NamedAttestation.erase := by
    rw [hmap]
    simpa only [st, Protocol.proposerDutyStore, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
        hprocessed
  obtain ⟨b, hb, hberase⟩ := List.mem_map.mp hmemMap
  have hbFlat := hb
  rw [Protocol.NamedProposalRows.processedRows] at hbFlat
  obtain ⟨k, -, hbk⟩ := List.mem_flatMap.mp hbFlat
  have hrounds : Proofs.NamedStoreBridge.SgRowRounds st := by
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.sgRowRounds_stateBeforeTime S rho
          (Protocol.proposal_time S.E s) (S.E.proposer s)
  have hbr : b.round = k := hrounds k b hbk
  have hbOwn : b ∈ st.sg_rows b.round := by
    rw [hbr]
    exact hbk
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.proposal_time S.E s)
  have hbN : b ∈
      (rho.stateBefore S n (S.E.proposer s)).st.sg_rows b.round := by
    rw [← congrFun hn (S.E.proposer s)]
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hbOwn
  have hbval : b.val_index = a.val_index :=
    congrArg CombinedAttestation.val_index hberase
  have hbHon : b.val_index ∈ rho.honest := by
    rw [hbval]
    exact haHon
  obtain ⟨_, _, _, _, _, hbEmit⟩ :=
    Proofs.Bridges.heldArePastEmissions_of_admissibleCore
      S adm.toNamedAdmissibleCore n (S.E.proposer s) hbN hbHon
  have hbEmit' : rho.emits S a.val_index
      (Object.attest b) (S.a b.round) := by
    simpa only [hbval] using hbEmit
  have hround : b.round = a.round :=
    congrArg CombinedAttestation.round hberase
  have hba : b = a := Proofs.Optimistic.emits_attest_unique S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
    hbEmit' hemit hround
  simpa only [st, hba] using hb

private theorem w4cu_predecessorRow_mem_selectedOpeningRows
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round}
    (hprop : S.E.proposer (S.hc.opening_slot r) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot r) ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hdelay : S.a (r - 1) + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    {v : V} (hv : v ∈ rho.honest) :
    actionAttestationAt S rho v (r - 1) ∈
      Protocol.NamedProposalRows.select .poolAndCarried S.hc
        (proposerReadAt S rho (S.hc.opening_slot r)).st := by
  let a := actionAttestationAt S rho v (r - 1)
  have hactionHor : S.a (r - 1) ≤ rho.horizon :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelay.trans hhor)
  have hemitV : rho.emits S v (Object.attest a) (S.a (r - 1)) := by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm hv (r - 1) hactionHor (by assumption)
  have haVal : a.val_index = v :=
    (actionAttestationAt_shape S rho v (r - 1)).1
  have haRound : a.round = r - 1 :=
    (actionAttestationAt_shape S rho v (r - 1)).2.1
  have hemit : rho.emits S a.val_index
      (Object.attest a) (S.a a.round) := by
    simpa only [haVal, haRound] using hemitV
  have hprocessed : a.erase ∈
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot r)).processed_attestations S.hc := by
    exact honestAttestation_mem_processedAtProposal_after_gst S adm hprop hhor
      (by simpa only [haVal] using hv)
      (by simpa only [haVal] using hemitV) hpost hdelay
  have haProcessed := w4cu_exactActionRow_mem_namedProcessed S adm
    (by simpa only [haVal] using hv) hemit hprocessed
  apply List.mem_append_left
  simp only [Protocol.NamedProposalRows.poolRows, List.mem_filter]
  refine ⟨haProcessed, ?_⟩
  rw [haRound]
  unfold Protocol.ProposalRows.inWindow
  have hslot : (proposerReadAt S rho
      (S.hc.opening_slot r)).st.core.s = S.hc.opening_slot r := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.Optimistic.slotOf_proposal_time S.E (S.hc.opening_slot r)
  rw [hslot, round_of_opening_slot_eq_schedule S.hc r, decide_eq_true_eq]
  constructor
  · have heta : 1 ≤ S.hc.η_SG := S.hc.η_SG_ge_one
    exact Nat.sub_le_sub_left heta r
  · exact Nat.sub_le r 1

/-! ### Proper target rows after predecessor source equality -/

theorem w4_caughtUp_targetRows_of_source
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {q0 r : Round} {Pprev P0 : NamedBlock V}
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (hPprev : proposedBlockAt S rho
      (S.hc.opening_slot (r - 1)) = some Pprev)
    (hPprevRun : RunBlock S rho Pprev)
    (hPrevParent : NamedBlock.Preceq Pprev P0.parent)
    (hHigh : (Protocol.derive_named S.E S.cfg P0).h ≤
      (Protocol.derive_named S.E S.cfg Pprev).h)
    (hP0nj : (Protocol.derive_named S.E S.cfg P0).nj = false)
    (hhistPrev : CanonicalHeightSourceHistoryAt S rho q0 (r - 1) Pprev)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hpostPrev : S.E.t_GST ≤ S.a (r - 1))
    (hsource : ∀ v ∈ rho.honest,
      actionFGSource S (actionReadAt S rho v (r - 1)) = some Pprev.erase) :
    ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v (r - 1)).height_pair =
        NamedHeightPair.vote
          (Protocol.derive_named S.E S.cfg P0.parent).h
          (Protocol.derive_named S.E S.cfg P0.parent).T_h.root false := by
  obtain ⟨hPrevHeight, hParentHeight⟩ :=
    w4_caughtUp_previousAndParent_flatHeight S hPrevParent hHigh
  have hPrevParentHeight :
      (Protocol.derive_named S.E S.cfg Pprev).h =
        (Protocol.derive_named S.E S.cfg P0.parent).h :=
    hPrevHeight.trans hParentHeight.symm
  have hPrevTarget := Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg
    hPrevParent hPrevParentHeight
  have hParentP0 : NamedBlock.Preceq P0.parent P0 := by
    cases P0 with
    | genesis => exact Proofs.NamedAncestry.named_self _
    | node parent slot root votes support rows proposer =>
        exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (Proofs.NamedAncestry.named_self parent)
  have hParentNj := NamedCheckpointAlgebra.namedNj_eq_of_preceq_sameHeight
    S.E S.cfg hParentP0 hParentHeight.symm
  have hPrevNj := NamedCheckpointAlgebra.namedNj_eq_of_preceq_sameHeight
    S.E S.cfg hPrevParent hPrevParentHeight.symm
  have hPrevNjFalse :
      (Protocol.derive_named S.E S.cfg Pprev).nj = false := by
    rw [← hPrevNj, ← hParentNj]
    exact hP0nj
  have hrecord := w4_caughtUp_successorRecord_of_previousHistory S adm
    hPrevParent hHigh hP0nj hhistPrev habove
  have haligned := w4_caughtUp_lockAlignment_of_previousHistory S adm hbelow
    hhistPrev hPrevHeight habove hpostPrev hprevHor
  intro v hv
  let ast := actionReadAt S rho v (r - 1)
  let Lambda := (rho.stateBeforeTime S (S.a (r - 1)) v).Λ
  have hsourceRead := hsource v hv
  obtain ⟨C, hCbody, hCerase, hCderive, -⟩ :=
    NamedActionSources.action_witness S rho v (r - 1) Pprev.erase hsourceRead
  have hCrun : RunBlock S rho C :=
    w4cu_actionBodyRun S adm hv (r := r - 1) hCbody
  have hCeq : C = Pprev := by
    apply adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      C Pprev hCrun hPprevRun C Pprev
      (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Pprev))
    calc
      C.root = C.erase.root := (Proofs.NamedWire.erase_root C).symm
      _ = Pprev.erase.root := by rw [hCerase]
      _ = Pprev.root := Proofs.NamedWire.erase_root Pprev
  have hσPprev : ast.st.core.σ Pprev.erase =
      Protocol.derive_named S.E S.cfg Pprev := by
    simpa only [ast, hCeq] using hCderive
  have hround : S.hc.round_of ast.st.core.s = r - 1 := by
    simpa only [ast] using actionStoreAt_round S rho v (r - 1)
  have hsourceRound :
      Protocol.fg_source_with (NamedProfile.gradeContract ast.cache)
        S.E S.hc ast.st.core.toHealing
        (S.hc.round_of ast.st.core.toHealing.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract ast.cache)
          S.E S.hc ast.st.core.toHealing
          (S.hc.round_of ast.st.core.toHealing.s)) = some Pprev.erase := by
    simpa only [actionFGSource, ast] using hsourceRead
  have hQheight : (ast.st.core.σ Pprev.erase).h =
      (Protocol.derive_named S.E S.cfg P0.parent).h := by
    rw [hσPprev, hPrevParentHeight]
  have hQtarget : (ast.st.core.σ Pprev.erase).T_h.root =
      (Protocol.derive_named S.E S.cfg P0.parent).T_h.root := by
    rw [hσPprev]
    exact congrArg Block.root hPrevTarget
  have hQnj : (ast.st.core.σ Pprev.erase).nj = false := by
    rw [hσPprev]
    exact hPrevNjFalse
  have hpair := round_action_height_pair_target_of_record
    (NamedProfile.gradeContract ast.cache) S.E S.hc (S.node v)
    ast.st.core.toHealing Lambda hsourceRound hQheight hQtarget hQnj
    (by simpa only [hParentHeight] using hrecord v hv)
    (by simpa only [ast, Lambda, hParentHeight, hPrevTarget] using haligned v hv)
  simpa only [actionAttestationAt, ast, Lambda] using hpair

#print axioms w4_caughtUp_targetRows_of_source

/- The row/coverage tail is closed once the carrier-chain layer supplies the
   two named parent facts consumed by `actionAttestationAt_coveredAtProposal_of_chainRows`.
   They stay explicit here because the current public opening-carrier pin does
   not itself state parent-store membership or chain-row carriage. -/


/- The earlier-shaped named coverage route. The predecessor source is the held
   target witness. The exact predecessor row is either already on the
   opening parent's chain or is carried freshly by the opening proposal's
   `poolAndCarried` payload. No parent-store or parent-chain residual is
   required. -/
theorem w4_caughtUp_coverage_of_source
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {q0 r : Round} {Pprev P0 : NamedBlock V}
    (hqr : q0 + 2 < r)
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (hPprev : proposedBlockAt S rho
      (S.hc.opening_slot (r - 1)) = some Pprev)
    (hPprevRun : RunBlock S rho Pprev)
    (hPrevParent : NamedBlock.Preceq Pprev P0.parent)
    (hHigh : (Protocol.derive_named S.E S.cfg P0).h ≤
      (Protocol.derive_named S.E S.cfg Pprev).h)
    (hP0nj : (Protocol.derive_named S.E S.cfg P0).nj = false)
    (hhistPrev : CanonicalHeightSourceHistoryAt S rho q0 (r - 1) Pprev)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hpostPrev : S.E.t_GST ≤ S.a (r - 1))
    (hsource : ∀ v ∈ rho.honest,
      actionFGSource S (actionReadAt S rho v (r - 1)) = some Pprev.erase) :
    NamedTargetedHonestActionProposalCoverageAt S rho (r - 1) P0
      (Protocol.derive_named S.E S.cfg P0.parent).h
      (Protocol.derive_named S.E S.cfg P0.parent).T_h.root := by
  obtain ⟨hPrevHeight, hParentHeight⟩ :=
    w4_caughtUp_previousAndParent_flatHeight S hPrevParent hHigh
  have hPrevParentHeight :
      (Protocol.derive_named S.E S.cfg Pprev).h =
        (Protocol.derive_named S.E S.cfg P0.parent).h :=
    hPrevHeight.trans hParentHeight.symm
  have hPrevTarget := Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg
    hPrevParent hPrevParentHeight
  have hrows := w4_caughtUp_targetRows_of_source S adm hbelow hP0 hPprev
    hPprevRun hPrevParent hHigh hP0nj hhistPrev habove hprevHor hpostPrev hsource
  have hrpos : 0 < r := Nat.zero_lt_of_lt
    ((Nat.le_add_left 2 q0).trans_lt hqr)
  have hpredLt : r - 1 < r := Nat.sub_lt hrpos Nat.one_pos
  have hdelay : S.a (r - 1) + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r) :=
    Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hpredLt
  have hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon :=
    (Protocol.proposal_time_mono S.E
      (Nat.le_add_right (S.hc.opening_slot r) 2)).trans
      ((Protocol.proposal_time_le_confirmation_time S.E _).trans
        hround.inHorizon)
  have hprop : S.E.proposer (S.hc.opening_slot r) ∈ rho.honest :=
    hround.carrier.1
  have hpayload := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract
      (proposerReadAt S rho (S.hc.opening_slot r)).cache)
    .poolAndCarried S.E S.hc
    (S.node (S.E.proposer (S.hc.opening_slot r)))
    (proposerReadAt S rho (S.hc.opening_slot r)).st P0 hP0
  intro v hv
  have hCcore : Pprev.erase ∈
      (actionStoreAt S rho v (r - 1)).st.core.T :=
    w4cu_fgSource_mem_actionStore S v (r - 1) (hsource v hv)
  have hselected := w4cu_predecessorRow_mem_selectedOpeningRows S adm
    hprop hproposalHor hpostPrev hdelay hv
  have hrow := hrows v hv
  by_cases hchain : actionAttestationAt S rho v (r - 1) ∈
      Protocol.NamedProposalRows.chainRows P0.parent
  · have hcovered := actionAttestationAt_coveredAtProposal_of_chainRows S adm
      (H := (Protocol.derive_named S.E S.cfg P0.parent).h)
      (T := (Protocol.derive_named S.E S.cfg P0.parent).T_h.root)
      hPprevRun hPrevParentHeight (congrArg Block.root hPrevTarget)
      hPrevParent rfl hprevHor hpostPrev hv hCcore hchain (Or.inl hrow)
    exact ⟨hcovered, Or.inl hrow⟩
  · have hown : actionAttestationAt S rho v (r - 1) ∈ P0.attestations := by
      rw [hpayload.2.2.2.2.2.2.1]
      apply NamedProposalRows.mem_proposalRows_of_unique P0.parent _ _ hselected hchain
      intro b hb hval hround
      have haVal : (actionAttestationAt S rho v (r - 1)).val_index = v :=
        (actionAttestationAt_shape S rho v (r - 1)).1
      exact honest_selected_row_unique S adm (S.hc.opening_slot r) hselected hb
        (by simpa only [haVal] using hv) hval hround
    exact ⟨Or.inr hown, Or.inl hrow⟩

#print axioms w4_caughtUp_coverage_of_source

/- Exact proper-target coverage fires `targetReady` before the timeout gate.
   Thus the opening crosses its parent's height without a timeout-maturity
   premise, and the opening is its own recent height entry. -/
theorem w4_caughtUp_recentEntry_of_source
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {q0 r : Round} {Pprev P0 : NamedBlock V}
    (hqr : q0 + 2 < r)
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (hPprev : proposedBlockAt S rho
      (S.hc.opening_slot (r - 1)) = some Pprev)
    (hPprevRun : RunBlock S rho Pprev)
    (hPrevParent : NamedBlock.Preceq Pprev P0.parent)
    (hHigh : (Protocol.derive_named S.E S.cfg P0).h ≤
      (Protocol.derive_named S.E S.cfg Pprev).h)
    (hP0nj : (Protocol.derive_named S.E S.cfg P0).nj = false)
    (hhistPrev : CanonicalHeightSourceHistoryAt S rho q0 (r - 1) Pprev)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hpostPrev : S.E.t_GST ≤ S.a (r - 1))
    (hsource : ∀ v ∈ rho.honest,
      actionFGSource S (actionReadAt S rho v (r - 1)) = some Pprev.erase) :
    CarrierRecentHeightEntryAt S rho r := by
  obtain ⟨hPrevHeight, hParentHeight⟩ :=
    w4_caughtUp_previousAndParent_flatHeight S hPrevParent hHigh
  have hparentP0 : NamedBlock.Preceq P0.parent P0 := by
    cases P0 with
    | genesis => exact Proofs.NamedAncestry.named_self _
    | node parent slot root votes support rows proposer =>
        exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (Proofs.NamedAncestry.named_self parent)
  have hParentNj := NamedCheckpointAlgebra.namedNj_eq_of_preceq_sameHeight
    S.E S.cfg hparentP0 hParentHeight.symm
  have hParentNjFalse :
      (Protocol.derive_named S.E S.cfg P0.parent).nj = false := by
    rw [← hParentNj]
    exact hP0nj
  have hcoverage := w4_caughtUp_coverage_of_source S adm hbelow hqr hround
    hP0 hPprev hPprevRun hPrevParent hHigh hP0nj hhistPrev habove
    hprevHor hpostPrev hsource
  have hrows := w4_caughtUp_targetRows_of_source S adm hbelow hP0 hPprev
    hPprevRun hPrevParent hHigh hP0nj hhistPrev habove hprevHor hpostPrev hsource
  have hcoverage' : NamedHonestActionProposalCoverageAt S rho (r - 1) P0
      (Protocol.derive_named S.E S.cfg P0.parent).h
      (Protocol.derive_named S.E S.cfg P0.parent).T_h.root := by
    intro v hv
    exact ⟨(hcoverage v hv).1, Or.inl (hrows v hv)⟩
  have hstep := namedOrdinaryHeightTargetProposal_of_actionCoverage S hbelow
    hP0 hcoverage' rfl rfl hParentNjFalse hrows
  apply w4_caughtUp_recentEntry_of_parentRise S rho r hP0
  rw [hstep.2]
  exact Nat.lt_succ_self _

#print axioms w4_caughtUp_recentEntry_of_source

/- The caught-up checkpoint arm in the exact shape used by the selected
   first-half composer. The callback already carries the named `+1` parent,
   so this adapter does not require the full execution record. -/
theorem w4_caughtUp_checkpointReady_of_source
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {delayExtra : Nat}
    (hdelay : TimeoutDelayBound S delayExtra)
    {q0 r : Round} {Pprev P0 P1 : NamedBlock V}
    (hqr : q0 + 2 < r)
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    (hparent : NamedBlock.parent? P1 = some P0)
    (hPprev : proposedBlockAt S rho
      (S.hc.opening_slot (r - 1)) = some Pprev)
    (hPprevRun : RunBlock S rho Pprev)
    (hPrevParent : NamedBlock.Preceq Pprev P0.parent)
    (hHigh : (Protocol.derive_named S.E S.cfg P0).h ≤
      (Protocol.derive_named S.E S.cfg Pprev).h)
    (hP0nj : (Protocol.derive_named S.E S.cfg P0).nj = false)
    (hhistPrev : CanonicalHeightSourceHistoryAt S rho q0 (r - 1) Pprev)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hpostPrev : S.E.t_GST ≤ S.a (r - 1))
    (hsource : ∀ v ∈ rho.honest,
      actionFGSource S (actionReadAt S rho v (r - 1)) = some Pprev.erase) :
    NamedJustifiedAt S.E S.cfg P1
        (Protocol.derive_named S.E S.cfg P0).T_h
        (Protocol.derive_named S.E S.cfg P0).h ∨
      ((Protocol.derive_named S.E S.cfg P1).h =
          (Protocol.derive_named S.E S.cfg P0).h ∧
        (Protocol.derive_named S.E S.cfg P1).T_h =
          (Protocol.derive_named S.E S.cfg P0).T_h) := by
  have hentry := w4_caughtUp_recentEntry_of_source S adm hbelow hqr hround
    hP0 hPprev hPprevRun hPrevParent hHigh hP0nj hhistPrev habove
    hprevHor hpostPrev hsource
  have hcanon : P0 = canonicalProposal S rho (S.hc.opening_slot r) := by
    have hspec := canonicalProposal_spec S rho (S.hc.opening_slot r)
    rw [hP0] at hspec
    exact Option.some.inj hspec
  unfold CarrierRecentHeightEntryAt at hentry
  rw [← hcanon] at hentry
  have hslot : P1.slot = S.hc.opening_slot r + 1 :=
    proposedBlockAt_slot S rho (S.hc.opening_slot r + 1) hP1
  have hgate : ¬ (Protocol.derive_named S.E S.cfg P0).T_h.slot +
      S.cfg.timeoutDelay ≤ P1.slot := by
    rw [hslot]
    exact timeoutGate_closed_at_plusOne_of_enteredRoundPred
      (delayExtra := delayExtra) S hdelay hentry
  exact NamedCheckpointAlgebra.namedCheckpointReady_of_parent_of_gate_closed
    S.E S.cfg hparent hgate hP0nj

#print axioms w4_caughtUp_checkpointReady_of_source

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
