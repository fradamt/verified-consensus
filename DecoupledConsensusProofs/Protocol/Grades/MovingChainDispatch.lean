module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.MovingChainStep
public import DecoupledConsensusProofs.Execution.RecoveryFreshAnchorAtRead
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFreshGradeProvenance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryRelativeMajorityProvenance
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingBoundaryCanonicality
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge

@[expose] public section

/-!
# Moving-chain read dispatch

This module converts the full-store root-side geometry of a moving endpoint
into the primed Goldfish inputs used by the slot fold. At a vote duty, the
preceding honest vote cone supplies frozen processing. At a confirmation
read, the full filtered tree is already the candidate tree.
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




private theorem movingDispatch_confAnchorWith_preceq_of_genuine
    (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (s : Slot) (D : Block V)
    (hD : GenuineConfirmationWith contract E hc st s D) :
    Block.Preceq (Protocol.confAnchorWith contract E hc st) D := by
  have hwalk : Protocol.confWalkWith contract E hc st s = D := by
    have hselected := hD.selected
    rw [Protocol.update_confirmation_with_live_confirmed, if_pos hD.genuine]
      at hselected
    exact hselected
  have hfloor : Block.Preceq
      (Protocol.confAnchorWith contract E hc st)
      (Protocol.confWalkWith contract E hc st s) :=
    Protocol.ghost_preceq
      (Protocol.confAnchorWith contract E hc st)
      (Protocol.confTree st) (Protocol.confScore E st s)
      (Protocol.confEligible E st s)
  rwa [hwalk] at hfloor

private theorem movingDispatch_actionAnchor_eq_openingConfAnchor
    (S : Setup V) (rho : Run V) (v : V) (q : Round) :
    PhaseGrades.nodeAnchor S (actionReadAt S rho v q) q =
      Protocol.confAnchorWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a q)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)) := by
  have hcore := actionStoreAt_eq_update_confirmation_confStore S rho v q
  have hs : (actionStoreAt S rho v q).st.core.s =
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).s := by
    rw [hcore]
    rfl
  have hround : S.hc.round_of
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).s = q := by
    rw [← hs]
    exact actionStoreAt_round S rho v q
  show ((NamedProfile.gradeContract (actionStoreAt S rho v q).cache).read
      S.E S.hc (actionStoreAt S rho v q).st.core.toHealing q).anchor = _
  rw [Protocol.confAnchorWith, Protocol.get_sg_root_with, hround, hcore]
  rfl

/-! ## Named prepared action dispatch -/

/-- Named action-event facts at a Section 7 tick. The previous route selected from
the erased action store; this route selects from the prepared action read and
keeps the confirmation contract carried by that read. -/
theorem movingEventFacts_action_of_previousCarrierCeiling_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (_hfb : BelowOneThird S rho.honest)
    {i : Nat}
    {q : Round} (hq : 0 < q)
    (_hpost : S.E.t_GST ≤ S.a (q - 1))
    (_hcut : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest)
    (hi : rho.events[i]? = some (Event.tick v (S.a q)))
    {D : Block V}
    (hD : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadAt S rho v (S.a q)).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
        (S.hc.opening_slot q) D)
    {Next : Block V}
    (_hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) Next)
    (hDNext : Block.Preceq D Next) :
    Block.Preceq (actionSGBlockAt S rho v q) Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next := by
  have hstate := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi
  have hqHor : S.a q ≤ rho.horizon := by
    simpa only [Event.time] using
      (adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.in_horizon
        (Event.tick v (S.a q)) (List.mem_of_getElem? hi)).2
  have hDlive : (actionReadAt S rho v q).st.core.live_confirmed = D := by
    change (actionStoreAt S rho v q).st.core.live_confirmed = D
    rw [actionStoreAt_eq_update_confirmation_confStore, hD.selected]
  have hDliveNext : Block.Preceq
      (actionReadAt S rho v q).st.core.live_confirmed Next := by
    rw [hDlive]
    exact hDNext
  have hanchorD : Block.Preceq
      (PhaseGrades.nodeAnchor S (actionReadAt S rho v q) q) D := by
    rw [movingDispatch_actionAnchor_eq_openingConfAnchor S rho v q]
    exact movingDispatch_confAnchorWith_preceq_of_genuine _ S.E S.hc _ _ _ hD
  let n := actionReadAt S rho v q
  let st := n.st.core.toHealing
  let grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st q
  have hround : S.hc.round_of st.s = q := by
    simpa only [st, n] using actionStoreAt_round S rho v q
  have hround' : S.hc.round_of
      (actionReadAt S rho v q).st.core.s = q := by
    simpa only [n, st] using hround
  have hanchorGrades : Block.Preceq grades.anchor D := by
    simpa only [grades, n, PhaseGrades.nodeAnchor, PhaseGrades.nodeRead] using hanchorD
  have hfgAnchor : Block.Preceq
      (Protocol.get_fg_root st.toFG) grades.anchor := by
    dsimp only [grades, DecoupledConsensusModel.Protocol.frameGradeRead,
      DecoupledConsensusModel.Protocol.anchor]
    cases hframe : (DecoupledConsensusModel.Protocol.readFrame n.cache st q).g1 with
    | none =>
        simp only [hframe]
        exact Block.preceq_self _
    | some hroot =>
        cases hroot with
        | none =>
            simp only [hframe]
            exact Block.preceq_self _
        | some root =>
            cases hactive : DecoupledConsensusModel.Protocol.activePrefix
                (Protocol.get_filtered_block_tree st.toFG) root with
            | none =>
                simp only [hframe, hactive]
                exact Block.preceq_self _
            | some A =>
                have hmem := Proofs.Engine.deepest?_mem hactive
                have hAfilter : A ∈
                    Protocol.get_filtered_block_tree st.toFG :=
                  (Finset.mem_filter.mp hmem).1
                have hrootA := Proofs.Records.preceq_get_fg_root_of_mem_filtered hAfilter
                simpa only [hframe, hactive, Option.getD_some] using hrootA
  have hsgRootD : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract n.cache) S.E S.hc st q) D := by
    simpa only [grades, n, DecoupledConsensusModel.Protocol.frameGradeRead,
      PhaseGrades.nodeAnchor, PhaseGrades.nodeRead] using hanchorD
  have hQNext : ∀ Q : Block V,
      Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
        S.E S.hc st q = some Q → Block.Preceq Q Next := by
    intro Q hQ
    have hQanchor : Block.Preceq Q grades.anchor := by
      exact actionQ2_preceq_actionAnchor S adm.toNamedAdmissibleCore hv hq hqHor
        (by simpa only [grades, n, hround] using hQ)
    exact Block.preceq_trans hQanchor
      (Block.preceq_trans hanchorGrades hDNext)
  have hcarrierNext : Block.Preceq (actionSGBlockAt S rho v q) Next := by
    have heq : actionSGBlockAt S rho v q = Protocol.currentSGVote st grades := by
      show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache)
          S.E S.hc st (S.hc.round_of st.s)
          (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
            S.E S.hc st (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
      rw [hround]
      rfl
    rw [heq]
    unfold Protocol.currentSGVote
    cases hclear : Protocol.deepest_clear (some grades.anchor)
        st.live_confirmed grades.clear with
    | some X =>
        have hliveNext : Block.Preceq st.live_confirmed Next := by
          simpa only [n, st] using hDliveNext
        exact Block.preceq_trans (Proofs.Engine.deepest_clear_preceq hclear) hliveNext
    | none =>
        cases hq2 : grades.Q2 with
        | some Q =>
            simp only [hclear, hq2]
            exact hQNext Q (by simpa only [hround] using hq2)
        | none =>
            by_cases hraw : grades.rawG2
            · simp only [hclear, hq2, hraw, ↓reduceIte]
              exact Block.preceq_trans hfgAnchor
                (Block.preceq_trans hanchorGrades hDNext)
            · simp only [hclear, hq2, hraw, Bool.false_eq_true, ↓reduceIte]
              exact Block.preceq_trans hanchorGrades hDNext
  have hread : Protocol.actionEventRead S rho i v q = actionReadAt S rho v q :=
    Protocol.actionEventRead_eq_actionReadAt_of_tick S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi
  have hAttestRound : ∀ {w : V} {time : Time} {a : NamedAttestation V},
      rho.events[i]? = some (Event.tick w time) →
      Object.attest a ∈ NamedRun.emittedAt S rho i w time →
      a.round = q := by
    intro w time a hi' ha
    have hemit := Protocol.emits_of_emittedAt_tick S hi' ha
    have hshape := Proofs.Optimistic.emits_attest_shape S hemit
    have heqTime : time = S.a q := by
      exact congrArg Event.time (Option.some.inj (hi'.symm.trans hi))
    have hroundEq : q = a.round :=
      (actionTime_strictMono S).injective (heqTime.symm.trans hshape.2)
    exact hroundEq.symm
  have hsources : HonestRoundActionActiveSourcesPreceqAtIndex S rho i Next := by
    refine ⟨?_, ?_, ?_⟩
    · intro w time a hw hi' ha
      have haq := hAttestRound hi' ha
      have heq := Option.some.inj (hi'.symm.trans hi)
      obtain ⟨rfl, rfl⟩ := NamedEvent.tick.inj heq
      rw [haq]
      simpa only [hread] using hDliveNext
    · intro w time a hw hi' ha Q hQ
      have haq := hAttestRound hi' ha
      have heq := Option.some.inj (hi'.symm.trans hi)
      obtain ⟨rfl, rfl⟩ := NamedEvent.tick.inj heq
      rw [haq] at hQ
      have hQ' := hQ
      rw [hread] at hQ'
      rw [hround'] at hQ'
      exact hQNext Q (by simpa only [n, st] using hQ')
    · intro w time a hw hi' ha
      have haq := hAttestRound hi' ha
      have heq := Option.some.inj (hi'.symm.trans hi)
      obtain ⟨rfl, rfl⟩ := NamedEvent.tick.inj heq
      rw [haq]
      have hrootNext := Block.preceq_trans hsgRootD hDNext
      have hrootNext' : Block.Preceq
          (Protocol.get_sg_root_with
            (NamedProfile.gradeContract (actionReadAt S rho w q).cache)
            S.E S.hc (actionReadAt S rho w q).st.core.toHealing
            (S.hc.round_of (actionReadAt S rho w q).st.core.s)) Next := by
        rw [hround']
        exact hrootNext
      simpa only [hread] using hrootNext'
  have hout : HonestAttestationOutputPreceqAtIndex S rho i Next :=
    honestAttestationOutputPreceqAtIndex_of_activeSources S adm hsources
  have hsg : HonestActionSGCarriersPreceqAtIndex S rho i Next := by
    intro w r a hw hi' ha
    have heq := Option.some.inj (hi'.symm.trans hi)
    obtain ⟨rfl, htime⟩ := NamedEvent.tick.inj heq
    have hr : r = q := (actionTime_strictMono S).injective htime
    subst r
    exact hcarrierNext
  exact ⟨hcarrierNext, hsg, hout⟩

#print axioms movingEventFacts_action_of_previousCarrierCeiling_named


/- /-- The five event-local facts at one honest Section 7 action event.
The ceiling `hupper` is the only history input: every honest previous-round SG
carrier is already below the target endpoint. No FG-root regime is inspected,
and no numeric frontier value is used. -/
/-- The five event-local facts at one honest Section 7 action event.

The ceiling `hupper` is the only history input: every honest previous-round SG
carrier is already below the target endpoint. No FG-root regime is inspected,
and no numeric frontier value is used. -/
theorem movingEventFacts_action_of_previousCarrierCeiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {i: Nat}
    {q: Round} (hq: 0 < q)
    (hpost: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    {v: V} (hv: v ∈ rho.honest)
    (hi: rho.events[i]? = some (Event.tick v (S.a q)))
    {D: Block V}
    (hD: GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
      (S.hc.opening_slot q) D)
    {Next: Block V}
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) Next)
    (hDNext: Block.Preceq D Next):
    Block.Preceq (actionSGBlockAt S rho v q) Next ∧
      GenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      ReadAnchorsAtIndex S rho i Next:= by
  have hpred: q - 1 + 1 = q:= Nat.sub_add_cancel
    (Nat.succ_le_iff.mpr hq)
  have hstate:= Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toScheduleWellFormed hi
  let ast:= actionStoreAt S rho v q
  have hast: Proofs.Optimistic.attestStore S
      (rho.stateBefore S i v).st (S.a q) = ast:= by
    rw [hstate]
    rfl
  have hroundAst: S.hc.round_of ast.s = q:= by
    simpa only [ast] using actionStoreAt_round S rho v q
  have hliveD: ast.live_confirmed = D:= by
    simp only [ast]
    rw [actionStoreAt_eq_update_confirmation_confStore, hD.selected]
  have hconfRound: S.hc.round_of
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).s = q:= by
    simp only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      opening_confirmation_time_eq_action]
    exact round_of_slotOf_a S q
  have hanchorD: Block.Preceq
      (confAnchor S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))) D:=
    confAnchor_preceq_of_genuineConfirmation S.E S.hc
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
      (S.hc.opening_slot q) D hD
  have hsgRootNext: Block.Preceq
      (Protocol.get_sg_root S.E S.hc ast.toHealing q) Next:= by
    rw [show ast = Protocol.update_confirmation S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
        (S.hc.opening_slot q) by
      simpa only [ast] using
        actionStoreAt_eq_update_confirmation_confStore S rho v q]
    exact Block.preceq_trans (by
      simpa only [confAnchor, hconfRound, Protocol.update_confirmation,
        Protocol.Store.toHealing] using hanchorD) hDNext
  have hgrade2Next: ∀ Q: Block V,
      Protocol.G2 S.E ast.toHealing.gradeView S.hc q Q = true →
        Block.Preceq Q Next:= by
    intro Q hQG2Action
    have hQG2: Protocol.G2 S.E (gradeViewAt S rho v q)
        S.hc q Q = true:= by
      have hQ:= hQG2Action
      simp only [ast, actionStoreAt] at hQ
      rw [Protocol.G2_attestStore_eq S] at hQ
      simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime] using hQ
    obtain ⟨u, hu, hQcarrier⟩:=
      G2_preceq_honestPreviousActionCarrier
        S adm hfb hv (q - 1) hpost
          (by simpa only [hpred] using hcut)
          (by simpa only [hpred] using hQG2)
    exact Block.preceq_trans hQcarrier (hupper u hu)
  have hsources: HonestRoundActionActiveSourcesPreceqAtIndex
      S rho i Next:= by
    refine ⟨?_, ?_, ?_⟩
    · intro w time a hw hi' ha
      have heq:= Option.some.inj (hi'.symm.trans hi)
      obtain ⟨rfl, rfl⟩:= Event.tick.inj heq
      rw [hast, hliveD]
      exact hDNext
    · intro w time a hw hi' ha Q hQactive hQG2
      have heq:= Option.some.inj (hi'.symm.trans hi)
      obtain ⟨rfl, rfl⟩:= Event.tick.inj heq
      rw [hast, hroundAst] at hQG2
      exact hgrade2Next Q hQG2
    · intro w time a hw hi' ha
      have heq:= Option.some.inj (hi'.symm.trans hi)
      obtain ⟨rfl, rfl⟩:= Event.tick.inj heq
      rw [hast, hroundAst]
      exact hsgRootNext
  have hout: HonestAttestationOutputPreceqAtIndex S rho i Next:=
    honestAttestationOutputPreceqAtIndex_of_activeSources S adm hsources
  have hcarrierNext: Block.Preceq (actionSGBlockAt S rho v q) Next:= by
    have hlivePre: Block.Preceq ast.live_confirmed Next:= by
      rw [hliveD]
      exact hDNext
    rcases getSGVote_preceq_live_or_grade2_or_sgRoot
        S.E S.hc ast.toHealing q with hclear | hselected
    · exact Block.preceq_trans (by
        simpa only [actionSGBlockAt, ast] using hclear)
          hlivePre
    · rcases hselected with ⟨Q, hQ, hselected⟩ | hfgEq | hrootEq
      · have hQG2: Protocol.G2 S.E ast.toHealing.gradeView S.hc q Q = true:=
          (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hQ)).2
        rw [show actionSGBlockAt S rho v q = Q by
          simpa only [actionSGBlockAt, ast] using hselected]
        exact hgrade2Next Q hQG2
      · rw [show actionSGBlockAt S rho v q =
          Protocol.get_fg_root ast.toHealing.toFG by
            simpa only [actionSGBlockAt, ast] using hfgEq]
        have hFGpreceqSG: Block.Preceq
            (Protocol.get_fg_root ast.toHealing.toFG)
            (Protocol.get_sg_root S.E S.hc ast.toHealing q):= by
          simp only [Protocol.get_sg_root]
          split
          · rename_i A hA
            exact Proofs.Records.fresh_anchor_root_preceq S.E S.hc ast.toHealing _ hA
          · split
            · exact Block.preceq_self _
            · exact Protocol.ghost_preceq _ _ _ _
        exact Block.preceq_trans hFGpreceqSG hsgRootNext
      · rw [show actionSGBlockAt S rho v q =
          Protocol.get_sg_root S.E S.hc ast.toHealing q by
            simpa only [actionSGBlockAt, ast] using hrootEq]
        exact hsgRootNext
  have hsg: HonestActionSGCarriersPreceqAtIndex S rho i Next:= by
    intro w r a hw hi' ha
    have heq:= Option.some.inj (hi'.symm.trans hi)
    obtain ⟨rfl, htime⟩:= Event.tick.inj heq
    have hr: r = q:= (actionTime_strictMono S).injective htime
    subst r
    exact hcarrierNext
  have hconfirmations: GenuineConfirmationsPreceqAtIndex S rho i Next:= by
    intro w hw C hC
    rcases hC with ⟨s, hCi, hCgenuine⟩
    have heq:= Option.some.inj (hCi.symm.trans hi)
    obtain ⟨rfl, htime⟩:= Event.tick.inj heq
    have hs: s = S.hc.opening_slot q:= by
      have htime': Protocol.confirmation_time S.E s =
          Protocol.confirmation_time S.E (S.hc.opening_slot q):=
        htime.trans (Protocol.a_eq_confirmation_time S.hc S.E q)
      have hslot:= congrArg S.E.slotOf htime'
      simp only [Proofs.Optimistic.slotOf_confirmation_time] at hslot
      exact Nat.add_right_cancel hslot
    subst s
    have hCD: C = D:= hCgenuine.selected.symm.trans hD.selected
    simpa only [hCD] using hDNext
  have hanchors: ReadAnchorsAtIndex S rho i Next:= by
    refine { voteCompatible:= ?_, confirmationCompatible:= ?_ }
    · intro w s hw hwi
      have heq:= Option.some.inj (hwi.symm.trans hi)
      obtain ⟨rfl, htime⟩:= Event.tick.inj heq
      have hslot: s = S.E.slotOf (S.a q):= by
        simpa only [Proofs.Optimistic.slotOf_vote_time] using
          congrArg S.E.slotOf htime
      exact False.elim
        ((Proofs.Optimistic.a_ne_vote_time S (rfl: S.a q = S.a q)) (by
          rw [← hslot]
          exact htime.symm))
    · intro w s hw hwi
      have heq:= Option.some.inj (hwi.symm.trans hi)
      obtain ⟨rfl, htime⟩:= Event.tick.inj heq
      have hs: s = S.hc.opening_slot q:= by
        have htime': Protocol.confirmation_time S.E s =
            Protocol.confirmation_time S.E (S.hc.opening_slot q):=
          htime.trans (Protocol.a_eq_confirmation_time S.hc S.E q)
        have hslot:= congrArg S.E.slotOf htime'
        simp only [Proofs.Optimistic.slotOf_confirmation_time] at hslot
        exact Nat.add_right_cancel hslot
      subst s
      exact Block.compatible_of_preceq_common
        (Block.preceq_trans hanchorD hDNext) (Block.preceq_self Next)
  exact ⟨hcarrierNext, hconfirmations, hsg, hout, hanchors⟩
/-- Advance an honest action event without a common-grade premise.
The action's selected confirmation bounds the live source and the SG root.
Each active G2 source is below one honest previous-round action carrier, which
the moving history already bounds by the previous endpoint. -/
theorem MovingFrontierChainState.succ_action_of_previousCarrierCeiling
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {q: Round} (hq: 0 < q)
    (ht1: t1 ≤ S.a (q - 1))
    (hpost: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    {v: V} (hv: v ∈ rho.honest)
    (hi: rho.events[i]? = some (Event.tick v (S.a q)))
    {D: Block V}
    (hD: GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
      (S.hc.opening_slot q) D)
    {Next: Block V}
    (hEndNext: Block.Preceq (End i) Next)
    (hDNext: Block.Preceq D Next)
    (hNextRun: RunBlock S rho Next):
    ∃ End': Nat → Block V,
      (∀ j, j ≤ i → End' j = End j) ∧
      End' (i + 1) = Next ∧
      MovingFrontierChainState S rho t1 M0 n0 (i + 1) End':= by
  have hpred: q - 1 + 1 = q:= Nat.sub_add_cancel
    (Nat.succ_le_iff.mpr hq)
  have hbefore: S.a (q - 1) < S.a q:=
    action_strictMono S (Nat.sub_lt hq Nat.zero_lt_one)
  have hactionHor: S.a (q - 1) ≤ rho.horizon:=
    (le_of_lt (Int.lt_add_of_pos_right (S.a (q - 1)) S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S (q - 1)).trans (by
        simpa only [hpred] using hcut))
  have hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) Next:= by
    intro u hu
    exact Block.preceq_trans
      (h.previousActionCarriersPreceqAtIndex S adm hi ht1 hactionHor
        hbefore u hu) hEndNext
  obtain ⟨_hcarrier, hconfirmations, hsg, hout, hanchors⟩:=
    movingEventFacts_action_of_previousCarrierCeiling
      S adm hfb hq hpost hcut hv hi hD hupper hDNext
  exact h.succ_of_eventFacts Next hEndNext hNextRun
    (proposalChainObservationsSandwichedAtIndex_of_actionEvent
      S hi (End i) Next)
    hconfirmations hsg hout hanchors
-/



/-- Previous-round honest action carriers give directed relative-SG support
at any honest read after the next round's grade-zero cutoff. -/
theorem supportAlignedAtRead_of_previousActionCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {t : Time} {Can : Block V}
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hread : S.hc.Γ_0 S.E.Δ (r + 1) ≤ t)
    {w : V} (hw : w ∈ rho.honest)
    (hcanMem : Can ∈ (rho.storeBeforeTime S w t).T)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Can) :
    Proofs.Optimistic.SupportAligned
      (rho.storeBeforeTime S w t).toHealing.sg_votes S.hc.η_SG
      (rho.storeBeforeTime S w t).T rho.honest (r + 1) Can := by
  let B := Can
  let pre := rho.storeBeforeTime S w t
  have hrelay : ∀ v ∈ rho.honest,
      actionSGVoteAt S rho v r ∈ pre.toHealing.sg_votes r := by
    intro v hv
    have hdeadline : S.a r + S.E.Δ ≤ rho.horizon :=
      (action_add_delta_le_next_Γ_neg1 S r).trans hcut
    obtain ⟨j, e, hj, hjt, hpool⟩ :=
      actionSGVote_pooled_before_delta S adm hv hw r hpost hdeadline
    have hjt' : e.time < t :=
      lt_of_lt_of_le hjt
        ((action_add_delta_le_next_Γ_neg1 S r).trans
          ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread))
    simpa only [pre, Run.storeBeforeTime] using
      (Protocol.sgVote_mem_stateBeforeTime_of_post
        S adm.toNamedScheduleWellFormed hj hjt' hpool)
  refine ⟨?_, ?_⟩
  · intro v hv
    have hwindow : r ∈ Protocol.latest_window S.hc.η_SG (r + 1) := by
      simpa only [Nat.add_sub_cancel] using
        (Protocol.pred_mem_latest_window S.hc.η_SG (r + 1)
          S.hc.η_SG_ge_one (Nat.succ_pos r))
    exact Protocol.represented_of_vote_mem hwindow (hrelay v hv) rfl
  · intro v hv u hlatest
    let C := actionSGBlockAt S rho v r
    have hpc : ParentClosed pre.core := by
      simpa only [pre, Run.storeBeforeTime] using
        Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho t w
    have hBmem : B ∈ pre.T := by simpa only [B, pre] using hcanMem
    have hCsource : C ∈ (rho.storeBeforeTime S v (S.a r)).T := by
      simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S rho v r
    obtain ⟨CN, hCNerase, hCNrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedScheduleWellFormed hv (S.a r)
        (by simpa only [Run.storeBeforeTime] using hCsource)
    have hCB : Block.Preceq C B := by
      simpa only [C, B] using hupper v hv
    have hCmem : C ∈ pre.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff pre.core).mp hpc).2 C B hBmem hCB
    have hfind : Block.find? pre.T C.root = some C := by
      apply Proofs.Optimistic.find?_eq_some_of_unique hCmem
      intro X hX hrootX
      obtain ⟨XN, hXNerase, hXNrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedScheduleWellFormed hw t
          (by simpa only [pre, Run.storeBeforeTime] using hX)
      have hrootN : XN.root = CN.root := by
        rw [← Proofs.NamedWire.erase_root XN, ← Proofs.NamedWire.erase_root CN,
          hXNerase, hCNerase]
        exact hrootX
      have hXCN : XN = CN :=
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
          XN CN hXNrun hCNrun XN CN
          (Or.inl (Proofs.NamedAncestry.named_self XN))
          (Or.inr (Proofs.NamedAncestry.named_self CN)) hrootN
      rw [← hXNerase, ← hCNerase, hXCN]
    have hresolved : Protocol.holds_resolved_vote_by
        pre.T (pre.toHealing.sg_votes r) v = true := by
      unfold Protocol.holds_resolved_vote_by
      rw [decide_eq_true_eq]
      apply Finset.card_pos.mpr
      refine ⟨actionSGVoteAt S rho v r, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨hrelay v hv, by rfl⟩
      · change (Block.find? pre.T C.root).isSome = true
        rw [hfind]
        rfl
    have hetaPos : 0 < S.hc.η_SG :=
      Nat.succ_le_iff.mp S.hc.η_SG_ge_one
    have hlenPos : 0 < min (r + 1) S.hc.η_SG :=
      Nat.lt_min.mpr ⟨Nat.succ_pos r, hetaPos⟩
    have hlen : min (r + 1) S.hc.η_SG =
        min (r + 1) S.hc.η_SG - 1 + 1 :=
      (Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hlenPos))).symm
    have hlast : (r + 1 - S.hc.η_SG) +
        (min (r + 1) S.hc.η_SG - 1) = r := by
      by_cases hle : S.hc.η_SG ≤ r + 1
      · rw [Nat.min_eq_right hle]
        have hsucc : ((r + 1 - S.hc.η_SG) +
            (S.hc.η_SG - 1)) + 1 = r + 1 := by
          calc
            ((r + 1 - S.hc.η_SG) + (S.hc.η_SG - 1)) + 1 =
                (r + 1 - S.hc.η_SG) + ((S.hc.η_SG - 1) + 1) :=
              Nat.add_assoc _ _ _
            _ = (r + 1 - S.hc.η_SG) + S.hc.η_SG := by
              rw [Nat.sub_add_cancel S.hc.η_SG_ge_one]
            _ = r + 1 := Nat.sub_add_cancel hle
        exact Nat.succ.inj (by
          simpa only [Nat.succ_eq_add_one] using hsucc)
      · have hle' : r + 1 ≤ S.hc.η_SG := Nat.le_of_not_ge hle
        rw [Nat.min_eq_left hle', Nat.sub_eq_zero_of_le hle',
          Nat.zero_add, Nat.add_sub_cancel]
    have hwindow : Protocol.latest_window S.hc.η_SG (r + 1) =
        List.range' (r + 1 - S.hc.η_SG)
          (min (r + 1) S.hc.η_SG - 1) ++ [r] := by
      unfold Protocol.latest_window
      calc
        List.range' (r + 1 - S.hc.η_SG) (min (r + 1) S.hc.η_SG) =
            List.range' (r + 1 - S.hc.η_SG)
              (min (r + 1) S.hc.η_SG - 1 + 1) :=
          congrArg (List.range' (r + 1 - S.hc.η_SG)) hlen
        _ = List.range' (r + 1 - S.hc.η_SG)
              (min (r + 1) S.hc.η_SG - 1) ++
            [r + 1 - S.hc.η_SG +
              (min (r + 1) S.hc.η_SG - 1)] := by
          simpa only [Nat.one_mul] using
            (List.range'_concat (s := r + 1 - S.hc.η_SG)
              (n := min (r + 1) S.hc.η_SG - 1) (step := 1))
        _ = List.range' (r + 1 - S.hc.η_SG)
              (min (r + 1) S.hc.η_SG - 1) ++ [r] := by rw [hlast]
    have hlatestRound : Protocol.latest_support_round
        pre.toHealing.sg_votes S.hc.η_SG pre.T v (r + 1) = some r := by
      unfold Protocol.latest_support_round
      rw [hwindow, List.filter_append]
      simp [hresolved]
    have hsole : Protocol.sole_vote? (pre.toHealing.sg_votes r) v = some u := by
      unfold Protocol.latest_support_vote at hlatest
      rw [hlatestRound] at hlatest
      exact hlatest
    obtain ⟨hu, huv⟩ := Protocol.sole_vote_mem_and_author hsole
    have huState : u ∈
        (rho.stateBeforeTime S t w).st.toHealing.sg_votes r := by
      simpa only [pre, Run.storeBeforeTime] using hu
    have hactionState : actionSGVoteAt S rho v r ∈
        (rho.stateBeforeTime S t w).st.toHealing.sg_votes r := by
      simpa only [pre, Run.storeBeforeTime] using hrelay v hv
    have huEq : u = actionSGVoteAt S rho v r :=
      Protocol.honest_sgVote_unique_stateBeforeTime S adm hv
        huState hactionState huv (by rfl)
    rw [huEq]
    change Proofs.Optimistic.rootOnCan pre.T B (some C.root) = true
    simp only [Proofs.Optimistic.rootOnCan, hfind]
    exact hCB

/-- A previous-action carrier ceiling orients the integrated SG root at one
honest raw read. The fresh-anchor and relative-majority cases use the same
ceiling. -/
theorem readAnchor_preceq_of_previousActionCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {r : Round} {t : Time} {C : Block V}
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hread : S.hc.Γ_0 S.E.Δ (r + 1) ≤ t)
    {w : V} (hw : w ∈ rho.honest)
    (hmem : C ∈ (rho.storeBeforeTime S w t).T)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w t).toHealing.toFG) C)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) C) :
    Block.Preceq
      (Protocol.get_sg_root S.E S.hc
        (rho.storeBeforeTime S w t).toHealing (r + 1)) C := by
  have hsupport := supportAlignedAtRead_of_previousActionCeiling
    S adm hpost hcut hread hw hmem hupper
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  simp only [Protocol.get_sg_root, Protocol.get_sg_root_with,
    Protocol.GradeContract.current, Protocol.currentGradeRead]
  split
  · rename_i A hA
    exact freshAnchor_preceq_of_previousActionCarriersPreceq_at_read
      S adm hfb hpost hcut hupper hw
        ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread)
        hA
  · split
    · exact hroot
    · exact Protocol.HonestWeightMajority.majority_fork_choice_preceq
        S hsupport hmajority hroot

#print axioms supportAlignedAtRead_of_previousActionCeiling
#print axioms readAnchor_preceq_of_previousActionCeiling


/-
/-- Convert full-store root-side geometry to one primed vote-duty input.

The root-below branch uses a frozen processed descendant of `C` to transfer
the endpoint and all strict path blocks to the frozen candidate tree. The
root-above branch needs no candidate transfer. -/
theorem voteInputs_of_rootSideWithPath
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} {C: Block V} {w: V} (hw: w ∈ rho.honest)
    (hprocessed: C ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s)
    (hmax: (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max ≤
      (derived_state S.E S.cfg C).h + 1)
    (hrootSide:
      (Block.Preceq
          (Protocol.get_fg_root
            (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) C ∧
        C ∈ Protocol.get_filtered_block_tree
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG ∧
        ∀ D: Block V,
          Block.Preceq
            (Protocol.get_fg_root
              (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) D →
          Block.Preceq D C →
          D ∈ Protocol.get_filtered_block_tree
            (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) ∨
      Block.Preceq C
        (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG))
    (hanchor: Block.compatible
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing) C = true):
    GoldfishConeVoteInputs' S rho s C w:= by
  refine { rootSide:= ?_, anchor:= hanchor }
  rcases hrootSide with hbelow | habove
  · refine Or.inl ⟨hbelow.1, ?_, ?_⟩
    · exact ancestorCandidate_of_processedDescendant_and_hMax
        S adm hw hprocessed (Block.preceq_self C) hbelow.2.1 hmax
    · intro D hAD _hAne hDC _hDne
      have hrootAnchor: Block.Preceq
          (Protocol.get_fg_root
            (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG)
          (Proofs.Optimistic.healAnchor S.E S.hc
            (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing):= by
        rw [Proofs.Optimistic.healAnchor_eq_get_sg_root]
        exact StoreFinality.get_fg_root_preceq_get_sg_root
          S.E S.hc (Proofs.Optimistic.voteDutyStore S rho w (s + 1))
      have hrootD:= Block.preceq_trans hrootAnchor hAD
      exact ancestorCandidate_of_processedDescendant_and_hMax
        S adm hw hprocessed hDC (hbelow.2.2 D hrootD hDC) hmax
  · exact Or.inr habove

/-- Full-store root-side geometry is already the primed confirmation input.
The confirmation candidate tree is the full filtered tree at that read. -/
theorem confInputs_of_rootSideWithPath
    (S: Setup V) {rho: Run V} {s: Slot} {C: Block V} {w: V}
    (hrootSide:
      (Block.Preceq (confRoot (Proofs.Optimistic.confStore S rho w s)) C ∧
        C ∈ confTree (Proofs.Optimistic.confStore S rho w s) ∧
        ∀ D: Block V,
          Block.Preceq (confRoot (Proofs.Optimistic.confStore S rho w s)) D →
          Block.Preceq D C →
          D ∈ confTree (Proofs.Optimistic.confStore S rho w s)) ∨
      Block.Preceq C (confRoot (Proofs.Optimistic.confStore S rho w s)))
    (hanchor: Block.compatible
      (confAnchor S.E S.hc (Proofs.Optimistic.confStore S rho w s)) C = true):
    GoldfishConeConfirmationInputs' S rho s C w:= by
  refine { rootSide:= ?_, anchor:= hanchor }
  rcases hrootSide with hbelow | habove
  · refine Or.inl ⟨hbelow.1, hbelow.2.1, ?_⟩
    intro D hAD _hAne hDC _hDne
    have hrootD:= Block.preceq_trans
      (confRoot_preceq_confAnchor S.E S.hc
        (Proofs.Optimistic.confStore S rho w s)) hAD
    exact hbelow.2.2 D hrootD hDC
  · exact Or.inr habove

/-- One moving endpoint supplies the complete primed vote input at an exact
vote event once its FG root and SG anchor are below the endpoint.

The preceding vote cone supplies the frozen processed endpoint. The moving
frontier invariant supplies the local `h_max - 1` height gate. -/
theorem MovingFrontierChainState.voteInputsAtIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {s: Slot}
    (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    {w: V} (hw: w ∈ rho.honest)
    (hevent: rho.events[i]? = some
      (Event.tick w (Protocol.vote_time S.E (s + 1))))
    (hroot: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) (End i))
    (hanchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing) (End i)):
    GoldfishConeVoteInputs' S rho s (End i) w:= by
  have havailable:= honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    S adm hw hpost
      ((support_cutoff_le_confirmation_time S.E s).trans hhor)
      hroot hvotes
  have hprocessed:= Protocol.voterProcessedConeEndpoint_of_availableBefore
    S adm hcom havailable hvotes
  have hmemDuty: End i ∈
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T:= by
    have hdata:= hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    exact hdata.1
  have hstate:= Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toScheduleWellFormed hevent
  have hmemState: End i ∈ (rho.stateBefore S i w).st.T:= by
    rw [hstate]
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hmemDuty
  have hrootState: Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S i w).st.toHealing.toFG) (End i):= by
    rw [hstate]
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hroot
  have hrootSideState:= h.endpoint_rootSideWithPath_atIndex
    S adm hmajority hw hmemState
      (Block.compatible_of_preceq_common hrootState (Block.preceq_self (End i)))
  have hrootSide:
      (Block.Preceq
          (Protocol.get_fg_root
            (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) (End i) ∧
        End i ∈ Protocol.get_filtered_block_tree
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG ∧
        ∀ D: Block V,
          Block.Preceq
            (Protocol.get_fg_root
              (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) D →
          Block.Preceq D (End i) →
          D ∈ Protocol.get_filtered_block_tree
            (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) ∨
      Block.Preceq (End i)
        (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG):= by
    rw [hstate] at hrootSideState
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootSideState
  have hlocal: (rho.stateBefore S i w).st.h_max ≤
      honestHMaxBeforeIndex S rho i:=
    localHMax_le_honestHMaxBeforeIndex S rho i hw
  have hfloor: (rho.stateBefore S i w).st.h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:=
    (Nat.sub_le_sub_right hlocal 1).trans
      (h.frontier_sub_one_le_endpointHeight S adm hmajority)
  have hmaxState: (rho.stateBefore S i w).st.h_max ≤
      (derived_state S.E S.cfg (End i)).h + 1:=
    Nat.sub_le_iff_le_add.mp hfloor
  have hmax: (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max ≤
      (derived_state S.E S.cfg (End i)).h + 1:= by
    rw [hstate] at hmaxState
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hmaxState
  exact voteInputs_of_rootSideWithPath S adm hw hprocessed hmax hrootSide
    (Block.compatible_of_preceq_common hanchor (Block.preceq_self (End i)))

/-- Dispatch one exact moving-chain vote read from the previous action
carrier ceiling. The selected FG root can be gate-on or gate-off. -/
theorem MovingFrontierChainState.voteInputs_of_previousActionCeilingAtIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {r: Round} {s: Slot}
    (hround: S.hc.round_of (s + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hslotHor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    {w: V} (hw: w ∈ rho.honest)
    (hevent: rho.events[i]? = some
      (Event.tick w (Protocol.vote_time S.E (s + 1))))
    (htwoRises: M0 + 2 ≤ (rho.stateBefore S i w).st.h_max):
    GoldfishConeVoteInputs' S rho s (End i) w:= by
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hrootState:= h.newRoot_on_endpointChainAtIndex
    S adm hfb (Nat.le_refl i) hw htwoRises
  have hstate:= Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toScheduleWellFormed hevent
  have hroot: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) (End i):= by
    rw [hstate] at hrootState
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootState
  have havailable:= honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E s).trans hslotHor)
      hroot hvotes
  have hprocessed:= Protocol.voterProcessedConeEndpoint_of_availableBefore
    S adm hcom havailable hvotes
  have hmem: End i ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).T:= by
    have hdata:= hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hdata.1
  have hread: S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.vote_time S.E (s + 1):= by
    simpa only using Γ_0_le_vote_time_of_round_eq S hround
  have hbefore: S.a r < Protocol.vote_time S.E (s + 1):= by
    exact (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread))
  have hactionHor: S.a r ≤ rho.horizon:=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
  have hupper:= h.previousActionCarriersPreceqAtIndex
    S adm hevent ht1 hactionHor hbefore
  have hrootRaw: Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (s + 1))).toHealing.toFG) (End i):= by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hroot
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hw hmem hrootRaw hupper
  have hanchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing) (End i):= by
    rw [Proofs.Optimistic.healAnchor_eq_get_sg_root]
    have hslot:= Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
    have hslot':
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s = s + 1:= by
      simpa only [Protocol.Store.toHealing] using hslot
    rw [hslot', hround]
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hanchorRaw
  exact h.voteInputsAtIndex S adm hcom hmajority hpostVote hslotHor
    hvotes hw hevent hroot hanchor

/-- One moving endpoint supplies the complete primed confirmation input at an
exact confirmation event once its FG root and SG anchor are below it. -/
theorem MovingFrontierChainState.confInputsAtIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {s: Slot}
    (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    {w: V} (hw: w ∈ rho.honest)
    (hevent: rho.events[i]? = some
      (Event.tick w (Protocol.confirmation_time S.E s)))
    (hroot: Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho w s)) (End i))
    (hanchor: Block.Preceq
      (confAnchor S.E S.hc (Proofs.Optimistic.confStore S rho w s)) (End i)):
    GoldfishConeConfirmationInputs' S rho s (End i) w:= by
  have hresolve:= headsResolveIn_confStore_of_postHealingCone
    S adm hw hpost ((support_cutoff_le_confirmation_time S.E s).trans hhor)
      hroot hvotes
  have hpositive: 0 < ((S.E.committee s) ∩ rho.honest).card:= by
    have hc:= hcom s
    omega
  obtain ⟨x, hx⟩:= Finset.card_pos.mp hpositive
  have hxCommittee: x ∈ S.E.committee s:= (Finset.mem_inter.mp hx).1
  have hxHonest: x ∈ rho.honest:= (Finset.mem_inter.mp hx).2
  obtain ⟨X, hEndX, _hXrun, hXemit⟩:=
    hvotes x hxHonest hxCommittee
  have hfind:= (hresolve X
    ⟨x, hxHonest, hxCommittee, _hXrun, hXemit⟩).1
  have hXmem: X ∈ (Proofs.Optimistic.confStore S rho w s).T:=
    Proofs.HealingLemmas.find?_mem hfind
  let pre:= rho.storeBeforeTime S w (Protocol.confirmation_time S.E s)
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.confirmation_time S.E s) w)
  have hpc: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hmemPre: End i ∈ pre.T:= by
    apply Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hpc).2 (End i) X
    · simpa only [pre, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hXmem
    · exact hEndX
  have hstate:= Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toScheduleWellFormed hevent
  have hmemState: End i ∈ (rho.stateBefore S i w).st.T:= by
    rw [hstate]
    simpa only [pre, Run.storeBeforeTime] using hmemPre
  have hrootState: Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S i w).st.toHealing.toFG) (End i):= by
    rw [hstate]
    simpa only [pre, confRoot, Proofs.Optimistic.confStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hroot
  have hrootSideState:= h.endpoint_rootSideWithPath_atIndex
    S adm hmajority hw hmemState
      (Block.compatible_of_preceq_common hrootState (Block.preceq_self (End i)))
  have hrootSide:
      (Block.Preceq (confRoot (Proofs.Optimistic.confStore S rho w s)) (End i) ∧
        End i ∈ confTree (Proofs.Optimistic.confStore S rho w s) ∧
        ∀ D: Block V,
          Block.Preceq (confRoot (Proofs.Optimistic.confStore S rho w s)) D →
          Block.Preceq D (End i) →
          D ∈ confTree (Proofs.Optimistic.confStore S rho w s)) ∨
      Block.Preceq (End i) (confRoot (Proofs.Optimistic.confStore S rho w s)):= by
    rw [hstate] at hrootSideState
    simpa only [pre, confRoot, confTree, Proofs.Optimistic.confStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootSideState
  exact confInputs_of_rootSideWithPath S hrootSide
    (Block.compatible_of_preceq_common hanchor (Block.preceq_self (End i)))

/-- Dispatch one exact moving-chain confirmation read from the previous
action carrier ceiling. The selected FG root can be gate-on or gate-off. -/
theorem MovingFrontierChainState.confInputs_of_previousActionCeilingAtIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {r: Round} {s: Slot}
    (hround: S.hc.round_of (s + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hslotHor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    {w: V} (hw: w ∈ rho.honest)
    (hevent: rho.events[i]? = some
      (Event.tick w (Protocol.confirmation_time S.E s)))
    (htwoRises: M0 + 2 ≤ (rho.stateBefore S i w).st.h_max):
    GoldfishConeConfirmationInputs' S rho s (End i) w:= by
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hrootState:= h.newRoot_on_endpointChainAtIndex
    S adm hfb (Nat.le_refl i) hw htwoRises
  have hstate:= Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toScheduleWellFormed hevent
  have hroot: Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho w s)) (End i):= by
    rw [hstate] at hrootState
    simpa only [confRoot, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime] using hrootState
  have hresolve:= headsResolveIn_confStore_of_postHealingCone
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E s).trans hslotHor)
      hroot hvotes
  have hpositive: 0 < ((S.E.committee s) ∩ rho.honest).card:= by
    have hc:= hcom s
    omega
  obtain ⟨x, hx⟩:= Finset.card_pos.mp hpositive
  have hxCommittee: x ∈ S.E.committee s:= (Finset.mem_inter.mp hx).1
  have hxHonest: x ∈ rho.honest:= (Finset.mem_inter.mp hx).2
  obtain ⟨X, hEndX, hXrun, hXemit⟩:=
    hvotes x hxHonest hxCommittee
  have hfind:= (hresolve X
    ⟨x, hxHonest, hxCommittee, hXrun, hXemit⟩).1
  have hXmem: X ∈ (Proofs.Optimistic.confStore S rho w s).T:=
    Proofs.HealingLemmas.find?_mem hfind
  let pre:= rho.storeBeforeTime S w (Protocol.confirmation_time S.E s)
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.confirmation_time S.E s) w)
  have hpc: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hmem: End i ∈ pre.T:= by
    apply Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hpc).2 (End i) X
    · simpa only [pre, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hXmem
    · exact hEndX
  have hread: S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.confirmation_time S.E s:= by
    simpa only using Γ_0_le_confirmation_time_of_round_succ S hround
  have hbefore: S.a r < Protocol.confirmation_time S.E s:= by
    exact (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread))
  have hactionHor: S.a r ≤ rho.horizon:=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
  have hupper:= h.previousActionCarriersPreceqAtIndex
    S adm hevent ht1 hactionHor hbefore
  have hrootRaw: Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) (End i):= by
    simpa only [pre, confRoot, Proofs.Optimistic.confStore,
      Proofs.Optimistic.tickStore] using hroot
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hw hmem hrootRaw hupper
  have hanchor: Block.Preceq
      (confAnchor S.E S.hc (Proofs.Optimistic.confStore S rho w s)) (End i):= by
    rw [confAnchor]
    have hroundSt: S.hc.round_of
        (Proofs.Optimistic.confStore S rho w s).s = r + 1:= by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Proofs.Optimistic.slotOf_confirmation_time] using hround
    rw [hroundSt]
    simpa only [pre, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hanchorRaw
  exact h.confInputsAtIndex S adm hcom hmajority hpostVote hslotHor
    hvotes hw hevent hroot hanchor

/-- The same exact-read dispatch makes the local confirmation output genuine
and advances it from the moving endpoint. -/
theorem MovingFrontierChainState.confOutcome_of_previousActionCeilingAtIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {r: Round} {s: Slot} (hs: 0 < s)
    (hround: S.hc.round_of (s + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hslotHor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    {w: V} (hw: w ∈ rho.honest)
    (hevent: rho.events[i]? = some
      (Event.tick w (Protocol.confirmation_time S.E s)))
    (htwoRises: M0 + 2 ≤ (rho.stateBefore S i w).st.h_max):
    GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (Proofs.Optimistic.confStore S rho w s) s
        (Protocol.update_confirmation S.E S.hc
          (Proofs.Optimistic.confStore S rho w s) s).live_confirmed ∧
      Block.Preceq (End i)
        (Protocol.update_confirmation S.E S.hc
          (Proofs.Optimistic.confStore S rho w s) s).live_confirmed:= by
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hrootState:= h.newRoot_on_endpointChainAtIndex
    S adm hfb (Nat.le_refl i) hw htwoRises
  have hstate:= Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toScheduleWellFormed hevent
  have hroot: Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho w s)) (End i):= by
    rw [hstate] at hrootState
    simpa only [confRoot, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime] using hrootState
  have hresolve:= headsResolveIn_confStore_of_postHealingCone
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E s).trans hslotHor)
      hroot hvotes
  have hpositive: 0 < ((S.E.committee s) ∩ rho.honest).card:= by
    have hc:= hcom s
    omega
  obtain ⟨x, hx⟩:= Finset.card_pos.mp hpositive
  have hxCommittee: x ∈ S.E.committee s:= (Finset.mem_inter.mp hx).1
  have hxHonest: x ∈ rho.honest:= (Finset.mem_inter.mp hx).2
  obtain ⟨X, hEndX, hXrun, hXemit⟩:=
    hvotes x hxHonest hxCommittee
  have hfind:= (hresolve X
    ⟨x, hxHonest, hxCommittee, hXrun, hXemit⟩).1
  have hXmem: X ∈ (Proofs.Optimistic.confStore S rho w s).T:=
    Proofs.HealingLemmas.find?_mem hfind
  let pre:= rho.storeBeforeTime S w (Protocol.confirmation_time S.E s)
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.confirmation_time S.E s) w)
  have hpc: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hmem: End i ∈ pre.T:= by
    apply Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hpc).2 (End i) X
    · simpa only [pre, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hXmem
    · exact hEndX
  have hmemState: End i ∈ (rho.stateBefore S i w).st.T:= by
    rw [hstate]
    simpa only [pre, Run.storeBeforeTime] using hmem
  have hcandidateState:= h.endpoint_mem_filtered_atIndex
    S adm hmajority hw hmemState hrootState
  have hcandidate: End i ∈ confTree (Proofs.Optimistic.confStore S rho w s):= by
    rw [hstate] at hcandidateState
    simpa only [confTree, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime] using hcandidateState
  have hread: S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.confirmation_time S.E s:= by
    simpa only using Γ_0_le_confirmation_time_of_round_succ S hround
  have hbefore: S.a r < Protocol.confirmation_time S.E s:= by
    exact (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread))
  have hactionHor: S.a r ≤ rho.horizon:=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
  have hupper:= h.previousActionCarriersPreceqAtIndex
    S adm hevent ht1 hactionHor hbefore
  have hrootRaw: Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) (End i):= by
    simpa only [pre, confRoot, Proofs.Optimistic.confStore,
      Proofs.Optimistic.tickStore] using hroot
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hw hmem hrootRaw hupper
  have hanchor: Block.Preceq
      (confAnchor S.E S.hc (Proofs.Optimistic.confStore S rho w s)) (End i):= by
    rw [confAnchor]
    have hroundSt: S.hc.round_of
        (Proofs.Optimistic.confStore S rho w s).s = r + 1:= by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Proofs.Optimistic.slotOf_confirmation_time] using hround
    rw [hroundSt]
    simpa only [pre, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hanchorRaw
  exact genuineConfirmationAndPreceq_of_postHealingCone
    S adm hcom hs hpostVote hslotHor hw hvotes hroot hanchor hcandidate

-/
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
