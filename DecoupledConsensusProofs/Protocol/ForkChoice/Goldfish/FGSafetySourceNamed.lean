module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FGSafetyRootNamed
public import DecoupledConsensusProofs.Execution.FGSourceAdmission
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryFGRoundAgreement
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
public import DecoupledConsensusProofs.Execution.SeedBaseCone
public import DecoupledConsensusProofs.Execution.MovingChainBase
public import DecoupledConsensusProofs.Objects.MovingChainStep
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.FGSourceRawGrade

@[expose] public section

/-!
# Named healed source ancestry and SG visibility

This is the run-scoped named proof of the source-ancestry part of the
post-recovery height-filter argument.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem runBlock_of_action_body
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈
      (NamedRun.stateBeforeTime S rho (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨j, hj, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDj : D ∈ (rho.stateBefore S j v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho j v).st.bodies
    rw [← hj]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv j hDj)

private theorem runBlock_of_read_body
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {read : Time} {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S v read).bodies) :
    RunBlock S rho D := by
  obtain ⟨j, hj, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed read
  have hDj : D ∈ (rho.stateBefore S j v).st.bodies := by
    simpa only [Run.storeBeforeTime, hj] using hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDj

private theorem NamedHeightRegimeRun.sgHistory_source
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {c : Round} (hc : a.round ≤ c) (hhor : S.a c ≤ rho.horizon) :
    HonestSGEmissionsCompatibleAtRound S rho c T.erase := by
  rcases eq_or_lt_of_le hc with rfl | hlt
  · exact h.seed.sgEmissionsCompatible_of_source_of_frame_named
      adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
  · exact ((h.laterHistory_main adm hcom hbelow
      (Nat.succ_le_of_lt hlt)).2 hhor).1

private theorem NamedHeightRegimeRun.sourceMem_at_read
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {read : Time} (hread : S.a a.round <= read)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (rho.storeBeforeTime S w read).bodies := by
  have hsource := h.seed.sourceMem_at_action_of_frame_named
    adm h.frame h.ready hw
  have hsourcePre : Cfg ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hsource
  have heqSource := congrFun
    (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed (S.a a.round)) w
  have heqRead := congrFun
    (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed read) w
  rw [heqSource] at hsourcePre
  have hCfgRead : Cfg ∈
      (NamedRun.stateBeforeTime S rho read w).st.bodies := by
    rw [heqRead]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hsourcePre
  simpa only [Run.storeBeforeTime] using hCfgRead

omit [DecidableEq V] [Fintype V] in
private theorem named_height_of_matches_source
    {a : NamedAttestation V} {H : Height} {root : BlockId}
    (hmatch : NamedHeightPair.matchesEntry H root a.height_pair = true) :
    a.height_pair.erase.height? = some H := by
  cases hp : a.height_pair with
  | empty =>
      simp [hp, NamedHeightPair.matchesEntry] at hmatch
  | vote height entry timeout =>
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hmatch
      cases timeout <;>
        simp [NamedHeightPair.erase, HeightPair.height?, hmatch.1]

omit [Fintype V] in
private theorem named_row_mem_chain_of_ancestor_source
    {A B : NamedBlock V} {a : NamedAttestation V}
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations B := by
  induction B generalizing A with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      subst A
      simp [NamedBlock.attestations] at ha
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      simp only [Protocol.named_chain_attestations, Finset.mem_union,
        List.mem_toFinset]
      rcases hAB with rfl | hparent
      · exact Or.inr ha
      · exact Or.inl (ih hparent ha)

namespace NamedHeightRegimeBaseRun

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first : Nat} {Tprev : NamedBlock V}

/-- Every actual honest row above a base is late enough for its grade
delivery window. -/
theorem honestHeightRow_gradeRoundReady (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1)) :
    GradeRoundReady S rho b.round := by
  obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
    h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
  have hround := hreg.minimal b tb hb hemit hrow
  have hbtime := (Proofs.Optimistic.emits_attest_shape S hemit).2
  have hhor : S.a b.round ≤ rho.horizon := by
    obtain ⟨j, hevent, -⟩ := hemit
    simpa only [Event.time, hbtime] using
      (adm.in_horizon _ (List.mem_of_getElem? hevent)).2
  have haround : r0 ≤ a.round := by
    by_contra hnot
    have htimeLt : ta < S.a r0 := by
      rw [hreg.seed.actionTime_eq]
      exact action_strictMono S (Nat.lt_of_not_ge hnot)
    have hstartCursor : strictEventIndex rho (S.a r0) ≤ i :=
      (strictEventIndex_le_inclusiveEventIndex rho (S.a r0)).trans
        hreg.seed.startLeIndex
    have htimeLe : S.a r0 ≤ ta :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        hstartCursor hreg.seed.exactTick
    exact (not_le_of_gt htimeLt) htimeLe
  exact gradeRoundReady_of_action_horizon S hgst (haround.trans hround) hhor

/-- A higher actual named FG source extends any lower named run block that a
preceding honest head protects. -/
theorem honestFGSource_preceq_of_previousHead (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1))
    {Cfg : Block V}
    (hsource : actionFGSource S
      (actionStoreAt S rho b.val_index b.round) = some Cfg)
    {s : Slot} (hs : S.hc.opening_slot b.round + 1 ≤ s)
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {C : NamedBlock V}
    (hCrun : RunBlock S rho C)
    (hC : Block.Preceq C.erase (voteDutyHead S rho v s))
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1) :
    Block.Preceq C.erase Cfg := by
  obtain ⟨first_n, i, a, ta, Cfg0, T, Tprev', c0, hreg⟩ :=
    h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
  obtain ⟨D, K, hW, hDmem, hsourceD, hDheight, hKmem,
      hKerase, hKheight, hKD, -⟩ :=
    honestHeightRow_confirmationWitness S adm hb hemit hrow
  have hDCfg : D.erase = Cfg := Option.some.inj (hsourceD.symm.trans hsource)
  have hTeq : T.erase =
      (Protocol.derive_named S.E S.cfg K).T_h :=
    Option.some.inj ((hreg.witness_eq adm hcom hbelow hb hemit hrow).symm.trans hW)
  have hab : a.round ≤ b.round := hreg.minimal b tb hb hemit hrow
  have hopen : S.hc.opening_slot a.round + 1 ≤ s :=
    (Nat.add_le_add_right
      (Nat.mul_le_mul_right S.hc.R hab) 1).trans hs
  have hheads := hreg.heads_from_firstInterior adm hcom hbelow
    hopen hshor v hv
  have hcompat := Block.compatible_of_preceq_common hC hheads
  have hCT : Block.Preceq C.erase T.erase := by
    rcases (show Block.Preceq C.erase T.erase ∨
        Block.Preceq T.erase C.erase by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompat) with hCT | hTC
    · exact hCT
    · obtain ⟨hTrun, hTheight⟩ := hreg.checkpoint_runBlock adm
      have hTCnamed : NamedBlock.Preceq T C :=
        Protocol.namedPreceq_of_runBlock_erase_preceq
          adm hTrun hCrun hTC
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTCnamed
      rw [hTheight] at hmono
      exact False.elim ((not_lt_of_ge hmono) hheight)
  rw [← hDCfg]
  rw [hTeq] at hCT
  exact Block.preceq_trans hCT
    (Block.preceq_trans
      (Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg K) hKD)

/-- Named relay-parametrized twin of the source admission theorem. The
relay premise is pinned in the same argument order as the compatibility admission
lemma, but returns the named body retained at the read. -/
theorem honestFGSource_preceq_and_mem_before_nextVote_of_relay
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (hrelay : ∀ {p w : V}, p ∈ rho.honest → w ∈ rho.honest →
      ∀ {r : Round}, GradeRoundReady S rho r →
      ∀ {B : NamedBlock V},
        B ∈ (actionStoreAt S rho p r).st.bodies →
        actionFGSource S (actionStoreAt S rho p r) = some B.erase →
        ∀ {read : Time}, S.a r ≤ read → read ≤ rho.horizon →
          Block.Preceq (rho.storeBeforeTime S w read).F B.erase →
          B ∈ (rho.storeBeforeTime S w read).bodies)
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1))
    {read : Time} (hread : S.a b.round ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot} (hnext : read ≤ Protocol.vote_time S.E (s + 1))
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C : NamedBlock V} (hCrun : RunBlock S rho C)
    (hC : Block.Preceq C.erase (voteDutyHead S rho v s))
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1)
    (hF : Block.Preceq (rho.storeBeforeTime S u read).F C.erase) :
    ∃ Y : NamedBlock V, RunBlock S rho Y ∧
      Y.erase ∈ (rho.storeBeforeTime S u read).T ∧
      Block.Preceq C.erase Y.erase ∧
      (Protocol.derive_named S.E S.cfg Y).h = blocked + n + 1 := by
  have hs : S.hc.opening_slot b.round + 1 ≤ s := by
    by_contra hn
    have hslot : s + 1 ≤ S.hc.opening_slot b.round + 1 :=
      Nat.succ_le_succ (Nat.le_of_lt_succ (Nat.lt_of_not_ge hn))
    have htime := vote_time_mono_slots S.E hslot
    exact (not_lt_of_ge htime)
      ((next_vote_time_lt_action S b.round).trans_le (hread.trans hnext))
  obtain ⟨D, J, -, -, hsource, hDmem, -, hDheight, -, -⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm hb hemit hrow
  have hCD := h.honestFGSource_preceq_of_previousHead
    adm hcom hbelow hgst n hb hemit hrow hsource hs hshor hv
      hCrun hC hheight
  have hready := h.honestHeightRow_gradeRoundReady
    adm hcom hbelow hgst n hb hemit hrow
  have hDread : D ∈ (rho.storeBeforeTime S u read).bodies :=
    hrelay hb hu hready hDmem hsource hread hhor
      (Block.preceq_trans hF hCD)
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
  have hDerased : D.erase ∈ (rho.storeBeforeTime S u read).T := by
    change D.erase ∈
      (NamedRun.stateBeforeTime S rho read u).st.core.T
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hDread
  exact ⟨D, runBlock_of_action_body S adm hb hDmem,
    hDerased, hCD, hDheight⟩

/-- A higher named FG source is retained at the later reader without a
separate relay premise: the source's own regime seed supplies the body. -/
theorem honestFGSource_preceq_and_mem_before_nextVote
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1))
    {read : Time} (hread : S.a b.round ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot} (hnext : read ≤ Protocol.vote_time S.E (s + 1))
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C : NamedBlock V} (hCrun : RunBlock S rho C)
    (hC : Block.Preceq C.erase (voteDutyHead S rho v s))
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1)
    (hF : Block.Preceq (rho.storeBeforeTime S u read).F C.erase) :
    ∃ Y : NamedBlock V, RunBlock S rho Y ∧
      Y.erase ∈ (rho.storeBeforeTime S u read).T ∧
      Block.Preceq C.erase Y.erase ∧
      (Protocol.derive_named S.E S.cfg Y).h = blocked + n + 1 := by
  have hs : S.hc.opening_slot b.round + 1 ≤ s := by
    by_contra hn
    have hslot : s + 1 ≤ S.hc.opening_slot b.round + 1 :=
      Nat.succ_le_succ (Nat.le_of_lt_succ (Nat.lt_of_not_ge hn))
    have htime := vote_time_mono_slots S.E hslot
    exact (not_lt_of_ge htime)
      ((next_vote_time_lt_action S b.round).trans_le (hread.trans hnext))
  obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
    h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
  have hseedRow : a.height_pair.erase.height? =
      some (blocked + n + 1) := by
    rcases hreg.seed.targetOrTimeout with heq | heq <;>
      simp only [heq, HeightPair.height?, Nat.add_assoc]
  have hab : a.round ≤ b.round := hreg.minimal b tb hb hemit hrow
  have hseedSlot : S.hc.opening_slot a.round + 1 ≤ s :=
    (Nat.add_le_add_right
      (Nat.mul_le_mul_right S.hc.R hab) 1).trans hs
  have hCCfg := h.honestFGSource_preceq_of_previousHead
    adm hcom hbelow hgst n hreg.seed.signerHonest hreg.seed.emitted
      hseedRow hreg.seed.exactFGSource hseedSlot hshor hv
      hCrun hC hheight
  have haRead : S.a a.round ≤ read :=
    ((action_strictMono S).monotone hab).trans hread
  have hCfgRead : Cfg ∈ (rho.storeBeforeTime S u read).bodies :=
    hreg.sourceMem_at_read adm haRead hu
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
  have hDerased : Cfg.erase ∈ (rho.storeBeforeTime S u read).T := by
    change Cfg.erase ∈
      (NamedRun.stateBeforeTime S rho read u).st.core.T
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hCfgRead
  exact ⟨Cfg,
    runBlock_of_action_body S adm hreg.seed.signerHonest hreg.seed.sourceMem,
    hDerased, hCCfg, hreg.seed.sourceDerivedHeight⟩

/-- An honest SG vote, represented by its named run body, is below every
earlier honest named FG source at a higher named height. -/
theorem honestFGSource_preceq_of_actionSGBlock (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1))
    {Cfg : Block V}
    (hsource : actionFGSource S
      (actionStoreAt S rho b.val_index b.round) = some Cfg)
    {c : Round} (hbc : b.round ≤ c) (hchor : S.a c ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {C : NamedBlock V}
    (hCrun : RunBlock S rho C)
    (hCerased : C.erase = actionSGBlockAt S rho v c)
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1) :
    Block.Preceq C.erase Cfg := by
  obtain ⟨first_n, i, a, ta, Cfg0, T, Tprev', c0, hreg⟩ :=
    h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
  obtain ⟨D, K, hW, hDmem, hsourceD, hDheight, hKmem,
      hKerase, hKheight, hKD, -⟩ :=
    honestHeightRow_confirmationWitness S adm hb hemit hrow
  have hDCfg : D.erase = Cfg := Option.some.inj (hsourceD.symm.trans hsource)
  have hTeq : T.erase =
      (Protocol.derive_named S.E S.cfg K).T_h :=
    Option.some.inj ((hreg.witness_eq adm hcom hbelow hb hemit hrow).symm.trans hW)
  have hpostC : S.E.t_GST ≤ S.a c :=
    hreg.postPrev.trans (Assembly.a_mono S
      ((Nat.sub_le a.round 1).trans
        ((hreg.minimal b tb hb hemit hrow).trans hbc)))
  have hSG := hreg.sgHistory_source adm hcom hbelow
    ((hreg.minimal b tb hb hemit hrow).trans hbc) hchor
      v hv (honest_emits_exact_actionAttestationAt S adm hv c hchor hpostC)
  have hCT : Block.Preceq C.erase T.erase := by
    rcases (show Block.Preceq C.erase T.erase ∨
        Block.Preceq T.erase C.erase by
      rw [hCerased]
      simpa only [Block.compatible, Bool.or_eq_true] using hSG) with hCT | hTC
    · exact hCT
    · obtain ⟨hTrun, hTheight⟩ := hreg.checkpoint_runBlock adm
      have hTCnamed : NamedBlock.Preceq T C :=
        Protocol.namedPreceq_of_runBlock_erase_preceq
          adm hTrun hCrun hTC
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTCnamed
      rw [hTheight] at hmono
      exact False.elim ((not_lt_of_ge hmono) hheight)
  rw [← hDCfg]
  rw [hTeq] at hCT
  exact Block.preceq_trans hCT
    (Block.preceq_trans
      (Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg K) hKD)

/-- A named height crossing in a reader's tree supplies a named stored
descendant of the current honest SG vote. -/
theorem exists_descendant_at_crossing_of_actionSGBlock_of_relay
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (hrelay : ∀ {p w : V}, p ∈ rho.honest → w ∈ rho.honest →
      ∀ {r : Round}, GradeRoundReady S rho r →
      ∀ {B : NamedBlock V},
        B ∈ (actionStoreAt S rho p r).st.bodies →
        actionFGSource S (actionStoreAt S rho p r) = some B.erase →
        ∀ {read : Time}, S.a r ≤ read → read ≤ rho.horizon →
          Block.Preceq (rho.storeBeforeTime S w read).F B.erase →
          B ∈ (rho.storeBeforeTime S w read).bodies)
    (n : Nat) {read : Time} (hhor : read ≤ rho.horizon)
    {c : Round} (hchor : S.a c ≤ rho.horizon)
    (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C X : NamedBlock V} (hCrun : RunBlock S rho C)
    (hCerased : C.erase = actionSGBlockAt S rho v c)
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1)
    (hF : Block.Preceq (rho.storeBeforeTime S u read).F C.erase)
    (hX : X ∈ (rho.storeBeforeTime S u read).bodies)
    (hcross : blocked + n + 1 <
      (Protocol.derive_named S.E S.cfg X).h) :
    ∃ Y : NamedBlock V, RunBlock S rho Y ∧
      Y.erase ∈ (rho.storeBeforeTime S u read).T ∧
      Block.Preceq C.erase Y.erase ∧
      (Protocol.derive_named S.E S.cfg Y).h = blocked + n + 1 := by
  obtain ⟨K, hKX, hKheight, Q, hQ, hwit⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg X
      (blocked + n + 1) (Nat.succ_le_succ (Nat.zero_le _)) hcross
  obtain ⟨p, hpQ, hpHon⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbelow hQ
  obtain ⟨carrier, b, hcarrierX, hbCarrier, hbp, hpair⟩ :=
    hwit p hpQ
  have hb : b.val_index ∈ rho.honest := hbp ▸ hpHon
  have hbChain : b ∈ Protocol.named_chain_attestations X :=
    named_row_mem_chain_of_ancestor_source hcarrierX hbCarrier
  obtain ⟨N, hN, hpast⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed read
  have hXN : X ∈ (rho.stateBefore S N u).st.bodies := by
    simpa only [Run.storeBeforeTime, hN] using hX
  obtain ⟨j, tb, hjN, hjevent, hjout, hemit⟩ :=
    honestCarriedAttestation_emittedBeforeIndex S adm hXN hbChain hb
  have htb : tb < read :=
    hpast j (Event.tick b.val_index tb) hjN hjevent
  have hread : S.a b.round < read := by
    simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using htb
  have hrow : b.height_pair.erase.height? = some (blocked + n + 1) :=
    named_height_of_matches_source hpair
  obtain ⟨Y, J, -, -, hsource, hYmem, -, hYheight, -, -⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm hb hemit hrow
  have hbc : b.round ≤ c :=
    Nat.le_of_lt_succ
      ((action_strictMono S).lt_iff_lt.mp (hread.trans_le hnext))
  have hCY := h.honestFGSource_preceq_of_actionSGBlock
    adm hcom hbelow hgst n hb hemit hrow hsource hbc hchor hv
      hCrun hCerased hheight
  have hready := h.honestHeightRow_gradeRoundReady
    adm hcom hbelow hgst n hb hemit hrow
  have hYread : Y ∈ (rho.storeBeforeTime S u read).bodies :=
    hrelay hb hu hready hYmem hsource hread.le hhor
      (Block.preceq_trans hF hCY)
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
  have hYerased : Y.erase ∈ (rho.storeBeforeTime S u read).T := by
    change Y.erase ∈
      (NamedRun.stateBeforeTime S rho read u).st.core.T
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hYread
  exact ⟨Y, runBlock_of_action_body S adm hb hYmem,
    hYerased, hCY, hYheight⟩

/-- A named height crossing supplies a named stored descendant through the
crossing row's own regime seed. -/
theorem exists_descendant_at_crossing_of_actionSGBlock
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat) {read : Time} (hhor : read ≤ rho.horizon)
    {c : Round} (hchor : S.a c ≤ rho.horizon)
    (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C X : NamedBlock V} (hCrun : RunBlock S rho C)
    (hCerased : C.erase = actionSGBlockAt S rho v c)
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1)
    (hF : Block.Preceq (rho.storeBeforeTime S u read).F C.erase)
    (hX : X ∈ (rho.storeBeforeTime S u read).bodies)
    (hcross : blocked + n + 1 <
      (Protocol.derive_named S.E S.cfg X).h) :
    ∃ Y : NamedBlock V, RunBlock S rho Y ∧
      Y.erase ∈ (rho.storeBeforeTime S u read).T ∧
      Block.Preceq C.erase Y.erase ∧
      (Protocol.derive_named S.E S.cfg Y).h = blocked + n + 1 := by
  obtain ⟨K, hKX, hKheight, Q, hQ, hwit⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg X
      (blocked + n + 1) (Nat.succ_le_succ (Nat.zero_le _)) hcross
  obtain ⟨p, hpQ, hpHon⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbelow hQ
  obtain ⟨carrier, b, hcarrierX, hbCarrier, hbp, hpair⟩ :=
    hwit p hpQ
  have hb : b.val_index ∈ rho.honest := hbp ▸ hpHon
  have hbChain : b ∈ Protocol.named_chain_attestations X :=
    named_row_mem_chain_of_ancestor_source hcarrierX hbCarrier
  obtain ⟨N, hN, hpast⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed read
  have hXN : X ∈ (rho.stateBefore S N u).st.bodies := by
    simpa only [Run.storeBeforeTime, hN] using hX
  obtain ⟨j, tb, hjN, hjevent, hjout, hemit⟩ :=
    honestCarriedAttestation_emittedBeforeIndex S adm hXN hbChain hb
  have htb : tb < read :=
    hpast j (Event.tick b.val_index tb) hjN hjevent
  have hread : S.a b.round < read := by
    simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using htb
  have hrow : b.height_pair.erase.height? = some (blocked + n + 1) :=
    named_height_of_matches_source hpair
  have hbc : b.round ≤ c :=
    Nat.le_of_lt_succ
      ((action_strictMono S).lt_iff_lt.mp (hread.trans_le hnext))
  obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
    h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
  have hseedRow : a.height_pair.erase.height? =
      some (blocked + n + 1) := by
    rcases hreg.seed.targetOrTimeout with heq | heq <;>
      simp only [heq, HeightPair.height?, Nat.add_assoc]
  have hab : a.round ≤ b.round := hreg.minimal b tb hb hemit hrow
  have hac : a.round ≤ c := hab.trans hbc
  have hCCfg := h.honestFGSource_preceq_of_actionSGBlock
    adm hcom hbelow hgst n hreg.seed.signerHonest hreg.seed.emitted
      hseedRow hreg.seed.exactFGSource hac hchor hv
      hCrun hCerased hheight
  have haRead : S.a a.round ≤ read :=
    ((action_strictMono S).monotone hab).trans hread.le
  have hCfgRead : Cfg ∈ (rho.storeBeforeTime S u read).bodies :=
    hreg.sourceMem_at_read adm haRead hu
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
  have hCfgErased : Cfg.erase ∈ (rho.storeBeforeTime S u read).T := by
    change Cfg.erase ∈
      (NamedRun.stateBeforeTime S rho read u).st.core.T
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hCfgRead
  exact ⟨Cfg,
    runBlock_of_action_body S adm hreg.seed.signerHonest hreg.seed.sourceMem,
    hCfgErased, hCCfg, hreg.seed.sourceDerivedHeight⟩

/-- After one delivery delay, an honest SG-voted block is filtered at each
honest reader or is below that reader's FG root. All frontier heights and
crossing witnesses use named run blocks. -/
theorem filteredMem_or_preceq_root_of_actionSGBlock_of_relay
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (hrelay : ∀ {p w : V}, p ∈ rho.honest → w ∈ rho.honest →
      ∀ {r : Round}, GradeRoundReady S rho r →
      ∀ {B : NamedBlock V},
        B ∈ (actionStoreAt S rho p r).st.bodies →
        actionFGSource S (actionStoreAt S rho p r) = some B.erase →
        ∀ {read : Time}, S.a r ≤ read → read ≤ rho.horizon →
          Block.Preceq (rho.storeBeforeTime S w read).F B.erase →
          B ∈ (rho.storeBeforeTime S w read).bodies)
    {deadline : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {c : Round} (hc : deadline ≤ c)
    {read : Time} (hdelay : S.a c + S.E.Δ ≤ read)
    (hhor : read ≤ rho.horizon) (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    actionSGBlockAt S rho v c ∈
        Protocol.get_filtered_block_tree
          (rho.storeBeforeTime S u read).toHealing.toFG ∨
      Block.Preceq (actionSGBlockAt S rho v c)
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u read).toHealing.toFG) := by
  let C := actionSGBlockAt S rho v c
  let st := rho.storeBeforeTime S u read
  have hcread : S.a c ≤ read :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans hdelay
  have hchor : S.a c ≤ rho.horizon := hcread.trans hhor
  have hread : S.a deadline ≤ read :=
    ((action_strictMono S).monotone hc).trans hcread
  have hcompat := h.fgRoot_compatible_actionSGBlock_at_read_after_deadline
    adm hcom hbelow hgst hdeadline hc hchor hread hhor hnext hu hv
  rcases (show Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) C ∨
      Block.Preceq C (Protocol.get_fg_root st.toHealing.toFG) by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompat) with
    hroot | hroot
  · left
    obtain ⟨i, a, ta, Cfg0, T, hreg, ha⟩ :=
      h.exists_regime_before_deadline adm hbelow hgst hdeadline
    have hac : a.round ≤ c := ha.trans hc
    have hpost : S.E.t_GST ≤ S.a c := hreg.postPrev.trans
      ((action_strictMono S).monotone ((Nat.sub_le a.round 1).trans hac))
    have hrootMem :=
      named_fgRoot_mem_filtered_stateBeforeTime S rho read u
    have hFC : Block.Preceq st.F C := Block.preceq_trans
      (GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read
        S rho hrootMem) hroot
    have hCmem : C ∈ st.T :=
      honestBlock_mem_after_delay_of_finalizedPreceq S adm hv hu
        (actionSGBlockAt_mem_storeBeforeTime S rho v c)
        hpost hdelay hhor hFC
    have hCmemTime : C ∈
        (NamedRun.stateBeforeTime S rho read u).st.core.T := by
      simpa only [st, Run.storeBeforeTime] using hCmem
    obtain ⟨Cn, hCnbody, hCnerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho read u hCmemTime
    have hCnbody' : Cn ∈ (rho.storeBeforeTime S u read).bodies := by
      simpa only [Run.storeBeforeTime] using hCnbody
    have hCnrun : RunBlock S rho Cn :=
      runBlock_of_read_body S adm hu hCnbody'
    have hFCn : Block.Preceq st.F Cn.erase := by
      rw [hCnerase]
      exact hFC
    have hstoredC : (st.σ C).h =
        (Protocol.derive_named S.E S.cfg Cn).h := by
      dsimp only [st]
      rw [← hCnerase]
      exact congrArg Protocol.ChainState.h
        (Proofs.NamedStoreBridge.derivedView_stateBeforeTime
          S rho read u Cn hCnbody)
    have hwitness : ∃ Y ∈ st.T, Block.Preceq C Y ∧
        st.h_max - 1 ≤ (st.σ Y).h := by
      by_cases hcap : st.h_max ≤
          (Protocol.derive_named S.E S.cfg Cn).h + 1
      · refine ⟨C, hCmem, Block.preceq_self C, ?_⟩
        rw [hstoredC]
        exact Nat.sub_le_iff_le_add.mpr hcap
      · have hlt : (Protocol.derive_named S.E S.cfg Cn).h + 1 <
            st.h_max := Nat.lt_of_not_le hcap
        have hCH : (Protocol.derive_named S.E S.cfg Cn).h <
            st.h_max - 1 := Nat.lt_sub_of_add_lt hlt
        by_cases hlow : st.h_max - 1 ≤ blocked + 1
        · have hrow : a.height_pair.erase.height? =
              some (blocked + 0 + 1) := by
            rcases hreg.seed.targetOrTimeout with heq | heq <;>
              simp only [heq, HeightPair.height?, Nat.add_zero]
          have hCCfg := h.honestFGSource_preceq_of_actionSGBlock
            adm hcom hbelow hgst 0 hreg.seed.signerHonest
              hreg.seed.emitted hrow hreg.seed.exactFGSource hac hchor hv
              hCnrun hCnerase (hCH.trans_le hlow)
          have hCCfgC : Block.Preceq C Cfg0.erase := by
            rw [← hCnerase]
            exact hCCfg
          have hCfgBody : Cfg0 ∈ (rho.storeBeforeTime S u read).bodies :=
            hrelay hreg.seed.signerHonest hu hreg.ready
              hreg.seed.sourceMem hreg.seed.exactFGSource
              (((action_strictMono S).monotone hac).trans hcread) hhor
              (Block.preceq_trans hFC hCCfgC)
          have hcoh :=
            (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
          have hCfgMem : Cfg0.erase ∈ st.T := by
            change Cfg0.erase ∈
              (NamedRun.stateBeforeTime S rho read u).st.core.T
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hCfgBody
          refine ⟨Cfg0.erase, hCfgMem, hCCfgC, ?_⟩
          have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
            S rho read u Cfg0 hCfgBody
          change st.h_max - 1 ≤ (st.σ Cfg0.erase).h
          rw [show st.σ Cfg0.erase =
              Protocol.derive_named S.E S.cfg Cfg0 by
            simpa only [st, Run.storeBeforeTime] using hview,
            hreg.seed.sourceDerivedHeight]
          exact hlow
        · let n := (st.h_max - 1) - (blocked + 1)
          have heq : blocked + n + 1 = st.h_max - 1 := by
            calc
              _ = n + (blocked + 1) := by ac_rfl
              _ = st.h_max - 1 :=
                Nat.sub_add_cancel
                  (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
          obtain ⟨X, hXbody, hXmax⟩ :=
            Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime
              S rho read u
          have hXbody' : X ∈ (rho.storeBeforeTime S u read).bodies := by
            simpa only [Run.storeBeforeTime] using hXbody
          have hmaxPos : st.h_max ≠ 0 := Nat.ne_of_gt
            ((Nat.zero_le
              ((Protocol.derive_named S.E S.cfg Cn).h + 1)).trans_lt hlt)
          obtain ⟨Y, hYrun, hYmem, hCY, hYheight⟩ :=
            h.exists_descendant_at_crossing_of_actionSGBlock_of_relay
              adm hcom hbelow hgst hrelay n hhor hchor hnext hu hv
                hCnrun hCnerase (heq.symm ▸ hCH) hFCn hXbody'
                (by
                  rw [heq, hXmax]
                  exact Nat.sub_one_lt hmaxPos)
          have hYmemTime : Y.erase ∈
              (NamedRun.stateBeforeTime S rho read u).st.core.T := by
            simpa only [st, Run.storeBeforeTime] using hYmem
          obtain ⟨Yn, hYnbody, hYnerase⟩ :=
            Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
              S rho read u hYmemTime
          have hYnbody' : Yn ∈ (rho.storeBeforeTime S u read).bodies := by
            simpa only [Run.storeBeforeTime] using hYnbody
          have hYnrun : RunBlock S rho Yn :=
            runBlock_of_read_body S adm hu hYnbody'
          have hYnY : Yn = Y := by
            apply adm.toNamedRootCollisionFree.root_injective
              Yn Y hYnrun hYrun Yn Y
                (Or.inl (Proofs.NamedAncestry.named_self Yn))
                (Or.inr (Proofs.NamedAncestry.named_self Y))
            rw [← Proofs.NamedWire.erase_root Yn, hYnerase,
              Proofs.NamedWire.erase_root]
          subst Yn
          have hCYC : Block.Preceq C Y.erase := by
            rw [← hCnerase]
            exact hCY
          refine ⟨Y.erase, hYmem, hCYC, ?_⟩
          have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
            S rho read u Y hYnbody
          change st.h_max - 1 ≤ (st.σ Y.erase).h
          rw [show st.σ Y.erase =
              Protocol.derive_named S.E S.cfg Y by
            simpa only [st, Run.storeBeforeTime] using hview,
            hYheight, heq]
    apply Proofs.Records.mem_filtered_of_mem_V_tree ?_ hroot
    change C ∈ Protocol.V_tree st.toHealing.toFG
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨hCmem, hFC⟩, hwitness⟩
  · exact Or.inr hroot

/-- After one delivery delay, an honest SG-voted block is filtered at each
honest reader or is below that reader's FG root. -/
theorem filteredMem_or_preceq_root_of_actionSGBlock
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {deadline : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {c : Round} (hc : deadline ≤ c)
    {read : Time} (hdelay : S.a c + S.E.Δ ≤ read)
    (hhor : read ≤ rho.horizon) (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    actionSGBlockAt S rho v c ∈
        Protocol.get_filtered_block_tree
          (rho.storeBeforeTime S u read).toHealing.toFG ∨
      Block.Preceq (actionSGBlockAt S rho v c)
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u read).toHealing.toFG) := by
  let C := actionSGBlockAt S rho v c
  let st := rho.storeBeforeTime S u read
  have hcread : S.a c ≤ read :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans hdelay
  have hchor : S.a c ≤ rho.horizon := hcread.trans hhor
  have hread : S.a deadline ≤ read :=
    ((action_strictMono S).monotone hc).trans hcread
  have hcompat := h.fgRoot_compatible_actionSGBlock_at_read_after_deadline
    adm hcom hbelow hgst hdeadline hc hchor hread hhor hnext hu hv
  rcases (show Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) C ∨
      Block.Preceq C (Protocol.get_fg_root st.toHealing.toFG) by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompat) with
    hroot | hroot
  · left
    obtain ⟨i, a, ta, Cfg0, T, hreg, ha⟩ :=
      h.exists_regime_before_deadline adm hbelow hgst hdeadline
    have hac : a.round ≤ c := ha.trans hc
    have hpost : S.E.t_GST ≤ S.a c := hreg.postPrev.trans
      ((action_strictMono S).monotone ((Nat.sub_le a.round 1).trans hac))
    have hrootMem :=
      named_fgRoot_mem_filtered_stateBeforeTime S rho read u
    have hFC : Block.Preceq st.F C := Block.preceq_trans
      (GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read
        S rho hrootMem) hroot
    have hCmem : C ∈ st.T :=
      honestBlock_mem_after_delay_of_finalizedPreceq S adm hv hu
        (actionSGBlockAt_mem_storeBeforeTime S rho v c)
        hpost hdelay hhor hFC
    have hCmemTime : C ∈
        (NamedRun.stateBeforeTime S rho read u).st.core.T := by
      simpa only [st, Run.storeBeforeTime] using hCmem
    obtain ⟨Cn, hCnbody, hCnerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho read u hCmemTime
    have hCnbody' : Cn ∈ (rho.storeBeforeTime S u read).bodies := by
      simpa only [Run.storeBeforeTime] using hCnbody
    have hCnrun : RunBlock S rho Cn :=
      runBlock_of_read_body S adm hu hCnbody'
    have hFCn : Block.Preceq st.F Cn.erase := by
      rw [hCnerase]
      exact hFC
    have hstoredC : (st.σ C).h =
        (Protocol.derive_named S.E S.cfg Cn).h := by
      dsimp only [st]
      rw [← hCnerase]
      exact congrArg Protocol.ChainState.h
        (Proofs.NamedStoreBridge.derivedView_stateBeforeTime
          S rho read u Cn hCnbody)
    have hwitness : ∃ Y ∈ st.T, Block.Preceq C Y ∧
        st.h_max - 1 ≤ (st.σ Y).h := by
      by_cases hcap : st.h_max ≤
          (Protocol.derive_named S.E S.cfg Cn).h + 1
      · refine ⟨C, hCmem, Block.preceq_self C, ?_⟩
        rw [hstoredC]
        exact Nat.sub_le_iff_le_add.mpr hcap
      · have hlt : (Protocol.derive_named S.E S.cfg Cn).h + 1 <
            st.h_max := Nat.lt_of_not_le hcap
        have hCH : (Protocol.derive_named S.E S.cfg Cn).h <
            st.h_max - 1 := Nat.lt_sub_of_add_lt hlt
        by_cases hlow : st.h_max - 1 ≤ blocked + 1
        · have hrow : a.height_pair.erase.height? =
              some (blocked + 0 + 1) := by
            rcases hreg.seed.targetOrTimeout with heq | heq <;>
              simp only [heq, HeightPair.height?, Nat.add_zero]
          have hCCfg := h.honestFGSource_preceq_of_actionSGBlock
            adm hcom hbelow hgst 0 hreg.seed.signerHonest
              hreg.seed.emitted hrow hreg.seed.exactFGSource hac hchor hv
              hCnrun hCnerase (hCH.trans_le hlow)
          have hCCfgC : Block.Preceq C Cfg0.erase := by
            rw [← hCnerase]
            exact hCCfg
          have hCfgBody : Cfg0 ∈ (rho.storeBeforeTime S u read).bodies :=
            hreg.sourceMem_at_read adm
              (((action_strictMono S).monotone hac).trans hcread) hu
          have hcoh :=
            (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
          have hCfgMem : Cfg0.erase ∈ st.T := by
            change Cfg0.erase ∈
              (NamedRun.stateBeforeTime S rho read u).st.core.T
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hCfgBody
          refine ⟨Cfg0.erase, hCfgMem, hCCfgC, ?_⟩
          have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
            S rho read u Cfg0 hCfgBody
          change st.h_max - 1 ≤ (st.σ Cfg0.erase).h
          rw [show st.σ Cfg0.erase =
              Protocol.derive_named S.E S.cfg Cfg0 by
            simpa only [st, Run.storeBeforeTime] using hview,
            hreg.seed.sourceDerivedHeight]
          exact hlow
        · let n := (st.h_max - 1) - (blocked + 1)
          have heq : blocked + n + 1 = st.h_max - 1 := by
            calc
              _ = n + (blocked + 1) := by ac_rfl
              _ = st.h_max - 1 :=
                Nat.sub_add_cancel
                  (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
          obtain ⟨X, hXbody, hXmax⟩ :=
            Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime
              S rho read u
          have hXbody' : X ∈ (rho.storeBeforeTime S u read).bodies := by
            simpa only [Run.storeBeforeTime] using hXbody
          have hmaxPos : st.h_max ≠ 0 := Nat.ne_of_gt
            ((Nat.zero_le
              ((Protocol.derive_named S.E S.cfg Cn).h + 1)).trans_lt hlt)
          obtain ⟨Y, hYrun, hYmem, hCY, hYheight⟩ :=
            h.exists_descendant_at_crossing_of_actionSGBlock
              adm hcom hbelow hgst n hhor hchor hnext hu hv
                hCnrun hCnerase (heq.symm ▸ hCH) hFCn hXbody'
                (by
                  rw [heq, hXmax]
                  exact Nat.sub_one_lt hmaxPos)
          have hYmemTime : Y.erase ∈
              (NamedRun.stateBeforeTime S rho read u).st.core.T := by
            simpa only [st, Run.storeBeforeTime] using hYmem
          obtain ⟨Yn, hYnbody, hYnerase⟩ :=
            Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
              S rho read u hYmemTime
          have hYnbody' : Yn ∈ (rho.storeBeforeTime S u read).bodies := by
            simpa only [Run.storeBeforeTime] using hYnbody
          have hYnrun : RunBlock S rho Yn :=
            runBlock_of_read_body S adm hu hYnbody'
          have hYnY : Yn = Y := by
            apply adm.toNamedRootCollisionFree.root_injective
              Yn Y hYnrun hYrun Yn Y
                (Or.inl (Proofs.NamedAncestry.named_self Yn))
                (Or.inr (Proofs.NamedAncestry.named_self Y))
            rw [← Proofs.NamedWire.erase_root Yn, hYnerase,
              Proofs.NamedWire.erase_root]
          subst Yn
          have hCYC : Block.Preceq C Y.erase := by
            rw [← hCnerase]
            exact hCY
          refine ⟨Y.erase, hYmem, hCYC, ?_⟩
          have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
            S rho read u Y hYnbody
          change st.h_max - 1 ≤ (st.σ Y.erase).h
          rw [show st.σ Y.erase =
              Protocol.derive_named S.E S.cfg Y by
            simpa only [st, Run.storeBeforeTime] using hview,
            hYheight, heq]
    apply Proofs.Records.mem_filtered_of_mem_V_tree ?_ hroot
    change C ∈ Protocol.V_tree st.toHealing.toFG
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨hCmem, hFC⟩, hwitness⟩
  · exact Or.inr hroot

/-- Every named run-block ancestor of an honest SG vote is below every
earlier honest FG source at a higher named height. -/
theorem honestFGSource_preceq_of_actionSGBlock_ancestor
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1))
    {Cfg : Block V}
    (hsource : actionFGSource S
      (actionStoreAt S rho b.val_index b.round) = some Cfg)
    {c : Round} (hbc : b.round ≤ c) (hchor : S.a c ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {C : NamedBlock V}
    (hCrun : RunBlock S rho C)
    (hCle : Block.Preceq C.erase (actionSGBlockAt S rho v c))
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1) :
    Block.Preceq C.erase Cfg := by
  obtain ⟨first_n, i, a, ta, Cfg0, T, Tprev', c0, hreg⟩ :=
    h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
  obtain ⟨D, K, hW, hDmem, hsourceD, hDheight, hKmem,
      hKerase, hKheight, hKD, -⟩ :=
    honestHeightRow_confirmationWitness S adm hb hemit hrow
  have hDCfg : D.erase = Cfg := Option.some.inj (hsourceD.symm.trans hsource)
  have hTeq : T.erase =
      (Protocol.derive_named S.E S.cfg K).T_h :=
    Option.some.inj
      ((hreg.witness_eq adm hcom hbelow hb hemit hrow).symm.trans hW)
  have hpostC : S.E.t_GST ≤ S.a c :=
    hreg.postPrev.trans (Assembly.a_mono S
      ((Nat.sub_le a.round 1).trans
        ((hreg.minimal b tb hb hemit hrow).trans hbc)))
  have hSG := hreg.sgHistory_source adm hcom hbelow
    ((hreg.minimal b tb hb hemit hrow).trans hbc) hchor
      v hv (honest_emits_exact_actionAttestationAt S adm hv c hchor hpostC)
  have hCTor : Block.Preceq C.erase T.erase ∨
      Block.Preceq T.erase C.erase := by
    rcases (show Block.Preceq (actionSGBlockAt S rho v c) T.erase ∨
        Block.Preceq T.erase (actionSGBlockAt S rho v c) by
      simpa only [Block.compatible, Bool.or_eq_true] using hSG) with hST | hTS
    · exact Or.inl (Block.preceq_trans hCle hST)
    · exact Block.preceq_linear hCle hTS
  have hCT : Block.Preceq C.erase T.erase := by
    rcases hCTor with hCT | hTC
    · exact hCT
    · obtain ⟨hTrun, hTheight⟩ := hreg.checkpoint_runBlock adm
      have hTCnamed : NamedBlock.Preceq T C :=
        Protocol.namedPreceq_of_runBlock_erase_preceq
          adm hTrun hCrun hTC
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTCnamed
      rw [hTheight] at hmono
      exact False.elim ((not_lt_of_ge hmono) hheight)
  rw [← hDCfg]
  rw [hTeq] at hCT
  exact Block.preceq_trans hCT
    (Block.preceq_trans
      (Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg K) hKD)

/-- A named crossing supplies a named stored descendant of any named
run-block ancestor of the current honest SG vote. -/
theorem exists_descendant_at_crossing_of_actionSGBlock_ancestor_of_relay
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (hrelay : ∀ {p w : V}, p ∈ rho.honest → w ∈ rho.honest →
      ∀ {r : Round}, GradeRoundReady S rho r →
      ∀ {B : NamedBlock V},
        B ∈ (actionStoreAt S rho p r).st.bodies →
        actionFGSource S (actionStoreAt S rho p r) = some B.erase →
        ∀ {read : Time}, S.a r ≤ read → read ≤ rho.horizon →
          Block.Preceq (rho.storeBeforeTime S w read).F B.erase →
          B ∈ (rho.storeBeforeTime S w read).bodies)
    (n : Nat) {read : Time} (hhor : read ≤ rho.horizon)
    {c : Round} (hchor : S.a c ≤ rho.horizon)
    (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C X : NamedBlock V} (hCrun : RunBlock S rho C)
    (hCle : Block.Preceq C.erase (actionSGBlockAt S rho v c))
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1)
    (hF : Block.Preceq (rho.storeBeforeTime S u read).F C.erase)
    (hX : X ∈ (rho.storeBeforeTime S u read).bodies)
    (hcross : blocked + n + 1 <
      (Protocol.derive_named S.E S.cfg X).h) :
    ∃ Y : NamedBlock V, RunBlock S rho Y ∧
      Y.erase ∈ (rho.storeBeforeTime S u read).T ∧
      Block.Preceq C.erase Y.erase ∧
      (Protocol.derive_named S.E S.cfg Y).h = blocked + n + 1 := by
  obtain ⟨K, hKX, hKheight, Q, hQ, hwit⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg X
      (blocked + n + 1) (Nat.succ_le_succ (Nat.zero_le _)) hcross
  obtain ⟨p, hpQ, hpHon⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbelow hQ
  obtain ⟨carrier, b, hcarrierX, hbCarrier, hbp, hpair⟩ :=
    hwit p hpQ
  have hb : b.val_index ∈ rho.honest := hbp ▸ hpHon
  have hbChain : b ∈ Protocol.named_chain_attestations X :=
    named_row_mem_chain_of_ancestor_source hcarrierX hbCarrier
  obtain ⟨N, hN, hpast⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed read
  have hXN : X ∈ (rho.stateBefore S N u).st.bodies := by
    simpa only [Run.storeBeforeTime, hN] using hX
  obtain ⟨j, tb, hjN, hjevent, hjout, hemit⟩ :=
    honestCarriedAttestation_emittedBeforeIndex S adm hXN hbChain hb
  have htb : tb < read :=
    hpast j (Event.tick b.val_index tb) hjN hjevent
  have hread : S.a b.round < read := by
    simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using htb
  have hrow : b.height_pair.erase.height? = some (blocked + n + 1) :=
    named_height_of_matches_source hpair
  obtain ⟨Y, J, -, -, hsource, hYmem, -, hYheight, -, -⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm hb hemit hrow
  have hbc : b.round ≤ c :=
    Nat.le_of_lt_succ
      ((action_strictMono S).lt_iff_lt.mp (hread.trans_le hnext))
  have hCY := h.honestFGSource_preceq_of_actionSGBlock_ancestor
    adm hcom hbelow hgst n hb hemit hrow hsource hbc hchor hv
      hCrun hCle hheight
  have hready := h.honestHeightRow_gradeRoundReady
    adm hcom hbelow hgst n hb hemit hrow
  have hYread : Y ∈ (rho.storeBeforeTime S u read).bodies :=
    hrelay hb hu hready hYmem hsource hread.le hhor
      (Block.preceq_trans hF hCY)
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
  have hYerased : Y.erase ∈ (rho.storeBeforeTime S u read).T := by
    change Y.erase ∈
      (NamedRun.stateBeforeTime S rho read u).st.core.T
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hYread
  exact ⟨Y, runBlock_of_action_body S adm hb hYmem,
    hYerased, hCY, hYheight⟩

/-- A named crossing supplies a named stored descendant of any named
run-block ancestor of the current honest SG vote through the row's regime
seed. -/
theorem exists_descendant_at_crossing_of_actionSGBlock_ancestor
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (n : Nat) {read : Time} (hhor : read ≤ rho.horizon)
    {c : Round} (hchor : S.a c ≤ rho.horizon)
    (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C X : NamedBlock V} (hCrun : RunBlock S rho C)
    (hCle : Block.Preceq C.erase (actionSGBlockAt S rho v c))
    (hheight : (Protocol.derive_named S.E S.cfg C).h <
      blocked + n + 1)
    (hF : Block.Preceq (rho.storeBeforeTime S u read).F C.erase)
    (hX : X ∈ (rho.storeBeforeTime S u read).bodies)
    (hcross : blocked + n + 1 <
      (Protocol.derive_named S.E S.cfg X).h) :
    ∃ Y : NamedBlock V, RunBlock S rho Y ∧
      Y.erase ∈ (rho.storeBeforeTime S u read).T ∧
      Block.Preceq C.erase Y.erase ∧
      (Protocol.derive_named S.E S.cfg Y).h = blocked + n + 1 := by
  obtain ⟨K, hKX, hKheight, Q, hQ, hwit⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg X
      (blocked + n + 1) (Nat.succ_le_succ (Nat.zero_le _)) hcross
  obtain ⟨p, hpQ, hpHon⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbelow hQ
  obtain ⟨carrier, b, hcarrierX, hbCarrier, hbp, hpair⟩ :=
    hwit p hpQ
  have hb : b.val_index ∈ rho.honest := hbp ▸ hpHon
  have hbChain : b ∈ Protocol.named_chain_attestations X :=
    named_row_mem_chain_of_ancestor_source hcarrierX hbCarrier
  obtain ⟨N, hN, hpast⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed read
  have hXN : X ∈ (rho.stateBefore S N u).st.bodies := by
    simpa only [Run.storeBeforeTime, hN] using hX
  obtain ⟨j, tb, hjN, hjevent, hjout, hemit⟩ :=
    honestCarriedAttestation_emittedBeforeIndex S adm hXN hbChain hb
  have htb : tb < read :=
    hpast j (Event.tick b.val_index tb) hjN hjevent
  have hread : S.a b.round < read := by
    simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using htb
  have hrow : b.height_pair.erase.height? = some (blocked + n + 1) :=
    named_height_of_matches_source hpair
  have hbc : b.round ≤ c :=
    Nat.le_of_lt_succ
      ((action_strictMono S).lt_iff_lt.mp (hread.trans_le hnext))
  obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
    h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
  have hseedRow : a.height_pair.erase.height? =
      some (blocked + n + 1) := by
    rcases hreg.seed.targetOrTimeout with heq | heq <;>
      simp only [heq, HeightPair.height?, Nat.add_assoc]
  have hab : a.round ≤ b.round := hreg.minimal b tb hb hemit hrow
  have hac : a.round ≤ c := hab.trans hbc
  have hCCfg := h.honestFGSource_preceq_of_actionSGBlock_ancestor
    adm hcom hbelow hgst n hreg.seed.signerHonest hreg.seed.emitted
      hseedRow hreg.seed.exactFGSource hac hchor hv
      hCrun hCle hheight
  have haRead : S.a a.round ≤ read :=
    ((action_strictMono S).monotone hab).trans hread.le
  have hCfgRead : Cfg ∈ (rho.storeBeforeTime S u read).bodies :=
    hreg.sourceMem_at_read adm haRead hu
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
  have hCfgErased : Cfg.erase ∈ (rho.storeBeforeTime S u read).T := by
    change Cfg.erase ∈
      (NamedRun.stateBeforeTime S rho read u).st.core.T
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hCfgRead
  exact ⟨Cfg,
    runBlock_of_action_body S adm hreg.seed.signerHonest hreg.seed.sourceMem,
    hCfgErased, hCCfg, hreg.seed.sourceDerivedHeight⟩

/-- From the base deadline through the next action, a stored named ancestor
of an honest SG vote is filtered at the reader or is below its FG root. -/
theorem filteredMem_or_preceq_root_of_actionSGBlock_ancestor_of_relay
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    (hrelay : ∀ {p w : V}, p ∈ rho.honest → w ∈ rho.honest →
      ∀ {r : Round}, GradeRoundReady S rho r →
      ∀ {B : NamedBlock V},
        B ∈ (actionStoreAt S rho p r).st.bodies →
        actionFGSource S (actionStoreAt S rho p r) = some B.erase →
        ∀ {read : Time}, S.a r ≤ read → read ≤ rho.horizon →
          Block.Preceq (rho.storeBeforeTime S w read).F B.erase →
          B ∈ (rho.storeBeforeTime S w read).bodies)
    {deadline : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {c : Round} (hc : deadline ≤ c) (hchor : S.a c ≤ rho.horizon)
    {read : Time} (hread : S.a deadline ≤ read)
    (hhor : read ≤ rho.horizon) (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C : NamedBlock V} (hCrun : RunBlock S rho C)
    (hCle : Block.Preceq C.erase (actionSGBlockAt S rho v c))
    (hCbody : C ∈ (rho.storeBeforeTime S u read).bodies) :
    C.erase ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S u read).toHealing.toFG ∨
      Block.Preceq C.erase
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u read).toHealing.toFG) := by
  let st := rho.storeBeforeTime S u read
  have hcompatVote :=
    h.fgRoot_compatible_actionSGBlock_at_read_after_deadline
      adm hcom hbelow hgst hdeadline hc hchor hread hhor hnext hu hv
  have hrootVote : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG)
        (actionSGBlockAt S rho v c) ∨
      Block.Preceq (actionSGBlockAt S rho v c)
        (Protocol.get_fg_root st.toHealing.toFG) := by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompatVote
  have hrootCases : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG) C.erase ∨
      Block.Preceq C.erase
        (Protocol.get_fg_root st.toHealing.toFG) := by
    rcases hrootVote with hrv | hvr
    · exact Block.preceq_linear hrv hCle
    · exact Or.inr (Block.preceq_trans hCle hvr)
  rcases hrootCases with hroot | hroot
  · left
    obtain ⟨i, a, ta, Cfg0, T, hreg, ha⟩ :=
      h.exists_regime_before_deadline adm hbelow hgst hdeadline
    have hac : a.round ≤ c := ha.trans hc
    have hrootMem :=
      named_fgRoot_mem_filtered_stateBeforeTime S rho read u
    have hFC : Block.Preceq st.F C.erase := Block.preceq_trans
      (GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read
        S rho hrootMem) hroot
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
    have hCmem : C.erase ∈ st.T := by
      change C.erase ∈
        (NamedRun.stateBeforeTime S rho read u).st.core.T
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hCbody
    have hstoredC : (st.σ C.erase).h =
        (Protocol.derive_named S.E S.cfg C).h := by
      have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
        S rho read u C hCbody
      exact congrArg Protocol.ChainState.h
        (by simpa only [st, Run.storeBeforeTime] using hview)
    have hwitness : ∃ Y ∈ st.T, Block.Preceq C.erase Y ∧
        st.h_max - 1 ≤ (st.σ Y).h := by
      by_cases hcap : st.h_max ≤
          (Protocol.derive_named S.E S.cfg C).h + 1
      · refine ⟨C.erase, hCmem, Block.preceq_self C.erase, ?_⟩
        rw [hstoredC]
        exact Nat.sub_le_iff_le_add.mpr hcap
      · have hlt : (Protocol.derive_named S.E S.cfg C).h + 1 <
            st.h_max := Nat.lt_of_not_le hcap
        have hCH : (Protocol.derive_named S.E S.cfg C).h <
            st.h_max - 1 := Nat.lt_sub_of_add_lt hlt
        by_cases hlow : st.h_max - 1 ≤ blocked + 1
        · have hrow : a.height_pair.erase.height? =
              some (blocked + 0 + 1) := by
            rcases hreg.seed.targetOrTimeout with heq | heq <;>
              simp only [heq, HeightPair.height?, Nat.add_zero]
          have hCCfg := h.honestFGSource_preceq_of_actionSGBlock_ancestor
            adm hcom hbelow hgst 0 hreg.seed.signerHonest
              hreg.seed.emitted hrow hreg.seed.exactFGSource hac hchor hv
              hCrun hCle (hCH.trans_le hlow)
          have hCfgBody : Cfg0 ∈ (rho.storeBeforeTime S u read).bodies :=
            hrelay hreg.seed.signerHonest hu hreg.ready
              hreg.seed.sourceMem hreg.seed.exactFGSource
              (((action_strictMono S).monotone ha).trans hread) hhor
              (Block.preceq_trans hFC hCCfg)
          have hCfgMem : Cfg0.erase ∈ st.T := by
            change Cfg0.erase ∈
              (NamedRun.stateBeforeTime S rho read u).st.core.T
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hCfgBody
          refine ⟨Cfg0.erase, hCfgMem, hCCfg, ?_⟩
          have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
            S rho read u Cfg0 hCfgBody
          change st.h_max - 1 ≤ (st.σ Cfg0.erase).h
          rw [show st.σ Cfg0.erase =
              Protocol.derive_named S.E S.cfg Cfg0 by
            simpa only [st, Run.storeBeforeTime] using hview,
            hreg.seed.sourceDerivedHeight]
          exact hlow
        · let n := (st.h_max - 1) - (blocked + 1)
          have heq : blocked + n + 1 = st.h_max - 1 := by
            calc
              _ = n + (blocked + 1) := by ac_rfl
              _ = st.h_max - 1 :=
                Nat.sub_add_cancel
                  (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
          obtain ⟨X, hXbody, hXmax⟩ :=
            Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime S rho read u
          have hXbody' : X ∈ (rho.storeBeforeTime S u read).bodies := by
            simpa only [Run.storeBeforeTime] using hXbody
          have hmaxPos : st.h_max ≠ 0 := Nat.ne_of_gt
            ((Nat.zero_le
              ((Protocol.derive_named S.E S.cfg C).h + 1)).trans_lt hlt)
          obtain ⟨Y, hYrun, hYmem, hCY, hYheight⟩ :=
            h.exists_descendant_at_crossing_of_actionSGBlock_ancestor_of_relay
              adm hcom hbelow hgst hrelay n hhor hchor hnext hu hv
                hCrun hCle (heq.symm ▸ hCH) hFC hXbody'
                (by
                  rw [heq, hXmax]
                  exact Nat.sub_one_lt hmaxPos)
          have hYmemTime : Y.erase ∈
              (NamedRun.stateBeforeTime S rho read u).st.core.T := by
            simpa only [st, Run.storeBeforeTime] using hYmem
          obtain ⟨Yn, hYnbody, hYnerase⟩ :=
            Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
              S rho read u hYmemTime
          have hYnbody' : Yn ∈ (rho.storeBeforeTime S u read).bodies := by
            simpa only [Run.storeBeforeTime] using hYnbody
          have hYnrun : RunBlock S rho Yn :=
            runBlock_of_read_body S adm hu hYnbody'
          have hYnY : Yn = Y := by
            apply adm.toNamedRootCollisionFree.root_injective
              Yn Y hYnrun hYrun Yn Y
                (Or.inl (Proofs.NamedAncestry.named_self Yn))
                (Or.inr (Proofs.NamedAncestry.named_self Y))
            rw [← Proofs.NamedWire.erase_root Yn, hYnerase,
              Proofs.NamedWire.erase_root]
          subst Yn
          refine ⟨Y.erase, hYmem, hCY, ?_⟩
          have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
            S rho read u Y hYnbody
          change st.h_max - 1 ≤ (st.σ Y.erase).h
          rw [show st.σ Y.erase =
              Protocol.derive_named S.E S.cfg Y by
            simpa only [st, Run.storeBeforeTime] using hview,
            hYheight, heq]
    apply Proofs.Records.mem_filtered_of_mem_V_tree ?_ hroot
    change C.erase ∈ Protocol.V_tree st.toHealing.toFG
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨hCmem, hFC⟩, hwitness⟩
  · exact Or.inr hroot

/-- From the base deadline through the next action, a stored named ancestor
of an honest SG vote is filtered at the reader or is below its FG root. -/
theorem filteredMem_or_preceq_root_of_actionSGBlock_ancestor
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {deadline : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {c : Round} (hc : deadline ≤ c) (hchor : S.a c ≤ rho.horizon)
    {read : Time} (hread : S.a deadline ≤ read)
    (hhor : read ≤ rho.horizon) (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C : NamedBlock V} (hCrun : RunBlock S rho C)
    (hCle : Block.Preceq C.erase (actionSGBlockAt S rho v c))
    (hCbody : C ∈ (rho.storeBeforeTime S u read).bodies) :
    C.erase ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S u read).toHealing.toFG ∨
      Block.Preceq C.erase
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u read).toHealing.toFG) := by
  let st := rho.storeBeforeTime S u read
  have hcompatVote :=
    h.fgRoot_compatible_actionSGBlock_at_read_after_deadline
      adm hcom hbelow hgst hdeadline hc hchor hread hhor hnext hu hv
  have hrootVote : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG)
        (actionSGBlockAt S rho v c) ∨
      Block.Preceq (actionSGBlockAt S rho v c)
        (Protocol.get_fg_root st.toHealing.toFG) := by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompatVote
  have hrootCases : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG) C.erase ∨
      Block.Preceq C.erase
        (Protocol.get_fg_root st.toHealing.toFG) := by
    rcases hrootVote with hrv | hvr
    · exact Block.preceq_linear hrv hCle
    · exact Or.inr (Block.preceq_trans hCle hvr)
  rcases hrootCases with hroot | hroot
  · left
    obtain ⟨i, a, ta, Cfg0, T, hreg, ha⟩ :=
      h.exists_regime_before_deadline adm hbelow hgst hdeadline
    have hac : a.round ≤ c := ha.trans hc
    have hrootMem :=
      named_fgRoot_mem_filtered_stateBeforeTime S rho read u
    have hFC : Block.Preceq st.F C.erase := Block.preceq_trans
      (GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read
        S rho hrootMem) hroot
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read u).1.1.1
    have hCmem : C.erase ∈ st.T := by
      change C.erase ∈
        (NamedRun.stateBeforeTime S rho read u).st.core.T
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hCbody
    have hstoredC : (st.σ C.erase).h =
        (Protocol.derive_named S.E S.cfg C).h := by
      have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
        S rho read u C hCbody
      exact congrArg Protocol.ChainState.h
        (by simpa only [st, Run.storeBeforeTime] using hview)
    have hwitness : ∃ Y ∈ st.T, Block.Preceq C.erase Y ∧
        st.h_max - 1 ≤ (st.σ Y).h := by
      by_cases hcap : st.h_max ≤
          (Protocol.derive_named S.E S.cfg C).h + 1
      · refine ⟨C.erase, hCmem, Block.preceq_self C.erase, ?_⟩
        rw [hstoredC]
        exact Nat.sub_le_iff_le_add.mpr hcap
      · have hlt : (Protocol.derive_named S.E S.cfg C).h + 1 <
            st.h_max := Nat.lt_of_not_le hcap
        have hCH : (Protocol.derive_named S.E S.cfg C).h <
            st.h_max - 1 := Nat.lt_sub_of_add_lt hlt
        by_cases hlow : st.h_max - 1 ≤ blocked + 1
        · have hrow : a.height_pair.erase.height? =
              some (blocked + 0 + 1) := by
            rcases hreg.seed.targetOrTimeout with heq | heq <;>
              simp only [heq, HeightPair.height?, Nat.add_zero]
          have hCCfg := h.honestFGSource_preceq_of_actionSGBlock_ancestor
            adm hcom hbelow hgst 0 hreg.seed.signerHonest
              hreg.seed.emitted hrow hreg.seed.exactFGSource hac hchor hv
              hCrun hCle (hCH.trans_le hlow)
          have hCfgBody : Cfg0 ∈ (rho.storeBeforeTime S u read).bodies :=
            hreg.sourceMem_at_read adm
              (((action_strictMono S).monotone ha).trans hread) hu
          have hCfgMem : Cfg0.erase ∈ st.T := by
            change Cfg0.erase ∈
              (NamedRun.stateBeforeTime S rho read u).st.core.T
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hCfgBody
          refine ⟨Cfg0.erase, hCfgMem, hCCfg, ?_⟩
          have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
            S rho read u Cfg0 hCfgBody
          change st.h_max - 1 ≤ (st.σ Cfg0.erase).h
          rw [show st.σ Cfg0.erase =
              Protocol.derive_named S.E S.cfg Cfg0 by
            simpa only [st, Run.storeBeforeTime] using hview,
            hreg.seed.sourceDerivedHeight]
          exact hlow
        · let n := (st.h_max - 1) - (blocked + 1)
          have heq : blocked + n + 1 = st.h_max - 1 := by
            calc
              _ = n + (blocked + 1) := by ac_rfl
              _ = st.h_max - 1 :=
                Nat.sub_add_cancel
                  (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
          obtain ⟨X, hXbody, hXmax⟩ :=
            Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime S rho read u
          have hXbody' : X ∈ (rho.storeBeforeTime S u read).bodies := by
            simpa only [Run.storeBeforeTime] using hXbody
          have hmaxPos : st.h_max ≠ 0 := Nat.ne_of_gt
            ((Nat.zero_le
              ((Protocol.derive_named S.E S.cfg C).h + 1)).trans_lt hlt)
          obtain ⟨Y, hYrun, hYmem, hCY, hYheight⟩ :=
            h.exists_descendant_at_crossing_of_actionSGBlock_ancestor
              adm hcom hbelow hgst n hhor hchor hnext hu hv
                hCrun hCle (heq.symm ▸ hCH) hFC hXbody'
                (by
                  rw [heq, hXmax]
                  exact Nat.sub_one_lt hmaxPos)
          have hYmemTime : Y.erase ∈
              (NamedRun.stateBeforeTime S rho read u).st.core.T := by
            simpa only [st, Run.storeBeforeTime] using hYmem
          obtain ⟨Yn, hYnbody, hYnerase⟩ :=
            Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
              S rho read u hYmemTime
          have hYnbody' : Yn ∈ (rho.storeBeforeTime S u read).bodies := by
            simpa only [Run.storeBeforeTime] using hYnbody
          have hYnrun : RunBlock S rho Yn :=
            runBlock_of_read_body S adm hu hYnbody'
          have hYnY : Yn = Y := by
            apply adm.toNamedRootCollisionFree.root_injective
              Yn Y hYnrun hYrun Yn Y
                (Or.inl (Proofs.NamedAncestry.named_self Yn))
                (Or.inr (Proofs.NamedAncestry.named_self Y))
            rw [← Proofs.NamedWire.erase_root Yn, hYnerase,
              Proofs.NamedWire.erase_root]
          subst Yn
          refine ⟨Y.erase, hYmem, hCY, ?_⟩
          have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
            S rho read u Y hYnbody
          change st.h_max - 1 ≤ (st.σ Y.erase).h
          rw [show st.σ Y.erase =
              Protocol.derive_named S.E S.cfg Y by
            simpa only [st, Run.storeBeforeTime] using hview,
            hYheight, heq]
    apply Proofs.Records.mem_filtered_of_mem_V_tree ?_ hroot
    change C.erase ∈ Protocol.V_tree st.toHealing.toFG
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨hCmem, hFC⟩, hwitness⟩
  · exact Or.inr hroot

end NamedHeightRegimeBaseRun

/-! ## Direct post-GST wrappers -/

private theorem storeGrade_mem_domainTree_source
    (S : Setup V) (rho : Run V) {r : Round} {w : V}
    {p : DecoupledConsensusModel.Protocol.Phase} {Q : Block V}
    (hgrade : PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r p) w).st r p Q = true) :
    Q ∈ (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r p) w).st.core.T := by
  let n := PhaseGrades.readAt S rho
    (DecoupledConsensusModel.Protocol.domain S.E S.hc r p) w
  have hg : DecoupledConsensusModel.Protocol.gradeBool S.E
      n.st.core.toHealing.gradeView n.st.core.F S.hc.η_SG r
      (DecoupledConsensusModel.Protocol.early S.E S.hc r p)
      (DecoupledConsensusModel.Protocol.late S.E S.hc r p) Q = true := by
    simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade, n] using hgrade
  simp only [DecoupledConsensusModel.Protocol.gradeBool,
    decide_eq_true_eq] at hg
  have hne : (Finset.univ.filter fun s =>
      DecoupledConsensusModel.Protocol.positive n.st.core.toHealing.gradeView
        n.st.core.F S.hc.η_SG r
        (DecoupledConsensusModel.Protocol.early S.E S.hc r p)
        (DecoupledConsensusModel.Protocol.late S.E S.hc r p) s Q = true).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hg
    simp only [Electorate.weightOf, Finset.sum_empty] at hg
    omega
  obtain ⟨s, hs⟩ := hne
  obtain ⟨tok, -, -, hcov, -, -⟩ := by
    simpa only [DecoupledConsensusModel.Protocol.positive,
      decide_eq_true_eq] using (Finset.mem_filter.mp hs).2
  cases hkey : tok.key with
  | none =>
      simp [DecoupledConsensusModel.Protocol.localCovers,
        Protocol.head_covers, hkey] at hcov
  | some root =>
      cases hfind : Block.find? n.st.core.toHealing.gradeView.T root with
      | none =>
          simp [DecoupledConsensusModel.Protocol.localCovers,
            Protocol.head_covers, hkey, hfind] at hcov
      | some H =>
          have hQH : Block.Preceq Q H := by
            simpa [DecoupledConsensusModel.Protocol.localCovers,
              Protocol.head_covers, hkey, hfind] using hcov
          have hHT : H ∈ n.st.core.T := Proofs.HealingLemmas.find?_mem hfind
          have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime
            S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r p) w
          exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
            Q H hHT hQH


/-- Direct post-GST filter split for a stored named ancestor of an honest SG
vote, using the regime seed relay. -/
theorem actionSGBlock_filteredMem_or_preceq_root_after_GST_ancestor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round}
    (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hchor : S.a c ≤ rho.horizon)
    {read : Time}
    (hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ read)
    (hhor : read ≤ rho.horizon) (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C : NamedBlock V} (hCrun : RunBlock S rho C)
    (hCle : Block.Preceq C.erase (actionSGBlockAt S rho v c))
    (hCbody : C ∈ (rho.storeBeforeTime S u read).bodies) :
    C.erase ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S u read).toHealing.toFG ∨
      Block.Preceq C.erase
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u read).toHealing.toFG) := by
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost (hread.trans hhor)
  exact hbase.filteredMem_or_preceq_root_of_actionSGBlock_ancestor
    adm hcom hbelow (gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost)
      hfirst hc hchor hread hhor hnext hu hv hCrun hCle hCbody


/-- The selected prepared Q2 instance of the named post-GST ancestor split,
using the regime seed relay. -/
theorem selectedG2_filteredMem_or_preceq_root_after_GST_ancestor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round}
    (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (ready : GradeRoundReady S rho c) (hchor : S.a c ≤ rho.horizon)
    {read : Time}
    (hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ read)
    (hcut : S.hc.Γ_0 S.E.Δ c ≤ read)
    (hhor : read ≤ rho.horizon) (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {Q : NamedBlock V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v c) c =
      some Q.erase) :
    Q.erase ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S u read).toHealing.toFG ∨
      Block.Preceq Q.erase
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u read).toHealing.toFG) := by
  have hdeadlinePos : 0 <
      fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.zero_lt_succ rGST).trans_le
      (Nat.le_add_right (rGST + 1) _)
  have hcpos : 0 < c := hdeadlinePos.trans_le hc
  have hguard := actionQ2_crossReaderBodyReadyGuard_history
    S adm hbelow hcpos ready hv u hu Q.erase hQ
  have hG1 := selectedG2_G1_at_read_after_cutoff
    S adm hbelow ready hchor hv hu hQ hguard
  have hQdomain := storeGrade_mem_domainTree_source S rho hG1
  have hdomain : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 =
      S.hc.Γ_0 S.E.Δ c := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.Γ_0_eq_proposal_time S.hc S.E c).symm
  have hQdomain' : Q.erase ∈
      (rho.storeBeforeTime S u
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1)).T := by
    simpa only [Run.storeBeforeTime] using hQdomain
  have hQread : Q.erase ∈ (rho.storeBeforeTime S u read).T := by
    rw [storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed] at hQdomain' ⊢
    exact stateBefore_T_subset S rho u _
      (strictEventIndex_mono rho (hdomain.trans_le hcut)) hQdomain'
  have hQreadTime : Q.erase ∈
      (NamedRun.stateBeforeTime S rho read u).st.core.T := by
    simpa only [Run.storeBeforeTime] using hQread
  obtain ⟨Qn, hQnbody, hQnerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho read u hQreadTime
  have hQnbody' : Qn ∈ (rho.storeBeforeTime S u read).bodies := by
    simpa only [Run.storeBeforeTime] using hQnbody
  have hQnrun : RunBlock S rho Qn :=
    runBlock_of_read_body S adm hu hQnbody'
  have hQsg : Block.Preceq Q.erase (actionSGBlockAt S rho v c) :=
    preceq_actionSGBlockAt_of_actionQ2 S adm.toNamedAdmissibleCore
      hv hcpos hchor hQ (Block.preceq_self Q.erase)
  have hQnsg : Block.Preceq Qn.erase (actionSGBlockAt S rho v c) := by
    rw [hQnerase]
    exact hQsg
  have hsplit :=
    actionSGBlock_filteredMem_or_preceq_root_after_GST_ancestor
      S adm hcom hbelow hrec hdelay hpost hc hchor hread hhor
        hnext hu hv hQnrun hQnsg hQnbody'
  simpa only [hQnerase] using hsplit

#print axioms NamedHeightRegimeBaseRun.honestHeightRow_gradeRoundReady
#print axioms NamedHeightRegimeBaseRun.honestFGSource_preceq_of_previousHead
#print axioms NamedHeightRegimeBaseRun.honestFGSource_preceq_and_mem_before_nextVote_of_relay
#print axioms NamedHeightRegimeBaseRun.honestFGSource_preceq_and_mem_before_nextVote
#print axioms NamedHeightRegimeBaseRun.honestFGSource_preceq_of_actionSGBlock
#print axioms NamedHeightRegimeBaseRun.exists_descendant_at_crossing_of_actionSGBlock_of_relay
#print axioms NamedHeightRegimeBaseRun.exists_descendant_at_crossing_of_actionSGBlock
#print axioms NamedHeightRegimeBaseRun.filteredMem_or_preceq_root_of_actionSGBlock_of_relay
#print axioms NamedHeightRegimeBaseRun.filteredMem_or_preceq_root_of_actionSGBlock
#print axioms NamedHeightRegimeBaseRun.honestFGSource_preceq_of_actionSGBlock_ancestor
#print axioms NamedHeightRegimeBaseRun.exists_descendant_at_crossing_of_actionSGBlock_ancestor_of_relay
#print axioms NamedHeightRegimeBaseRun.exists_descendant_at_crossing_of_actionSGBlock_ancestor
#print axioms NamedHeightRegimeBaseRun.filteredMem_or_preceq_root_of_actionSGBlock_ancestor_of_relay
#print axioms NamedHeightRegimeBaseRun.filteredMem_or_preceq_root_of_actionSGBlock_ancestor
#print axioms actionSGBlock_filteredMem_or_preceq_root_after_GST_ancestor
#print axioms selectedG2_filteredMem_or_preceq_root_after_GST_ancestor

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
