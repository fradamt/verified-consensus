module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.RecoveryInitialSourceHistory
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryFGRoundAgreement
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrameBase
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.FirstProgressFGWitness
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# The regime step: identification of justified and finalized blocks

Above a recovery height the regime frame at the next height is built from
The previous regime's exports (plan section 44c, step 3). The two facts that
carry the previous checkpoint into every honest store are proved here:

1. a justified block at the checkpoint's height is the checkpoint, because
   its certificate holds an honest target vote whose witness is the
   checkpoint and roots are collision free;
2. an honest finalized block in the window below the next crossing is below
   the checkpoint: below its height by finality safety, at its height
   through the justified block.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem actionBody_runBlock_heightRegime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
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

omit [DecidableEq V] [Fintype V] in
private theorem namedGenesis_of_erase_genesis {B : NamedBlock V}
    (h : B.erase = Block.genesis) : B = NamedBlock.genesis := by
  cases B with
  | genesis => rfl
  | node parent s root votes support rows proposer =>
      simp only [NamedBlock.erase] at h
      exact absurd h (by simp)

/-- **A justified block at the checkpoint height is the checkpoint.** The
certificate of the store's justification holds an honest target vote at
that height; its witness is the checkpoint, so the justified root is the
checkpoint's root. -/
theorem storeJustified_eq_of_honestWitnesses
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {n : Nat} {k : Height} {T : NamedBlock V}
    (hTrun : RunBlock S rho T) (hk : k ≠ 0)
    (hwit : ∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some k →
      fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T.erase)
    (hhj : (rho.stateBefore S n v).st.core.h_j = k) :
    (rho.stateBefore S n v).st.core.J = T.erase := by
  have hmajority := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
  obtain ⟨C, hC, hCJ, hhjC⟩ :=
    Proofs.Bridges.storeJustificationOnChain_stateBefore S rho n v
  have hCrun : RunBlock S rho C :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hC
  have hhjC' : (Protocol.derive_named S.E S.cfg C).h_j = k := hhjC.trans hhj
  obtain ⟨J, hJC, hJerase, Q, hQ, hwitQ⟩ :=
    NamedJustificationCertificates.justification_certificate S.E S.cfg C
      (by rw [hhjC']; exact hk)
  obtain ⟨i, hiQ, hiHon⟩ :=
    Protocol.HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨carrier, a, hcarrier, ha, hai, hap⟩ := hwitQ i hiQ
  have haHon : a.val_index ∈ rho.honest := by rw [hai]; exact hiHon
  have haChain : a.erase ∈ chain_attestations C.erase :=
    Proofs.Bridges.erase_mem_chain_attestations C carrier hcarrier a ha
  obtain ⟨b, tb, hba, hemit⟩ :=
    Proofs.NamedStoreBridge.carriedByHonest_of_runBlock S adm.toNamedAdmissibleCore hCrun
      a.erase haChain haHon
  have hbHon : b.val_index ∈ rho.honest := by
    have hvb : b.val_index = a.val_index := by
      exact congrArg CombinedAttestation.val_index hba
    rw [hvb]
    exact haHon
  have hpairEq : b.height_pair.erase = a.height_pair.erase :=
    congrArg CombinedAttestation.height_pair hba
  have hbrow : b.height_pair.erase.height? = some k := by
    rw [hpairEq, hap, hhjC']
    rfl
  have hva : a.erase.val_index = b.val_index := by
    exact congrArg CombinedAttestation.val_index hba.symm
  rw [hva] at hemit
  have hW := hwit b tb hbHon hemit hbrow
  obtain ⟨D, K, hK, hD, hsource, hDheight, hKmem, hKentry, hKheight,
      hKD, hshape⟩ := honestHeightRow_confirmationWitness S adm hbHon hemit hbrow
  have hKT : (Protocol.derive_named S.E S.cfg K).T_h = T.erase :=
    Option.some.inj (hK.symm.trans hW)
  have hJroot : J.root = K.erase.root := by
    have hpair : a.height_pair.erase = HeightPair.target k J.erase.root := by
      simp [hap, NamedHeightPair.erase, hhjC', Proofs.NamedWire.erase_root]
    rcases hshape with htarget | htimeout
    · have htarget' : HeightPair.target k J.erase.root =
          HeightPair.target k K.erase.root := by
        calc
          HeightPair.target k J.erase.root = a.height_pair.erase := hpair.symm
          _ = b.height_pair.erase := hpairEq.symm
          _ = HeightPair.target k K.erase.root := htarget
      exact (Proofs.NamedWire.erase_root J).symm.trans (HeightPair.target.inj htarget').2
    · rw [hpairEq, hpair] at htimeout
      cases htimeout
  have hDrun : RunBlock S rho D :=
    actionBody_runBlock_heightRegime S adm hbHon hD
  have hKrun : RunBlock S rho K :=
    actionBody_runBlock_heightRegime S adm hbHon hKmem
  obtain ⟨K', hK'D, hK'entry⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift D hKD
  have hK'run : RunBlock S rho K' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDrun hK'D
  have hK'eq : K' = K := by
    apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun K' K
      (Or.inl (Proofs.NamedAncestry.named_self K'))
      (Or.inr (Proofs.NamedAncestry.named_self K))
    rw [← Proofs.NamedWire.erase_root K', hK'entry, Proofs.NamedWire.erase_root]
  have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
    have hplateau : (Protocol.derive_named S.E S.cfg K).T_h =
        (Protocol.derive_named S.E S.cfg D).T_h := by
      rw [← hK'eq]
      exact Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hK'D
        ((hK'eq ▸ hKheight).trans hDheight.symm)
    exact hplateau.trans hKentry.symm
  have hTroot : T.root = K.root := by
    calc
      T.root = T.erase.root := (Proofs.NamedWire.erase_root T).symm
      _ = (Protocol.derive_named S.E S.cfg K).T_h.root :=
        (congrArg Block.root hKT).symm
      _ = K.erase.root := congrArg Block.root hKtarget
      _ = K.root := Proofs.NamedWire.erase_root K
  have hJroot' : J.root = K.root := hJroot.trans (Proofs.NamedWire.erase_root K)
  have hJrun : RunBlock S rho J :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hJC
  have hJK : J = T := by
    apply adm.toNamedRootCollisionFree.root_injective J T hJrun hTrun J T
      (Or.inl (Proofs.NamedAncestry.named_self J))
      (Or.inr (Proofs.NamedAncestry.named_self T))
    exact hJroot'.trans hTroot.symm
  rw [← hCJ, ← hJerase, hJK]

/-- **Honest finalized blocks below the next crossing are below the
checkpoint.** With the store's frontier at most one above the checkpoint
height, the finalized height is at most the checkpoint height; strictly
below, finality safety applies; at it, the finalized block is below the
justified block, which is the checkpoint. -/
theorem storeF_preceq_checkpoint_of_window
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {n : Nat} {k : Height} {T : NamedBlock V}
    (hTrun : RunBlock S rho T)
    (hTh : (Protocol.derive_named S.E S.cfg T).h = k) (hk : 2 ≤ k)
    (hwit : ∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some k →
      fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T.erase)
    (hwin : (rho.stateBefore S n v).st.core.h_max ≤ k + 1) :
    Block.Preceq (rho.stateBefore S n v).st.core.F T.erase := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  obtain ⟨C, hC, hF, hFheight⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho n v
  have hCrun : RunBlock S rho C :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hC
  have hFle : (Protocol.derive_named S.E S.cfg C).h_F ≤ k :=
    Nat.le_of_lt_succ (hFheight.trans_le hwin)
  rcases lt_or_eq_of_le hFle with hFlt | hFeq
  · have hpre : Block.Preceq (Protocol.derive_named S.E S.cfg C).F T.erase :=
      NamedFinalizationBridge.finalized_preceq_of_height_lt S rho T C hsb
        adm.toNamedRootCollisionFree hTrun hCrun
        (by rw [hTh]; exact hFlt)
    simpa only [hF] using hpre
  · -- the finalized block sits at the checkpoint height: go through the justification
    have hFJ : Block.Preceq (rho.stateBefore S n v).st.core.F
        (rho.stateBefore S n v).st.core.J :=
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore S rho n v
    obtain ⟨C', hC', hJ, hhj'⟩ :=
      NamedJustificationCarrier.justification_carrier_stateBefore S rho n v
    have hC'run : RunBlock S rho C' :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hC'
    have hFnonzero : (Protocol.derive_named S.E S.cfg C).h_F ≠ 0 := by
      intro hzero
      exact (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hk))
        (hFeq.symm.trans hzero)
    obtain ⟨Fn, hFnC, hFnErase, hFnHeight⟩ :=
      (NamedCheckpointHeights.finalized_ancestor_height S.E S.cfg C).resolve_left hFnonzero
    have hFnState : Fn.erase = (rho.stateBefore S n v).st.core.F :=
      hFnErase.trans hF
    have hFnrun : RunBlock S rho Fn :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hFnC
    rcases NamedCheckpointHeights.justified_ancestor_height S.E S.cfg C' with
      hJzero | ⟨Jn, hJnC', hJnErase, hJnHeight⟩
    · exfalso
      have hJgen : (rho.stateBefore S n v).st.core.J = Block.genesis := by
        rw [← hJ]
        exact NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg C' hJzero
      have hFgen : (rho.stateBefore S n v).st.core.F = Block.genesis :=
        Block.preceq_antisymm (by rw [hJgen] at hFJ; exact hFJ)
          (Protocol.preceq_genesis _)
      have hFnGen : Fn = NamedBlock.genesis :=
        namedGenesis_of_erase_genesis (hFnState.trans hFgen)
      have hFnHeight' : (Protocol.derive_named S.E S.cfg Fn).h = k :=
        hFnHeight.trans hFeq
      rw [hFnGen] at hFnHeight'
      exact absurd hFnHeight'
        (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hk))
    have hJnState : Jn.erase =
        (rho.stateBefore S n v).st.core.J := hJnErase.trans hJ
    have hJnrun : RunBlock S rho Jn :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hC'run hJnC'
    have hFJ' : Block.Preceq (rho.stateBefore S n v).st.core.F Jn.erase := by
      rw [hJnState]
      exact hFJ
    obtain ⟨F'n, hF'nJn, hF'nErase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift Jn hFJ'
    have hF'nrun : RunBlock S rho F'n :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hJnrun hF'nJn
    have hF'nFn : F'n = Fn := by
      apply adm.toNamedRootCollisionFree.root_injective F'n Fn hF'nrun hFnrun F'n Fn
        (Or.inl (Proofs.NamedAncestry.named_self F'n))
        (Or.inr (Proofs.NamedAncestry.named_self Fn))
      rw [← Proofs.NamedWire.erase_root F'n, hF'nErase, hFnState.symm,
        Proofs.NamedWire.erase_root]
    have hFnHeight' : (Protocol.derive_named S.E S.cfg Fn).h = k := by
      exact hFnHeight.trans hFeq
    have hJnHeight' : (Protocol.derive_named S.E S.cfg Jn).h =
        (rho.stateBefore S n v).st.core.h_j := hJnHeight.trans hhj'
    have hjge : k ≤ (rho.stateBefore S n v).st.core.h_j := by
      rw [← hFnHeight', ← hJnHeight']
      rw [← hF'nFn]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hF'nJn
    have hjlt : (rho.stateBefore S n v).st.core.h_j <
        (rho.stateBefore S n v).st.core.h_max := by
      exact NamedJustificationBound.justificationBelowMax_stateBefore S rho n v
    have hjeq : (rho.stateBefore S n v).st.core.h_j = k :=
      Nat.le_antisymm (Nat.le_of_lt_succ (hjlt.trans_le hwin)) hjge
    have hJT := storeJustified_eq_of_honestWitnesses S adm hbelow hv hTrun
      (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hk)) hwit hjeq
    rw [hJT] at hFJ
    exact hFJ

/-
/-- Every honest source-height row has the checkpoint as its witness. The
source-round case uses same-round frame agreement; later rounds use the
existing all-round checkpoint history. -/
theorem PrefixFGSelectorConeAt.witness_eq_checkpoint_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: NamedAttestation V} {ta: Time}
      {Cfg: NamedBlock V} {T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0: c0 ≤ a.round)
    (ready: GradeRoundReady S rho a.round)
    (hpostPrev: S.E.t_GST ≤ S.a (a.round - 1))
    (hG1: ∀ w ∈ rho.honest,
      ((Proofs.Optimistic.voteDutyStore S rho w
        (S.hc.opening_slot a.round + 1)).toHealing.T.filter
          (fun X => Protocol.G1 S.E
            (Proofs.Optimistic.voteDutyStore S rho w
              (S.hc.opening_slot a.round + 1)).toHealing.gradeView
                S.hc a.round X = true)).Nonempty)
    (hpred: OldTargetRootBelow S rho first blocked T)
    (hminimal: ∀ (b: NamedAttestation V) (tb: Time),
      b.val_index ∈ rho.honest →
      rho.emits S b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {b: NamedAttestation V} {tb: Time}
    (hb: b.val_index ∈ rho.honest)
    (hemit: rho.emits S b.val_index (Object.attest b) tb)
    (hrow: b.height_pair.erase.height? = some (blocked + 1)):
    fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T:= by
  rcases eq_or_lt_of_le (hminimal b tb hb hemit hrow) with heq | hlt
  · exact hseed.confirmationWitness_of_sameRound_honestHeightRow_of_frame
      adm hcom hbelow hfirst hframe ready hb hemit hrow heq
  · obtain ⟨_, K, hW, _, _, _, _, _, hKh, _, _⟩:=
      honestHeightRow_confirmationWitness S adm hb hemit hrow
    have hhor: S.a b.round ≤ rho.horizon:= by
      have htime: tb = S.a b.round:= (emits_attest_shape S hemit).2
      obtain ⟨k, hk, _⟩:= hemit
      have h:= (adm.in_horizon
        (Event.tick b.val_index tb) (List.mem_of_getElem? hk)).2
      simpa only [Event.time, htime] using h
    have hheight:
        (derived_state S.E S.cfg
          (Protocol.derive_named S.E S.cfg K).T_h).h = blocked + 1:= by
      rw [Protocol.derived_target_height, hKh]
    have hWT:=
      (hseed.laterFGWitness_eq_or_extends_checkpoint_of_frame
        adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred
          hminimal hlt hhor hb hW).1 hheight
    rw [hW, hWT]

#print axioms PrefixFGSelectorConeAt.witness_eq_checkpoint_of_frame
-/




/-
/-- Every honest row at the source height has the checkpoint as witness, in
every round: the first round by same-round agreement, later rounds by the
all-round induction. -/
theorem PrefixFGSelectorConeAt.witness_eq_checkpoint_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest) (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0: c0 ≤ a.round)
    (ready: GradeRoundReady S rho a.round)
    (hpostPrev: S.E.t_GST ≤ S.a (a.round - 1))
    (hG1: ∀ w ∈ rho.honest,
      ((Proofs.Optimistic.voteDutyStore S rho w (S.hc.opening_slot a.round + 1)).toHealing.T.filter
        (fun X => Protocol.G1 S.E
          (Proofs.Optimistic.voteDutyStore S rho w
            (S.hc.opening_slot a.round + 1)).toHealing.gradeView S.hc a.round X = true)).Nonempty)
    (hpred: OldTargetRootBelow S rho first blocked T)
    (hminimal: ∀ (b: CombinedAttestation V) (tb: Time), b.val_index ∈ rho.honest →
      rho.emits S b.val_index (Object.attest b) tb →
      b.height_pair.height? = some (blocked + 1) → a.round ≤ b.round)
    {b: CombinedAttestation V} {tb: Time} (hb: b.val_index ∈ rho.honest)
    (hemit: rho.emits S b.val_index (Object.attest b) tb)
    (hrow: b.height_pair.height? = some (blocked + 1)):
    fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T:= by
  rcases eq_or_lt_of_le (hminimal b tb hb hemit hrow) with heq | hlt
  · exact hseed.confirmationWitness_of_sameRound_honestHeightRow_of_frame adm hcom hfirst hframe
      ready hb hemit hrow heq
  · obtain ⟨_, W, hW, -, -, -, hWh, -, -⟩:=
      honestHeightRow_confirmationWitness S adm hb hemit hrow
    have hhor: S.a b.round ≤ rho.horizon:= by
      have htime: tb = S.a b.round:= (emits_attest_shape S hemit).2
      obtain ⟨k, hk, -⟩:= hemit
      have h:= (adm.in_horizon (Event.tick b.val_index tb) (List.mem_of_getElem? hk)).2
      simpa only [Event.time, htime] using h
    have hWT:= (hseed.laterFGWitness_eq_or_extends_checkpoint_of_frame adm hcom hbelow hfirst
      hframe hc0 ready hpostPrev hG1 hpred hminimal hlt hhor hb hW).1 hWh
    rw [hW, hWT]
-/




/-
/-- The SG history relative to the checkpoint, in every round from the
source round on. -/
theorem PrefixFGSelectorConeAt.sgHistory_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest) (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0: c0 ≤ a.round)
    (ready: GradeRoundReady S rho a.round)
    (hpostPrev: S.E.t_GST ≤ S.a (a.round - 1))
    (hG1: ∀ w ∈ rho.honest,
      ((Proofs.Optimistic.voteDutyStore S rho w (S.hc.opening_slot a.round + 1)).toHealing.T.filter
        (fun X => Protocol.G1 S.E
          (Proofs.Optimistic.voteDutyStore S rho w
            (S.hc.opening_slot a.round + 1)).toHealing.gradeView S.hc a.round X = true)).Nonempty)
    (hpred: OldTargetRootBelow S rho first blocked T)
    (hminimal: ∀ (b: CombinedAttestation V) (tb: Time), b.val_index ∈ rho.honest →
      rho.emits S b.val_index (Object.attest b) tb →
      b.height_pair.height? = some (blocked + 1) → a.round ≤ b.round)
    {c: Round} (hc: a.round ≤ c) (hhor: S.a c ≤ rho.horizon):
    HonestSGEmissionsCompatibleAtRound S rho c T:= by
  rcases eq_or_lt_of_le hc with heq | hlt
  · rw [← heq]
    exact hseed.sgEmissionsCompatible_of_source_of_frame adm hcom hbelow
      hfirst hframe hc0 ready hpostPrev
  · exact ((hseed.checkpointProtection_and_actionHistory_of_frame adm hcom hbelow hfirst
      hframe hc0 ready hpostPrev hG1 hpred hminimal hlt).2 hhor).1
-/




/-
/-- Every honest vote-duty head in a round after the source round extends
the checkpoint. -/
theorem PrefixFGSelectorConeAt.heads_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest) (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0: c0 ≤ a.round)
    (ready: GradeRoundReady S rho a.round)
    (hpostPrev: S.E.t_GST ≤ S.a (a.round - 1))
    (hG1: ∀ w ∈ rho.honest,
      ((Proofs.Optimistic.voteDutyStore S rho w (S.hc.opening_slot a.round + 1)).toHealing.T.filter
        (fun X => Protocol.G1 S.E
          (Proofs.Optimistic.voteDutyStore S rho w
            (S.hc.opening_slot a.round + 1)).toHealing.gradeView S.hc a.round X = true)).Nonempty)
    (hpred: OldTargetRootBelow S rho first blocked T)
    (hminimal: ∀ (b: CombinedAttestation V) (tb: Time), b.val_index ∈ rho.honest →
      rho.emits S b.val_index (Object.attest b) tb →
      b.height_pair.height? = some (blocked + 1) → a.round ≤ b.round)
    {s: Slot} (hround: a.round + 1 ≤ S.hc.round_of s)
    (hhor: Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon):
    ∀ w ∈ rho.honest, Block.Preceq T (voteDutyHead S rho w s):=
  (hseed.checkpointProtection_from_sourceRound_of_frame adm hcom hbelow hfirst hframe hc0 ready
    hpostPrev hG1 hpred hminimal ((Nat.le_succ a.round).trans hround)
    (fun heq => False.elim ((Nat.not_succ_le_self a.round) (heq ▸ hround))) hhor).1
-/





/-
/-- A grade-1 block of a round after the source round, at an honest read, is
comparable with the checkpoint: its honest supporter's SG vote is compatible
with the checkpoint by the regime's SG history. -/
theorem PrefixFGSelectorConeAt.g1_comparable_checkpoint_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest) (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0: c0 ≤ a.round)
    (ready: GradeRoundReady S rho a.round)
    (hpostPrev: S.E.t_GST ≤ S.a (a.round - 1))
    (hG1: ∀ w ∈ rho.honest,
      ((Proofs.Optimistic.voteDutyStore S rho w (S.hc.opening_slot a.round + 1)).toHealing.T.filter
        (fun X => Protocol.G1 S.E
          (Proofs.Optimistic.voteDutyStore S rho w
            (S.hc.opening_slot a.round + 1)).toHealing.gradeView S.hc a.round X = true)).Nonempty)
    (hpred: OldTargetRootBelow S rho first blocked T)
    (hminimal: ∀ (b: CombinedAttestation V) (tb: Time), b.val_index ∈ rho.honest →
      rho.emits S b.val_index (Object.attest b) tb →
      b.height_pair.height? = some (blocked + 1) → a.round ≤ b.round)
    {reader: V} (hreader: reader ∈ rho.honest) {time: Time}
    {c: Round} (hc: a.round + 1 ≤ c) {L: Block V}
    (hL: Protocol.G1 S.E (rho.storeBeforeTime S reader time).toHealing.gradeView S.hc c L = true):
    Block.Preceq L T ∨ Block.Preceq T L:= by
  obtain ⟨v, hv, u, hu, head, hconf, hfind, -, hLhead, -⟩:=
    G1_honest_named_supporter S.E hbelow hL
  have hcpos: c ≠ 0:= Nat.pos_iff_ne_zero.mp ((Nat.succ_pos _).trans_le hc)
  have hc1: c - 1 + 1 = c:= Nat.sub_add_cancel (Nat.pos_of_ne_zero hcpos)
  have hupool: u ∈ (rho.storeBeforeTime S reader time).toHealing.sg_votes (c - 1):= by
    have h:= (Finset.mem_filter.mp hu).1
    simpa only [Protocol.round_batch, if_neg hcpos] using h
  have huv: u.val_index = v:= (Finset.mem_filter.mp hu).2
  have hhorPrev: S.a (c - 1) ≤ rho.horizon:=
    honestSGVote_round_horizon S adm (huv ▸ hv) hupool
  have hsg:= hseed.sgHistory_of_frame adm hcom hbelow hfirst hframe hc0 ready hpostPrev
    hG1 hpred hminimal (Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hc)) hhorPrev
  have hbatch:= batchCompatible_at_read_of_emittedSGHistory S adm hreader
    (time:= time) hsg
  rw [hc1] at hbatch
  have hcompat:= hbatch.heads v hv u hu
  rw [hconf] at hcompat
  simp only [rootCompatible, hfind] at hcompat
  rcases (show Block.Preceq head T ∨ Block.Preceq T head by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompat) with hhT | hTh
  · exact Or.inl (Block.preceq_trans hLhead hhT)
  · exact Block.preceq_linear hLhead hTh
-/



/-! ## The frame at the next height -/

/-- The window bound one crossing up: below the next first crossing every
honest frontier is at most one above the source height. -/
private theorem window_of_nextCrossing
    (S : Setup V) {rho : Run V} {blocked : Height} {first' : Nat}
    (hfirst' : HeightWindowAt S rho (blocked + 1 + 1) first')
    {v : V} (hv : v ∈ rho.honest) {n : Nat} (hn : n ≤ first' - 1) :
    (rho.stateBefore S n v).st.core.h_max ≤ blocked + 1 + 1 :=
  (localHMax_le_honestHMaxBeforeIndex S rho n hv).trans
    (hfirst'.before n (Nat.lt_of_le_pred hfirst'.positive hn))


/-
/-- **The regime frame at the next height.** From the regime at the source
height, with its checkpoint `T` as the previous checkpoint and its source
round as the round bound, the frame holds over the prefix strictly before
the next first crossing. -/
theorem PrefixFGSelectorConeAt.heightRegimeFrame_succ_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest) (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: CombinedAttestation V} {ta: Time} {Cfg T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0: c0 ≤ a.round)
    (ready: GradeRoundReady S rho a.round)
    (hpostPrev: S.E.t_GST ≤ S.a (a.round - 1))
    (hG1: ∀ w ∈ rho.honest,
      ((Proofs.Optimistic.voteDutyStore S rho w (S.hc.opening_slot a.round + 1)).toHealing.T.filter
        (fun X => Protocol.G1 S.E
          (Proofs.Optimistic.voteDutyStore S rho w
            (S.hc.opening_slot a.round + 1)).toHealing.gradeView S.hc a.round X = true)).Nonempty)
    (hpred: OldTargetRootBelow S rho first blocked T)
    (hminimal: ∀ (b: CombinedAttestation V) (tb: Time), b.val_index ∈ rho.honest →
      rho.emits S b.val_index (Object.attest b) tb →
      b.height_pair.height? = some (blocked + 1) → a.round ≤ b.round)
    (hblocked: 1 ≤ blocked)
    {first': Nat} (hfirst': HeightWindowAt S rho (blocked + 1 + 1) first'):
    HeightRegimeFrame S rho (blocked + 1) (first' - 1) T (a.round + 1):= by
  have hwit:= fun (b: CombinedAttestation V) (tb: Time) hb hemit hrow =>
    hseed.witness_eq_checkpoint_of_frame adm hcom hbelow hfirst hframe hc0 ready hpostPrev
      hG1 hpred hminimal (b:= b) (tb:= tb) hb hemit hrow
  have hTCfg: Block.Preceq T Cfg:= by
    rw [hseed.checkpointDerived]
    exact Proofs.Records.derived_state_T_h_preceq S.E S.cfg Cfg
  have hTrun: RunBlock S rho T:=
    (actionSourceAncestor_mem_and_runBlock S adm hseed.signerHonest hseed.sourceMem hTCfg).2
  have hTh: (derived_state S.E S.cfg T).h = blocked + 1:= by
    rw [hseed.checkpointDerived, Protocol.derived_target_height, hseed.sourceDerivedHeight]
  have hk2: 2 ≤ blocked + 1:= Nat.succ_le_succ hblocked
  -- honest finalized blocks in the window are below the checkpoint
  have hFT: ∀ v ∈ rho.honest, ∀ n: Nat, n ≤ first' - 1 →
      Block.Preceq (rho.stateBefore S n v).st.F T:= fun v hv n hn =>
    storeF_preceq_checkpoint_of_window S adm hbelow hv hTrun hTh hk2 hwit
      (window_of_nextCrossing S hfirst' hv hn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the floor
    intro v hv n hn X _ _ hTX
    exact Block.preceq_trans (hFT v hv n hn) hTX
  · -- the previous checkpoint's height
    rw [hTh]
  · -- the root below every source-height block above the checkpoint
    intro v hv n hn Q hQ hQh hTQ
    have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) (rho.stateBefore S n v).st:=
      Proofs.Bridges.depReachable_of_admissible S adm.toDeliveryWellFormed v n
    have hagree:= Proofs.Bridges.derivedStateAgrees_of_admissible S adm.toDeliveryWellFormed v n
    have hQle: blocked + 1 + 1 ≤ (rho.stateBefore S n v).st.h_max:= by
      have hbound:= treeHeightsLeHMax_depReachable S.E S.hc S.cfg (S.node v) hdep Q hQ
      rw [hagree Q hQ, hQh] at hbound
      exact hbound
    have hmax: (rho.stateBefore S n v).st.h_max = blocked + 1 + 1:=
      Nat.le_antisymm (window_of_nextCrossing S hfirst' hv hn) hQle
    by_cases hgate: (rho.stateBefore S n v).st.h_max = (rho.stateBefore S n v).st.h_j + 1
    · have hroot: Protocol.get_fg_root (rho.stateBefore S n v).st.toHealing.toFG =
          (rho.stateBefore S n v).st.J:= by
        simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_pos hgate]
      have hhj: (rho.stateBefore S n v).st.h_j = blocked + 1:= by
        rw [hmax] at hgate
        exact (Nat.add_right_cancel hgate).symm
      rw [hroot, storeJustified_eq_of_honestWitnesses S adm hbelow hv hTrun
        (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hk2)) hwit hhj]
      exact hTQ
    · have hroot: Protocol.get_fg_root (rho.stateBefore S n v).st.toHealing.toFG =
          (rho.stateBefore S n v).st.F:= by
        simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_neg hgate]
      rw [hroot]
      exact Block.preceq_trans (hFT v hv n hn) hTQ
  · -- every honest FG source at the next height extends the checkpoint
    intro p hp r hr hhor B hsource hBh
    obtain ⟨Q, hQ⟩: ∃ Q: Block V, Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho p r).toHealing r = some Q:= by
      cases hgrade: Protocol.grade2_block S.E S.hc (actionStoreAt S rho p r).toHealing r with
      | none => simp [Protocol.fg_source, hgrade] at hsource
      | some Q => exact ⟨Q, rfl⟩
    -- the round is after the source round: a source at the next height needs a
    -- frontier above the source height, which the first crossing forbids earlier
    have hrgt: a.round + 1 ≤ r:= by
      by_contra hn
      have hle: r ≤ a.round:= Nat.le_of_lt_succ (Nat.lt_of_not_le hn)
      have hBmem: B ∈ (actionStoreAt S rho p r).T:= fgSource_mem_actionStore S adm p r hsource
      have hfields:= Proofs.Optimistic.attestStore_fields S (rho.stateBeforeTime S (S.a r) p).st (S.a r)
      have hBpre: B ∈ (rho.storeBeforeTime S p (S.a r)).T:= by
        simpa only [actionStoreAt, hfields.2.1, Run.storeBeforeTime] using hBmem
      have hBidx: B ∈ (rho.stateBefore S (strictEventIndex rho (S.a r)) p).st.T:= by
        rw [← storeBeforeTime_eq_stateBefore_strictEventIndex S adm.toScheduleWellFormed p (S.a r)]
        exact hBpre
      have hdep:= Proofs.Bridges.depReachable_of_admissible S adm.toDeliveryWellFormed p
        (strictEventIndex rho (S.a r))
      have hagree:= Proofs.Bridges.derivedStateAgrees_of_admissible S adm.toDeliveryWellFormed p
        (strictEventIndex rho (S.a r))
      have hmaxB: blocked + 1 + 1 ≤
          (rho.stateBefore S (strictEventIndex rho (S.a r)) p).st.h_max:= by
        have hbound:= treeHeightsLeHMax_depReachable S.E S.hc S.cfg (S.node p) hdep B hBidx
        rw [hagree B hBidx, hBh] at hbound
        exact hbound
      have hfrontier: (rho.stateBefore S (strictEventIndex rho (S.a r)) p).st.h_max ≤
          blocked + 1:=
        (localHMax_le_honestHMaxBeforeIndex S rho _ hp).trans (hfirst.before _
          ((strictEventIndex_mono rho (Assembly.a_mono S hle)).trans_lt
            (hseed.actionPrefix_lt adm.toScheduleWellFormed)))
      exact Nat.not_succ_le_self (blocked + 1) (hmaxB.trans hfrontier)
    have hcompat: Block.Preceq B T ∨ Block.Preceq T B:= by
      rcases actionFGSource_genuineClear_or_selectedG2 S rho p r hQ hsource with
        ⟨C, hgenuine, -, -, -, hBC, -⟩ | ⟨hBQ, hG2, -⟩
      · -- a genuine confirmation is below an honest vote head, which extends T
        have hrpos: 0 < r:= (Nat.succ_pos _).trans_le hrgt
        have hs: 0 < S.hc.opening_slot r:=
          Nat.mul_pos hrpos (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
        have hle: a.round ≤ r:= (Nat.le_succ a.round).trans hrgt
        have hpost: S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r):= by
          rw [← Protocol.Γ_1_eq_vote_time]
          exact ready.1.trans ((Γ_neg1_mono S.hc S.E.Δ_pos hle).trans
            ((le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos r)).trans
              (le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos r))))
        have hconfHor: Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤ rho.horizon:= by
          rwa [opening_confirmation_time_eq_action]
        have hopenAction: Protocol.vote_time S.E (S.hc.opening_slot r) + S.E.Δ ≤ S.a r:= by
          rw [← opening_confirmation_time_eq_action S r,
            ← vote_time_succ_add_delta_eq_confirmation_time]
          exact add_le_add (vote_time_mono_slots S.E (Nat.le_succ _)) (le_refl S.E.Δ)
        have hheads:= hseed.heads_of_frame adm hcom hbelow hfirst hframe hc0 ready hpostPrev
          hG1 hpred hminimal (s:= S.hc.opening_slot r)
          (by rw [round_of_opening_slot_eq_schedule]; exact hrgt) (hopenAction.trans hhor)
        have hTC:= genuineConfirmation_compatible_of_priorProtectedHeads S adm hcom hp hs hpost
          hconfHor hgenuine (fun x hx _ => hheads x hx)
        rcases (show Block.Preceq T C ∨ Block.Preceq C T by
            simpa only [Block.compatible, Bool.or_eq_true] using hTC) with hTC' | hCT
        · exact Block.preceq_linear hBC hTC'
        · exact Or.inl (Block.preceq_trans hBC hCT)
      · -- a selected grade-2 block has an honest supporter compatible with T
        subst hBQ
        have hG1B:= Proofs.HealingLemmas.G2_imp_G1 S.E _ S.hc r B hG2
        rw [Protocol.actionStoreAt_gradeView_eq_storeBeforeTime] at hG1B
        have hG1B': Protocol.G1 S.E (rho.storeBeforeTime S p (S.a r)).toHealing.gradeView
            S.hc r B = true:= by
          simpa only [gradeViewAt, healStoreAt] using hG1B
        exact hseed.g1_comparable_checkpoint_of_frame adm hcom hbelow hfirst hframe hc0 ready
          hpostPrev hG1 hpred hminimal hp hrgt hG1B'
    rcases hcompat with hBT | hTB
    · exfalso
      have hmono:= Protocol.derived_h_mono S.E S.cfg hBT
      rw [hBh, hTh] at hmono
      exact Nat.not_succ_le_self (blocked + 1) hmono
    · exact hTB
-/



theorem PrefixFGSelectorConeAt.heightRegimeFrame_succ_of_frameN
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T0 : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T0)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) → a.round ≤ b.round)
    (hblocked : 1 ≤ blocked)
    {first' : Nat} (hfirst' : HeightWindowAt S rho (blocked + 1 + 1) first')
    {Tnext : NamedBlock V}
    (hTnextCfg : NamedBlock.Preceq Tnext Cfg)
    (hTnextRun : RunBlock S rho Tnext)
    (hTnextErase : Tnext.erase =
      (Protocol.derive_named S.E S.cfg Cfg).T_h)
    (hTnextHeight :
      (Protocol.derive_named S.E S.cfg Tnext).h = blocked + 1)
    (hsameRound : ∀ {b : NamedAttestation V} {tb : Time},
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round = b.round →
      fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) =
        some Tnext.erase)
    (hcompatLater : ∀ {r : Round}, a.round + 1 ≤ r →
      S.a r ≤ rho.horizon → ∀ {w : V}, w ∈ rho.honest →
      ∀ {W : Block V},
      fgConfirmationWitness S (actionStoreAt S rho w r) = some W →
      Block.compatible W Tnext.erase = true) :
    NamedHeightRegimeFrame S rho (blocked + 1) (first' - 1) Tnext
      (a.round + 1) := by
  have hwit : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) =
        some Tnext.erase := by
    intro b tb hb hemit hrow
    rcases eq_or_lt_of_le (hminimal b tb hb hemit hrow) with heq | hlt
    · exact hsameRound hb hemit hrow heq
    · obtain ⟨D, K, hW, hDmem, _hsource, hDheight, hKmem,
          hKerase, hKheight, hKD, _hshape⟩ :=
        honestHeightRow_confirmationWitness S adm hb hemit hrow
      have hhor : S.a b.round ≤ rho.horizon := by
        have htime : tb = S.a b.round :=
          (Proofs.Optimistic.emits_attest_shape S hemit).2
        obtain ⟨k, hk, _⟩ := hemit
        have hin := (adm.in_horizon
          (Event.tick b.val_index tb) (List.mem_of_getElem? hk)).2
        simpa only [Event.time, htime] using hin
      have hKfixed :
          (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
        have hDrun := actionBody_runBlock_heightRegime S adm hb hDmem
        have hKrun := actionBody_runBlock_heightRegime S adm hb hKmem
        have hKDnamed := Protocol.namedPreceq_of_runBlock_erase_preceq
          adm hKrun hDrun hKD
        exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKDnamed
          (hKheight.trans hDheight.symm)).trans hKerase.symm
      have hW' : fgConfirmationWitness S
          (actionStoreAt S rho b.val_index b.round) =
            some (Protocol.derive_named S.E S.cfg D).T_h := by
        rw [hW, hKfixed, hKerase]
      have hcompat := hcompatLater hlt hhor hb hW'
      exact (hseed.laterFGWitness_eq_or_extends_checkpoint_of_frameN
        adm hcom hbelow hfirst hframe hc0 ready hpostPrev hminimal
        hTnextCfg hTnextRun hTnextErase hTnextHeight hlt hhor hb hDmem
        hW' hcompat).1 hDheight ▸ hW'
  have hk2 : 2 ≤ blocked + 1 := Nat.succ_le_succ hblocked
  have hFT : ∀ v ∈ rho.honest, ∀ n : Nat, n ≤ first' - 1 →
      Block.Preceq (rho.stateBefore S n v).st.core.F Tnext.erase :=
    fun v hv n hn => storeF_preceq_checkpoint_of_window
      S adm hbelow hv hTnextRun hTnextHeight hk2 hwit
        (window_of_nextCrossing S hfirst' hv hn)
  refine {
    floor := ?_
    prevRun := hTnextRun
    prevHeight := hTnextHeight.le
    rootBelow := ?_
    sourceAbove := ?_ }
  · intro v hv n hn X _ _ hTX
    exact Block.preceq_trans (hFT v hv n hn) (Proofs.NamedWire.erase_preceq hTX)
  · intro v hv n hn Q hQ hQh hTQ
    have hQle : blocked + 1 + 1 ≤
        (rho.stateBefore S n v).st.core.h_max := by
      have hbound := Proofs.NamedStoreBridge.heights_le_hMax_stateBefore
        S rho n v Q hQ
      rw [hQh] at hbound
      exact hbound
    have hmax : (rho.stateBefore S n v).st.core.h_max = blocked + 1 + 1 :=
      Nat.le_antisymm (window_of_nextCrossing S hfirst' hv hn) hQle
    by_cases hgate : (rho.stateBefore S n v).st.core.h_max =
        (rho.stateBefore S n v).st.core.h_j + 1
    · have hroot : Protocol.get_fg_root
          (rho.stateBefore S n v).st.core.toHealing.toFG =
          (rho.stateBefore S n v).st.core.J := by
        simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
          if_pos hgate]
      have hhj : (rho.stateBefore S n v).st.core.h_j = blocked + 1 := by
        rw [hmax] at hgate
        exact (Nat.add_right_cancel hgate).symm
      rw [hroot, storeJustified_eq_of_honestWitnesses S adm hbelow hv
        hTnextRun (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hk2)) hwit hhj]
      exact Proofs.NamedWire.erase_preceq hTQ
    · have hroot : Protocol.get_fg_root
          (rho.stateBefore S n v).st.core.toHealing.toFG =
          (rho.stateBefore S n v).st.core.F := by
        simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
          if_neg hgate]
      rw [hroot]
      exact Block.preceq_trans (hFT v hv n hn) (Proofs.NamedWire.erase_preceq hTQ)
  · intro p hp r hr hhor B hBmem hsource hBh
    have hrgt : a.round + 1 ≤ r := by
      by_contra hnot
      have hle : r ≤ a.round := Nat.le_of_lt_succ (Nat.lt_of_not_le hnot)
      have hBpre : B ∈
          (NamedRun.stateBeforeTime S rho (S.a r) p).st.bodies := by
        simpa only [actionStoreAt, actionReadAt,
          NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hBmem
      have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed (S.a r)) p
      rw [heq] at hBpre
      have hmaxB : blocked + 1 + 1 ≤
          (rho.stateBefore S (strictEventIndex rho (S.a r)) p).st.core.h_max := by
        have hbound := Proofs.NamedStoreBridge.heights_le_hMax_stateBefore
          S rho (strictEventIndex rho (S.a r)) p B hBpre
        rw [hBh] at hbound
        exact hbound
      have hfrontier :
          (rho.stateBefore S (strictEventIndex rho (S.a r)) p).st.core.h_max ≤
            blocked + 1 :=
        (localHMax_le_honestHMaxBeforeIndex S rho _ hp).trans
          (hfirst.before _
            ((strictEventIndex_mono rho (Assembly.a_mono S hle)).trans_lt
              (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed)))
      exact Nat.not_succ_le_self (blocked + 1) (hmaxB.trans hfrontier)
    have hW : fgConfirmationWitness S (actionStoreAt S rho p r) =
        some (Protocol.derive_named S.E S.cfg B).T_h := by
      unfold fgConfirmationWitness
      rw [hsource]
      simp only [Option.map_some]
      rw [derivedStateAgrees_actionStoreAt S adm p r B hBmem]
    have hcompat := hcompatLater hrgt hhor hp hW
    have htarget :=
      (hseed.laterFGWitness_eq_or_extends_checkpoint_of_frameN
        adm hcom hbelow hfirst hframe hc0 ready hpostPrev hminimal
        hTnextCfg hTnextRun hTnextErase hTnextHeight hrgt hhor hp hBmem
        hW hcompat).2 (by rw [hBh]; exact Nat.le_succ (blocked + 1))
    obtain ⟨K, _hKmem, hKerase, _hKheight, hKB, hKrun⟩ :=
      action_named_checkpoint S adm hp hBmem
    rw [← hKerase] at htarget
    have hTnextK := Protocol.namedPreceq_of_runBlock_erase_preceq
      adm hTnextRun hKrun htarget
    have hBrun := actionBody_runBlock_heightRegime S adm hp hBmem
    apply Protocol.namedPreceq_of_runBlock_erase_preceq
      adm hTnextRun hBrun
    exact Block.preceq_trans (Proofs.NamedWire.erase_preceq hTnextK)
      (Proofs.NamedWire.erase_preceq hKB)

#print axioms PrefixFGSelectorConeAt.heightRegimeFrame_succ_of_frameN

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
