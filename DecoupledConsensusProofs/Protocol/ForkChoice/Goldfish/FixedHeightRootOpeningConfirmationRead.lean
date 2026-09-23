module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Objects.SGTargetG1Concentration
public import DecoupledConsensusProofs.Protocol.Grades.FixedHeightRootOpeningParentComplete
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedRootGradePersistence
public import DecoupledConsensusProofs.Execution.PreparedReadBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Fixed-height opening confirmation reads

This module supplies local fixed-root no-rise producers for the opening
proposal's admission, relative-SG fallback, and confirmation read.
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


/-- Exact fixed-root retention at the opening confirmation read makes every
proposal delivery finalized below the opening proposal. Thus the normal
post-GST proposal admission rule processes that proposal before each honest
opening vote read. -/
theorem openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {A : Block V} {B : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot q) = some B)
    (hq : 0 < q)
    (hpostRead : S.E.t_GST ≤ read)
    (hdelay : read + S.E.Δ ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q))
    (hconfHor : Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤
      rho.horizon)
    (hcap : honestHMaxAt S rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostProposal : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposer : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hJA : Block.Preceq (rho.storeBeforeTime S w read).J A)
    (hAparent : Block.Preceq A
      (proposedParent S rho (S.hc.opening_slot q))) :
    ∀ v ∈ rho.honest,
      AdmittedBefore S rho v B.erase
        (Protocol.vote_time S.E (S.hc.opening_slot q)) := by
  let s := S.hc.opening_slot q
  let J := (rho.storeBeforeTime S w read).J
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hparentB : Block.Preceq
      (proposedParent S rho s) B.erase := by
    have hpar : B.erase.parent = proposedParent S rho s :=
      proposedBlockErased_parent S rho s hB
    have hparent : Block.Preceq B.erase.parent B.erase := by
      cases B with
      | genesis => exact Block.preceq_self _
      | node parent slot root votes support rows proposer =>
          exact Protocol.preceq_of_parent? rfl
    rw [← hpar]
    exact hparent
  have hJB : Block.Preceq J B.erase :=
    Block.preceq_trans hJA (Block.preceq_trans hAparent hparentB)
  have hroot : ∀ v ∈ rho.honest,
      Protocol.get_fg_root
        (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).toHealing.toFG =
          J := by
    intro v hv
    exact (fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hv hpostRead (by simpa only [s] using hdelay)
        (by simpa only [s] using hconfHor) (by simpa only [s] using hcap)).1
  have hFhist : ProposalFinalizedBelowAtDeliveries S rho s B := by
    intro v hv i hi
    have hrootB : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).toHealing.toFG)
          B.erase := by
      rw [hroot v hv]
      exact hJB
    exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted hrootB
      (hi.trans (strict_filter_length_mono rho
        (Protocol.vote_time_le_confirmation_time S.E s)))
  have hs : 0 < s := by
    dsimp only [s]
    exact Nat.mul_pos hq
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E s).trans
      (by simpa only [s] using hconfHor)
  have hproposalVote : Protocol.proposal_time S.E s + S.E.Δ =
      Protocol.vote_time S.E s := by
    unfold Protocol.proposal_time Protocol.vote_time
    ring
  have hproposalVoteLt : Protocol.proposal_time S.E s <
      Protocol.vote_time S.E s := by
    unfold Protocol.vote_time
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hvoteCutoff : Protocol.vote_time S.E s <
      Protocol.support_cutoff S.E s := by
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hproposalCutoff : Protocol.proposal_time S.E s <
      Protocol.support_cutoff S.E s :=
    lt_trans hproposalVoteLt hvoteCutoff
  have hvoteFreeze : Protocol.vote_time S.E s <
      Protocol.view_freeze S.E s :=
    lt_trans hvoteCutoff (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)
  have hproposalLeVote : Protocol.proposal_time S.E s ≤
      Protocol.vote_time S.E s := le_of_lt hproposalVoteLt
  obtain ⟨B0, hB0, -, hemit0⟩ :=
    proposedBlockAt_emits_of_honest S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed s hs
      (by simpa only [s] using hproposer)
      (le_trans hproposalLeVote hvoteHor)
  have hBeq0 : B = B0 := (proposedBlockAt_unique S rho s hB0 hB).symm
  subst hBeq0
  intro v hv
  by_cases hvp : v = S.E.proposer s
  · subst v
    obtain ⟨i, hacc⟩ := Protocol.acceptsAt_proposedBlock S adm hs
      (by simpa only [s] using hproposer) (le_trans hproposalLeVote hvoteHor) hB
    exact ⟨B, rfl, i, Protocol.proposal_time S.E s, hacc, hproposalVoteLt⟩
  · have hmax : max (Protocol.proposal_time S.E s) S.E.t_GST =
        Protocol.proposal_time S.E s :=
      max_eq_left (by simpa only [s] using hpostProposal)
    have hdeadline :
        max (Protocol.proposal_time S.E s) S.E.t_GST + S.E.Δ ≤
          rho.horizon := by
      rw [hmax, hproposalVote]
      exact hvoteHor
    have hrootB : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).toHealing.toFG)
          B.erase := by
      rw [hroot v hv]
      exact hJB
    have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (Protocol.confirmation_time S.E s) v
    have hFroot := Proofs.Records.preceq_get_fg_root_of_F
      (st := (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).toHealing.toFG)
      hFJ
    have hFconf : Block.Preceq
        (NamedRun.stateBeforeTime S rho (Protocol.confirmation_time S.E s) v).st.core.F
          B.erase := Block.preceq_trans hFroot hrootB
    have hdeadlineConf :
        max (Protocol.proposal_time S.E s) S.E.t_GST + S.E.Δ ≤
          Protocol.confirmation_time S.E s := by
      rw [hmax, hproposalVote]
      exact Protocol.vote_time_le_confirmation_time S.E s
    have hguard := not_excludes_of_F_preceq_later_time S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
      hdeadlineConf hFconf
    obtain ⟨t, hlo, hhi, j, hidx, e, he, hnode, htime⟩ :=
      adm.toNamedAdmissibleCore.toNamedSynchrony.broadcast
        (S.E.proposer s) (by simpa only [s] using hproposer) _ _ hemit0 v hv
          hdeadline hguard
    have hbeforeVote : t < Protocol.vote_time S.E s := by
      rw [hmax, hproposalVote] at hhi
      exact hhi
    rcases hidx with ⟨t'', htick, hem⟩ | ⟨t'', hdeliver⟩
    · have hemitv : NamedRun.emits S rho v (.block B) t'' := ⟨j, htick, hem⟩
      have hshape := emits_block_shape S rho hemitv
      have hBslot : B.slot = s := by
        have hBslot' : B.erase.slot = s := by
          rw [Proofs.NamedWire.erase_slot]
          exact proposedBlockAt_slot S rho s hB
        rwa [Proofs.NamedWire.erase_slot] at hBslot'
      have hEq : S.E.proposer s = v := by rw [← hBslot]; exact hshape.2.2
      exact absurd hEq.symm hvp
    · have het : t = t'' := by
        have heq : Event.deliver v (Object.block B) t'' = e :=
          Option.some.inj (hdeliver.symm.trans he)
        exact ((congrArg Event.time heq).trans htime).symm
      subst het
      have hstoreSlot : (rho.stateBefore S j v).st.core.s = s :=
        Protocol.delivery_store_slot_before_freeze S adm hv hdeliver hlo
          (lt_trans hbeforeVote hvoteFreeze)
      have hBslot : B.erase.slot = s := by
        rw [Proofs.NamedWire.erase_slot]
        exact proposedBlockAt_slot S rho s hB
      have hslot : ¬ (rho.stateBefore S j v).st.core.s < B.erase.slot := by
        rw [hstoreSlot, hBslot]
        exact Nat.lt_irrefl s
      exact Protocol.admittedBefore_of_delivery_guards S adm hdeliver hslot
        (hFhist v hv j (Nat.le_trans (Nat.le_succ j)
          (index_succ_le_strict_filter_length rho
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
            (Protocol.vote_time S.E s) hdeliver
            (by simpa only [Event.time] using hbeforeVote))))
        (Protocol.proposedBlock_proposer S rho s hB)
        (Protocol.proposedBlock_parent_slot_lt S adm hs hB)
        (Protocol.proposedBlock_carried_attestations_admissible S rho s hB)
        hbeforeVote




/-
/-- Exact-root proposal admission and the callback-free preceding-action
parent ceiling orient the relative-SG fallback at each opening confirmation
read. -/
theorem openingConfirmationSupportAlignedParent_of_fixedJustificationRootNoRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time}
    (hfix: FixedHeightJustificationRootAtRead S rho H w read)
    {q: Round} {A: Block V} {B: NamedBlock V}
    (hB: proposedBlockAt S rho (S.hc.opening_slot q) = some B)
    (hq: 0 < q)
    (hpostRead: S.E.t_GST ≤ read)
    (hdelay: read + S.E.Δ ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q))
    (hconfHor: Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤
      rho.horizon)
    (hcap: honestHMaxAt S rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostProposal: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hproposer: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hJA: Block.Preceq (rho.storeBeforeTime S w read).J A)
    (hAparent: Block.Preceq A
      (Protocol.proposedParent S rho (S.hc.opening_slot q)))
    (hparents: FixedHeightRootOpeningParentRun S rho q):
    ∀ v ∈ rho.honest,
      Proofs.Optimistic.SupportAligned
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).toHealing.sg_votes
        S.hc.η_SG
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).T
        rho.honest q
        (Protocol.proposedParent S rho (S.hc.opening_slot q)):= by
  let s:= S.hc.opening_slot q
  let B:= Internal.proposedBlock S rho s
  let Can:= Protocol.proposedParent S rho s
  have hqOne: 1 ≤ q:= Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  have hcutQ: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon:= by
    calc
      S.hc.Γ_neg1 S.E.Δ q ≤ S.hc.Γ_0 S.E.Δ q:=
        le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)
      _ ≤ S.hc.Γ_1 S.E.Δ q:=
        le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)
      _ ≤ S.hc.Γ_2 S.E.Δ q:=
        le_of_lt (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q)
      _ ≤ S.a q:= Γ_2_le_a S.hc S.E.Δ_pos q
      _ = Protocol.confirmation_time S.E s:= by
        simp only [s]
        exact (opening_confirmation_time_eq_action S q).symm
      _ ≤ rho.horizon:= by simpa only [s] using hconfHor
  have hcut: S.hc.Γ_neg1 S.E.Δ (q - 1 + 1) ≤ rho.horizon:= by
    simpa only [Nat.sub_add_cancel hqOne] using hcutQ
  have hadmit:= openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRise
    S adm hfb hfix hq hpostRead hdelay hconfHor hcap hpostProposal
      hproposer hJA hAparent
  have hvoteAction: Protocol.vote_time S.E s ≤ S.a q:= by
    calc
      Protocol.vote_time S.E s ≤ Protocol.confirmation_time S.E s:=
        Protocol.vote_time_le_confirmation_time S.E s
      _ = S.a q:= by
        simpa only [s] using opening_confirmation_time_eq_action S q
  have hBaction: ∀ v ∈ rho.honest, B ∈ (actionStoreAt S rho v q).T:= by
    intro v hv
    have hpre:= (admittedBefore_mem_and_stamp_at S adm.toScheduleWellFormed
      (hadmit v hv) (by simpa only [s] using hvoteAction)).1
    change B ∈ (Proofs.Optimistic.attestStore S
      (rho.stateBeforeTime S (S.a q) v).st (S.a q)).T
    rw [(Proofs.Optimistic.attestStore_fields S
      (rho.stateBeforeTime S (S.a q) v).st (S.a q)).2.1]
    simpa only [Run.storeBeforeTime] using hpre
  have hparentB: Block.Preceq Can B:= by
    dsimp only [Can, B]
    exact Protocol.preceq_of_parent?
      (Protocol.proposedBlock_parent S rho s)
  have hCanaction: ∀ v ∈ rho.honest,
      Can ∈ (actionStoreAt S rho v q).T:= by
    intro v hv
    let ast:= actionStoreAt S rho v q
    let pre:= rho.storeBeforeTime S v (S.a q)
    have hdep:= Proofs.Bridges.depReachable_stateBeforeTime S
      adm.toScheduleWellFormed adm.toDeliveryWellFormed (S.a q) v
    have hpcPre: ParentClosed pre:=
      parentClosed_depReachable S.E S.hc S.cfg (S.node v) pre (by
        simpa only [pre, Run.storeBeforeTime] using hdep)
    have hpc: ParentClosed ast:= by
      rw [parentClosed_iff] at hpcPre ⊢
      change Block.genesis ∈ (Proofs.Optimistic.attestStore S pre (S.a q)).T ∧
        ∀ X ∈ (Proofs.Optimistic.attestStore S pre (S.a q)).T,
          X.parent? = none ∨ X.parent ∈
            (Proofs.Optimistic.attestStore S pre (S.a q)).T
      rw [(Proofs.Optimistic.attestStore_fields S pre (S.a q)).2.1]
      exact hpcPre
    have hBmem: B ∈ ast.T:= by
      simpa only [ast] using hBaction v hv
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff ast).mp hpc).2
      Can B hBmem hparentB
  have hCanAtNext: ∀ v ∈ rho.honest,
      Can ∈ (actionStoreAt S rho v (q - 1 + 1)).T:= by
    intro v hv
    simpa only [Nat.sub_add_cancel hqOne] using hCanaction v hv
  have hupperAction: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) Can:= by
    intro u hu
    simpa only [Can, s] using hparents.actionTargetParent u hu
  have hact: ∀ v ∈ rho.honest,
      Proofs.Optimistic.SupportAligned
        (actionStoreAt S rho v q).toHealing.sg_votes S.hc.η_SG
        (actionStoreAt S rho v q).T rho.honest q Can:= by
    have hraw:= actionStoreSupportAligned_of_currentActionVote
      (S:= S) (rho:= rho) adm (r:= q - 1) (Can:= Can)
        hpostPreviousAction hcut hCanAtNext hupperAction
    simpa only [Nat.sub_add_cancel hqOne] using hraw
  intro v hv
  have h:= hact v hv
  rw [actionStoreAt_eq_update_confirmation_openingConfStore S rho v q] at h
  simpa only [Protocol.Store.toHealing, update_confirmation_T,
    Proofs.Optimistic.update_confirmation_sg_votes] using h

-/

/- The exact earlier declaration and proof remain byte-exact below. -/

/-- The exact fixed root, its height cap, and the prepared preceding-action
parent run give the three named opening-confirmation read facts. -/
theorem sgOpeningConfirmationReads_of_fixedJustificationRootNoRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {A : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hq : 0 < q)
    (hpostRead : S.E.t_GST ≤ read)
    (hdelay : read + S.E.Δ ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q))
    (hconfHor : Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤
      rho.horizon)
    (hcap : honestHMaxAt S rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostProposal : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hproposer : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hJA : Block.Preceq (rho.storeBeforeTime S w read).J A)
    (hAparent : Block.Preceq A
      (proposedParent S rho (S.hc.opening_slot q)))
    (hparents : FixedHeightRootOpeningParentRun S rho q) :
    ∀ v ∈ rho.honest,
      NamedSGOpeningConfirmationRead S rho (S.hc.opening_slot q) v P := by
  let s := S.hc.opening_slot q
  let J := (rho.storeBeforeTime S w read).J
  have hqOne : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hparentP : Block.Preceq (proposedParent S rho s) P.erase := by
    obtain ⟨parent, hparent, hparentErase⟩ := proposedBlockAt_parent S rho s hP
    have hpre : NamedBlock.Preceq parent P := by
      cases P with
      | genesis => cases hparent
      | node parent' slot root votes support rows proposer =>
          simp only [NamedBlock.parent?, Option.some.injEq] at hparent
          subst parent
          simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
          exact Or.inr (Proofs.NamedAncestry.named_self parent')
    rw [← hparentErase]
    exact Proofs.NamedWire.erase_preceq hpre
  have hJparent : Block.Preceq J (proposedParent S rho s) :=
    Block.preceq_trans hJA hAparent
  have hJP : Block.Preceq J P.erase :=
    Block.preceq_trans hJparent hparentP
  have hspos : 0 < s := by
    exact Nat.mul_pos hq
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E s).trans hconfHor
  have hPrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      s hspos hproposer hproposalHor hP
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    fixedRoot_namedTarget_of_fixedRoot S hfix
  obtain ⟨Jp, hJpP, hJpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift P hJP
  have hJpRun : RunBlock S rho Jp :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hPrun hJpP
  have hrootEq : Jp.root = Jn.root := by
    rw [← Proofs.NamedWire.erase_root Jp, ← Proofs.NamedWire.erase_root Jn,
      hJpErase, hJnErase]
  have hJpEq : Jp = Jn :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      Jp Jn hJpRun hJnRun Jp Jn
      (Or.inl (Proofs.NamedAncestry.named_self Jp))
      (Or.inr (Proofs.NamedAncestry.named_self Jn)) hrootEq
  have hPheight : H - 1 ≤
      (Protocol.derive_named S.E S.cfg P).h := by
    rw [← hJnHeight, ← hJpEq]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJpP
  have hcutQ : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon := by
    calc
      S.hc.Γ_neg1 S.E.Δ q ≤ S.hc.Γ_0 S.E.Δ q :=
        le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)
      _ ≤ S.hc.Γ_1 S.E.Δ q :=
        le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)
      _ ≤ S.hc.Γ_2 S.E.Δ q :=
        le_of_lt (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q)
      _ ≤ S.a q := Γ_2_le_a S.hc S.E.Δ_pos q
      _ = Protocol.confirmation_time S.E s := by
        simp only [s]
        exact (opening_confirmation_time_eq_action S q).symm
      _ ≤ rho.horizon := hconfHor
  intro v hv
  let t := Protocol.confirmation_time S.E s
  let st := rho.storeBeforeTime S v t
  have hrootMax :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hv hpostRead (by simpa only [s, t] using hdelay)
        (by simpa only [s, t] using hconfHor)
        (by simpa only [s, t] using hcap)
  have hroot : Protocol.get_fg_root st.toHealing.toFG = J := by
    simpa only [st, t, J] using hrootMax.1
  have hmax : st.h_max = H := by
    simpa only [st, t] using hrootMax.2
  have hadmit :=
    openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRise
      S adm hfb hfix hP hq hpostRead hdelay hconfHor hcap hpostProposal
        hproposer hJA hAparent v hv
  have hPtree : P.erase ∈ st.T := by
    have hmem := (admittedBefore_mem_and_stamp_at S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit
      (Protocol.vote_time_le_confirmation_time S.E s)).1
    simpa only [st, t] using hmem
  have hcandidateRaw : P.erase ∈
      Protocol.get_filtered_block_tree st.toHealing.toFG :=
    fixedRootGrade_mem_filtered_of_exactRoot S adm hv hPrun hPtree hJP
      hPheight hroot hmax
  have hrootP : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) P.erase := by
    rw [hroot]
    exact hJP
  have hrootParent : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG)
      (proposedParent S rho s) := by
    rw [hroot]
    exact hJparent
  have hround : S.hc.round_of (s + 1) = (q - 1) + 1 := by
    rw [Nat.sub_add_cancel hqOne]
    simpa only [s] using Proofs.HealingLemmas.round_of_opening_succ S.hc q
  have hanchorParent := confirmationAnchorAt_preceq_of_previousCarriers
    S adm hfb hround hpostPreviousAction
      (by simpa only [Nat.sub_add_cancel hqOne] using hcutQ)
      (by simpa only [s] using hconfHor)
      hparents.actionTargetParent hv hrootParent
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      st, t] using hrootP
  · exact Block.preceq_trans hanchorParent hparentP
  · simpa only [Internal.PhaseGrades.filteredTree,
      Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      st, t] using hcandidateRaw

#print axioms sgOpeningConfirmationReads_of_fixedJustificationRootNoRise

/-
/-- The exact fixed root, its height cap, and the preceding-action parent run
give all three local facts for the opening confirmation read of the proposal. -/
theorem sgOpeningConfirmationReads_of_fixedJustificationRootNoRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time}
    (hfix: FixedHeightJustificationRootAtRead S rho H w read)
    {q: Round} {A: Block V}
    (hq: 0 < q)
    (hpostRead: S.E.t_GST ≤ read)
    (hdelay: read + S.E.Δ ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q))
    (hconfHor: Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤
      rho.horizon)
    (hcap: honestHMaxAt S rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostProposal: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hproposer: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hJA: Block.Preceq (rho.storeBeforeTime S w read).J A)
    (hAparent: Block.Preceq A
      (Protocol.proposedParent S rho (S.hc.opening_slot q)))
    (hparents: FixedHeightRootOpeningParentRun S rho q):
    ∀ v ∈ rho.honest,
      SGOpeningConfirmationRead S rho (S.hc.opening_slot q) v
        (Internal.proposedBlock S rho (S.hc.opening_slot q)):= by
  let s:= S.hc.opening_slot q
  let B:= Internal.proposedBlock S rho s
  let Can:= Protocol.proposedParent S rho s
  let J:= (rho.storeBeforeTime S w read).J
  have hqOne: 1 ≤ q:= Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hparentB: Block.Preceq Can B:= by
    dsimp only [Can, B]
    exact Protocol.preceq_of_parent?
      (Protocol.proposedBlock_parent S rho s)
  have hJCan: Block.Preceq J Can:= by
    exact Block.preceq_trans hJA hAparent
  have hJB: Block.Preceq J B:=
    Block.preceq_trans hJCan hparentB
  have hcutQ: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon:= by
    calc
      S.hc.Γ_neg1 S.E.Δ q ≤ S.hc.Γ_0 S.E.Δ q:=
        le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)
      _ ≤ S.hc.Γ_1 S.E.Δ q:=
        le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)
      _ ≤ S.hc.Γ_2 S.E.Δ q:=
        le_of_lt (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q)
      _ ≤ S.a q:= Γ_2_le_a S.hc S.E.Δ_pos q
      _ = Protocol.confirmation_time S.E s:= by
        simp only [s]
        exact (opening_confirmation_time_eq_action S q).symm
      _ ≤ rho.horizon:= by simpa only [s] using hconfHor
  have hcut: S.hc.Γ_neg1 S.E.Δ (q - 1 + 1) ≤ rho.horizon:= by
    simpa only [Nat.sub_add_cancel hqOne] using hcutQ
  have hadmit:= openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRise
    S adm hfb hfix hq hpostRead hdelay hconfHor hcap hpostProposal
      hproposer hJA hAparent
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
      (S:= S) hfb
  intro v hv
  let read':= Protocol.confirmation_time S.E s
  let pre:= rho.storeBeforeTime S v read'
  let st:= Proofs.Optimistic.confStore S rho v s
  have hBT: B ∈ pre.T:= by
    exact (admittedBefore_mem_and_stamp_at S adm.toScheduleWellFormed
      (hadmit v hv)
      (Protocol.vote_time_le_confirmation_time S.E s)).1
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:=
    Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
      adm.toDeliveryWellFormed read' v
  have hagree: DerivedStateAgrees S.E S.cfg pre:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node v) pre hdep
  have hFJ: Block.Preceq pre.F pre.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg (S.node v) pre
      (Proofs.Bridges.reachableStore_of_depReachableStore
        S.E S.hc S.cfg (S.node v) hdep)
  obtain ⟨hroot, hmax⟩:=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hv hpostRead
        (by simpa only [s] using hdelay)
        (by simpa only [s] using hconfHor)
        (by simpa only [s] using hcap)
  have hrootCan: Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) Can:= by
    have hbase: Block.Preceq
        (Protocol.get_fg_root pre.toHealing.toFG) Can:= by
      rw [hroot]
      exact hJCan
    simpa only [st, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore, pre, read'] using
      hbase
  have hbatchAction: Proofs.Optimistic.BatchAligned
      (actionStoreAt S rho v q).toHealing.gradeView rho.honest q Can:= by
    simpa only [Nat.sub_add_cancel hqOne] using
      nextActionBatchAligned_of_carriersPreceq S adm
        hpostPreviousAction hcut hparents.actionTargetParent v hv
  have hbatch: Proofs.Optimistic.BatchAligned
      st.toHealing.gradeView rho.honest q Can:= by
    rw [actionStoreAt_eq_update_confirmation_openingConfStore S rho v q] at hbatchAction
    simpa only [st, s, Protocol.Store.toHealing, update_confirmation_T] using
      hbatchAction
  have hsupport: Proofs.Optimistic.SupportAligned
      st.toHealing.sg_votes S.hc.η_SG st.T rho.honest q Can:= by
    simpa only [st, s] using
      openingConfirmationSupportAlignedParent_of_fixedJustificationRootNoRise
        S adm hfb hfix hq hpostRead hdelay hconfHor hcap hpostProposal
          hpostPreviousAction hproposer hJA hAparent hparents v hv
  have hsg: Block.Preceq
      (Protocol.get_sg_root S.E S.hc st.toHealing q) Can:=
    Protocol.get_sg_root_preceq_of_aligned
      S hmajority hbatch hsupport hrootCan
  have hround: S.hc.round_of (s + 1) = q:= by
    simpa only [s] using Proofs.HealingLemmas.round_of_opening_succ S.hc q
  have hslot: st.s = s + 1:= by
    simp only [st, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_confirmation_time]
  have hanchorCan: Block.Preceq
      (confAnchor S.E S.hc st) Can:= by
    unfold confAnchor
    rw [hslot, hround]
    exact hsg
  have hrootB: Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B:= by
    rw [hroot]
    exact hJB
  have hFB: Block.Preceq pre.F B:=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st:= pre.toHealing.toFG) hFJ)
      hrootB
  have hheight: pre.h_max - 1 ≤ (pre.σ B).h:= by
    calc
      pre.h_max - 1 = H - 1:= by rw [hmax]
      _ = (derived_state S.E S.cfg J).h:= by
        simpa only [J] using hfix.targetDerivedHeight.symm
      _ ≤ (derived_state S.E S.cfg B).h:=
        Protocol.derived_h_mono S.E S.cfg hJB
      _ = (pre.σ B).h:=
        (congrArg (fun state => state.h) (hagree B hBT)).symm
  have hV: B ∈ Protocol.V_tree pre.toHealing.toFG:= by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hBT, hFB⟩, B, hBT, Block.preceq_self B, hheight⟩
  have hfiltered:= Proofs.Records.mem_filtered_of_mem_V_tree hV hrootB
  refine ⟨?_, ?_, ?_⟩
  · simpa only [confRoot, st, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      pre, read'] using hrootB
  · exact Block.preceq_trans hanchorCan hparentB
  · simpa only [confTree, st, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      pre, read'] using hfiltered

-/




/-
/-- Compatibility corollary for the original strict-read interference record. -/
theorem openingConfirmationSupportAlignedParent_of_fixedRootNoRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time} {P: Block V}
    (hfix: FixedHeightRootInterferenceAtRead S rho H w read P)
    {q: Round} {A: Block V}
    (hq: 0 < q)
    (hpostRead: S.E.t_GST ≤ read)
    (hdelay: read + S.E.Δ ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q))
    (hconfHor: Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤
      rho.horizon)
    (hcap: honestHMaxAt S rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostProposal: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hproposer: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hJA: Block.Preceq (rho.storeBeforeTime S w read).J A)
    (hAparent: Block.Preceq A
      (Protocol.proposedParent S rho (S.hc.opening_slot q)))
    (hparents: FixedHeightRootOpeningParentRun S rho q):
    ∀ v ∈ rho.honest,
      Proofs.Optimistic.SupportAligned
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).toHealing.sg_votes
        S.hc.η_SG
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).T
        rho.honest q
        (Protocol.proposedParent S rho (S.hc.opening_slot q)):=
  openingConfirmationSupportAlignedParent_of_fixedJustificationRootNoRise
    S adm hfb hfix.toJustificationRootAtRead hq hpostRead hdelay hconfHor
      hcap hpostProposal hpostPreviousAction hproposer hJA hAparent hparents

/-- Compatibility corollary for the original strict-read interference record. -/
theorem sgOpeningConfirmationReads_of_fixedRootNoRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time} {P: Block V}
    (hfix: FixedHeightRootInterferenceAtRead S rho H w read P)
    {q: Round} {A: Block V}
    (hq: 0 < q)
    (hpostRead: S.E.t_GST ≤ read)
    (hdelay: read + S.E.Δ ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q))
    (hconfHor: Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤
      rho.horizon)
    (hcap: honestHMaxAt S rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostProposal: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hproposer: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hJA: Block.Preceq (rho.storeBeforeTime S w read).J A)
    (hAparent: Block.Preceq A
      (Protocol.proposedParent S rho (S.hc.opening_slot q)))
    (hparents: FixedHeightRootOpeningParentRun S rho q):
    ∀ v ∈ rho.honest,
      SGOpeningConfirmationRead S rho (S.hc.opening_slot q) v
        (Internal.proposedBlock S rho (S.hc.opening_slot q)):=
  sgOpeningConfirmationReads_of_fixedJustificationRootNoRise
    S adm hfb hfix.toJustificationRootAtRead hq hpostRead hdelay hconfHor
      hcap hpostProposal hpostPreviousAction hproposer hJA hAparent hparents

-/

#print axioms openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRise


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
