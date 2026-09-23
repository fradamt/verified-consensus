module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Generic.FrontierCoverage
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.Handlers.NamedStore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Protocol.Handlers.Proposer

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Carrier first-run facts

This module records the part of the carrier-round argument that follows from
the schedule and the existing proposal-pool bridge. Resolution of an action
row also needs a resolved SG carrier; that is deliberately kept separate.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The `+2` carrier proposal is at least one network delay after the round
action. -/
theorem action_add_delta_le_plusTwo_proposal_time
    (S : Setup V) (q : Round) :
    S.a q + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2) := by
  unfold Setup.a Protocol.HealConfig.a Protocol.proposal_time Env.t slotStart
  have hdelta : (0 : Int) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  push_cast
  ring_nf
  apply add_le_add_left
  exact Int.mul_le_mul_of_nonneg_left (by omega) hdelta

/-- Every honest round-`q` action is in the processed-attestation list read by
the honest `+2` proposer. -/
theorem honestPlusTwoBlock_holdsRoundRows
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hpost : S.E.t_GST ≤ S.a q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    (actionAttestationAt S rho v q).erase ∈
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q + 2)).processed_attestations S.hc := by
  have hemit := honest_emits_exact_actionAttestationAt S adm hv q
    (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (action_add_delta_le_plusTwo_proposal_time S q) |>.trans hhor) (by assumption)
  have haHon : (actionAttestationAt S rho v q).val_index ∈ rho.honest := by
    rw [(actionAttestationAt_shape S rho v q).1]
    exact hv
  have hemit' : rho.emits S (actionAttestationAt S rho v q).val_index
      (Object.attest (actionAttestationAt S rho v q)) (S.a q) := by
    rw [(actionAttestationAt_shape S rho v q).1]
    exact hemit
  exact honestAttestation_mem_processedAtProposal_after_gst S adm hcar.2.2 hhor
    haHon hemit' hpost (action_add_delta_le_plusTwo_proposal_time S q)



/-- No accepted block before the carrier's `+2` proposal can carry an exact
honest round-`q` action row. -/
theorem noEarlierCarrier_of_roundRows
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    {reader : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i reader (.block B) t)
    (ht : t < Protocol.proposal_time S.E (S.hc.opening_slot q + 2))
    {v : V} (hv : v ∈ rho.honest)
    (ha : actionAttestationAt S rho v q ∈ B.attestations) : False := by
  have hroundGuard : q ≤ S.hc.round_of B.slot := by
    have hall : ∀ a ∈ B.erase.attestations,
        a.round ≤ S.hc.round_of B.erase.slot := by
      simpa only [Protocol.carried_attestations_admissible, List.all_eq_true,
        decide_eq_true_eq] using
        (Protocol.carried_attestations_admissible_of_acceptsAt_block S hacc)
    have ha' : (actionAttestationAt S rho v q).erase ∈ B.erase.attestations := by
      rw [Proofs.NamedWire.erase_attestations]
      exact List.mem_map.mpr ⟨actionAttestationAt S rho v q, ha, rfl⟩
    have hround : (actionAttestationAt S rho v q).erase.round = q := by
      simpa only [NamedAttestation.erase] using
        (actionAttestationAt_shape S rho v q).2.1
    rw [← hround]
    simpa only [Proofs.NamedWire.erase_slot] using hall _ ha'
  have hslotLt : B.slot < S.hc.opening_slot q + 2 := by
    by_contra hnot
    have hle : S.hc.opening_slot q + 2 ≤ B.erase.slot := by
      simpa only [Proofs.NamedWire.erase_slot] using Nat.le_of_not_gt hnot
    have htime := Protocol.proposal_time_mono S.E hle
    exact (not_lt_of_ge (htime.trans
      (Protocol.proposal_time_le_of_acceptsAt_block S adm hacc))) ht
  have hopenLe : S.hc.opening_slot q ≤ B.slot := by
    have hR : 0 < S.hc.R := lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
    have hmul : q * S.hc.R ≤ B.slot :=
      (Nat.le_div_iff_mul_le hR).mp hroundGuard
    simpa only [Protocol.HealConfig.opening_slot] using hmul
  have hslots : B.slot = S.hc.opening_slot q ∨
      B.slot = S.hc.opening_slot q + 1 := by
    rcases Nat.eq_or_lt_of_le hopenLe with hslot | hslot
    · exact Or.inl hslot.symm
    · right
      apply Nat.le_antisymm
      · exact Nat.le_of_lt_succ (by
          simpa only [Nat.succ_eq_add_one] using hslotLt)
      · exact Nat.succ_le_iff.mpr hslot
  have hprop : S.E.proposer B.slot ∈ rho.honest := by
    rcases hslots with hslot | hslot
    · rw [hslot]; exact hcar.1
    · rw [hslot]; exact hcar.2.1
  have hpos : 0 < B.slot := by
    have hparent := Protocol.parent_slot_lt_of_acceptsAt_block S hacc
    simpa only [Proofs.NamedWire.erase_slot] using
      (lt_of_le_of_lt (Nat.zero_le _) hparent)
  have hslotHor : Protocol.proposal_time S.E B.slot ≤ rho.horizon :=
    by
      have htime := Protocol.proposal_time_le_of_acceptsAt_block S adm hacc
      have htime' : Protocol.proposal_time S.E B.slot ≤ t := by
        simpa only [Proofs.NamedWire.erase_slot] using htime
      exact htime'.trans (le_of_lt ht |>.trans hhor)
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho B.slot
  obtain ⟨j, hself⟩ := Protocol.acceptsAt_proposedBlock S adm hpos hprop hslotHor hP
  have hBproc : NamedRun.processes S rho reader (.block B) t := by
    obtain ⟨hindex, e, he, -, htime⟩ := hacc.1
    rcases hindex with hindex | hdelivery
    · left
      obtain ⟨t', htick, hmem⟩ := hindex
      have heq : Event.tick reader t' = e :=
        Option.some.inj (htick.symm.trans he)
      have ht' : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      exact ⟨i, htick, hmem⟩
    · right
      obtain ⟨t', hdeliver⟩ := hdelivery
      have heq : Event.deliver reader (.block B) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have ht' : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      exact ⟨i, hdeliver⟩
  have hPproc : NamedRun.processes S rho (S.E.proposer B.slot)
      (.block P) (Protocol.proposal_time S.E B.slot) := by
    obtain ⟨hindex, e, he, -, htime⟩ := hself.1
    rcases hindex with hindex | hdelivery
    · left
      obtain ⟨t', htick, hmem⟩ := hindex
      have heq : Event.tick (S.E.proposer B.slot) t' = e :=
        Option.some.inj (htick.symm.trans he)
      have ht' : t' = Protocol.proposal_time S.E B.slot :=
        (congrArg Event.time heq).trans htime
      subst t'
      exact ⟨j, htick, hmem⟩
    · right
      obtain ⟨t', hdeliver⟩ := hdelivery
      have heq : Event.deliver (S.E.proposer B.slot) (.block P) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have ht' : t' = Protocol.proposal_time S.E B.slot :=
        (congrArg Event.time heq).trans htime
      subst t'
      exact ⟨j, hdeliver⟩
  have hBp : B.proposer? = some (S.E.proposer B.slot) := by
    simpa only [Proofs.NamedWire.erase_proposer, Proofs.NamedWire.erase_slot] using
      (Protocol.proposer_eq_of_acceptsAt_block S hacc)
  have hPslot : P.slot = B.slot := proposedBlockAt_slot S rho B.slot hP
  have hPp : P.proposer? = some (S.E.proposer B.slot) := by
    simpa only [Proofs.NamedWire.erase_proposer, Proofs.NamedWire.erase_slot, hPslot] using
      (Protocol.proposedBlock_proposer S rho B.slot hP)
  have hBP : B = P :=
    unique_slot_block S adm hprop hBproc hPproc hBp hPp rfl hPslot
  have haHon : (actionAttestationAt S rho v q).val_index ∈ rho.honest := by
    rw [(actionAttestationAt_shape S rho v q).1]
    exact hv
  have haP : actionAttestationAt S rho v q ∈ P.attestations := by
    rw [← hBP]
    exact ha
  obtain ⟨te, hte, hemit⟩ :=
    adm.toNamedAdmissibleCore.toNamedUnforgeable.carried_attest _ _ _ hPproc
    (actionAttestationAt S rho v q) haP haHon
  have hteq : te = S.a q := by
    calc
      te = S.a (actionAttestationAt S rho v q).round :=
        (Proofs.Optimistic.emits_attest_shape S hemit).2
      _ = S.a q := by rw [(actionAttestationAt_shape S rho v q).2.1]
  have hbefore : Protocol.proposal_time S.E B.slot < S.a q := by
    rcases hslots with hslot | hslot
    · rw [hslot]
      unfold Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a slotStart
      ring_nf
      have h6 : (0 : Int) < 6 := by omega
      have hd6 : 0 < S.E.Δ * 6 := Int.mul_pos S.E.Δ_pos h6
      exact lt_add_of_pos_left _ hd6
    · rw [hslot]
      unfold Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a slotStart
      push_cast
      ring_nf
      have h46num : (4 : Int) < 6 := by omega
      have h46 : S.E.Δ * 4 < S.E.Δ * 6 :=
        Int.mul_lt_mul_of_pos_left h46num S.E.Δ_pos
      simpa only [add_comm] using
        (add_lt_add_left h46 (S.E.Δ * (S.hc.opening_slot q : Int) * 4))
  rw [hteq] at hte
  exact (not_lt_of_ge hte) hbefore






omit [Fintype V] in
private theorem named_chain_row_ancestor
    {B : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ Protocol.NamedProposalRows.chainRows B) :
    ∃ A : NamedBlock V, NamedBlock.Preceq A B ∧ a ∈ A.attestations := by
  induction B with
  | genesis => simp [Protocol.NamedProposalRows.chainRows] at ha
  | node p s root votes support rows proposer ih =>
      simp only [Protocol.NamedProposalRows.chainRows, List.mem_append] at ha
      rcases ha with ha | ha
      · exact ⟨.node p s root votes support rows proposer,
          Proofs.NamedAncestry.named_self _, ha⟩
      · obtain ⟨A, hA, hrow⟩ := ih ha
        exact ⟨A, Proofs.NamedAncestry.named_extend s root votes support rows proposer hA,
          hrow⟩

omit [Fintype V] in
private theorem named_ancestor_body_mem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

/-! The named proposal row source is the prepared read's own source. -/

/-- A resolved action row is either already on the `+2` proposal's parent
chain or is carried by the new `+2` proposal. -/
theorem plusTwoProposal_covers_resolvedRoundRow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) (q : Round)
    {a : NamedAttestation V} {B : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot q + 2) = some B)
    (hhon : a.val_index ∈ rho.honest)
    (hresolved : a ∈ Protocol.NamedProposalRows.select .poolAndCarried S.hc
      (proposerReadAt S rho (S.hc.opening_slot q + 2)).st) :
    a ∈ Protocol.NamedProposalRows.chainRows B.parent ∨
      a ∈ B.attestations := by
  let s := S.hc.opening_slot q + 2
  have hpay := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract (proposerReadAt S rho s).cache) .poolAndCarried
    S.E S.hc (S.node (S.E.proposer s)) (proposerReadAt S rho s).st B hB
  have hrows : B.attestations = Protocol.NamedProposalRows.proposalRows B.parent
      (Protocol.NamedProposalRows.select .poolAndCarried S.hc
        (proposerReadAt S rho s).st) := hpay.2.2.2.2.2.2.1
  by_cases hchain : a ∈ Protocol.NamedProposalRows.chainRows B.parent
  · exact Or.inl hchain
  · right
    rw [hrows]
    apply NamedProposalRows.mem_proposalRows_of_unique B.parent _ a hresolved hchain
    intro b hb hval hround
    exact honest_selected_row_unique S adm s hresolved hb hhon hval hround

/-- A resolved honest round action is carried by the `+2` proposal itself:
the parent-chain alternative would give an earlier accepted carrier, which
`noEarlierCarrier_of_roundRows` excludes. -/
theorem plusTwoProposal_carries_resolvedRoundRow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hcar : ProposerCarrierAt S rho q)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {B : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot q + 2) = some B)
    (hresolved : actionAttestationAt S rho v q ∈
      Protocol.NamedProposalRows.select .poolAndCarried S.hc
        (proposerReadAt S rho (S.hc.opening_slot q + 2)).st) :
    actionAttestationAt S rho v q ∈ B.attestations := by
  let s := S.hc.opening_slot q + 2
  let tp := Protocol.proposal_time S.E s
  let p := S.E.proposer s
  let pre := rho.storeBeforeTime S p tp
  have hpay := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract (proposerReadAt S rho s).cache) .poolAndCarried
    S.E S.hc (S.node p) (proposerReadAt S rho s).st B hB
  have haVal : (actionAttestationAt S rho v q).val_index = v :=
    (actionAttestationAt_shape S rho v q).1
  rcases plusTwoProposal_covers_resolvedRoundRow S adm q hB
      (by simpa only [haVal] using hv) hresolved with hparent | hcarry
  · have hparentPre : B.parent ∈ pre.bodies := by
      have hparentRead := hpay.1
      change B.parent ∈ (rho.stateBeforeTime S tp p).st.bodies at hparentRead
      simpa only [pre, Run.storeBeforeTime] using hparentRead
    obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed tp
    have hparentN : B.parent ∈ (rho.stateBefore S n p).st.bodies := by
      rw [← hn]
      exact hparentPre
    have hpc : NamedStore.NamedParentClosed (rho.stateBefore S n p).st :=
      (Proofs.NamedRuntime.stateBefore_invariants S rho n p).1.1.1.2.2.1
    obtain ⟨X, hXP, hrow⟩ := named_chain_row_ancestor hparent
    have hXn := named_ancestor_body_mem hpc hparentN hXP
    have hprocessed : Object.processed (rho.stateBefore S n p).st
        (Object.block X) = true := by
      simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq] using hXn
    rcases Protocol.acceptsAt_block_of_processed S rho p n X hprocessed with
        hgen | ⟨ix, hix, tx, hacc⟩
    · subst X
      simp [NamedBlock.attestations] at hrow
    · have hacc' := hacc
      obtain ⟨hhandle, -, -⟩ := hacc
      obtain ⟨-, e, he, -, htime⟩ := hhandle
      have htx : tx < tp := by
        have htxe : tx = e.time := htime.symm
        rw [htxe]
        exact hbefore ix e hix he
      exact False.elim (noEarlierCarrier_of_roundRows S adm hcar
        (by simpa only [s, tp] using hhor) hacc'
        (by simpa only [s, tp] using htx) hv hrow)
  · exact hcarry

#print axioms action_add_delta_le_plusTwo_proposal_time
#print axioms honestPlusTwoBlock_holdsRoundRows
#print axioms noEarlierCarrier_of_roundRows
#print axioms plusTwoProposal_covers_resolvedRoundRow
#print axioms plusTwoProposal_carries_resolvedRoundRow

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
