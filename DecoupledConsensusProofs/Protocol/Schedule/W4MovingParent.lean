module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainCeiling

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The moving endpoint is at or below the honest proposal's parent, named

`MovingSlotAdoptionSupply` (`MovingChainIterateRun`) asks the fold, at every
slot it enters with an honest proposer, for four facts about that slot. Three
of them are the adoption step's own business. The fourth is the PARENT: the
window endpoint the fold carries is at or below the parent the honest slot
proposer selects. Its erased forms are parked in `MovingChainParentRun`
(`MovingFrontierChainState.endpoint_preceq_proposedParent`,
`MovingSlotEntryState.honestParent`), and they stay parked: their route runs
through `coneSupport_proposerDutyStore_after_gst`, which is itself parked.

This leaf gives the N form on the prepared proposal read instead. earlier's
argument is unchanged — the previous slot's honest votes lie above the
endpoint, they resolve in the proposer's own frozen view because the read's
selected root is below the endpoint, the endpoint is active there because it
sits at the local frontier band, and the composed head IS the proposal parent.
Only the surface moves: the prepared read `proposalDutyRead` in place of the
erased `proposerDutyStore`, `NamedHonestVotesCone` in place of
`Proofs.Optimistic.HonestVotesCone`, and `Protocol.derive_named` in place of
`derived_state`, so the cone support comes from
`fixedRoot_preparedProposalConeSupport_of_namedCone` and the head step from
`fixedRoot_preparedProposalHead_preceq_of_cone`.

The previous round's carrier ceiling is supplied, not read back out of the
history, exactly as everywhere else in `MovingChainCeilingRun`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The endpoint is in the proposer's own prepared read

The named proof of the parked `proposerStore_mem_of_cone`
(`MovingChainParentRun.lean:66`): same two cases, with the named cone's witness
erased at the one place the erased proof used the block directly. -/

/-- An available honest slot-`c` head above `P` puts `P` in the slot-`(c+1)`
proposer's own store. -/
private theorem w4p_proposerStore_mem_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {c : Slot} {P : Block V}
    (havailable : HonestHeadsAvailableBefore S rho c
      (S.E.proposer (c + 1)) (Protocol.support_cutoff S.E c))
    (hvotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq P X)) :
    P ∈ (rho.storeBeforeTime S (S.E.proposer (c + 1))
      (Protocol.proposal_time S.E (c + 1))).T := by
  have hpositive : 0 < ((S.E.committee c) ∩ rho.honest).card := by
    have hcc := hcom c
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  have hxCommittee : x ∈ S.E.committee c := (Finset.mem_inter.mp hx).1
  have hxHonest : x ∈ rho.honest := (Finset.mem_inter.mp hx).2
  obtain ⟨X, hPX, hXrun, hXemit⟩ := hvotes x hxHonest hxCommittee
  rcases havailable X.erase
    ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩ with
    hXgen | hXadmit
  · have hPgen : P = Block.genesis :=
      Block.preceq_antisymm (hXgen ▸ hPX) (Protocol.preceq_genesis P)
    rw [hPgen]
    exact (Protocol.genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed
      (S.E.proposer (c + 1)) (Protocol.proposal_time S.E (c + 1))
      (Protocol.support_cutoff S.E c)).1
  · exact (WeakGoldfish.admittedBefore_ancestor_mem_and_stamp_at S adm
      hXadmit hPX (support_cutoff_le_proposal_time_succ S.E c)).1

/-! ## 2. The proposal read against the moving endpoint -/

/-- **The moving endpoint is at or below the honest slot-`(c+1)` proposal
parent**, with the previous round's carrier ceiling supplied.

The N twin of the parked `MovingFrontierChainState.endpoint_preceq_proposedParent`
and of the parked `..._of_ceiling` in `MovingChainCeilingRun`. Everything is
keyed on the moving history at any cursor at or after the strict proposal
cursor, so the caller may use the history through the proposer's own tick. -/
theorem MovingFrontierChainStateN.endpoint_preceq_proposedParent_of_ceiling_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {EndAt : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k EndAt)
    {c : Slot} (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (EndAt k))
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hcutHor : Protocol.support_cutoff S.E c ≤ rho.horizon)
    (hpropHor : Protocol.proposal_time S.E (c + 1) ≤ rho.horizon)
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) ≤ k)
    (hprop : S.E.proposer (c + 1) ∈ rho.honest)
    (hvotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq (EndAt k) X))
    (hstart : t1 ≤ Protocol.proposal_time S.E (c + 1)) :
    Block.Preceq (EndAt k) (proposedParent S rho (c + 1)) := by
  classical
  obtain ⟨E, hE, hErun⟩ := h.endpointRun k h.start_le (Nat.le_refl k)
  have hsep : ∀ q : Round,
      S.a q < Protocol.proposal_time S.E (c + 1) →
      S.a q < Protocol.proposal_time S.E (c + 1) := fun _ hq => hq
  -- the proposer's own read: root below the endpoint, and the frontier band
  have hrootRaw : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer (c + 1))
          (Protocol.proposal_time S.E (c + 1))).core.toHealing.toFG) E.erase :=
    h.readRoot_preceq_endpointAtCursor_named S adm hfb hsep hcursor hprop
      hstart hE hErun
  have hbandRaw :
      (rho.storeBeforeTime S (S.E.proposer (c + 1))
        (Protocol.proposal_time S.E (c + 1))).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h :=
    h.readFrontier_sub_one_le_endpointAtCursor_named S adm hfb hsep hcursor
      hprop hE hErun
  have hsourceRoot : Block.Preceq
      (Protocol.get_fg_root
        (proposalDutyRead S rho (c + 1)).st.core.toHealing.toFG) E.erase := by
    simpa only [proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using hrootRaw
  have hsourceBand :
      (proposalDutyRead S rho (c + 1)).st.core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg E).h := by
    simpa only [proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using hbandRaw
  -- The previous round's carriers, supplied rather than read back
  have hupperE : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) E.erase := by
    intro u hu
    simpa only [hE] using hupper u hu
  have hsourceAnchor : Block.Preceq
      (PhaseGrades.nodeAnchor S (proposalDutyRead S rho (c + 1))
        (S.hc.round_of (proposalDutyRead S rho (c + 1)).st.core.s)) E.erase :=
    proposalAnchorAt_preceq_of_previousCarriers_named S adm hfb hround
      hpostAction hcut hpropHor hupperE hprop
      (by simpa only [proposalDutyRead] using hsourceRoot)
  -- the endpoint is in the proposer's store
  have hvotesE : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq E.erase X) := by
    simpa only [hE] using hvotes
  have havailable := honestHeadsAvailableBefore_of_postHealingCone_at
    S adm.toNamedAdmissibleCore hprop hpostVote hcutHor
      (support_cutoff_le_proposal_time_succ S.E c) hrootRaw hvotesE
  have hmemRaw : E.erase ∈ (rho.storeBeforeTime S (S.E.proposer (c + 1))
      (Protocol.proposal_time S.E (c + 1))).T :=
    w4p_proposerStore_mem_of_cone S adm hcom havailable hvotesE
  have hmem : E.erase ∈ (proposalDutyRead S rho (c + 1)).st.core.T := by
    simpa only [proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using hmemRaw
  -- the endpoint's own named body at that read, so the view is `derive_named`
  have hmemPre : E.erase ∈
      (rho.stateBeforeTime S (Protocol.proposal_time S.E (c + 1))
        (S.E.proposer (c + 1))).st.core.T := by
    simpa only [proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hmem
  obtain ⟨E0, hE0body, hE0erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.proposal_time S.E (c + 1)) (S.E.proposer (c + 1)) hmemPre
  have hE0run : RunBlock S rho E0 := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.proposal_time S.E (c + 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hprop
    simpa only [Run.storeBeforeTime, hn] using hE0body
  have hE0eq : E0 = E := by
    apply adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      E0 E hE0run hErun E0 E (Or.inl (Proofs.NamedAncestry.named_self E0))
      (Or.inr (Proofs.NamedAncestry.named_self E))
    rw [← Proofs.NamedWire.erase_root E0, hE0erase, ← Proofs.NamedWire.erase_root E]
  have hEbody : E ∈
      (rho.stateBeforeTime S (Protocol.proposal_time S.E (c + 1))
        (S.E.proposer (c + 1))).st.bodies := by
    rw [← hE0eq]
    exact hE0body
  have hsigma :
      (proposalDutyRead S rho (c + 1)).st.core.σ E.erase =
        Protocol.derive_named S.E S.cfg E := by
    rw [← hE0erase, hE0eq]
    simpa only [proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.proposal_time S.E (c + 1)) (S.E.proposer (c + 1)) E hEbody
  have hwitness : CanonicalConeWitness
      (proposalDutyRead S rho (c + 1)).st.core E.erase := by
    refine ⟨E.erase, hmem, Block.preceq_self _, ?_⟩
    rw [hsigma]
    exact hsourceBand
  -- the Goldfish inputs at the proposal read
  have hrootCompat : Block.compatible
      (Protocol.get_fg_root
        (proposalDutyRead S rho (c + 1)).st.core.toHealing.toFG)
      E.erase = true :=
    Block.compatible_of_preceq_common hsourceRoot (Block.preceq_self E.erase)
  have hsupport := fixedRoot_preparedProposalConeSupport_of_namedCone
    S adm hcom hc hpostVote hcutHor hprop hsourceRoot hvotesE
  have hvalid := Protocol.proposerDutyStore_proposer_view_valid_core
    S adm.toNamedAdmissibleCore (c + 1)
  have hhead := fixedRoot_preparedProposalHead_preceq_of_cone S adm
    hrootCompat hwitness hsourceAnchor hsupport hvalid
  simpa only [hE] using hhead

#print axioms MovingFrontierChainStateN.endpoint_preceq_proposedParent_of_ceiling_named

/-! ## 3. The parent fact at an N slot-entry state

The history through the proposer's own tick, which the entry state and the
named window facts already determine, is the whole input. This is what removes
the apparent circularity: the fold needs the parent fact, and the parent fact
needs only the pre-proposal history. -/

private theorem w4p_int_le_add_two {x d : Int} (hd : 0 < d) :
    x ≤ x + 2 * d := by omega

/-- `t_{s+1} ≤ t_s + 6Δ`: the next slot's proposal precedes this slot's
confirmation evaluation. -/
private theorem w4p_proposalTimeSucc_le_confirmationTime (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ]
  simp only [Protocol.proposal_time, Protocol.support_cutoff]
  exact w4p_int_le_add_two E.Δ_pos

/-- **`endpointBelowHonestParent` at one slot, over the N history.**

The window endpoint of slot `c + 1` is at or below the parent the honest
slot-`(c + 2)` proposer selects, with the previous round's carrier ceiling
supplied by the caller. -/
theorem MovingSlotEntryStateN.honestParent_of_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowDataC S rho M0 c Prev)
    (hdata' : MovingSlotWindowDataC S rho M0 (c + 1) Next)
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq Next (proposedParent S rho (c + 1 + 1)) := by
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  obtain ⟨r', hround', hpostAction', hcut', hupper'⟩ := hdata'.round
  have hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hhorProp : Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon :=
    (w4p_proposalTimeSucc_le_confirmationTime S.E (c + 1)).trans hdata'.slotHor
  have hcone := hentry.windowVotesCone_of_ceiling S adm hcom hfb hdata.pos
    hround hupper hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor
    hfrontier
  obtain ⟨p, EndAt, _hpevent, hsnp, hEndAtp, hstate⟩ :=
    hentry.historyAtHonestProposalEvent S adm hfrontier hfacts hprop
      hhorProp hhorSC hv
  have hcone' : NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq (EndAt p) X) := by
    rw [hEndAtp]
    exact hcone
  have hupperK : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r') (EndAt p) := by
    rw [hEndAtp]
    exact hupper'
  have hparent := hstate.endpoint_preceq_proposedParent_of_ceiling_named
    S adm hcom hfb (Nat.succ_pos c) hround' hupperK hpostAction' hcut'
    hdata'.postVote hhorSC hhorProp hsnp hprop hcone'
    (hentry.startTime.trans
      (Protocol.proposal_time_mono S.E (Nat.le_succ (c + 1))))
  rw [hEndAtp] at hparent
  exact hparent

#print axioms MovingSlotEntryStateN.honestParent_of_ceiling

/-! ## 4. The conjunct the fold's adoption supply asks for

`MovingSlotAdoptionSupply` (`MovingChainIterateRun.lean:723`) quantifies the
next endpoint, because the endpoint moves at every step of the iteration. The
endpoint is nevertheless determined: `MovingSlotFrontierAt.selected` picks it
out of the candidate set with `Block.deepest?`, so two frontier witnesses over
the same old endpoint agree, and the quantified `Next` is the one the ceiling
window facts produce. -/




/-! ## 5. The parent pin of the ceiling fold step, discharged

`MovingSlotFoldAtN.step_of_ceiling_of_pins` (`MovingChainCeilingRun`) takes the
parent read, the honest entry step and the Byzantine entry step as hypotheses.
Section 3 supplies the first of the three, so the ceiling fold step inside the
boundary round now waits on the two entry steps alone. -/
theorem MovingSlotFoldAtN.step_of_ceiling_of_stepPins
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {s0 c : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hdata : MovingSlotWindowDataC S rho M0 c (F (c + 1)))
    (htiming : MovingSlotActionCeiling S rho c (F (c + 1)))
    (hdata' : MovingSlotWindowDataC S rho M0 (c + 1) (F (c + 1)))
    {v : V} (hv : v ∈ rho.honest)
    (hpinHonest : ∀ Nxt : Block V,
      MovingSlotFrontierAt S rho c End Nxt →
      NamedMovingSlotWindowFacts S rho (c + 1) End Nxt →
      MovingSlotWindowDataC S rho M0 (c + 1) Nxt →
      S.E.proposer (c + 1 + 1) ∈ rho.honest →
      Block.Preceq Nxt (proposedParent S rho (c + 1 + 1)) →
      ∃ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P ∧
        MovingSlotEntryStateN S rho t1 M0 (c + 1 + 1) Nxt P.erase)
    (hpinByzantine : ∀ Nxt : Block V,
      MovingSlotFrontierAt S rho c End Nxt →
      NamedMovingSlotWindowFacts S rho (c + 1) End Nxt →
      MovingSlotWindowDataC S rho M0 (c + 1) Nxt →
      S.E.proposer (c + 1 + 1) ∉ rho.honest →
      MovingSlotEntryStateN S rho t1 M0 (c + 1 + 1) Nxt Nxt) :
    ∃ (F' : Slot → Block V) (End' : Block V),
      MovingSlotFoldAtN S rho t1 M0 s0 (c + 1 + 1) F' End' ∧
        ∀ d : Slot, d ≤ c + 1 → F' d = F d :=
  MovingSlotFoldAtN.step_of_ceiling_of_pins S adm hcom hfb hfold hdata htiming
    hdata' hv
    (fun Nxt hfr hfa hdN hprop =>
      hfold.entry.honestParent_of_ceiling S adm hcom hfb hdata hdN hfr hfa
        hprop hv)
    hpinHonest hpinByzantine

#print axioms MovingSlotFoldAtN.step_of_ceiling_of_stepPins

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
