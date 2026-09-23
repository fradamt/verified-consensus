module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4CarrierChainFinalitySplit
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainJustification
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # W4 branches fk-chain, part 2: `W4CarrierChainFinalityPin` from one producer

the corresponding branch split its carrier-chain pin into `W4CarrierJustificationHeightPin`
and `W4CommonFinalizedOfJustifiedPrefixPin`
(`W4CarrierChainFinalitySplitRun.lean:88,100`). The first of those two is not
provable as stated, and the reason is a statement gap, not a missing proof:

* it quantifies over every round `r` with `CarrierFinalityFirstHalfAt` as the
  only round premise, and asks for a NAMED ancestor `X` of the slot-`+2`
  proposal `P2`;
* earlier's twin (`CanonicalRegimeSecondCheckpointRun.lean:224-268`) gets the
  chain link `P1 ⪯ P2` from `hhalf.plusTwoParent` outright, because there both
  blocks are erased and `Block.parent` is a function of the block;
* in the selection `plusTwoParent` only pins the ERASURE of `P2`'s parent
  (`proposedParent S rho (s+2) = P1.erase`). Identifying `P2.parent` with the
  named `P1` is run-wide root collision freedom, which needs both proposals to
  be run blocks, i.e. the honest proposers and the horizon bound of
  `ProposerCarrierAt S rho r`. `CarrierFinalityFirstHalfAt` has no carrier
  field, so the premise is unavailable inside that pin.

`W4CarrierChainFinalityPin` itself does carry `ProposerCarrierAt S rho c`, and
its own body already derives the horizon bound at slot `opening_slot c + 2`, so
nothing is missing at the real consumer.

**Do not discharge `W4CarrierJustificationHeightPin`.** It typecheks and cannot
be inhabited, for the reason above; the three residual goals of an attempt are
`⊢ ProposerCarrierAt S rho r`, `⊢ 0 < S.hc.opening_slot r` and
`⊢ Protocol.proposal_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon`. Its
replacement is `w4CarrierChainFinalityPin_of_voteHeads_and_actionRoot_of_fields`
(`W4FKChainClosedRun.lean`), or `w4CarrierChainFinalityPin_of_fields`
(`W4FKChainSpineRun.lean`) if the head cone and the reader finality advance
should stay abstract. `w4CarrierChainFinalityPin_of_split`
(`W4CarrierChainFinalitySplitRun.lean`) consumes the false pin and is therefore
not usable either. This file therefore reproduces branches
w4-d2's composition with the justification step taken from
`namedCarrierJustificationHeight_of_firstHalf`
(`W4FKChainJustificationRun.lean`), which has those two premises. The result is
that the whole carrier-chain pin rests on ONE outstanding producer, the named
form of `canonicalCarrier_commonFinalized_of_justifiedPrefix`, pinned by branches
w4-d2 as `W4CommonFinalizedOfJustifiedPrefixPin`.

Everything else here is w4-d2's argument: the two carriers' proposals are
linked by `proposedBlock_preceq_of_canonicalSuffixFrom` on erasures (fk-proj's
field-level twin, so this file reads only the `canonicalSuffixFrom` field and
serves either execution record), lifted to named ancestry by
`namedPreceq_iff_erase_preceq`, and the justification height travels along it by
`namedJustification_le_of_preceq`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem w4fkNamedTrans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hBC
      subst B
      exact hAB
  | node parent s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hBC
      rcases hBC with rfl | hparent
      · exact hAB
      · simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
        exact Or.inr (ih hparent)

private theorem w4fkBoundaryBeforeOpening (S : Setup V) {q r : Round} (hr : q + 1 < r) :
    healingBoundaryTime S q < Protocol.proposal_time S.E (S.hc.opening_slot r) := by
  have hfirst := Nat.add_le_add_right
    (openingSlot_add_two_le_openingSlot_of_lt S (Nat.lt_succ_self q)) 1
  have hslots : S.hc.opening_slot q + 3 ≤ S.hc.opening_slot r :=
    hfirst.trans ((Nat.le_succ (S.hc.opening_slot (q + 1) + 1)).trans
      (openingSlot_add_two_le_openingSlot_of_lt S hr))
  refine lt_of_lt_of_le (lt_trans ?_
    (support_cutoff_lt_proposal_time_succ S.E (S.hc.opening_slot q + 2)))
    (proposal_time_mono S.E hslots)
  rw [← vote_time_add_delta]
  exact Int.lt_add_of_pos_right _ S.E.Δ_pos

/-- The carrier-chain finality step at one carrier pair, with the first
carrier's justification proved rather than pinned. -/
theorem w4fkCarrierChainFinality_at_carrier_of_suffix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest) {q0 : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hcommonPin : W4CommonFinalizedOfJustifiedPrefixPin S rho q0)
    {source c r : Round} {C Cr Endr : Block V}
    (hqc : q0 + 2 < c) (hcr : c < r)
    (hcarrier : ProposerCarrierAt S rho c)
    (hhalf : CarrierFinalityFirstHalfAt S rho c C)
    (hnjC : ∀ P0 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot c) = some P0 →
      (Protocol.derive_named S.E S.cfg P0).nj = false)
    (hroundR : CanonicalRegimeRoundAt S rho q0 r)
    (hchainR : MovingChainAtCarrierFor S rho q0 r Cr Endr)
    (hnlR : ¬ LostRoundAt S rho r)
    (hpostR : S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r))
    (habove : honestHMaxAt S rho (S.a q0) < carrierOpeningHeight S rho c)
    (hone : 1 < carrierOpeningHeight S rho c)
    (hsource : source < r)
    (hhor : S.a (r + 1) ≤ rho.horizon) :
    AlreadyCommonFinalizedAtOrAbove S rho q0 source (r + 1)
      (carrierOpeningHeight S rho c) := by
  obtain ⟨P0c, hP0c⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot c)
  obtain ⟨P1c, hP1c⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot c + 1)
  obtain ⟨P2c, hP2c⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot c + 2)
  obtain ⟨P1r, hP1r⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r + 1)
  have hcpos : 0 < c := Nat.zero_lt_of_lt hqc
  have hslotC : 0 < S.hc.opening_slot c :=
    Nat.mul_pos hcpos (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hsC : 0 < S.hc.opening_slot c + 2 := Nat.zero_lt_succ _
  have hsR : 0 < S.hc.opening_slot r + 1 := Nat.zero_lt_succ _
  have hslotLink : S.hc.opening_slot c + 2 ≤ S.hc.opening_slot r + 1 :=
    (openingSlot_add_two_le_openingSlot_of_lt S hcr).trans (Nat.le_succ _)
  have htimes := proposal_time_mono S.E hslotLink
  have hhorR : Protocol.proposal_time S.E (S.hc.opening_slot r + 1) ≤ rho.horizon :=
    (proposal_time_mono S.E (Nat.le_succ _)).trans
      ((proposal_time_le_confirmation_time S.E _).trans hroundR.inHorizon)
  have hhorC : Protocol.proposal_time S.E (S.hc.opening_slot c + 2) ≤ rho.horizon :=
    htimes.trans hhorR
  have hafterC : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot c + 2) :=
    (w4fkBoundaryBeforeOpening S ((Nat.le_succ (q0 + 1)).trans_lt hqc)).trans_le
      (proposal_time_mono S.E (Nat.le_add_right _ 2))
  have hemitC := proposedBlock_emitted_of_admissible S adm hsC hcarrier.2.2 hhorC hP2c
  have hemitR := proposedBlock_emitted_of_admissible S adm hsR
    hroundR.carrier.2.1 hhorR hP1r
  have hlink := proposedBlock_preceq_of_canonicalSuffixFrom S adm hsuffix
    hsC hsR hafterC hcarrier.2.2 hroundR.carrier.2.1 hP2c hP1r hemitC hemitR htimes
  have hrunC := proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
    (S.hc.opening_slot c + 2) hsC hcarrier.2.2 hhorC hP2c
  have hrunR := proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
    (S.hc.opening_slot r + 1) hsR hroundR.carrier.2.1 hhorR hP1r
  have hnamedLink : NamedBlock.Preceq P2c P1r :=
    (namedPreceq_iff_erase_preceq S rho
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree hrunC hrunR).mpr hlink
  have hopening : (Protocol.derive_named S.E S.cfg P0c).h =
      carrierOpeningHeight S rho c := by
    have hcanon : canonicalProposal S rho (S.hc.opening_slot c) = P0c :=
      Option.some.inj ((canonicalProposal_spec S rho (S.hc.opening_slot c)).symm.trans hP0c)
    rw [carrierOpeningHeight, hcanon]
  obtain ⟨X, hXP2, hXj⟩ := namedCarrierJustificationHeight_of_firstHalf
    S adm hbot hcarrier hslotC hhorC hP0c hP1c hP2c hhalf (hnjC P0c hP0c)
  have hjust : carrierOpeningHeight S rho c ≤
      (Protocol.derive_named S.E S.cfg P1r).h_j := by
    rw [← hopening, ← hXj]
    exact namedJustification_le_of_preceq S.E S.cfg (w4fkNamedTrans hXP2 hnamedLink)
  exact hcommonPin source c r Cr Endr P1r hroundR hchainR hnlR hpostR hP1r
    hjust habove hone hsource hhor


/-- the corresponding branch's carrier-chain pin, discharged from the single outstanding
producer `W4CommonFinalizedOfJustifiedPrefixPin`. -/
theorem w4CarrierChainFinalityPin_of_commonFinalized_of_suffix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest) {q0 : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hcommonPin : W4CommonFinalizedOfJustifiedPrefixPin S rho q0) :
    W4CarrierChainFinalityPin S rho q0 :=
  fun _ _ _ _ _ _ hqc hcr hcarrier hhalf hnjC hroundR hchainR hnlR
      hpostR habove hone hsource hhor =>
    w4fkCarrierChainFinality_at_carrier_of_suffix S adm hbot hsuffix hcommonPin
      hqc hcr hcarrier hhalf hnjC hroundR hchainR hnlR hpostR habove hone
      hsource hhor


#print axioms w4fkCarrierChainFinality_at_carrier_of_suffix
#print axioms w4CarrierChainFinalityPin_of_commonFinalized_of_suffix

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
