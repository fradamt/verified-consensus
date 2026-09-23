module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalDensity
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The targeted row fold and target participation -/

omit [Fintype V] in
/-- The targeted fold never removes a target-participation bit. -/
private theorem w4fkFold_targetParticipation_subset
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    sigma.target_participation ⊆
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        sigma).target_participation := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      refine Finset.Subset.trans ?_ (ih _)
      intro i hi
      rw [(TargetedTimeoutBinding.process_height_fields sigma row).2]
      split_ifs
      · exact Finset.mem_insert_of_mem hi
      · exact hi

omit [Fintype V] in
/-- An exact proper target row at the state's own entry enters the fold's
target participation. -/
private theorem w4fkFold_mem_targetParticipation_of_target
    {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V)) (sigma : ChainState V),
      a ∈ rows →
      a.height_pair = .vote sigma.h sigma.T_h.root false →
      a.val_index ∈
        (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
          sigma).target_participation := by
  intro rows
  induction rows with
  | nil => intro sigma ha _; simp at ha
  | cons row rows ih =>
      intro sigma ha hpair
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | htail
      · apply w4fkFold_targetParticipation_subset
        rw [(TargetedTimeoutBinding.process_height_fields sigma a).2]
        simp [hpair, NamedHeightPair.matchesEntry, NamedHeightPair.properTarget]
      · apply ih _ htail
        have hfields := TimeoutBindingDefaults.process_context_fields
          (TimeoutBinding.targeted V) sigma row
        rw [hfields.2.1, hfields.2.2.1]
        exact hpair

omit [Fintype V] in
/-- The targeted fold does not move the nonjustifiability latch. -/
private theorem w4fkFold_nj
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
      sigma).nj = sigma.nj := by
  induction rows generalizing sigma with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      exact NjGap.process_attestation_nj sigma _

omit [Fintype V] in
private theorem w4fkRows_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h = sigma.h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem w4fkRows_T_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).T_h = sigma.T_h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.1

omit [Fintype V] in
private theorem w4fkRows_nj (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).nj = sigma.nj := by
  unfold fold_rows
  exact w4fkFold_nj rows { sigma with s := geometry.slot }

omit [Fintype V] in
private theorem w4fkRows_targetParticipation (sigma : ChainState V)
    (geometry : Block V) (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).target_participation =
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        { sigma with s := geometry.slot }).target_participation := rfl

/-! ## 2. Named target coverage and the justification write -/

/-- Named twin of `TargetQuorumCoveredByChild`
(`FinalityQuorumCore.lean:85`): every quorum member is already live in the
parent's target participation, or the child's own named rows carry that
member's exact proper target row at the parent's entry. -/
def NamedTargetQuorumCoveredByChild
    (E : Env V) (sigma : ChainState V) (B : NamedBlock V) : Prop :=
  ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
    ∀ i ∈ Q,
      i ∈ sigma.target_participation ∨
      ∃ a ∈ B.attestations,
        a.val_index = i ∧
        a.height_pair = NamedHeightPair.vote sigma.h sigma.T_h.root false

/-- Honest exact target coverage is a named target quorum under the fault
bound. -/
theorem namedTargetQuorumCoveredByChild_of_honest
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {sigma : ChainState V} {B : NamedBlock V}
    (hcovered : ∀ i ∈ rho.honest,
      i ∈ sigma.target_participation ∨
      ∃ a ∈ B.attestations,
        a.val_index = i ∧
        a.height_pair = NamedHeightPair.vote sigma.h sigma.T_h.root false) :
    NamedTargetQuorumCoveredByChild S.E sigma B :=
  ⟨rho.honest, AlignedRoundLemmas.honestQuorum_of_belowOneThird hfb, hcovered⟩

/-- Mixed live parent/child target coverage is a quorum after the targeted row
fold. -/
theorem namedTargetQuorum_after_fold
    (E : Env V) {sigma : ChainState V} {B : NamedBlock V}
    (hcovered : NamedTargetQuorumCoveredByChild E sigma B) :
    E.electorate.IsQuorum
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase
        B.attestations).target_participation := by
  obtain ⟨Q, hQ, hcov⟩ := hcovered
  apply Protocol.isQuorum_of_subset hQ
  intro i hi
  rw [w4fkRows_targetParticipation]
  rcases hcov i hi with hold | ⟨a, ha, hai, hpair⟩
  · exact w4fkFold_targetParticipation_subset _ _ hold
  · rw [← hai]
    exact w4fkFold_mem_targetParticipation_of_target _ _ ha hpair

/-- With the latch clear, named target coverage makes the folded child
target-ready. -/
theorem namedTargetReady_of_covered
    (E : Env V) {sigma : ChainState V} {B : NamedBlock V}
    (hcovered : NamedTargetQuorumCoveredByChild E sigma B)
    (hnj : sigma.nj = false) :
    Protocol.targetReady E
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase B.attestations) = true := by
  have hQ := namedTargetQuorum_after_fold E hcovered
  have hquorum :
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase
        B.attestations).targetQuorum E = true := by
    simpa only [ChainState.targetQuorum, ChainState.Q_target,
      Electorate.quorumCheck, decide_eq_true_eq] using hQ
  simp only [Protocol.targetReady, Bool.and_eq_true]
  refine ⟨?_, hquorum⟩
  rw [w4fkRows_nj, hnj]
  rfl

/-- Named twin of `justifiedAt_of_targetQuorumCoveredByChild` and
`derived_state_h_of_targetQuorumCoveredByChild`
(`RecurringFinalityRun.lean:620,656`): live target coverage at a justifiable
parent entry performs the actual justification write and advances the height by
one. Target justification has priority over progress consumption, so no
timeout-delay maturity premise appears. -/
theorem namedJustifiedAt_of_targetQuorumCoveredByChild
    (E : Env V) (cfg : HeightConfig) {B : NamedBlock V}
    (hBne : B ≠ NamedBlock.genesis)
    (hcovered : NamedTargetQuorumCoveredByChild E (derive_named E cfg B.parent) B)
    (hjustifiable : (derive_named E cfg B.parent).nj = false) :
    NamedJustifiedAt E cfg B
        (derive_named E cfg B.parent).T_h (derive_named E cfg B.parent).h ∧
      (derive_named E cfg B).h = (derive_named E cfg B.parent).h + 1 := by
  cases B with
  | genesis => exact (hBne rfl).elim
  | node p s root gv gsv ats proposer =>
      have htarget := namedTargetReady_of_covered E hcovered hjustifiable
      have htargetAfter :
          Protocol.targetReady E (Protocol.afterFin E
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
              (NamedBlock.node p s root gv gsv ats proposer).erase
              (NamedBlock.node p s root gv gsv ats proposer).attestations)) = true := by
        unfold Protocol.afterFin
        split
        · simpa only [Protocol.targetReady] using htarget
        · exact htarget
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
              (NamedBlock.node p s root gv gsv ats proposer).erase
              (NamedBlock.node p s root gv gsv ats proposer).attestations) := rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hderive, Protocol.process_height_events_eq, if_pos htargetAfter,
          Protocol.advance_height_J, Protocol.afterFin_T_h, w4fkRows_T_h]
        rfl
      · rw [hderive, Protocol.process_height_events_eq, if_pos htargetAfter,
          Protocol.advance_height_h_j, Protocol.afterFin_h, w4fkRows_h]
        rfl
      · rw [hderive, Protocol.process_height_events_eq, if_pos htargetAfter,
          Protocol.advance_height_h, Protocol.afterFin_h, w4fkRows_h]
        rfl

/-! ## 3. Exact action rows supply the named target quorum -/

/-- Named twin of `targetQuorumCoveredByProposedBlock_of_actionCoverage`
(earlier `RawHeightCoverageRun.lean:1642`): if every covered honest action row is
the exact proper target at the parent's entry, the proposal's coverage is a
live target quorum, parent-carried rows included. -/
theorem namedTargetQuorumCoveredByChild_of_actionCoverage
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {r : Round} {H : Height} {T : BlockId} {B : NamedBlock V}
    (hcoverage : NamedHonestActionProposalCoverageAt S rho r B H T)
    (hPheight : (derive_named S.E S.cfg B.parent).h = H)
    (hPtarget : (derive_named S.E S.cfg B.parent).T_h.root = T)
    (hexact : ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair = .vote H T false) :
    NamedTargetQuorumCoveredByChild S.E (derive_named S.E S.cfg B.parent) B := by
  apply namedTargetQuorumCoveredByChild_of_honest S hfb
  intro v hv
  have hpair := hexact v hv
  rcases (hcoverage v hv).1 with hparent | hchild
  · exact Or.inl (hparent.2.2 hpair)
  · exact Or.inr ⟨actionAttestationAt S rho v r, hchild,
      (actionAttestationAt_shape S rho v r).1,
      by simpa only [hPheight, hPtarget] using hpair⟩


/-- Named twin of `ordinaryHeightTargetProposal_of_actionCoverage`
(earlier `RecurringFinalityRun.lean:725`): at an ordinary height, exact target
rows in the live proposal coverage both perform the named justification write
and cross the height. This is the producer the Open at
`CanonicalRegimeSecondCheckpointRun.lean:222-232` names as missing. -/
theorem namedOrdinaryHeightTargetProposal_of_actionCoverage
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {r : Round} {s : Slot} {H : Height} {T : BlockId} {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B)
    (hcoverage : NamedHonestActionProposalCoverageAt S rho r B H T)
    (hPheight : (derive_named S.E S.cfg B.parent).h = H)
    (hPtarget : (derive_named S.E S.cfg B.parent).T_h.root = T)
    (hPjustifiable : (derive_named S.E S.cfg B.parent).nj = false)
    (hexact : ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair = .vote H T false) :
    NamedJustifiedAt S.E S.cfg B (derive_named S.E S.cfg B.parent).T_h H ∧
      (derive_named S.E S.cfg B).h = H + 1 := by
  have hne : B ≠ NamedBlock.genesis := by
    obtain ⟨p, hp, -⟩ := proposedBlockAt_parent S rho s hB
    intro hgen
    rw [hgen] at hp
    cases hp
  have hcov := namedTargetQuorumCoveredByChild_of_actionCoverage S hfb hcoverage
    hPheight hPtarget hexact
  obtain ⟨hjust, hheight⟩ :=
    namedJustifiedAt_of_targetQuorumCoveredByChild S.E S.cfg hne hcov hPjustifiable
  exact ⟨by simpa only [hPheight] using hjust, by simpa only [hPheight] using hheight⟩

/-! ## 4. The nonjustifiability latch along a named plateau -/

private theorem w4fkNamedNj_eq_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (gv gsv : List (GoldfishVote V)) (ats : List (NamedAttestation V)) (proposer : V)
    (hh : (derive_named E cfg (.node p s root gv gsv ats proposer)).h =
      (derive_named E cfg p).h) :
    (derive_named E cfg (.node p s root gv gsv ats proposer)).nj =
      (derive_named E cfg p).nj := by
  have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
      Protocol.process_height_events E cfg
        (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
          (NamedBlock.node p s root gv gsv ats proposer).erase
          (NamedBlock.node p s root gv gsv ats proposer).attestations) := rfl
  rw [hderive, Protocol.process_height_events_eq]
  split_ifs with htarget hprogress
  · exfalso
    have hh' := hh
    rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
      Protocol.advance_height_h, Protocol.afterFin_h, w4fkRows_h] at hh'
    exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm
  · exfalso
    have hh' := hh
    rw [hderive, Protocol.process_height_events_eq, if_neg htarget, if_pos hprogress,
      Protocol.advance_height_h, Protocol.afterFin_h, w4fkRows_h] at hh'
    exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm
  · rw [Protocol.afterFin_nj, w4fkRows_nj]

/-- Named twin of `derivedNj_eq_of_preceq_same_height`
(`RawHeightCoverageRun.lean:137`): on a height plateau the latch is the
ancestor's. -/
theorem namedNj_eq_of_preceq_same_height
    (E : Env V) (cfg : HeightConfig) {C P : NamedBlock V}
    (hCP : NamedBlock.Preceq C P)
    (hh : (derive_named E cfg P).h = (derive_named E cfg C).h) :
    (derive_named E cfg P).nj = (derive_named E cfg C).nj := by
  induction P with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hCP
      subst C
      rfl
  | node p s root gv gsv ats proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hCP
      rcases hCP with rfl | hCp
      · rfl
      · have hmono := Proofs.NamedEntryHeight.derive_height_mono E cfg hCp
        rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p s root gv gsv
          ats proposer with hc | hc
        · have hpHeight : (derive_named E cfg p).h = (derive_named E cfg C).h := by
            rw [← hc]; exact hh
          exact (w4fkNamedNj_eq_node_of_same_height E cfg p s root gv gsv ats proposer
            (by rw [hh, hpHeight])).trans (ih hCp hpHeight)
        · exfalso
          rw [hc] at hh
          rw [← hh] at hmono
          exact Nat.not_succ_le_self _ hmono

/-! ## 5. The carrier's own justification -/

omit [Fintype V] in
private theorem w4fkParentPreceq (B : NamedBlock V) : NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, NamedBlock.parent,
        Bool.or_eq_true]
      exact Or.inr (Proofs.NamedAncestry.named_self parent)

private theorem w4fkRunBlock_unique
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- The named parent of the slot-`s+1` proposal is the slot-`s` proposal.
earlier reads this off `parent_eq_of_parent?` because its blocks are erased; here
the two blocks are named, `proposedParent` only pins the erasures, and the
identification is run-wide root collision freedom. Both proposers must be
honest inside the horizon, which is exactly what `ProposerCarrierAt` gives at a
carrier round. -/
theorem namedProposalParent_eq_of_honest
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) {s : Slot}
    (hs : 0 < s)
    (hprev : S.E.proposer s ∈ rho.honest)
    (hnext : S.E.proposer (s + 1) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon)
    {P Q : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hQ : proposedBlockAt S rho (s + 1) = some Q)
    (hparent : proposedParent S rho (s + 1) = P.erase) :
    Q.parent = P := by
  have hhorP : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (proposal_time_mono S.E (Nat.le_succ s)).trans hhor
  have hrunP := proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
    s hs hprev hhorP hP
  have hrunQ := proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
    (s + 1) (Nat.zero_lt_succ s) hnext hhor hQ
  obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho (s + 1) hQ
  have hQp : Q.parent = p := by
    cases Q with
    | genesis => cases hp
    | node parent slot root votes support rows proposer =>
        simpa only [NamedBlock.parent] using Option.some.inj hp
  have hrunp : RunBlock S rho p :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hrunQ (hQp ▸ w4fkParentPreceq Q)
  have hpP : p = P := w4fkRunBlock_unique adm hrunp hrunP (by rw [hpe, hparent])
  rw [hQp, hpP]

/-- Named form of `carrierJustificationHeight_of_firstHalf`
(earlier `CanonicalRegimeSecondCheckpointRun.lean:224-268`, parked in the selection
at `:236`): a justifiable carrier with the first-half record justifies its own
opening height in its slot-`+1` or slot-`+2` proposal.

The two carrier premises are the only difference from earlier's statement. earlier's
blocks are erased, so `plusTwoParent` orders `P1` below `P2` outright; here the
heights are `derive_named` of *named* proposals, and the named chain link needs
the honest proposers and the horizon that `ProposerCarrierAt` supplies. -/
theorem namedCarrierJustificationHeight_of_firstHalf
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {r : Round} {C : Block V} {P0 P1 P2 : NamedBlock V}
    (hcarrier : ProposerCarrierAt S rho r)
    (hslot : 0 < S.hc.opening_slot r)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    (hP2 : proposedBlockAt S rho (S.hc.opening_slot r + 2) = some P2)
    (hhalf : CarrierFinalityFirstHalfAt S rho r C)
    (hnj : (derive_named S.E S.cfg P0).nj = false) :
    ∃ X : NamedBlock V, NamedBlock.Preceq X P2 ∧
      (derive_named S.E S.cfg X).h_j = (derive_named S.E S.cfg P0).h := by
  have hhorOne : Protocol.proposal_time S.E (S.hc.opening_slot r + 1) ≤ rho.horizon :=
    (proposal_time_mono S.E (Nat.le_succ _)).trans hhor
  have hP1parent : P1.parent = P0 :=
    namedProposalParent_eq_of_honest S adm hslot hcarrier.1 hcarrier.2.1 hhorOne
      hP0 hP1 (hhalf.plusOneParent P0 P1 hP0 hP1)
  have hP2parent : P2.parent = P1 :=
    namedProposalParent_eq_of_honest S adm (Nat.zero_lt_succ _)
      hcarrier.2.1 hcarrier.2.2 hhor hP1 hP2 (hhalf.plusTwoParent P1 P2 hP1 hP2)
  have hP0P1 : NamedBlock.Preceq P0 P1 := hP1parent ▸ w4fkParentPreceq P1
  have hP1P2 : NamedBlock.Preceq P1 P2 := hP2parent ▸ w4fkParentPreceq P2
  rcases hhalf.checkpointReady P0 P1 hP0 hP1 with hearly | ⟨hP1height, hP1target⟩
  · exact ⟨P1, hP1P2, hearly.2⟩
  · refine ⟨P2, Proofs.NamedAncestry.named_self P2, ?_⟩
    have hP1nj : (derive_named S.E S.cfg P1).nj = false :=
      (namedNj_eq_of_preceq_same_height S.E S.cfg hP0P1 hP1height).trans hnj
    have htrans := namedOrdinaryHeightTargetProposal_of_actionCoverage
      S hbot hP2 (hhalf.actionCoverage P0 P2 hP0 hP2)
      (by rw [hP2parent]; exact hP1height)
      (by rw [hP2parent, hP1target])
      (by rw [hP2parent]; exact hP1nj)
      (hhalf.targetRows P0 hP0)
    exact htrans.1.2

#print axioms namedTargetQuorumCoveredByChild_of_honest
#print axioms namedTargetQuorum_after_fold
#print axioms namedTargetReady_of_covered
#print axioms namedJustifiedAt_of_targetQuorumCoveredByChild
#print axioms namedTargetQuorumCoveredByChild_of_actionCoverage
#print axioms namedOrdinaryHeightTargetProposal_of_actionCoverage
#print axioms namedNj_eq_of_preceq_same_height
#print axioms namedProposalParent_eq_of_honest
#print axioms namedCarrierJustificationHeight_of_firstHalf

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
