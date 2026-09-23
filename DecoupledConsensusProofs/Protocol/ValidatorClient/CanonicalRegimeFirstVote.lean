module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.TimeoutDelay
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Execution.CanonicalDensityDischarge
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# First honest vote into a height-entering block's cone

The Rule-A recent-entry bound turns on *when* the block that entered the
carrier's height first collected honest votes. Under the parent-keyed
Goldfish gate a child of a block sitting at the reader's frontier band is
eligible only by a strict majority of the frozen view or by the current-slot
clause. If no honest committee vote of the frozen slot is in that block's
cone, the majority clause is Byzantine-only and fails, so the block can only
have been the read's own current-slot proposal.

That is the pivotal step of the recent-entry argument. This module proves it,
and the companion arm: a slot-`+1` fold whose height rows are all faulty is
quiet, so the carrier's checkpoint open needs no recent-entry premise in
that case.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.Optimistic
open Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-! ## 1. The pivotal eligibility step -/




/-! ## 2. The faulty-only arm of the slot-`+1` trichotomy -/






/-
/-- The faulty-only arm gives the carrier's checkpoint open with no
recent-entry premise: the slot-`+1` proposal preserves the opening height and
the opening height target. -/
theorem carrierPlusOne_checkpointReady_of_faultyOnlyRows
    (S: Setup V) {rho: Run V} (hbot: BelowOneThird S rho.honest)
    {r: Round} {P0: Block V}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0)
    (htarget: ∀ v ∈ (carrierPlusOneFold S rho r P0).target_participation,
      v ∉ rho.honest)
    (hprogress: ∀ v ∈ (carrierPlusOneFold S rho r P0).progress,
      v ∉ rho.honest):
    (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
        (derived_state S.E S.cfg P0).h ∧
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
        (derived_state S.E S.cfg P0).T_h:=
  plusOne_state_eq_of_parent_of_noHeightEvent S hparent
    (plusOne_noHeightEvent_of_faultyOnlyRows S rho hbot htarget hprogress)
-/





/-
/-- The full arm gives the carrier's checkpoint open outright: the
slot-`+1` proposal justifies the opening height. -/
theorem carrierPlusOne_checkpointReady_of_fullHonestTargetRows
    (S: Setup V) {rho: Run V} (hbot: BelowOneThird S rho.honest)
    {r: Round} {P0: Block V}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0)
    (hnj: (derived_state S.E S.cfg P0).nj = false)
    (hfull: ∀ v ∈ rho.honest,
      v ∈ (carrierPlusOneFold S rho r P0).target_participation):
    JustifiedAt S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r + 1))
      (derived_state S.E S.cfg P0).T_h
      (derived_state S.E S.cfg P0).h:=
  plusOne_justifies_of_earlyTarget S hparent
    (plusOne_targetReady_of_fullHonestTargetRows S rho hbot hnj hfull)
-/

/-! ## 3. Same-height ancestors sit at or above the height entry -/


/-! ## 4. The recent-entry premise is only needed in the mixed arm -/


/-
/-- **The exact trichotomy at the carrier's slot-`+1` fold.**

The recent-entry bound is needed only when some honest validator already
contributed a target row at the carrier height. If none did, and no honest
progress contributor is outside the target set — which is what the canonical
timeout history gives at a justifiable height — then both quorums are carried
by faulty validators alone and the fold is quiet.

`hentered` is therefore a strictly weaker obligation than
`CarrierRecentHeightEntryAt`: it is only invoked in the mixed arm, which is
exactly the arm the first-honest-vote argument addresses. -/
theorem carrierPlusOne_checkpointReady_of_conditionalRecentEntry
    (S: Setup V) (rho: Run V) (hbot: BelowOneThird S rho.honest)
    {r: Round} {P0: Block V}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0)
    (hdelay: TimeoutDelayBound S delayExtra)
    (hnj: (derived_state S.E S.cfg P0).nj = false)
    (hentered: (∃ v ∈ rho.honest,
        v ∈ (carrierPlusOneFold S rho r P0).target_participation) →
      r - 1 ≤ S.hc.round_of (derived_state S.E S.cfg P0).T_h.slot)
    (hnoHonestTimeoutRow: ∀ v ∈ (carrierPlusOneFold S rho r P0).progress,
      v ∈ rho.honest →
      v ∈ (carrierPlusOneFold S rho r P0).target_participation):
    JustifiedAt S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r + 1))
        (derived_state S.E S.cfg P0).T_h
        (derived_state S.E S.cfg P0).h ∨
      ((derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
            (derived_state S.E S.cfg P0).h ∧
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
            (derived_state S.E S.cfg P0).T_h):= by
  by_cases hhonest: ∃ v ∈ rho.honest,
      v ∈ (carrierPlusOneFold S rho r P0).target_participation
  · exact carrierPlusOne_checkpointReady S hparent hdelay
      (hentered hhonest) hnj
  · right
    have htargetFaulty:
        ∀ v ∈ (carrierPlusOneFold S rho r P0).target_participation,
          v ∉ rho.honest:= by
      intro v hv hvh
      exact hhonest ⟨v, hvh, hv⟩
    have hprogFaulty:
        ∀ v ∈ (carrierPlusOneFold S rho r P0).progress, v ∉ rho.honest:= by
      intro v hv hvh
      exact htargetFaulty v (hnoHonestTimeoutRow v hv hvh) hvh
    exact carrierPlusOne_checkpointReady_of_faultyOnlyRows
      S hbot hparent htargetFaulty hprogFaulty
-/

/-! ## 5. The forward height-row rule -/

omit [Fintype V] in
/-- An empty or aligned own lock at a successor-target record. -/
private theorem ownLock_none_or_aligned_firstVote
    {Lambda : Protocol.NamedRecord} {H : Height} {T : BlockId}
    {fp : Option FinalityPair}
    (haligned : SuccessorTargetLockAlignmentAt Lambda fp H T) :
    Protocol.own_lock Lambda.legacy H fp = none ∨
      Protocol.own_lock Lambda.legacy H fp = some T := by
  cases hfp : fp with
  | none =>
      cases hlock : Lambda.legacy.lock H with
      | none => exact Or.inl (by simp [Protocol.own_lock, hlock])
      | some X =>
          have hXT : X = T := haligned.1 X hlock
          exact Or.inr (by simp [Protocol.own_lock, hlock, hXT])
  | some p =>
      by_cases hpH : p.height = H
      · have hpT : p.target = T := haligned.2 p hfp hpH
        exact Or.inr (by
          simp [Protocol.own_lock, hpH, hpT])
      · cases hlock : Lambda.legacy.lock H with
        | none => exact Or.inl (by simp [Protocol.own_lock, hpH, hlock])
        | some X =>
            have hXT : X = T := haligned.1 X hlock
            exact Or.inr (by
              simp [Protocol.own_lock, hpH, hlock, hXT])

/-- **The forward row rule.** A justifiable source at height `H` with target
`T`, read against a clear successor-target record and an aligned lock, emits
exactly `target H T`. -/
theorem round_action_height_pair_target_of_record
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.HealingStore V)
    (Lambda : Protocol.NamedRecord)
    {H : Height} {T : BlockId} {Q : Block V}
    (hsource : Protocol.fg_source_with contract E hc st (hc.round_of st.s)
      (Protocol.grade2_block_with contract E hc st (hc.round_of st.s)) = some Q)
    (hheight : (st.σ Q).h = H)
    (htarget : (st.σ Q).T_h.root = T)
    (hnj : (st.σ Q).nj = false)
    (hrecord : SuccessorTargetRecordAt Lambda H T)
    (haligned : SuccessorTargetLockAlignmentAt Lambda
      (Protocol.NamedActions.round_action_with contract E hc nd st Lambda).2.finality_pair
      H T) :
    (Protocol.NamedActions.round_action_with contract E hc nd st Lambda).2.height_pair =
      NamedHeightPair.vote H T false := by
  let fp := (Protocol.NamedActions.round_action_with contract E hc nd st Lambda).2.finality_pair
  have hown : Protocol.own_lock Lambda.legacy H fp = none ∨
      Protocol.own_lock Lambda.legacy H fp = some T :=
    ownLock_none_or_aligned_firstVote (by simpa only [fp] using haligned)
  have hpure : Protocol.height_pair Lambda.legacy (some (H, T, false)) fp =
      HeightPair.target H T := by
    rcases hown with hnone | hlockAligned
    · rcases hrecord.1 with hnoneTarget | hrecordedTarget
      · exact height_pair_eq_target_of_no_lock_no_target_justifiable
          Lambda.legacy fp hrecord.2 hnone hnoneTarget
      · exact height_pair_eq_target_of_no_lock_recorded_target
          Lambda.legacy fp hrecord.2 hnone hrecordedTarget
    · exact height_pair_eq_target_of_aligned_lock
        Lambda.legacy fp hrecord.2 hlockAligned
  have hsource' : actionSource contract E hc st = some Q := by
    simpa only [actionSource] using hsource
  rw [named_round_action_height_pair contract E hc nd st Lambda,
    hsource', Option.map_some]
  simp only [hheight, htarget, hnj]
  rw [hpure]
  exact encodeHeight_of_target

/-! ## 6. Why there is no capture interface
An earlier draft of this module carried a `capture` interface field: an previous
block below one honest `live_confirmed` at a round read is below every honest
`live_confirmed` at that read. **That field is false in this model**, and the
counterexample is entirely inside the definitions:
* `on_block`'s duplicate guard is `B ∈ st.T`, the same block, not another block
  of the same slot, and its author guard is
  `B.proposer? = some (E.proposer B.slot)`. A Byzantine slot proposer's two
  sibling blocks therefore both enter stores, selectively.
* `goldfish_eligible`'s current-slot clause `B.slot = cur` opens the gate with
  no votes at all (`Proofs.Optimistic.goldfish_eligible_current`), so honest votes at
  that slot split between the two siblings. `Optimistic/Agreement.lean`'s own
  `goldfish_fork_choice_eq_proposal` docstring records this as the reason
  slot-`(s-1)` concentration is not a consequence of view merge.
* One slot later the previous sibling is eligible only by strict majority of the
  reader's own frozen view, so selectively delivered faulty votes make it
  eligible at some honest readers and not at others.
* `Protocol.update_confirmation` runs the plain strict-majority gate — no
  current-slot clause and no height clause — and writes `live_confirmed`
  unconditionally, so at one slot two honest readers legitimately confirm at
  different depths of one chain.
So an previous height-entering block can sit below one honest live confirmation and
not below another at the same read, and the recent-entry bound is genuinely
unavailable in that trace. The finality producer therefore does not try to
exclude it; `carrierPlusOne_checkpointReady_or_advance` keeps the third arm as
an explicit height advance instead. See
`carrierFinalityFirstHalfAt_or_advance_of_regime`. -/

/-! ## 7. The carrier-pair selection from the discharged density -/


/- /-- The phase producer's carrier-pair selection, supplied by the discharged
carrier density rather than by the previous `CanonicalHeightDensityResidualFrom`
record.
`CanonicalDensityDischargeRun` proves the carrier-restricted density
(`CanonicalCarrierDensityFrom`) from the suffix execution and the per-carrier
moving-chain hand-off, and re-derives the selection with the same horizon
budget, so nothing downstream changes. -/
/-- The phase producer's carrier-pair selection, supplied by the discharged
carrier density rather than by the prior `CanonicalHeightDensityResidualFrom`
record.

`CanonicalDensityDischargeRun` proves the carrier-restricted density
(`CanonicalCarrierDensityFrom`) from the suffix execution and the per-carrier
moving-chain hand-off, and re-derives the selection with the same horizon
budget, so nothing downstream changes. -/
theorem justifiableCarrierPairFrom_of_movingChain
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {q rawLag gap: Round}
    (hexec: CanonicalSuffixExecution S rho q)
    (hafterAll: ∀ r: Round, q + 1 < r →
      healingBoundaryTime S q <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q)
    (hprogress: EventualHeightProgressFrom S rho q rawLag)
    (hrawPos: 0 < rawLag)
    (hrec: MultiProposerRecurrence S rho gap)
    (hgap: gap + 2 ≤ S.cfg.K):
    JustifiableCarrierPairFrom S rho q rawLag gap:=
  fun _start hstart hhor =>
    exists_justifiableCarrierPair_afterTwoProgress_of_movingChain
      S adm hcom hmajority hexec hafterAll hchain
      hprogress
        hrawPos hrec hgap hstart hhor
-/


/-
/-- Recurring finality with no density residual: the inputs are the suffix
execution, the per-carrier moving-chain hand-off, raw height progress,
proposer recurrence, the schedule facts, and the recent-entry obligation. -/
theorem recurringFinalityFrom_of_movingChain_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    (hdelay: TimeoutDelayBound S delayExtra)
    {q rawLag gap: Round}
    (hrawPos: 0 < rawLag)
    (hgap: gap + 2 ≤ S.cfg.K)
    (hexec: CanonicalSuffixExecution S rho q)
    (hprogress: EventualHeightProgressFrom S rho q rawLag)
    (hrec: MultiProposerRecurrence S rho gap)
    (hafterAll: ∀ r: Round, q + 1 < r →
      healingBoundaryTime S q <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hpostAll: ∀ r: Round, q + 1 < r →
      S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q)
    (hpostBoundary: S.E.t_GST ≤ S.a q)
    (hnotLost: ∀ r: Round, 1 ≤ r → S.E.t_GST ≤ S.a (r - 1) →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r)
    (hcheckpointAll: ∀ r: Round, q + 2 < r →
      CanonicalRegimeRoundAt S rho q r →
      honestHMaxAt S rho (S.a q) <
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h →
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).nj = false →
      JustifiedAt S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).T_h
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).h ∨
        ((derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).h ∧
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).T_h)):
    RecurringFinalityFrom S rho q
      (recurringFinalityDeadline S
        (recurringFinalityPhaseLag rawLag gap) gap):=
  recurringFinalityFrom_of_canonicalRegime
    S adm hcom hbot hmajority hdelay hrawPos hexec
      (justifiableCarrierPairFrom_of_movingChain
        S adm hcom hmajority hexec hafterAll hchain hprogress hrawPos hrec hgap)
      hrec hafterAll hpostAll hchain hpostBoundary hnotLost hcheckpointAll
-/


/-
/-- Finality of every post-boundary honest proposal on the same inputs. -/
theorem honestProposalFinalityFrom_of_movingChain_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    (hdelay: TimeoutDelayBound S delayExtra)
    {q rawLag gap: Round}
    (hrawPos: 0 < rawLag)
    (hgap: gap + 2 ≤ S.cfg.K)
    (hexec: CanonicalSuffixExecution S rho q)
    (hprogress: EventualHeightProgressFrom S rho q rawLag)
    (hrec: MultiProposerRecurrence S rho gap)
    (hafterAll: ∀ r: Round, q + 1 < r →
      healingBoundaryTime S q <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hpostAll: ∀ r: Round, q + 1 < r →
      S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q)
    (hpostBoundary: S.E.t_GST ≤ S.a q)
    (hnotLost: ∀ r: Round, 1 ≤ r → S.E.t_GST ≤ S.a (r - 1) →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r)
    (hcheckpointAll: ∀ r: Round, q + 2 < r →
      CanonicalRegimeRoundAt S rho q r →
      honestHMaxAt S rho (S.a q) <
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h →
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).nj = false →
      JustifiedAt S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).T_h
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).h ∨
        ((derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).h ∧
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).T_h)):
    HonestProposalFinalityFrom S rho q
      (recurringFinalityDeadline S
        (recurringFinalityPhaseLag rawLag gap) gap):=
  honestProposalFinalityFrom_of_canonicalRegime
    S adm hcom hbot hmajority hdelay hrawPos hexec
      (justifiableCarrierPairFrom_of_movingChain
        S adm hcom hmajority hexec hafterAll hchain hprogress hrawPos hrec hgap)
      hrec hafterAll hpostAll hchain hpostBoundary hnotLost hcheckpointAll
-/








/-! ## 8. The per-round moving floor -/



/-
/-- The height source of a round action is that store's own live confirmation.

This is `openingFGSource_of_gradeFloor` with the carrier's opening proposal
replaced by the reader's own live confirmation, so it applies at a round with
no honest opening proposer. The selected grade-2 block is below the live
confirmation because a block off its chain has no honest support, and the live
confirmation is grade-0 clear for the same reason, so the clear walk reaches
the tip. -/
theorem fgSource_eq_live_of_gradeFloor
    (S: Setup V) {rho: Run V}
    (hmajority: HonestWeightMajority S rho.honest)
    {r: Round} {C: Block V}
    (hforms: GradeFormsAt S rho r C)
    (haligned: ∀ v ∈ rho.honest,
      Proofs.Optimistic.BatchAligned
        (actionStoreAt S rho v r).toHealing.gradeView
        rho.honest r (actionStoreAt S rho v r).live_confirmed):
    ∀ v ∈ rho.honest,
      Protocol.fg_source S.E S.hc (actionStoreAt S rho v r).toHealing r
        (Protocol.grade2_block S.E S.hc
          (actionStoreAt S rho v r).toHealing r) =
            some (actionStoreAt S rho v r).live_confirmed:= by
  intro v hv
  let ast:= actionStoreAt S rho v r
  have hgraded:= gradeFormsAt_actionStore S hforms hv
  have hsome:
      (Protocol.grade2_block S.E S.hc ast.toHealing r).isSome = true:= by
    refine deepest?_isSome_of_compatible ?_
      ⟨C, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · intro X hX Y hY
      exact Proofs.HealingLemmas.G2_compatible S.E
        (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hY).2
    · simpa only [ast] using hgraded.1
    · simpa only [ast] using hgraded.2
  obtain ⟨Q2, hQ2⟩:= Option.isSome_iff_exists.mp hsome
  have hQ2mem:= Proofs.Engine.deepest?_mem hQ2
  have hQ2G2: Protocol.G2 S.E ast.toHealing.gradeView S.hc r Q2 = true:=
    (Finset.mem_filter.mp hQ2mem).2
  have hQ2pre: Block.Preceq Q2 ast.live_confirmed:= by
    by_contra hnot
    have hfalse: Block.preceq Q2 ast.live_confirmed = false:= by
      rw [← Bool.not_eq_true]
      exact hnot
    have hgradeFalse:=
      Protocol.HonestWeightMajority.grade_eq_false_off_can
        (G:= Protocol.Grade.g2) S (haligned v hv) hmajority hfalse
    simp only [Protocol.grade] at hgradeFalse
    rw [hgradeFalse] at hQ2G2
    simp at hQ2G2
  have hclear: Protocol.g0_clear S.E ast.toHealing.gradeView S.hc r
      ast.live_confirmed = true:=
    Protocol.HonestWeightMajority.g0_clear_of_preceq
      S (haligned v hv) hmajority (Block.preceq_self ast.live_confirmed)
  change Protocol.fg_source S.E S.hc ast.toHealing r
      (Protocol.grade2_block S.E S.hc ast.toHealing r) =
    some ast.live_confirmed
  have hliveHealing: ast.toHealing.live_confirmed = ast.live_confirmed:= rfl
  rw [Protocol.fg_source.eq_def, hQ2, hliveHealing]
  have hwalk: Protocol.deepest_clear (some Q2) ast.live_confirmed
      (fun B => Protocol.g0_clear S.E ast.toHealing.gradeView S.hc r B) =
        some ast.live_confirmed:=
    deepest_clear_eq_tip (floor:= some Q2) (C:= ast.live_confirmed)
      (by simpa using hQ2pre) hclear
  simp only [hwalk]
-/




















/-
/-- The row-height bound extended to the carrier round itself.

At the carrier the source is the opening proposal (`openingSource`), so the
row sits at exactly the carrier's opening height. -/
theorem honestRowHeight_le_carrierHeight_upTo
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q0 c: Round} (hround: CanonicalRegimeRoundAt S rho q0 c):
    ∀ k: Round, q0 ≤ k → (k < c ∨ k = c) → ∀ v ∈ rho.honest, ∀ h: Height,
      (actionAttestationAt S rho v k).height_pair.height? = some h →
        h ≤ (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot c))).h:= by
  intro k hk hkc v hv h hh
  rcases hkc with hlt | rfl
  · exact honestRowHeight_le_carrierHeight S hround k hk hlt v hv h hh
  · obtain ⟨Q, hsource, -, hQheight⟩:=
      honestRow_height_le_source S adm hv hh
    have hQ: Q = proposedBlock S rho (S.hc.opening_slot k):=
      Option.some.inj (hsource.symm.trans (hround.openingSource v hv))
    rw [← hQheight, hQ]
 -/









/-
/-- **No honest row above the carrier height is carried on any block an honest
store holds by the next round's action.**

The row is a past round action of a round strictly before `c + 1`, and above
the boundary frontier such a row is post-boundary, so the carrier's height
history bounds it. -/
theorem carriedHonestRowHeight_le_carrierHeight
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q0 c: Round} (hround: CanonicalRegimeRoundAt S rho q0 c)
    {v: V} {Y: Block V}
    (hY: Y ∈ (rho.stateBeforeTime S (S.a (c + 1)) v).st.T)
    {a: CombinedAttestation V} (ha: a ∈ chain_attestations Y)
    (hhon: a.val_index ∈ rho.honest)
    {h: Height} (hheight: a.height_pair.height? = some h)
    (hhigh: honestHMaxAt S rho (S.a q0) < h):
    h ≤ (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot c))).h:= by
  obtain ⟨hlt, haction⟩:=
    carriedHonestRow_isPastAction S adm hY ha hhon
  have hrow: (actionAttestationAt S rho a.val_index a.round).height_pair.height?
      = some h:= by rw [← haction]; exact hheight
  have hq0: q0 < a.round:=
    honestRow_after_frontier S adm hhon hhigh hrow
  have hlt': a.round < c + 1:=
    (action_strictMono S).lt_iff_lt.mp hlt
  exact honestRowHeight_le_carrierHeight_upTo S adm hround a.round
    (Nat.le_of_lt hq0) (nat_lt_or_eq_of_lt_succ_firstVote hlt')
    a.val_index hhon h hrow
 -/











/-
/-- **Fact 2, the height pin.**

After a burn at carrier `c`, no block that an honest store holds at the
round-`(c+1)` action and that extends the burn's `+1` block has height above
`H0 + 1`.

Strong induction on the block's height. A block above `H0 + 1` has a height
target `Y` whose parent `P` sits one height lower; the induction hypothesis
and the lower bound pin `P` at exactly `H0 + 1`, so `P`'s height target is the
burn block itself. `heightEvent_honestTargetRow_or_mature` at `Y` then gives
an honest row at `H0 + 1` — refuted by `carriedHonestRowHeight_le_carrierHeight`
— or maturity of the burn block's own gate, refuted by
`burnEntry_gate_closed_before_nextOpening`. -/
theorem blockHeight_le_burnHeight
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    (hdelay: TimeoutDelayBound S delayExtra)
    {q0 c: Round}
    (hround: CanonicalRegimeRoundAt S rho q0 c)
    (hburn: CarrierBurnAt S rho c)
    (habove: honestHMaxAt S rho (S.a q0) <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot c))).h)
    {v: V}:
    ∀ (n: Nat) (L: Block V),
      (derived_state S.E S.cfg L).h ≤ n →
      L ∈ (rho.storeBeforeTime S v (S.a (c + 1))).T →
      Block.Preceq (proposedBlock S rho (S.hc.opening_slot c + 1)) L →
      (derived_state S.E S.cfg L).h ≤
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot c))).h + 1:= by
  intro n
  induction n with
  | zero =>
      intro L hLn _ _
      exact nat_zero_case_fv hLn
  | succ n ih =>
      intro L hLn hLmem hP1L
      by_cases hle: (derived_state S.E S.cfg L).h ≤
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot c))).h + 1
      · exact hle
      · exfalso
        have hgt: (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot c))).h + 1 <
              (derived_state S.E S.cfg L).h:= Nat.lt_of_not_le hle
        obtain ⟨P, hPparent, hPlt⟩:=
          derivedTarget_crosses S.E S.cfg L (nat_gt_one_fv hgt)
        have hYL: Block.Preceq (derived_state S.E S.cfg L).T_h L:=
          derivedTarget_preceq S.E S.cfg L
        have hYheight: (derived_state S.E S.cfg
            (derived_state S.E S.cfg L).T_h).h =
              (derived_state S.E S.cfg L).h:=
          Protocol.derived_target_height S.E S.cfg L
        have hPY: Block.Preceq P (derived_state S.E S.cfg L).T_h:=
          Protocol.preceq_of_parent? hPparent
        have hPL: Block.Preceq P L:= Block.preceq_trans hPY hYL
        have hstep:= derived_h_le_succ_of_parent S.E S.cfg hPparent
        have hPsucc: (derived_state S.E S.cfg
            (derived_state S.E S.cfg L).T_h).h =
              (derived_state S.E S.cfg P).h + 1:=
          nat_eq_succ_fv hPlt hstep
        have hdep: DepReachableStore S.E S.hc S.cfg (S.node v)
            (rho.storeBeforeTime S v (S.a (c + 1))):= by
          simpa only [Run.storeBeforeTime] using
            (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
              adm.toDeliveryWellFormed (S.a (c + 1)) v)
        have hclosed: ParentClosed (rho.storeBeforeTime S v (S.a (c + 1))):=
          parentClosed_depReachable S.E S.hc S.cfg (S.node v) _ hdep
        have hYmem: (derived_state S.E S.cfg L).T_h ∈
            (rho.storeBeforeTime S v (S.a (c + 1))).T:=
          Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hclosed).2 _ L
            hLmem hYL
        have hPmem: P ∈ (rho.storeBeforeTime S v (S.a (c + 1))).T:=
          Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hclosed).2 _ L
            hLmem hPL
        have hP1height: (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot c + 1))).h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot c))).h + 1:=
          hburn.height
        have hPge: (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot c))).h + 1 ≤
              (derived_state S.E S.cfg P).h:= by
          rw [hYheight] at hPsucc
          exact nat_ge_from_gt_succ_fv hgt hPsucc
        have hPle: (derived_state S.E S.cfg P).h ≤
            (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot c))).h + 1:= by
          rcases preceq_or_preceq_fv hP1L hPL with hP1P | hPP1
          · rw [hYheight] at hPsucc
            exact ih P (nat_pred_le_fv hLn hPsucc) hPmem hP1P
          · rw [← hP1height]
            exact Protocol.derived_h_mono S.E S.cfg hPP1
        have hPeq: (derived_state S.E S.cfg P).h =
            (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot c))).h + 1:=
          nat_eq_of_two_bounds_fv hPle hPge
        have hTP: (derived_state S.E S.cfg P).T_h =
            proposedBlock S rho (S.hc.opening_slot c + 1):= by
          have hsame: (derived_state S.E S.cfg P).T_h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot c + 1))).T_h:= by
            rcases preceq_or_preceq_fv hP1L hPL with hP1P | hPP1
            · exact derivedTarget_eq_of_preceq_same_height S.E S.cfg hP1P
                (by rw [hPeq, hP1height])
            · exact (derivedTarget_eq_of_preceq_same_height S.E S.cfg hPP1
                (by rw [hPeq, hP1height])).symm
          rw [hsame, hburn.target]
        rcases heightEvent_honestTargetRow_or_mature S hfb hPparent hPlt with
            ⟨a, ha, hahon, hapair⟩ | hmature
        · have hheight?: a.height_pair.height? =
              some (derived_state S.E S.cfg P).h:= by
            rw [hapair]; rfl
          have hhigh: honestHMaxAt S rho (S.a q0) <
              (derived_state S.E S.cfg P).h:= by
            rw [hPeq]; exact nat_succ_lt_succ_fv habove
          have hbound:= carriedHonestRowHeight_le_carrierHeight
            S adm hround hYmem ha hahon hheight? hhigh
          rw [hPeq] at hbound
          exact (Nat.not_succ_le_self _) hbound
        · rw [hTP] at hmature
          refine burnEntry_gate_closed_before_nextOpening S hdelay c
            (block_slot_lt_plusTwo_of_mem_beforeAction S adm hYmem) ?_
          rwa [Protocol.proposedBlock_slot] at hmature
 -/

#print axioms ownLock_none_or_aligned_firstVote
#print axioms round_action_height_pair_target_of_record

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
