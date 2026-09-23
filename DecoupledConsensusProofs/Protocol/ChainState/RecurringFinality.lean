module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.LocalFinality
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Walk
public import DecoupledConsensusProofs.Execution.PostHealingProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotoneCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityUpgrade
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Grades.EventualHeightProgress
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Execution.RecurringArithmeticCore
public import DecoupledConsensusProofs.Protocol.ChainState.WholeRunFinalitySafety
public import DecoupledConsensusInternal.Definitions.NamedLifecycle
public import DecoupledConsensusInternal.Definitions.NamedDerived
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Recurring finality from the canonical execution suffix

This module turns exact target, progress, and finality rows in the canonical
post-healing execution into common finalized checkpoints. The public theorem
below consumes only the declarative canonical, lifecycle, recurrence, and raw
progress surfaces.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol (HeightConfig derive_named)

open Internal.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The exact number of recurrence-selected honest openings used by one
recurring-finality search. -/
def recurringFinalityPhaseCount (S : Setup V) : Round :=
  S.cfg.D + S.cfg.K + 5

/-- Sequential recurrence selection starts strictly after the current round.
Each of the selected openings therefore costs at most `gap + 1` rounds. -/
def recurringFinalitySelectionLag
    (S : Setup V) (recurrenceGap : Round) : Round :=
  recurringFinalityPhaseCount S * (recurrenceGap + 1)

/-- An honest proposal already supplies a common finalized checkpoint at or
above `H`. The time bounds keep the exact proposal provenance that the
honest-proposal finality adapter needs. -/
abbrev AlreadyCommonFinalizedAtOrAbove
    (S : Setup V) (rho : Run V)
    (q source endRound : Round) (H : Height) : Prop :=
  Internal.CommonFinalizedWitnessAt S rho q source endRound H

/-- Exact selected-round input for the carrier-`+2` finality kernel.

The first carrier justifies the opening block's height in its `+1` or `+2`
proposal.
The second carrier either starts after an earlier common finality success or
finalizes the current checkpoint on its `+1` action head in its `+2` proposal.
All inputs are chain-local. -/
def NamedHonestActionProposalCoverageAt
    (S : Setup V) (rho : Run V) (r : Round)
    (B : NamedBlock V) (H : Height) (T : BlockId) : Prop :=
  let sigma := derive_named S.E S.cfg B.parent
  ∀ v ∈ rho.honest,
    (((actionAttestationAt S rho v r ∈
          Protocol.named_chain_attestations B.parent ∧
        v ∈ sigma.progress ∧
        ((actionAttestationAt S rho v r).height_pair = .vote H T false →
          v ∈ sigma.target_participation)) ∨
      actionAttestationAt S rho v r ∈ B.attestations) ∧
      ((actionAttestationAt S rho v r).height_pair = .vote H T false ∨
        ∃ e : BlockId, (actionAttestationAt S rho v r).height_pair = .vote H e true))


/-- Open: canonical suffix duties do not yet prove that every honest
round action adopts the carrier's `+1` proposal. This is the exact missing
slot-to-slot cone fact; slot terminality turns it into equality below. -/
structure CarrierActionHeadPlusOneConeAt
    (S : Setup V) (rho : Run V) (r : Round) (P : NamedBlock V) : Prop where
  proposal : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P
  plusOneCone : ∀ v ∈ rho.honest,
    Block.Preceq
      P.erase (actionHeadAt S rho v r)


/-- One raw-height step followed by the complete sequential recurrence
selection window. -/
def recurringFinalityOneHeightLag
    (S : Setup V) (rawLag recurrenceGap : Round) : Round :=
  rawLag + recurringFinalitySelectionLag S recurrenceGap

/-- A finality deadline relative to the common finalized frontier at the
starting round. `D + K` pays for the next debt-qualified `K` multiple, and the
two remaining phases pay for the separated openings that justify and finalize
the selected source height. -/
def recurringFinalityDeadline
    (S : Setup V) (rawLag recurrenceGap : Round) : Round :=
  (S.cfg.D + S.cfg.K + 2) *
    recurringFinalityOneHeightLag S rawLag recurrenceGap


/-- Proof-carrying refinement of recurring finality. It retains the exact
honest proposal whose candidate performs each finality advance. The public
`RecurringFinalityFrom` projection below erases only this provenance. -/
def RecurringFinalityCarrierFrom
    (S : Setup V) (rho : Run V) (q0 : Round) (t0 : Time)
    (deadline : Round) : Prop :=
  ∀ (r : Round) (B : Block V) (h : Height), q0 ≤ r →
    (∀ v ∈ rho.honest,
      Block.Preceq B (rho.storeAt S v (S.a r)).F ∧
        h ≤ (rho.storeAt S v (S.a r)).core.finalized_height) →
    S.a (r + deadline) ≤ rho.horizon →
      ∃ (s : Slot) (Pblk P : NamedBlock V) (h' : Height),
        0 < s ∧
          t0 < Protocol.proposal_time S.E s ∧
          S.E.proposer s ∈ rho.honest ∧
          Protocol.confirmation_time S.E s ≤ rho.horizon ∧
          proposedBlockAt S rho s = some Pblk ∧
          NamedFinalizedAt S.E S.cfg Pblk P.erase h' ∧
          NamedRun.blockInRun S rho P ∧
          Block.Preceq B P.erase ∧
          h < h' ∧
          (derive_named S.E S.cfg P).h = h' ∧
          S.a r ≤ Protocol.proposal_time S.E s ∧
          S.a r ≤ Protocol.confirmation_time S.E s ∧
          Protocol.confirmation_time S.E s ≤
            S.a (r + deadline) ∧
          ∀ v ∈ rho.honest,
            Block.Preceq P.erase
                (rho.storeAt S v
                  (Protocol.confirmation_time S.E s)).F ∧
              h' ≤ (rho.storeAt S v
                (Protocol.confirmation_time S.E s)).core.finalized_height

/-- Forgetting the exact finality carrier yields the declarative recurring
finality contract. -/
theorem RecurringFinalityCarrierFrom.toRecurringFinalityFrom
    {S : Setup V} {rho : Run V} {q0 : Round} {t0 : Time}
    {deadline : Round}
    (h : RecurringFinalityCarrierFrom S rho q0 t0 deadline) :
    RecurringFinalityFrom S rho q0 deadline := by
  intro r B height hr hcommon hhor
  obtain ⟨s, Pblk, P, height', -, -, -, -, hPblk, hfin, hPinRun,
    hBP, hadvance, hPheight, -, htLo, htHi, hnew⟩ :=
    h r B height hr hcommon hhor
  exact ⟨P, height', Protocol.confirmation_time S.E s, hPinRun, hBP, hadvance,
    hPheight, htLo, htHi, hnew⟩

/-- The real raw-progress lag and the complete recurrence-selection window both
fit in one declared height phase. -/
theorem recurringFinalityOneHeightLag_bounds
    (S : Setup V) (rawLag recurrenceGap : Round) :
    rawLag ≤ recurringFinalityOneHeightLag S rawLag recurrenceGap ∧
      recurringFinalitySelectionLag S recurrenceGap ≤
        recurringFinalityOneHeightLag S rawLag recurrenceGap := by
  constructor
  · simpa only [recurringFinalityOneHeightLag] using
      Nat.le_add_right rawLag
        (recurringFinalitySelectionLag S recurrenceGap)
  · simpa only [recurringFinalityOneHeightLag] using
      Nat.le_add_left
        (recurringFinalitySelectionLag S recurrenceGap) rawLag

/-- One proof-carrying raw phase fits every declared recurring-finality
deadline. -/
theorem recurringFinalityOneHeightLag_le_deadline
    (S : Setup V) (rawLag recurrenceGap : Round) :
    recurringFinalityOneHeightLag S rawLag recurrenceGap ≤
      recurringFinalityDeadline S rawLag recurrenceGap := by
  unfold recurringFinalityDeadline
  have hcoefficient :
      1 ≤ S.cfg.D + S.cfg.K + 2 := by
    exact (by decide : 1 ≤ 2).trans
      (Nat.le_add_left 2 (S.cfg.D + S.cfg.K))
  simpa only [Nat.one_mul] using
    Nat.mul_le_mul_right
      (recurringFinalityOneHeightLag S rawLag recurrenceGap) hcoefficient

/-- The raw crossing budget from the current frontier, followed by one complete
sequential recurrence selection window, fits the constant deadline. -/
theorem rawRecoveryAndRecurrence_le_recurringFinalityDeadline
    (S : Setup V) (rawLag recurrenceGap : Round) :
    (S.cfg.D + S.cfg.K + 2) * rawLag +
        recurringFinalitySelectionLag S recurrenceGap ≤
      recurringFinalityDeadline S rawLag recurrenceGap := by
  let count := S.cfg.D + S.cfg.K + 2
  let window := recurringFinalitySelectionLag S recurrenceGap
  have hcount : 1 ≤ count := by
    exact (by decide : 1 ≤ 2).trans
      (Nat.le_add_left 2 (S.cfg.D + S.cfg.K))
  have hwindow : window ≤ count * window := by
    have := Nat.mul_le_mul_right window hcount
    simpa only [Nat.one_mul, Nat.mul_comm] using this
  calc
    (S.cfg.D + S.cfg.K + 2) * rawLag +
          recurringFinalitySelectionLag S recurrenceGap =
        count * rawLag + window := rfl
    _ ≤ count * rawLag + count * window := Nat.add_le_add_left hwindow _
    _ = recurringFinalityDeadline S rawLag recurrenceGap := by
      simp only [recurringFinalityDeadline, recurringFinalityOneHeightLag,
        count, window, Nat.mul_add]



/-
/-- Every common finalized-height lower bound lies strictly below the current
honest processed-height frontier. -/
theorem commonFinalizedHeight_lt_honestHMaxAt
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hbot: BelowOneThird S rho.honest)
    {r: Round} {h: Height}
    (hcommon: ∀ v ∈ rho.honest,
      h ≤ (rho.storeAt S v (S.a r)).finalized_height):
    h < honestHMaxAt S rho (S.a r):= by
  have hquorum:=
    AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot
  obtain ⟨v, -, hv⟩:=
    AlignedRoundLemmas.honest_member_of_quorum hbot hquorum
  have hbelow:=
    NamedJustificationBound.justificationBelowMax_readAt S rho (S.a r) v
  have hfinal:= NamedJustificationBound.storeFinality_readAt
    S rho (S.a r) v
  have hordered: (rho.storeAt S v (S.a r)).finalized_height ≤
      (rho.storeAt S v (S.a r)).core.h_j:= by
    change (if (rho.storeAt S v (S.a r)).core.F = Block.genesis then 0 else
      ((rho.storeAt S v (S.a r)).core.σ
        (rho.storeAt S v (S.a r)).core.F).h) ≤
      (rho.storeAt S v (S.a r)).core.h_j
    by_cases hF: (rho.storeAt S v (S.a r)).core.F = Block.genesis
    · simp [hF]
    · rw [if_neg hF]
      exact (hfinal.1 (rho.storeAt S v (S.a r)).core.F).2.heights_ordered
  exact (hcommon v hv).trans hordered |>.trans_lt (by
    simpa only [Internal.JustificationBelowMax] using hbelow) |>.trans_le
    (localHMax_le_honestHMaxAt S rho (S.a r) hv)

-/

/-- A block below every honest finalized root is no higher than the public
honest frontier at that read. -/
theorem commonFinalizedBlock_height_le_honestHMaxAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {r : Round} {B : Block V}
    (hcommon : ∀ v ∈ rho.honest,
      Block.Preceq B (rho.storeAt S v (S.a r)).F) :
    ∃ v ∈ rho.honest, ∃ D ∈ (rho.storeAt S v (S.a r)).bodies,
      D.erase = B ∧
        (derive_named S.E S.cfg D).h ≤ honestHMaxAt S rho (S.a r) := by
  have hquorum :=
    AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot
  obtain ⟨v, -, hv⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbot hquorum
  let st := rho.storeAt S v (S.a r)
  have hFmem : st.F ∈ st.T :=
    Proofs.NamedStoreBridge.finalizedInTree_readAt S rho (S.a r) v
  have hclosed : ParentClosed st.core :=
    Proofs.NamedStoreBridge.parentClosed_readAt S rho (S.a r) v
  have hBmem : B ∈ st.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff st.core).mp hclosed).2
      B st.F hFmem (hcommon v hv)
  obtain ⟨D, hD, hDB⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_readAt S rho (S.a r) v hBmem
  have hheight :=
    Proofs.NamedStoreBridge.heights_le_hMax_readAt S rho (S.a r) v D hD
  exact ⟨v, hv, D, hD, hDB, hheight.trans
    (localHMax_le_honestHMaxAt S rho (S.a r) hv)⟩




/-
/-- Whole-run store safety orients an old common finalized prefix below a
strictly higher new common finalized prefix. -/
theorem preceq_of_commonFinalityAdvance
    (S: Setup V) {rho: Run V}
    (hsafe: WholeRunFinalitySafety S rho)
    {u v: V} (hu: u ∈ rho.honest) (hv: v ∈ rho.honest)
    {t t': Time} (ht: t ≤ rho.horizon) (ht': t' ≤ rho.horizon)
    {B P: Block V} {h: Height}
    (hB: Block.Preceq B (rho.storeAt S u t).F)
    (hP: Block.Preceq P (rho.storeAt S v t').F)
    (hBheight: (derived_state S.E S.cfg B).h ≤ h)
    (hadvance: h < (derived_state S.E S.cfg P).h):
    Block.Preceq B P:= by
  have hstores:= hsafe.2 u hu v hv t t'
  have hcompat: Block.compatible B P = true:= by
    simp only [Block.compatible, Bool.or_eq_true] at hstores
    rcases hstores with hforward | hbackward
    · exact Block.compatible_of_preceq_common
        (Block.preceq_trans hB hforward) hP
    · exact Block.compatible_of_preceq_common
        hB (Block.preceq_trans hP hbackward)
  exact preceq_of_compatible_of_derived_h_lt
    S.E S.cfg hcompat (hBheight.trans_lt hadvance)

/-- If the supplied common prefix already has strictly higher derived height,
the recurring-finality obligation is discharged at the starting read. -/
theorem recurringFinalityWitness_of_existingCommonHeight
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r d: Round} {B: Block V} {h: Height}
    (hcommon: ∀ v ∈ rho.honest,
      Block.Preceq B (rho.storeAt S v (S.a r)).F ∧
        h ≤ (rho.storeAt S v (S.a r)).finalized_height)
    (hadvance: h < (derived_state S.E S.cfg B).h)
    (hBne: B ≠ Block.genesis):
    ∃ (P: Block V) (h': Height) (t: Time),
      Block.Preceq B P ∧
        h < h' ∧
        (derived_state S.E S.cfg P).h = h' ∧
        S.a r ≤ t ∧
        t ≤ S.a (r + d) ∧
        ∀ v ∈ rho.honest,
          Block.Preceq P (rho.storeAt S v t).F ∧
            h' ≤ (rho.storeAt S v t).finalized_height:= by
  refine ⟨B, (derived_state S.E S.cfg B).h, S.a r,
    Block.preceq_self B, hadvance, rfl, le_rfl,
    Assembly.a_mono S (Nat.le_add_right r d), ?_⟩
  intro v hv
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v)
      (rho.storeAt S v (S.a r)):=
    Proofs.Bridges.depReachable_stateAt S adm.toScheduleWellFormed
      adm.toDeliveryWellFormed (S.a r) v
  exact ⟨(hcommon v hv).1,
    derived_height_le_finalized_height_of_preceq
      S hdep hBne (hcommon v hv).1⟩

/-- A new common finalized checkpoint with strictly larger height satisfies the
recurring witness, including ancestry of the caller's old common prefix. -/
theorem recurringFinalityWitness_of_commonAdvance
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hbot: BelowOneThird S rho.honest)
    {r d: Round} {B P: Block V} {h h': Height} {t: Time}
    (hcommon: ∀ v ∈ rho.honest,
      Block.Preceq B (rho.storeAt S v (S.a r)).F ∧
        h ≤ (rho.storeAt S v (S.a r)).finalized_height)
    (hBheight: (derived_state S.E S.cfg B).h ≤ h)
    (hadvance: h < h')
    (hPheight: (derived_state S.E S.cfg P).h = h')
    (htLo: S.a r ≤ t)
    (htHi: t ≤ S.a (r + d))
    (horizon: S.a (r + d) ≤ rho.horizon)
    (hnew: ∀ v ∈ rho.honest,
      Block.Preceq P (rho.storeAt S v t).F ∧
        h' ≤ (rho.storeAt S v t).finalized_height):
    ∃ (P': Block V) (h'': Height) (t': Time),
      Block.Preceq B P' ∧
        h < h'' ∧
        (derived_state S.E S.cfg P').h = h'' ∧
        S.a r ≤ t' ∧
        t' ≤ S.a (r + d) ∧
        ∀ v ∈ rho.honest,
          Block.Preceq P' (rho.storeAt S v t').F ∧
            h'' ≤ (rho.storeAt S v t').finalized_height:= by
  have hquorum:=
    AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot
  obtain ⟨v, -, hv⟩:=
    AlignedRoundLemmas.honest_member_of_quorum hbot hquorum
  have hstartHor: S.a r ≤ rho.horizon:=
    (Assembly.a_mono S (Nat.le_add_right r d)).trans horizon
  have htHor: t ≤ rho.horizon:= htHi.trans horizon
  have hBP: Block.Preceq B P:= by
    apply preceq_of_commonFinalityAdvance S
      (wholeRunFinalitySafety_of_belowOneThird S adm.toAdmissibleCore hbot)
      hv hv hstartHor htHor
      (hcommon v hv).1 (hnew v hv).1 hBheight
    simpa only [hPheight] using hadvance
  exact ⟨P, h', t, hBP, hadvance, hPheight, htLo, htHi, hnew⟩

/-- Retain the exact honest proposal that supplied a common finality advance.
This is the final constructor used by the bounded two-opening assembly. -/
theorem recurringFinalityCarrierWitness_of_commonProposalFinality
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hbot: BelowOneThird S rho.honest)
    {t0: Time} {r d: Round} {B P: Block V}
    {h h': Height} {s: Slot}
    (hcommon: ∀ v ∈ rho.honest,
      Block.Preceq B (rho.storeAt S v (S.a r)).F ∧
        h ≤ (rho.storeAt S v (S.a r)).finalized_height)
    (hBheight: (derived_state S.E S.cfg B).h ≤ h)
    (hs: 0 < s)
    (hafter: t0 < Protocol.proposal_time S.E s)
    (hproposer: S.E.proposer s ∈ rho.honest)
    (hfinalized: FinalizedAt S.E S.cfg
      (proposedBlock S rho s) P h')
    (hadvance: h < h')
    (hPheight: (derived_state S.E S.cfg P).h = h')
    (hproposalLo: S.a r ≤ Protocol.proposal_time S.E s)
    (hconfirmationLo: S.a r ≤ Protocol.confirmation_time S.E s)
    (hconfirmationHi: Protocol.confirmation_time S.E s ≤
      S.a (r + d))
    (horizon: S.a (r + d) ≤ rho.horizon)
    (hnew: ∀ v ∈ rho.honest,
      Block.Preceq P
          (rho.storeAt S v (Protocol.confirmation_time S.E s)).F ∧
        h' ≤ (rho.storeAt S v
          (Protocol.confirmation_time S.E s)).finalized_height):
    ∃ (s': Slot) (P': Block V) (h'': Height),
      0 < s' ∧
        t0 < Protocol.proposal_time S.E s' ∧
        S.E.proposer s' ∈ rho.honest ∧
        Protocol.confirmation_time S.E s' ≤ rho.horizon ∧
        FinalizedAt S.E S.cfg (proposedBlock S rho s') P' h'' ∧
        Block.Preceq B P' ∧
        h < h'' ∧
        (derived_state S.E S.cfg P').h = h'' ∧
        S.a r ≤ Protocol.proposal_time S.E s' ∧
        S.a r ≤ Protocol.confirmation_time S.E s' ∧
        Protocol.confirmation_time S.E s' ≤ S.a (r + d) ∧
        ∀ v ∈ rho.honest,
          Block.Preceq P'
              (rho.storeAt S v
                (Protocol.confirmation_time S.E s')).F ∧
            h'' ≤ (rho.storeAt S v
              (Protocol.confirmation_time S.E s')).finalized_height:= by
  have hquorum:=
    AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot
  obtain ⟨v, -, hv⟩:=
    AlignedRoundLemmas.honest_member_of_quorum hbot hquorum
  have hstartHor: S.a r ≤ rho.horizon:=
    hconfirmationLo.trans (hconfirmationHi.trans horizon)
  have hconfirmationHor:
      Protocol.confirmation_time S.E s ≤ rho.horizon:=
    hconfirmationHi.trans horizon
  have hBP: Block.Preceq B P:= by
    apply preceq_of_commonFinalityAdvance S
      (wholeRunFinalitySafety_of_belowOneThird S adm.toAdmissibleCore hbot)
      hv hv hstartHor hconfirmationHor
      (hcommon v hv).1 (hnew v hv).1 hBheight
    simpa only [hPheight] using hadvance
  exact ⟨s, P, h', hs, hafter, hproposer,
    hconfirmationHor, hfinalized, hBP, hadvance,
    hPheight, hproposalLo, hconfirmationLo, hconfirmationHi, hnew⟩

/-- The canonical execution's inline action-coverage surface is exactly the raw
coverage predicate used by the quorum adapters. -/
theorem honestActionProposalCoverageAt_of_canonical
    (S: Setup V) (rho: Run V) (r: Round) (s: Slot)
    (H: Height) (T: BlockId)
    (h: Protocol.CanonicalActionProposalCoverageAt
      S rho r s H T):
    HonestActionProposalCoverageAt S rho r s H T:= by
  exact h


/-- A global honest-prefix freshness fact specializes to the exact local record
prefix consumed by the raw action-row producer. -/
theorem actionRecordPrefixFreshAt_of_noLocalHeightPairBefore
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {H: Height}
    (hfresh: Internal.NoLocalHeightPairBefore S rho
      (strictEventIndex rho (S.a r)) H)
    {v: V} (hv: v ∈ rho.honest):
    ActionRecordPrefixFreshAt S rho v r H:= by
  refine ⟨strictEventIndex rho (S.a r),
    congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toScheduleWellFormed (S.a r)) v, ?_⟩
  intro i t a hi hevent hemitted hheight
  exact hfresh hi hv hevent hemitted hheight


/-- At a fresh justifiable grade source, all honest action rows name the exact
target unless the public raw frontier has already escaped the height. -/
theorem honestTargetRows_or_hMaxRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {C: Block V} {H: Height} {T: BlockId}
    (hforms: GradeFormsAt S rho r C)
    (hCheight: (derived_state S.E S.cfg C).h = H)
    (hCtarget: (derived_state S.E S.cfg C).T_h.root = T)
    (hCnj: (derived_state S.E S.cfg C).nj = false)
    (hfresh: Internal.NoLocalHeightPairBefore S rho
      (strictEventIndex rho (S.a r)) H):
    (∀ v ∈ rho.honest,
        (actionAttestationAt S rho v r).height_pair =
          HeightPair.target H T) ∨
      H < honestHMaxAt S rho (S.a r):= by
  by_cases hrise: H < honestHMaxAt S rho (S.a r)
  · exact Or.inr hrise
  · left
    intro v hv
    rcases actionAttestationAt_target_of_prefixFresh_sourceJustifiable_or_hMaxRise
        S adm hforms hCheight hCtarget hCnj hv
        (actionRecordPrefixFreshAt_of_noLocalHeightPairBefore
          S adm hfresh hv) with htarget | hlocal
    · exact htarget
    · exfalso
      apply hrise
      apply hlocal.trans_le
      have hpre:
          (actionStoreAt S rho v r).h_max =
            (rho.storeBeforeTime S v (S.a r)).h_max:= by
        exact (attestStore_finality S
          (rho.stateBeforeTime S (S.a r) v).st (S.a r)).2.2.1
      rw [hpre]
      exact (storeBeforeTime_hMax_le_storeAt
          S adm.toScheduleWellFormed v (S.a r)).trans
        (localHMax_le_honestHMaxAt S rho (S.a r) hv)


/-- Live target coverage at a justifiable parent height performs the actual
justification write in the child transition. -/
theorem justifiedAt_of_targetQuorumCoveredByChild
    (E: Env V) (cfg: HeightConfig) {B: Block V}
    (hBne: B ≠ Block.genesis)
    (hcovered: TargetQuorumCoveredByChild E
      (derived_state E cfg B.parent) B)
    (hjustifiable: (derived_state E cfg B.parent).nj = false):
    JustifiedAt E cfg B
      (derived_state E cfg B.parent).T_h
      (derived_state E cfg B.parent).h:= by
  cases B with
  | genesis => exact (hBne rfl).elim
  | node p s root gv gsv ats proposer =>
      let sigma:= derived_state E cfg p
      let tau:= Protocol.foldBlock sigma
        (Block.node p s root gv gsv ats proposer)
      have htarget: Protocol.targetReady E tau = true:=
        targetQuorumCoveredByChild_targetReady E hcovered hjustifiable
      have htargetAfter:
          Protocol.targetReady E (Protocol.afterFin E tau) = true:= by
        unfold Protocol.afterFin
        split
        · simpa only [Protocol.targetReady] using htarget
        · exact htarget
      change
        (Protocol.process_height_events E cfg tau).J = sigma.T_h ∧
          (Protocol.process_height_events E cfg tau).h_j = sigma.h
      constructor
      · rw [Protocol.process_height_events_eq, if_pos htargetAfter,
          Protocol.advance_height_J, Protocol.afterFin_T_h,
          Protocol.foldBlock_T_h]
      · rw [Protocol.process_height_events_eq, if_pos htargetAfter,
          Protocol.advance_height_h_j, Protocol.afterFin_h,
          Protocol.foldBlock_h]

/-- Live target coverage advances the child height without the timeout-delay
guard because target justification has priority over progress consumption. -/
theorem derived_state_h_of_targetQuorumCoveredByChild
    (E: Env V) (cfg: HeightConfig) {B: Block V}
    (hBne: B ≠ Block.genesis)
    (hcovered: TargetQuorumCoveredByChild E
      (derived_state E cfg B.parent) B)
    (hjustifiable: (derived_state E cfg B.parent).nj = false):
    (derived_state E cfg B).h = (derived_state E cfg B.parent).h + 1:= by
  cases B with
  | genesis => exact (hBne rfl).elim
  | node p s root gv gsv ats proposer =>
      let sigma:= derived_state E cfg p
      let tau:= Protocol.foldBlock sigma
        (Block.node p s root gv gsv ats proposer)
      have htarget: Protocol.targetReady E tau = true:=
        targetQuorumCoveredByChild_targetReady E hcovered hjustifiable
      have htargetAfter:
          Protocol.targetReady E (Protocol.afterFin E tau) = true:= by
        unfold Protocol.afterFin
        split
        · simpa only [Protocol.targetReady] using htarget
        · exact htarget
      change (Protocol.process_height_events E cfg tau).h = sigma.h + 1
      rw [Protocol.process_height_events_eq, if_pos htargetAfter,
        Protocol.advance_height_h, Protocol.afterFin_h, Protocol.foldBlock_h]

/-- Live parent-or-child finality coverage performs an actual finality write in
the child transition. -/
theorem finalizedAt_of_finalityQuorumCoveredByChild
    (E: Env V) (cfg: HeightConfig) {B J: Block V} {h: Height}
    (hBne: B ≠ Block.genesis)
    (hcovered: FinalityQuorumCoveredByChild E
      (derived_state E cfg B.parent) B h J)
    (hdebt: (derived_state E cfg B.parent).h_F < h):
    FinalizedAt E cfg B J h:= by
  cases B with
  | genesis => exact (hBne rfl).elim
  | node p s root gv gsv ats proposer =>
      have hready:=
        finalityQuorumCoveredByChild_finalityReady E hcovered hdebt
      have hwrite:= process_height_events_actual_F E cfg
        (Protocol.foldBlock (derived_state E cfg p)
          (Block.node p s root gv gsv ats proposer)) hready
      have hcheckpoint:=
        finalityQuorumCoveredByChild_checkpoint_after_fold E hcovered
      change
        (Protocol.process_height_events E cfg
            (Protocol.foldBlock (derived_state E cfg p)
              (Block.node p s root gv gsv ats proposer))).F = J ∧
          (Protocol.process_height_events E cfg
            (Protocol.foldBlock (derived_state E cfg p)
              (Block.node p s root gv gsv ats proposer))).h_F = h
      exact
        ⟨hwrite.1.trans hcheckpoint.2,
          hwrite.2.trans hcheckpoint.1⟩

/-- Every protocol proposal has the node constructor and therefore is not
genesis. -/
theorem proposedBlock_ne_genesis
    (S: Setup V) (rho: Run V) (s: Slot):
    proposedBlock S rho s ≠ Block.genesis:= by
  intro hgen
  have hparent:= Protocol.proposedBlock_parent S rho s
  rw [hgen] at hparent
  change (none: Option (Block V)) =
    some (Protocol.proposedParent S rho s) at hparent
  cases hparent

/-- At an ordinary height, exact target rows in the live proposal coverage both
cross the height and perform the named justification write. -/
theorem ordinaryHeightTargetProposal_of_actionCoverage
    (S: Setup V) {rho: Run V}
    (hbot: BelowOneThird S rho.honest)
    {r: Round} {s: Slot} {H: Height} {T: BlockId}
    (hcoverage: HonestActionProposalCoverageAt S rho r s H T)
    (hparentHeight: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).h = H)
    (hparentTarget: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).T_h.root = T)
    (hparentJustifiable: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).nj = false)
    (hexact: ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair =
        HeightPair.target H T):
    JustifiedAt S.E S.cfg (proposedBlock S rho s)
        (derived_state S.E S.cfg (proposedBlock S rho s).parent).T_h H ∧
      (derived_state S.E S.cfg (proposedBlock S rho s)).h = H + 1:= by
  have htarget:=
    targetQuorumCoveredByProposedBlock_of_actionCoverage
      S hbot hcoverage hparentHeight hparentTarget hexact
  constructor
  · have hjust:= justifiedAt_of_targetQuorumCoveredByChild
      S.E S.cfg (proposedBlock_ne_genesis S rho s)
        htarget hparentJustifiable
    simpa only [hparentHeight] using hjust
  · have hheight:= derived_state_h_of_targetQuorumCoveredByChild
      S.E S.cfg (proposedBlock_ne_genesis S rho s) htarget
        hparentJustifiable
    simpa only [hparentHeight] using hheight

/-- Exact target rows and positive canonical action coverage perform the
ordinary justification/height transition. -/
theorem ordinaryHeightTargetProposal_of_canonicalCoverage
    (S: Setup V) {rho: Run V}
    (hbot: BelowOneThird S rho.honest)
    {r: Round} {s: Slot} {H: Height} {T: BlockId}
    (hcoverage: Protocol.CanonicalActionProposalCoverageAt
      S rho r s H T)
    (hparentHeight: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).h = H)
    (hparentTarget: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).T_h.root = T)
    (hparentJustifiable: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).nj = false)
    (hrows: ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair =
        HeightPair.target H T):
    JustifiedAt S.E S.cfg (proposedBlock S rho s)
        (derived_state S.E S.cfg (proposedBlock S rho s).parent).T_h H ∧
      (derived_state S.E S.cfg (proposedBlock S rho s)).h = H + 1:= by
  exact ordinaryHeightTargetProposal_of_actionCoverage
    S hbot
    (honestActionProposalCoverageAt_of_canonical
      S rho r s H T hcoverage)
    hparentHeight hparentTarget hparentJustifiable hrows

/-- A fresh ordinary source at height `H` either creates its exact
justification checkpoint in the selected first proposal and enters height
`H + 1`, or the raw frontier has already advanced. -/
theorem ordinaryTargetPhase_or_hMaxRise
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hbot: BelowOneThird S rho.honest)
    {source first: Round} {C: Block V} {H: Height} {T: BlockId}
    (hforms: GradeFormsAt S rho source C)
    (hCheight: (derived_state S.E S.cfg C).h = H)
    (hCtarget: (derived_state S.E S.cfg C).T_h.root = T)
    (hCnj: (derived_state S.E S.cfg C).nj = false)
    (hfresh: Internal.NoLocalHeightPairBefore S rho
      (strictEventIndex rho (S.a source)) H)
    (hdelay: S.a source + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot first))
    (hparentHeight: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot first)).parent).h = H)
    (hparentTarget: (derived_state S.E S.cfg
      (proposedBlock S rho
        (S.hc.opening_slot first)).parent).T_h.root = T)
    (hparentJustifiable: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot first)).parent).nj = false)
    (hcoverage: Protocol.CanonicalActionProposalCoverageAt S rho source
      (S.hc.opening_slot first) H T):
    (∃ J: Block V,
        (∀ v ∈ rho.honest,
          (actionAttestationAt S rho v source).height_pair =
            HeightPair.target H T) ∧
        JustifiedAt S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot first)) J H ∧
        J.root = T ∧
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot first))).h = H + 1) ∨
      H < honestHMaxAt S rho
        (Protocol.proposal_time S.E (S.hc.opening_slot first)):= by
  rcases honestTargetRows_or_hMaxRise S adm hforms hCheight hCtarget
      hCnj hfresh with hrows | hrise
  · have htarget:=
      ordinaryHeightTargetProposal_of_canonicalCoverage
        S hbot hcoverage hparentHeight hparentTarget
          hparentJustifiable hrows
    left
    exact ⟨(derived_state S.E S.cfg
      (proposedBlock S rho
        (S.hc.opening_slot first)).parent).T_h,
      hrows, htarget.1, hparentTarget, htarget.2⟩
  · right
    exact hrise.trans_le
      (honestHMaxAt_mono S adm.toScheduleWellFormed (by
        exact (Int.le_add_of_nonneg_right
          (le_of_lt S.E.Δ_pos)).trans hdelay))

/-- Exact first-action finality rows form a live parent-or-child quorum at the
selected second proposal. A row already carried by the parent comes with its
exact `finalize` contribution; every other row is in the child payload. -/
theorem finalityQuorumCoveredByProposedBlock_of_actionRows
    (S: Setup V) {rho: Run V}
    (hbot: BelowOneThird S rho.honest)
    {r: Round} {s: Slot} {hJ: Height}
    {TJ: BlockId} {J: Block V}
    (hcoverage: ∀ v ∈ rho.honest,
      let a:= actionAttestationAt S rho v r
      let B:= proposedBlock S rho s
      (a ∈ chain_attestations B.parent ∧
          v ∈ (derived_state S.E S.cfg B.parent).finalize) ∨
        a ∈ B.attestations)
    (hparentHJ: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).h_j = hJ)
    (hparentJ: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).J = J)
    (hroot: J.root = TJ)
    (hfinality: ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).finality_pair =
        some ⟨hJ, TJ⟩):
    FinalityQuorumCoveredByChild S.E
      (derived_state S.E S.cfg (proposedBlock S rho s).parent)
      (proposedBlock S rho s) hJ J:= by
  apply finalityQuorumCoveredByChild_of_honest S hbot hparentHJ hparentJ
  intro v hv
  have hcovered:= hcoverage v hv
  dsimp only at hcovered
  rcases hcovered with hparent | hchild
  · exact Or.inl hparent.2
  · right
    refine ⟨actionAttestationAt S rho v r, hchild, ?_, ?_⟩
    · exact (actionAttestationAt_shape S rho v r).1
    · rw [hfinality v hv, hroot]

/-- A selected second proposal performs the exact finality write once every
first-action row is live in its parent or child. -/
theorem finalizedAt_of_actionRows
    (S: Setup V) {rho: Run V}
    (hbot: BelowOneThird S rho.honest)
    {r: Round} {s: Slot} {hJ: Height}
    {TJ: BlockId} {J: Block V}
    (hcoverage: ∀ v ∈ rho.honest,
      let a:= actionAttestationAt S rho v r
      let B:= proposedBlock S rho s
      (a ∈ chain_attestations B.parent ∧
          v ∈ (derived_state S.E S.cfg B.parent).finalize) ∨
        a ∈ B.attestations)
    (hparentHJ: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).h_j = hJ)
    (hparentJ: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).J = J)
    (hroot: J.root = TJ)
    (hdebt: (derived_state S.E S.cfg
      (proposedBlock S rho s).parent).h_F < hJ)
    (hfinality: ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).finality_pair =
        some ⟨hJ, TJ⟩):
    FinalizedAt S.E S.cfg (proposedBlock S rho s) J hJ:= by
  apply finalizedAt_of_finalityQuorumCoveredByChild
    S.E S.cfg (proposedBlock_ne_genesis S rho s)
  · exact finalityQuorumCoveredByProposedBlock_of_actionRows
      S hbot hcoverage hparentHJ hparentJ hroot hfinality
  · exact hdebt

/-- A positive finalized checkpoint has the checkpoint height recorded by its
own derived state. -/
theorem derived_height_eq_of_finalizedAt
    (E: Env V) (cfg: HeightConfig) {C P: Block V} {h: Height}
    (hcheckpoint: FinalizedAt E cfg C P h) (hpos: 0 < h):
    (derived_state E cfg P).h = h:= by
  rcases Protocol.derived_finalized_height E cfg C with hzero | hheight
  · have hzero': h = 0:= hcheckpoint.2.symm.trans hzero
    exact (Nat.ne_of_gt hpos hzero').elim
  · simpa only [hcheckpoint.1, hcheckpoint.2] using hheight

/-- A finalized checkpoint above height one cannot be genesis. -/
theorem finalizedCheckpoint_ne_genesis
    (E: Env V) (cfg: HeightConfig) {C P: Block V} {h: Height}
    (hcheckpoint: FinalizedAt E cfg C P h) (hone: 1 < h):
    P ≠ Block.genesis:= by
  intro hgenesis
  have hheight:= derived_height_eq_of_finalizedAt E cfg hcheckpoint
    (Nat.zero_lt_of_lt hone)
  rw [hgenesis] at hheight
  have hgenesisHeight:
      (derived_state E cfg (Block.genesis: Block V)).h = 1:= rfl
  rw [hgenesisHeight] at hheight
  exact (Nat.ne_of_lt hone) hheight

/-- Along one parent edge the justification height strictly increases, or the
exact justification checkpoint is unchanged. -/
theorem derivedJustification_strict_or_eq_of_parent
    (E: Env V) (cfg: HeightConfig)
    (p: Block V) (s: Slot) (r: BlockId)
    (gv support: List (GoldfishVote V))
    (ats: List (CombinedAttestation V)) (i: V):
    (derived_state E cfg p).h_j <
        (derived_state E cfg
          (.node p s r gv support ats i)).h_j ∨
      ((derived_state E cfg p).h_j =
          (derived_state E cfg
            (.node p s r gv support ats i)).h_j ∧
        (derived_state E cfg p).J =
          (derived_state E cfg
            (.node p s r gv support ats i)).J):= by
  rw [Protocol.derived_state_node, Protocol.process_height_events_eq]
  split_ifs
  · left
    rw [Protocol.advance_height_h_j, Protocol.afterFin_h,
      Protocol.foldBlock_h]
    exact (Protocol.chainOrder_derived_state E cfg p).justified_below_height
  · right
    constructor
    · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j,
        Protocol.foldBlock_h_j]
    · rw [Protocol.advance_height_J, Protocol.afterFin_J,
        Protocol.foldBlock_J]
  · right
    constructor
    · rw [Protocol.afterFin_h_j, Protocol.foldBlock_h_j]
    · rw [Protocol.afterFin_J, Protocol.foldBlock_J]

/-- Along block ancestry the justification height strictly increases, or the
exact `(height, checkpoint)` pair is retained. -/
theorem derivedJustification_strict_or_eq_of_preceq
    (E: Env V) (cfg: HeightConfig) {A B: Block V}
    (hAB: Block.Preceq A B):
    (derived_state E cfg A).h_j < (derived_state E cfg B).h_j ∨
      ((derived_state E cfg A).h_j =
          (derived_state E cfg B).h_j ∧
        (derived_state E cfg A).J =
          (derived_state E cfg B).J):= by
  induction B with
  | genesis =>
      change Block.preceq A (.genesis: Block V) = true at hAB
      simp only [Block.preceq, decide_eq_true_eq] at hAB
      subst A
      exact Or.inr ⟨rfl, rfl⟩
  | node p s r gv support ats i ih =>
      change Block.preceq A
        (.node p s r gv support ats i) = true at hAB
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hAB
      rcases hAB with rfl | hAp
      · exact Or.inr ⟨rfl, rfl⟩
      · have hprefix:= ih hAp
        have hedge:=
          derivedJustification_strict_or_eq_of_parent
            E cfg p s r gv support ats i
        rcases hprefix with hprefix | ⟨hhPrefix, hJPrefix⟩
        · rcases hedge with hedge | ⟨hhEdge, -⟩
          · exact Or.inl (hprefix.trans hedge)
          · exact Or.inl (hprefix.trans_eq hhEdge)
        · rcases hedge with hedge | ⟨hhEdge, hJEdge⟩
          · exact Or.inl (hhPrefix.trans_lt hedge)
          · exact Or.inr
              ⟨hhPrefix.trans hhEdge, hJPrefix.trans hJEdge⟩

/-- An honest proposal's selected parent is already in the proposer read, so
its derived height is bounded by the public honest frontier at that read. -/
theorem proposedBlock_parent_height_le_honestHMaxAt
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot}
    (hproposer: S.E.proposer s ∈ rho.honest):
    (derived_state S.E S.cfg (proposedBlock S rho s).parent).h ≤
      honestHMaxAt S rho (Protocol.proposal_time S.E s):= by
  let t:= Protocol.proposal_time S.E s
  let v:= S.E.proposer s
  let pre:= rho.storeBeforeTime S v t
  have hparentDuty:
      (proposedBlock S rho s).parent ∈
        (Protocol.proposerDutyStore S rho s).T:= by
    rw [parent_eq_of_parent?
      (Protocol.proposedBlock_parent S rho s)]
    exact Protocol.proposedParent_mem S adm s
  have hparentPre: (proposedBlock S rho s).parent ∈ pre.T:= by
    simpa only [Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, pre, v, t] using hparentDuty
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:= by
    simpa only [pre, v, t] using
      (Proofs.Bridges.depReachable_stateBeforeTime S
        adm.toScheduleWellFormed adm.toDeliveryWellFormed t v)
  have hagree:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node v) pre hdep
      (proposedBlock S rho s).parent hparentPre
  have htree:=
    treeHeightsLeHMax_depReachable S.E S.hc S.cfg (S.node v) hdep
      (proposedBlock S rho s).parent hparentPre
  rw [hagree] at htree
  exact htree.trans
    ((storeBeforeTime_hMax_le_storeAt
        S adm.toScheduleWellFormed v t).trans
      (localHMax_le_honestHMaxAt S rho t hproposer))

/-- A canonical grade source and a selected honest proposal parent have the
same height, target, and NJ bit unless the public frontier has already risen. -/
theorem canonicalGradeParentFields_or_hMaxRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {first: Round} {C: Block V} {H: Height}
    (hCheight: (derived_state S.E S.cfg C).h = H)
    (hCparent: Block.Preceq C
      (Protocol.proposedParent S rho (S.hc.opening_slot first)))
    (hproposer: S.E.proposer (S.hc.opening_slot first) ∈ rho.honest):
    (Block.Preceq C
        (proposedBlock S rho (S.hc.opening_slot first)).parent ∧
      (derived_state S.E S.cfg
        (proposedBlock S rho
          (S.hc.opening_slot first)).parent).h = H ∧
      (derived_state S.E S.cfg
        (proposedBlock S rho
          (S.hc.opening_slot first)).parent).T_h =
        (derived_state S.E S.cfg C).T_h ∧
      (derived_state S.E S.cfg
        (proposedBlock S rho
          (S.hc.opening_slot first)).parent).nj =
        (derived_state S.E S.cfg C).nj) ∨
      H < honestHMaxAt S rho
        (Protocol.proposal_time S.E
          (S.hc.opening_slot first)):= by
  by_cases hrise: H < honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot first))
  · exact Or.inr hrise
  · left
    have hCparent': Block.Preceq C
        (proposedBlock S rho (S.hc.opening_slot first)).parent:= by
      rw [parent_eq_of_parent?
        (Protocol.proposedBlock_parent
          S rho (S.hc.opening_slot first))]
      exact hCparent
    have hlower: H ≤ (derived_state S.E S.cfg
        (proposedBlock S rho
          (S.hc.opening_slot first)).parent).h:= by
      rw [← hCheight]
      exact Protocol.derived_h_mono S.E S.cfg hCparent'
    have hupper: (derived_state S.E S.cfg
        (proposedBlock S rho
          (S.hc.opening_slot first)).parent).h ≤ H:=
      (proposedBlock_parent_height_le_honestHMaxAt
        S adm hproposer).trans (Nat.le_of_not_gt hrise)
    have hheight: (derived_state S.E S.cfg
        (proposedBlock S rho
          (S.hc.opening_slot first)).parent).h = H:=
      Nat.le_antisymm hupper hlower
    have hsame: (derived_state S.E S.cfg
        (proposedBlock S rho
          (S.hc.opening_slot first)).parent).h =
        (derived_state S.E S.cfg C).h:= by
      rw [hheight, hCheight]
    exact ⟨hCparent', hheight,
      derivedTarget_eq_of_preceq_same_height
        S.E S.cfg hCparent' hsame,
      derivedNj_eq_of_preceq_same_height
        S.E S.cfg hCparent' hsame⟩

/-- Ordered honest opening proposals in the moving canonical suffix retain the
first proposal below the later proposal's selected parent. -/
theorem proposedBlock_preceq_laterOpeningParent_of_canonical
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q first second: Round}
    (hexec: Protocol.CanonicalSuffixExecution S rho q)
    (hfirstPos: 0 < first)
    (hfirstLtSecond: first < second)
    (hafter: healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot first))
    (hproposerFirst:
      S.E.proposer (S.hc.opening_slot first) ∈ rho.honest)
    (hproposerSecond:
      S.E.proposer (S.hc.opening_slot second) ∈ rho.honest)
    (hproposalHorFirst: Protocol.proposal_time S.E
      (S.hc.opening_slot first) ≤ rho.horizon)
    (hproposalHorSecond: Protocol.proposal_time S.E
      (S.hc.opening_slot second) ≤ rho.horizon):
    Block.Preceq
      (proposedBlock S rho (S.hc.opening_slot first))
      (proposedBlock S rho (S.hc.opening_slot second)).parent:= by
  have hR: 0 < S.hc.R:=
    lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hopenLt: S.hc.opening_slot first <
      S.hc.opening_slot second:= by
    simp only [Protocol.HealConfig.opening_slot]
    exact Nat.mul_lt_mul_of_pos_right hfirstLtSecond hR
  have hsFirst: 0 < S.hc.opening_slot first:= by
    simp only [Protocol.HealConfig.opening_slot]
    exact Nat.mul_pos hfirstPos hR
  have hsSecond: 0 < S.hc.opening_slot second:=
    hsFirst.trans hopenLt
  have hemitFirst:=
    Protocol.proposedBlock_emitted_of_admissible
      S adm hsFirst hproposerFirst hproposalHorFirst
  have hemitSecond:=
    Protocol.proposedBlock_emitted_of_admissible
      S adm hsSecond hproposerSecond hproposalHorSecond
  have htime: Protocol.proposal_time S.E
      (S.hc.opening_slot first) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot second):=
    Protocol.proposal_time_mono S.E (Nat.le_of_lt hopenLt)
  have hblocks: Block.Preceq
      (proposedBlock S rho (S.hc.opening_slot first))
      (proposedBlock S rho (S.hc.opening_slot second)):=
    Protocol.proposedBlock_preceq_of_canonicalSuffixExecution
      S adm hexec hsFirst hsSecond hafter hproposerFirst hproposerSecond
        hemitFirst hemitSecond htime
  have hne:
      proposedBlock S rho (S.hc.opening_slot first) ≠
        proposedBlock S rho (S.hc.opening_slot second):= by
    intro heq
    have hslots:= congrArg Block.slot heq
    rw [Protocol.proposedBlock_slot,
      Protocol.proposedBlock_slot] at hslots
    exact (ne_of_lt hopenLt) hslots
  have hparent:= Proofs.Optimistic.preceq_parent_of_ne
    (Protocol.proposedBlock_parent
      S rho (S.hc.opening_slot second)) hblocks hne
  rw [parent_eq_of_parent?
    (Protocol.proposedBlock_parent
      S rho (S.hc.opening_slot second))]
  exact hparent

/-- The action store agrees with the derived state on its selected Goldfish
head. -/
private theorem actionHead_actionStore_agrees_recurringFinality
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (v: V) (r: Round):
    let ast:= actionStoreAt S rho v r
    let head:= actionHead S.E S.hc ast.toHealing
    ast.σ head = derived_state S.E S.cfg head:= by
  let pre:= rho.storeBeforeTime S v (S.a r)
  let ast:= actionStoreAt S rho v r
  let head:= actionHead S.E S.hc ast.toHealing
  have hheadPre: head ∈ pre.T:= by
    simpa only [head, ast, pre] using
      actionHead_mem_storeBeforeTime S adm v r
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (S.a r) v)
  have hagree: DerivedStateAgrees S.E S.cfg pre:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node v) pre hdep
  have hσ: ast.σ = pre.σ:= by
    simpa only [ast, actionStoreAt, pre, Run.storeBeforeTime] using
      (Proofs.Optimistic.attestStore_fields S pre (S.a r)).1
  calc
    ast.σ head = pre.σ head:= congrFun hσ head
    _ = derived_state S.E S.cfg head:= hagree head hheadPre

/-- The action store's local frontier is bounded by the public honest frontier
at the same action read. -/
private theorem actionStoreHMax_le_honestHMaxAt_recurringFinality
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {v: V} (hv: v ∈ rho.honest) (r: Round):
    (actionStoreAt S rho v r).h_max ≤
      honestHMaxAt S rho (S.a r):= by
  have hpre: (actionStoreAt S rho v r).h_max =
      (rho.storeBeforeTime S v (S.a r)).h_max:= by
    exact (attestStore_finality S
      (rho.stateBeforeTime S (S.a r) v).st (S.a r)).2.2.1
  rw [hpre]
  exact (storeBeforeTime_hMax_le_storeAt
      S adm.toScheduleWellFormed v (S.a r)).trans
    (localHMax_le_honestHMaxAt S rho (S.a r) hv)

/-- Every block held by an action reader has a slot strictly before the same
round's `+2` proposal. -/
theorem block_slot_lt_plusTwo_of_mem_beforeAction
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {v: V} {r: Round} {B: Block V}
    (hB: B ∈ (rho.storeBeforeTime S v (S.a r)).T):
    B.slot < S.hc.opening_slot r + 2:= by
  obtain ⟨n, hn, hbefore⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toScheduleWellFormed (S.a r)
  have hBn: B ∈ (rho.stateBefore S n v).st.T:= by
    simpa only [Run.storeBeforeTime, hn] using hB
  have hprocessed: (Object.block B).processed
      (rho.stateBefore S n v).st = true:= by
    simpa only [Object.processed, decide_eq_true_eq] using hBn
  rcases Protocol.acceptsAt_block_of_processed S rho v n B hprocessed with
      hgenesis | haccepted
  · subst B
    exact Nat.zero_lt_succ (S.hc.opening_slot r + 1)
  · obtain ⟨i, hi, t, hacc⟩:= haccepted
    obtain ⟨-, e, he, -, het⟩:= hacc.1
    have ht: t < S.a r:= by
      rw [← het]
      exact hbefore i e hi he
    have haction: S.a r <
        Protocol.proposal_time S.E (S.hc.opening_slot r + 2):= by
      unfold Setup.a Protocol.HealConfig.a Protocol.proposal_time Env.t slotStart
      push_cast
      have hd:= S.E.Δ_pos
      ring_nf
      have h: S.E.Δ * 6 < S.E.Δ * 8:=
        Int.mul_lt_mul_of_pos_left (show (6: Int) < 8 by omega) hd
      exact Int.add_lt_add_right h _
    by_contra hnot
    have hslots: S.hc.opening_slot r + 2 ≤ B.slot:= Nat.le_of_not_gt hnot
    have hmono:= Protocol.proposal_time_mono S.E hslots
    have hBtime:= Protocol.proposal_time_le_of_acceptsAt_block S adm hacc
    have hirrefl: Protocol.proposal_time S.E
        (S.hc.opening_slot r + 2) <
          Protocol.proposal_time S.E (S.hc.opening_slot r + 2):=
      (hmono.trans hBtime).trans_lt (ht.trans haction)
    exact (lt_irrefl _ hirrefl)

/-- In the canonical carrier regime, the named `Open` adoption cone
identifies every honest action head with the carrier's exact `+1` proposal. -/
theorem carrierActionHead_eq_plusOne
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q0 r: Round}
    (_hexec: Protocol.CanonicalSuffixExecution S rho q0)
    (_hcarrier: ProposerCarrierAt S rho r)
    (hcone: CarrierActionHeadPlusOneConeAt S rho r):
    ∀ v ∈ rho.honest,
      actionHead S.E S.hc
          (actionStoreAt S rho v r).toHealing =
        proposedBlock S rho (S.hc.opening_slot r + 1):= by
  intro v hv
  let B1:= proposedBlock S rho (S.hc.opening_slot r + 1)
  let head:= actionHead S.E S.hc
    (actionStoreAt S rho v r).toHealing
  let pre:= rho.storeBeforeTime S v (S.a r)
  have hheadPre: head ∈ pre.T:= by
    simpa only [head, pre] using actionHead_mem_storeBeforeTime S adm v r
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (S.a r) v)
  have hclosed: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node v) pre hdep
  have hB1head: Block.Preceq B1 head:= by
    simpa only [B1, head] using hcone.plusOneCone v hv
  by_contra hne
  have hB1neHead: B1 ≠ head:= fun h => hne h.symm
  obtain ⟨X, hXparent, hXhead⟩:=
    Protocol.exists_child_towards head hB1head hB1neHead
  have hXT: X ∈ pre.T:=
    Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hclosed).2
      X head hheadPre hXhead
  have hXprocessed: (Object.block X).processed
      (rho.stateBefore S (strictEventIndex rho (S.a r)) v).st = true:= by
    rw [← stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toScheduleWellFormed (S.a r)]
    simpa only [Object.processed, decide_eq_true_eq, pre, Run.storeBeforeTime]
      using hXT
  rcases Protocol.acceptsAt_block_of_processed S rho v
      (strictEventIndex rho (S.a r)) X hXprocessed with hgenesis | haccepted
  · subst X
    simp [Block.parent?] at hXparent
  · obtain ⟨_, _, _, hacc⟩:= haccepted
    have hparentSlot: B1.slot < X.slot:= by
      rw [← parent_eq_of_parent? hXparent]
      exact Protocol.parent_slot_lt_of_acceptsAt_block S hacc
    have hslotUpper: X.slot < S.hc.opening_slot r + 2:=
      block_slot_lt_plusTwo_of_mem_beforeAction S adm
        (by simpa only [pre] using hXT)
    have hB1slot: B1.slot = S.hc.opening_slot r + 1:= by
      simpa only [B1] using
        Protocol.proposedBlock_slot S rho (S.hc.opening_slot r + 1)
    rw [hB1slot] at hparentSlot
    have hslotLower: S.hc.opening_slot r + 2 ≤ X.slot:= by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        (Nat.succ_le_iff.mpr hparentSlot)
    exact (Nat.not_lt_of_ge hslotLower) hslotUpper

/-- Rule B permits an empty target record. The complete empty-or-matching
target and lock guards are sufficient for the round action to emit the current
head checkpoint. -/
theorem round_action_finality_pair_of_record_guard
    (E: Env V) (hc: Protocol.HealConfig)
    (nd: Protocol.Node V) (st: Protocol.HealingStore V) {Lambda: Protocol.Record}
    {h: Height} {J: BlockId}
    (htarget: Lambda.target h = none ∨ Lambda.target h = some J)
    (htimeout: Lambda.timeout h = false)
    (hlock: Lambda.lock h = none ∨ Lambda.lock h = some J)
    (hhj: (st.σ (actionHead E hc st)).h_j = h)
    (hJ: (st.σ (actionHead E hc st)).J.root = J)
    (hF: (st.σ (actionHead E hc st)).h_F < h):
    (Protocol.round_action E hc nd st Lambda).2.finality_pair =
      some ⟨h, J⟩:= by
  simp only [Protocol.round_action, Protocol.get_fg_vote,
    Protocol.create_attestation, actionHead] at *
  rw [hhj, hJ]
  have hguard:
      (Lambda.target h = none ∨ Lambda.target h = some J) ∧
        Lambda.timeout h = false ∧
        (Lambda.lock h = none ∨ Lambda.lock h = some J):=
    ⟨htarget, htimeout, hlock⟩
  simp only [Protocol.finality_pair, if_pos hF, if_pos hguard]

/-- The first carrier justifies at slot `+1` or `+2`. The second carrier
finalizes at slot `+2`, unless an earlier honest proposal has already supplied
a common checkpoint at or above that height. Raw `h_max` escape is not a
failure arm. -/
private theorem separatedCarrierPlusTwoFinalityPhase_raw
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho)
    (hbot: BelowOneThird S rho.honest)
    {q start source first second: Round} {C: Block V}
    (hphase: RecurringFinalityPhaseAt
      S rho q start source first second C):
    AlreadyCommonFinalizedAtOrAbove S rho q source (second + 1)
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot first))).h ∨
      ∃ (J: Block V) (hJ: Height),
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot first))).h ≤ hJ ∧
          FinalizedAt S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot second + 2)) J hJ:= by
  let P0:= proposedBlock S rho (S.hc.opening_slot first)
  let P1:= proposedBlock S rho (S.hc.opening_slot first + 1)
  let P2:= proposedBlock S rho (S.hc.opening_slot first + 2)
  let H:= (derived_state S.E S.cfg P0).h
  let T:= (derived_state S.E S.cfg P0).T_h.root
  have hP0P1: Block.Preceq P0 P1:= by
    apply Protocol.preceq_of_parent?
    rw [Protocol.proposedBlock_parent S rho
      (S.hc.opening_slot first + 1), hphase.firstPlusOneParent]
  have hP2parent: P2.parent = P1:= by
    rw [parent_eq_of_parent?
      (Protocol.proposedBlock_parent S rho
        (S.hc.opening_slot first + 2))]
    exact hphase.firstPlusTwoParent
  have _hfirstJustified:
      JustifiedAt S.E S.cfg P1
          (derived_state S.E S.cfg P0).T_h H ∨
        JustifiedAt S.E S.cfg P2
          (derived_state S.E S.cfg P2.parent).T_h H:= by
    rcases hphase.firstCheckpointReady with hearly | ⟨hP1height, hP1targetBlock⟩
    · exact Or.inl (by simpa only [P0, P1, H] using hearly)
    · right
      have hP1nj: (derived_state S.E S.cfg P1).nj = false:= by
        have hsame: (derived_state S.E S.cfg P1).h =
            (derived_state S.E S.cfg P0).h:= by
          simpa only [P0, P1] using hP1height
        exact (derivedNj_eq_of_preceq_same_height
          S.E S.cfg hP0P1 hsame).trans hphase.firstJustifiable
      have hfirstTransition:=
        ordinaryHeightTargetProposal_of_actionCoverage
          S hbot hphase.firstActionCoverage
            (by simpa only [P0, P1, P2, hP2parent] using hP1height)
            (by simpa only [P0, P1, P2, hP2parent] using
              congrArg Block.root hP1targetBlock)
            (by simpa only [P2, hP2parent] using hP1nj)
            (by simpa only [H, T] using hphase.firstTargetRows)
      simpa only [P2, H] using hfirstTransition.1
  rcases hphase.secondCheckpointReady with hearly | hready
  · exact Or.inl hearly
  · obtain ⟨hJ, J, hHJlower, hready⟩:= hready
    let Q1:= proposedBlock S rho (S.hc.opening_slot second + 1)
    let Q2:= proposedBlock S rho (S.hc.opening_slot second + 2)
    have hQ2parent: Q2.parent = Q1:= by
      rw [parent_eq_of_parent?
        (Protocol.proposedBlock_parent S rho
          (S.hc.opening_slot second + 2))]
      exact hphase.secondPlusTwoParent
    have hquorum:=
      AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot
    obtain ⟨v, -, hv⟩:=
      AlignedRoundLemmas.honest_member_of_quorum hbot hquorum
    obtain ⟨hhead, hheadHJ, hheadJ, hheadDebt, -, -, -⟩:= hready v hv
    rw [hhead] at hheadHJ hheadJ hheadDebt
    have hparentHJ: (derived_state S.E S.cfg Q2.parent).h_j = hJ:= by
      rw [hQ2parent]
      simpa only [Q1] using hheadHJ
    have hparentJ: (derived_state S.E S.cfg Q2.parent).J = J:= by
      rw [hQ2parent]
      simpa only [Q1] using hheadJ
    have hparentDebt: (derived_state S.E S.cfg Q2.parent).h_F < hJ:= by
      rw [hQ2parent]
      simpa only [Q1] using hheadDebt
    have hfinalityRows: ∀ w ∈ rho.honest,
        (actionAttestationAt S rho w second).finality_pair =
          some ⟨hJ, J.root⟩:= by
      intro w hw
      let ast:= actionStoreAt S rho w second
      let head:= actionHead S.E S.hc ast.toHealing
      obtain ⟨-, hheadHJ', hheadJ', hheadDebt', htarget, htimeout,
          hlockRecord⟩:=
        hready w hw
      have hσ: ast.σ head = derived_state S.E S.cfg head:= by
        simpa only [ast, head] using
          actionHead_actionStore_agrees_recurringFinality S adm w second
      unfold actionAttestationAt
      apply round_action_finality_pair_of_record_guard
        S.E S.hc (S.node w) ast.toHealing htarget htimeout hlockRecord
      · change (ast.σ head).h_j = hJ
        rw [hσ]
        exact hheadHJ'
      · change (ast.σ head).J.root = J.root
        rw [hσ, hheadJ']
      · change (ast.σ head).h_F < hJ
        rw [hσ]
        exact hheadDebt'
    have hfinalized: FinalizedAt S.E S.cfg Q2 J hJ:= by
      simpa only [Q2] using finalizedAt_of_actionRows
        S hbot hphase.secondRowsCoveredAtPlusTwo
          (by simpa only [Q2] using hparentHJ)
          (by simpa only [Q2] using hparentJ)
          rfl
          (by simpa only [Q2] using hparentDebt)
          hfinalityRows
    exact Or.inr ⟨J, hJ, hHJlower, by simpa only [Q2] using hfinalized⟩

/-- Candidate finality of an honest proposal becomes a common finalized prefix
at that proposal's exact confirmation duty.

The lifecycle contract gives actual store membership, not a hypothetical
propagation premise. We recover each store's accepting event, apply finality
preservation at that event, and then use finalized-root monotonicity up to the
confirmation read. -/
theorem commonFinalityAtConfirmation_of_proposedBlockCandidate
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hbot: BelowOneThird S rho.honest)
    {t0: Time} {s: Slot} {P: Block V} {h: Height}
    (hlifecycle: HonestProposalLifecycleFrom S rho t0)
    (hs: 0 < s)
    (hafter: t0 < Protocol.proposal_time S.E s)
    (hproposer: S.E.proposer s ∈ rho.honest)
    (hconfirmation: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hcheckpoint: FinalizedAt S.E S.cfg (proposedBlock S rho s) P h)
    (hpos: 0 < h) (hPne: P ≠ Block.genesis):
    ∀ v ∈ rho.honest,
      Block.Preceq P
          (rho.storeAt S v (Protocol.confirmation_time S.E s)).F ∧
        h ≤ (rho.storeAt S v
          (Protocol.confirmation_time S.E s)).finalized_height:= by
  intro v hv
  let t:= Protocol.confirmation_time S.E s
  let n:= inclusiveEventIndex rho t
  let B:= proposedBlock S rho s
  have hlive: (rho.storeAt S v t).live_confirmed = B:= by
    exact (hlifecycle s hs hafter hproposer hconfirmation).2 v hv |>.1
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v)
      (rho.storeAt S v t):=
    Proofs.Bridges.depReachable_stateAt S adm.toScheduleWellFormed
      adm.toDeliveryWellFormed t v
  have hBT: B ∈ (rho.storeAt S v t).T:= by
    have hconfirmed:=
      (Proofs.Optimistic.confirmedInTree_depReachable
        S.E S.hc S.cfg (S.node v) hdep).1
    simpa only [hlive] using hconfirmed
  have hprocessed: (Object.block B).processed
      (rho.stateBefore S n v).st = true:= by
    rw [← storeAt_eq_stateBefore_inclusiveEventIndex
      S adm.toScheduleWellFormed v t]
    simpa only [Object.processed, decide_eq_true_eq] using hBT
  have hBne: B ≠ Block.genesis:= by
    intro hgen
    have hparent:= Protocol.proposedBlock_parent S rho s
    have hgen': proposedBlock S rho s = Block.genesis:= by
      simpa only [B] using hgen
    rw [hgen'] at hparent
    change (none: Option (Block V)) =
      some (Protocol.proposedParent S rho s) at hparent
    cases hparent
  obtain ⟨i, hi, tacc, hacc⟩:=
    (Protocol.acceptsAt_block_of_processed S rho v n B hprocessed).resolve_left hBne
  have haccepted: Block.Preceq P
      (rho.stateBefore S (i + 1) v).st.F:= by
    rw [← hcheckpoint.1]
    exact acceptedBlock_candidateFinality_preceq S adm hbot hacc
  have hprefix: Block.Preceq P (rho.stateBefore S n v).st.F:=
    Block.preceq_trans haccepted
      (Protocol.stateBefore_F_mono S rho v
        (Nat.succ_le_iff.mpr hi))
  have hPF: Block.Preceq P (rho.storeAt S v t).F:= by
    rw [storeAt_eq_stateBefore_inclusiveEventIndex
      S adm.toScheduleWellFormed v t]
    exact hprefix
  refine ⟨hPF, ?_⟩
  exact finalized_height_ge_of_checkpoint_preceq
    S hdep hcheckpoint hpos hPne hPF

/-- The two selected carrier rounds yield a common finalized checkpoint. The
first branch of the phase record is already a success. The second branch
finalizes the current checkpoint on the second carrier's exact slot-`+1`
action head. -/
theorem separatedCarrierPlusTwoFinalityPhase
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    {q start source first second: Round} {C: Block V}
    (hexec: Protocol.CanonicalSuffixExecution S rho q)
    (hphase: RecurringFinalityPhaseAt
      S rho q start source first second C)
    (hsourceHeight: 1 <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot first))).h)
    (hsecondEndHor: S.a (second + 1) ≤ rho.horizon):
    AlreadyCommonFinalizedAtOrAbove S rho q source (second + 1)
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot first))).h:= by
  rcases separatedCarrierPlusTwoFinalityPhase_raw
      S adm hbot hphase with hearly | ⟨J, hJ, hHJlower, hfinalized⟩
  · exact hearly
  · have hJpos: 0 < hJ:=
      (Nat.zero_lt_of_lt hsourceHeight).trans_le hHJlower
    have hJheight: (derived_state S.E S.cfg J).h = hJ:=
      derived_height_eq_of_finalizedAt S.E S.cfg hfinalized hJpos
    have hJne: J ≠ Block.genesis:=
      finalizedCheckpoint_ne_genesis S.E S.cfg hfinalized
        (hsourceHeight.trans_le hHJlower)
    have hslotPositive: 0 < S.hc.opening_slot second + 2:=
      Nat.zero_lt_succ (S.hc.opening_slot second + 1)
    have hslotLe: S.hc.opening_slot second + 2 ≤
        S.hc.opening_slot (second + 1):= by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul,
        Nat.one_mul] using
        Nat.add_le_add_left S.hc.R_ge_two (second * S.hc.R)
    have hconfirmationUpper: Protocol.confirmation_time S.E
        (S.hc.opening_slot second + 2) ≤ S.a (second + 1):= by
      change Protocol.confirmation_time S.E
        (S.hc.opening_slot second + 2) ≤
          S.hc.a S.E.Δ (second + 1)
      rw [Protocol.a_eq_confirmation_time S.hc S.E (second + 1),
        Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact Proofs.Optimistic.support_cutoff_mono S.E
        (Nat.add_le_add_right hslotLe 1)
    have hconfirmationHor: Protocol.confirmation_time S.E
        (S.hc.opening_slot second + 2) ≤ rho.horizon:=
      hconfirmationUpper.trans hsecondEndHor
    have hlifecycle:=
      Protocol.honestProposalLifecycleFrom_of_canonicalSuffixExecution
        S adm hcom hexec
    have hnew:= commonFinalityAtConfirmation_of_proposedBlockCandidate
      S adm hbot hlifecycle hslotPositive hphase.secondAfterBoundary
        hphase.secondProposer.2.2 hconfirmationHor hfinalized hJpos hJne
    have hsourceSecond: source < second:=
      hphase.sourceLtFirst.trans hphase.firstLtSecond
    have hproposalLower: S.a source ≤ Protocol.proposal_time S.E
        (S.hc.opening_slot second + 2):= by
      exact (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
        ((Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
          S hsourceSecond).trans
            (Protocol.proposal_time_mono S.E
              (Nat.le_add_right (S.hc.opening_slot second) 2)))
    exact ⟨S.hc.opening_slot second + 2, J, hJ,
      hslotPositive, hphase.secondAfterBoundary,
      hphase.secondProposer.2.2, hfinalized, hHJlower, hJheight, hJne,
      hproposalLower,
      hproposalLower.trans
        (Protocol.proposal_time_le_confirmation_time S.E _),
      hconfirmationUpper, hnew⟩

/-- Exact finality coverage in an honest proposal yields a common actual
finalized checkpoint at that proposal's confirmation duty. -/
theorem commonFinalityAtConfirmation_of_finalityCoverage
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hbot: BelowOneThird S rho.honest)
    {t0: Time} {s: Slot} {J: Block V} {h: Height}
    (hlifecycle: HonestProposalLifecycleFrom S rho t0)
    (hs: 0 < s)
    (hafter: t0 < Protocol.proposal_time S.E s)
    (hproposer: S.E.proposer s ∈ rho.honest)
    (hconfirmation: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hcovered: FinalityQuorumCoveredByChild S.E
      (derived_state S.E S.cfg (proposedBlock S rho s).parent)
      (proposedBlock S rho s) h J)
    (hdebt:
      (derived_state S.E S.cfg (proposedBlock S rho s).parent).h_F < h)
    (hpos: 0 < h) (hJne: J ≠ Block.genesis):
    ∀ v ∈ rho.honest,
      Block.Preceq J
          (rho.storeAt S v (Protocol.confirmation_time S.E s)).F ∧
        h ≤ (rho.storeAt S v
          (Protocol.confirmation_time S.E s)).finalized_height:= by
  apply commonFinalityAtConfirmation_of_proposedBlockCandidate
    S adm hbot hlifecycle hs hafter hproposer hconfirmation
  · exact finalizedAt_of_finalityQuorumCoveredByChild
      S.E S.cfg (proposedBlock_ne_genesis S rho s) hcovered hdebt
  · exact hpos
  · exact hJne

/-- The fixed-height phase has an observable dichotomy: its finality write is
common at the exact confirmation read, or the raw frontier has escaped the
height and the bounded retry advances. -/
theorem commonFinalityAtConfirmation_or_hMaxRise
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hbot: BelowOneThird S rho.honest)
    {t0: Time} {s: Slot} {P: Block V} {h H: Height} {u: Time}
    (hlifecycle: HonestProposalLifecycleFrom S rho t0)
    (hs: 0 < s)
    (hafter: t0 < Protocol.proposal_time S.E s)
    (hproposer: S.E.proposer s ∈ rho.honest)
    (hconfirmation: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hphase:
      FinalizedAt S.E S.cfg (proposedBlock S rho s) P h ∨
        H < honestHMaxAt S rho u)
    (hpos: 0 < h) (hPne: P ≠ Block.genesis):
    (∀ v ∈ rho.honest,
        Block.Preceq P
            (rho.storeAt S v (Protocol.confirmation_time S.E s)).F ∧
          h ≤ (rho.storeAt S v
            (Protocol.confirmation_time S.E s)).finalized_height) ∨
      H < honestHMaxAt S rho u:= by
  rcases hphase with hfinalized | hrise
  · exact Or.inl
      (commonFinalityAtConfirmation_of_proposedBlockCandidate
        S adm hbot hlifecycle hs hafter hproposer hconfirmation
          hfinalized hpos hPne)
  · exact Or.inr hrise

/-- The successful arm of the separated two-opening trace is an actual common
finality advance at the selected second opening's confirmation/action
boundary. -/
theorem commonFinalityAdvance_or_hMaxRise_of_separatedTwoOpeningPhase
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho) (hbot: BelowOneThird S rho.honest)
    {q source first second: Round} {H: Height}
    (hlifecycle: HonestProposalLifecycleFrom S rho
      (healingBoundaryTime S q))
    (hafterSecond: healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot second))
    (hproposerSecond: S.E.proposer (S.hc.opening_slot second) ∈
      rho.honest)
    (hsourceLtSecond: source < second)
    (hH: 1 < H)
    (hhorSecond: S.a second ≤ rho.horizon)
    (hphase:
      (∃ (J: Block V) (h': Height),
          H ≤ h' ∧
          FinalizedAt S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot second)) J h' ∧
          (derived_state S.E S.cfg J).h = h' ∧
          J ≠ Block.genesis) ∨
        (H < honestHMaxAt S rho
            (Protocol.proposal_time S.E
              (S.hc.opening_slot first)) ∨
         H + 1 < honestHMaxAt S rho
            (Protocol.proposal_time S.E
              (S.hc.opening_slot second)))):
    (∃ (J: Block V) (h': Height),
        H ≤ h' ∧
        FinalizedAt S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot second)) J h' ∧
        (derived_state S.E S.cfg J).h = h' ∧
        S.a source ≤ Protocol.confirmation_time S.E
          (S.hc.opening_slot second) ∧
        Protocol.confirmation_time S.E
            (S.hc.opening_slot second) = S.a second ∧
        ∀ v ∈ rho.honest,
          Block.Preceq J
              (rho.storeAt S v
                (Protocol.confirmation_time S.E
                  (S.hc.opening_slot second))).F ∧
            h' ≤ (rho.storeAt S v
              (Protocol.confirmation_time S.E
                (S.hc.opening_slot second))).finalized_height) ∨
      (H < honestHMaxAt S rho
          (Protocol.proposal_time S.E
            (S.hc.opening_slot first)) ∨
       H + 1 < honestHMaxAt S rho
          (Protocol.proposal_time S.E
            (S.hc.opening_slot second))):= by
  rcases hphase with ⟨J, h', hlower, hfinalized, hJheight, hJne⟩ | hrise
  · left
    have hspos: 0 < S.hc.opening_slot second:= by
      simp only [Protocol.HealConfig.opening_slot]
      exact Nat.mul_pos
        (lt_of_le_of_lt (Nat.zero_le source) hsourceLtSecond)
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    have hconfirmation: Protocol.confirmation_time S.E
        (S.hc.opening_slot second) ≤ rho.horizon:= by
      rw [← Protocol.a_eq_confirmation_time S.hc S.E second]
      exact hhorSecond
    refine ⟨J, h', hlower, hfinalized, hJheight, ?_, ?_, ?_⟩
    · rw [← Protocol.a_eq_confirmation_time S.hc S.E second]
      exact Assembly.a_mono S (Nat.le_of_lt hsourceLtSecond)
    · exact (Protocol.a_eq_confirmation_time S.hc S.E second).symm
    · exact commonFinalityAtConfirmation_of_proposedBlockCandidate
        S adm hbot hlifecycle hspos hafterSecond hproposerSecond
          hconfirmation hfinalized
          ((Nat.zero_lt_of_lt hH).trans_le hlower) hJne
  · exact Or.inr hrise

/-- The exact recurring-finality witness also records that its checkpoint lies
strictly above the honest raw frontier at the starting action. The selected
source, first, and second rounds can be separated by arbitrary positive gaps. -/
theorem recurringFinalityWitnessAboveHMax_of_phaseCarrier
    (S: Setup V) (rawLag recurrenceGap: Round)
    {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    {q: Round}
    (hexec: Protocol.CanonicalSuffixExecution S rho q)
    (hraw: RecurringFinalityPhaseCarrierFrom S rho q
      (recurringFinalityOneHeightLag S rawLag recurrenceGap)):
    ∀ (r: Round) (B: Block V) (h: Height), q ≤ r →
      (∀ v ∈ rho.honest,
        Block.Preceq B (rho.storeAt S v (S.a r)).F ∧
          h ≤ (rho.storeAt S v (S.a r)).finalized_height) →
      S.a (r + recurringFinalityDeadline
        S rawLag recurrenceGap (h + 1)) ≤ rho.horizon →
        ∃ (s: Slot) (P: Block V) (h': Height),
          0 < s ∧
            healingBoundaryTime S q < Protocol.proposal_time S.E s ∧
            S.E.proposer s ∈ rho.honest ∧
            Protocol.confirmation_time S.E s ≤ rho.horizon ∧
            FinalizedAt S.E S.cfg (proposedBlock S rho s) P h' ∧
            Block.Preceq B P ∧
            h < h' ∧
            (derived_state S.E S.cfg P).h = h' ∧
            S.a r ≤ Protocol.proposal_time S.E s ∧
            S.a r ≤ Protocol.confirmation_time S.E s ∧
            Protocol.confirmation_time S.E s ≤
              S.a (r + recurringFinalityDeadline
                S rawLag recurrenceGap (h + 1)) ∧
            honestHMaxAt S rho (S.a r) < h' ∧
            ∀ v ∈ rho.honest,
              Block.Preceq P
                  (rho.storeAt S v
                    (Protocol.confirmation_time S.E s)).F ∧
                h' ≤ (rho.storeAt S v
                  (Protocol.confirmation_time S.E s)).finalized_height:= by
  let lag:= recurringFinalityOneHeightLag S rawLag recurrenceGap
  intro r B h hqr hcommon hdeadlineHor
  have hlagDeadline: lag ≤
      recurringFinalityDeadline S rawLag recurrenceGap (h + 1):= by
    exact recurringFinalityOneHeightLag_le_deadline
      S rawLag recurrenceGap (h + 1)
  have hlagRound:
      r + lag ≤ r +
        recurringFinalityDeadline S rawLag recurrenceGap (h + 1):=
    Nat.add_le_add_left hlagDeadline r
  have hlagHor: S.a (r + lag) ≤ rho.horizon:=
    (Assembly.a_mono S hlagRound).trans hdeadlineHor
  obtain ⟨source, first, second, C, hrsource, hsourceFirst,
      hfirstSecond, hsecondEnd, hphase⟩:=
    hraw.2 r hqr hlagHor
  let sourceHeight:= (derived_state S.E S.cfg
    (proposedBlock S rho (S.hc.opening_slot first))).h
  have hheightFrontier:
      h < honestHMaxAt S rho (S.a r):=
    commonFinalizedHeight_lt_honestHMaxAt S adm hbot
      (fun v hv => (hcommon v hv).2)
  have hfrontierPositive:
      0 < honestHMaxAt S rho (S.a r):=
    lt_of_le_of_lt (Nat.zero_le h) hheightFrontier
  have hsourceAboveOne: 1 < sourceHeight:=
    (Nat.succ_le_iff.mpr hfrontierPositive).trans_lt hphase.sourceAbove
  have hsecondEndHor: S.a (second + 1) ≤ rho.horizon:=
    (Assembly.a_mono S hsecondEnd).trans hlagHor
  have hkernel:= separatedCarrierPlusTwoFinalityPhase
    S adm hcom hbot hexec hphase hsourceAboveOne hsecondEndHor
  obtain ⟨s, J, h', hslotPositive, hafter, hproposer,
    hfinalized, hsourceLower, hJheight, -, hproposalFromSource,
    hconfirmationFromSource, hconfirmationEnd, hnew⟩:= hkernel
  have hconfirmationHor: Protocol.confirmation_time S.E s ≤ rho.horizon:=
    hconfirmationEnd.trans hsecondEndHor
  have hBheight:
      (derived_state S.E S.cfg B).h ≤
        honestHMaxAt S rho (S.a r):=
    commonFinalizedBlock_height_le_honestHMaxAt
      S adm hbot (fun v hv => (hcommon v hv).1)
  have hquorum:=
    AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot
  obtain ⟨v, -, hv⟩:=
    AlignedRoundLemmas.honest_member_of_quorum hbot hquorum
  have hstartHor: S.a r ≤ rho.horizon:=
    (Assembly.a_mono S (Nat.le_add_right r lag)).trans hlagHor
  have hfrontierAdvance:
      honestHMaxAt S rho (S.a r) <
        (derived_state S.E S.cfg J).h:= by
    rw [hJheight]
    exact hphase.sourceAbove.trans_le hsourceLower
  have hBJ: Block.Preceq B J:=
    preceq_of_commonFinalityAdvance S
      (wholeRunFinalitySafety_of_belowOneThird S adm.toAdmissibleCore hbot)
      hv hv hstartHor hconfirmationHor
      (hcommon v hv).1 (hnew v hv).1 hBheight hfrontierAdvance
  have hheightAdvance: h < h':=
    (hheightFrontier.trans hphase.sourceAbove).trans_le hsourceLower
  have hproposalLower: S.a r ≤ Protocol.proposal_time S.E s:=
    (Assembly.a_mono S hrsource).trans hproposalFromSource
  have hconfirmationLower: S.a r ≤ Protocol.confirmation_time S.E s:=
    (Assembly.a_mono S hrsource).trans hconfirmationFromSource
  have hconfirmationDeadline: Protocol.confirmation_time S.E s ≤
        S.a (r + recurringFinalityDeadline
          S rawLag recurrenceGap (h + 1)):= by
    exact hconfirmationEnd.trans
      ((Assembly.a_mono S hsecondEnd).trans
        (Assembly.a_mono S hlagRound))
  exact ⟨s, J, h',
    hslotPositive, hafter, hproposer,
    hconfirmationHor, hfinalized, hBJ, hheightAdvance, hJheight,
    hproposalLower, hconfirmationLower, hconfirmationDeadline,
    hfrontierAdvance.trans_le hJheight.le, hnew⟩

/-- Forgetting the raw-frontier comparison preserves the stable exact-carrier
surface. -/
theorem recurringFinalityCarrierFrom_of_phaseCarrier
    (S: Setup V) (rawLag recurrenceGap: Round)
    {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    {q: Round}
    (hexec: Protocol.CanonicalSuffixExecution S rho q)
    (hraw: RecurringFinalityPhaseCarrierFrom S rho q
      (recurringFinalityOneHeightLag S rawLag recurrenceGap)):
    RecurringFinalityCarrierFrom S rho q (healingBoundaryTime S q)
      (recurringFinalityDeadline S rawLag recurrenceGap):= by
  intro r B h hqr hcommon hdeadlineHor
  obtain ⟨s, P, h', hs, hafter, hproposer, hconfirmationHor,
    hfinalized, hBP, hheightAdvance, hPheight, hproposalLower,
    hconfirmationLower, hconfirmationDeadline, -, hnew⟩:=
    recurringFinalityWitnessAboveHMax_of_phaseCarrier
      S rawLag recurrenceGap
        adm hcom hbot hexec hraw r B h hqr hcommon hdeadlineHor
  exact ⟨s, P, h', hs, hafter, hproposer, hconfirmationHor,
    hfinalized, hBP, hheightAdvance, hPheight, hproposalLower,
    hconfirmationLower, hconfirmationDeadline, hnew⟩

/-- Erasing the exact proposal carrier gives the declarative recurring-finality
surface at the same setup-dependent deadline. -/
theorem recurringFinalityFrom_of_phaseCarrier
    (S: Setup V) (rawLag recurrenceGap: Round)
    {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    {q: Round}
    (hexec: Protocol.CanonicalSuffixExecution S rho q)
    (hraw: RecurringFinalityPhaseCarrierFrom S rho q
      (recurringFinalityOneHeightLag S rawLag recurrenceGap)):
    RecurringFinalityFrom S rho q
      (recurringFinalityDeadline S rawLag recurrenceGap):=
  (recurringFinalityCarrierFrom_of_phaseCarrier
    S rawLag recurrenceGap
    adm hcom hbot hexec hraw).toRecurringFinalityFrom

-/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
