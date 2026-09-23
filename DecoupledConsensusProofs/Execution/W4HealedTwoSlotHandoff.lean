module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.FGSafetyProgressDeadline
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalAdoptionNamedClosed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.SGLifetimeNamed
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryConeConfirmation
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFinalityFilterRetainedAdoption
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainBatch
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainRoundRead
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGSafetyFrozenHeadNamed
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Execution.W4HandoffStructures

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The healed two-slot handoff at a post-deadline carrier ( h2)

earlier's `healedTwoSlotHandoff_of_carrier_after_GST`
(`PostSafetyHandoffRun.lean:119`) builds
`Protocol.HealedTwoSlotHandoff S rho q D carrier` at a post-deadline
honest carrier and is the second residual of the corresponding branch's `hrecords`.

This leaf lands the timing half of the residual — the `hbaseTiming`
conjunction that every one of the three moving-chain record theorems takes
beside the handoff — and records, from an actual proof attempt, why the
handoff record itself is not producible in its pinned form.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- Verbatim copy of the private `round_of_mono'`
(`MovingChainExecutionRun.lean:140`). -/
private theorem w4_round_of_mono
    (hc : Protocol.HealConfig) {a b : Slot} (hab : a ≤ b) :
    hc.round_of a ≤ hc.round_of b :=
  Nat.div_le_div_right hab

/-- Verbatim copy of the private `round_of_opening_add_three_le_succ`
(`MovingChainExecutionRun.lean:117`). -/
private theorem w4_round_of_opening_add_three_le_succ
    (hc : Protocol.HealConfig) (q : Round) :
    hc.round_of (hc.opening_slot q + 3) ≤ q + 1 := by
  have hRpos : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  rw [show q * hc.R + 3 = 3 + hc.R * q by ring,
    Nat.add_mul_div_left _ _ hRpos]
  have hdiv : 3 / hc.R ≤ 1 := by
    have hlt : 3 / hc.R < 2 := by
      rw [Nat.div_lt_iff_lt_mul hRpos]
      exact lt_of_lt_of_le (by decide : 3 < 4)
        (by simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_left 2 hc.R_ge_two)
    exact Nat.le_of_lt_succ hlt
  simpa only [Nat.add_comm] using Nat.add_le_add_left hdiv q

/-- The fold's base round lies in `{q, q + 1}`: it is at least `q` because the
opening slot itself names `q`, and at most `q + 1` because three slots cannot
carry the schedule two rounds forward when `R ≥ 2`. -/
theorem w4_handoffBaseRound_bounds (S : Setup V) (q : Round) :
    q ≤ S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.hc.round_of (S.hc.opening_slot q + 3) ≤ q + 1 := by
  refine ⟨?_, w4_round_of_opening_add_three_le_succ S.hc q⟩
  have hmono := w4_round_of_mono S.hc
    (Nat.le_add_right (S.hc.opening_slot q) 3)
  rwa [round_of_opening_slot_eq_schedule S.hc q] at hmono

#print axioms w4_handoffBaseRound_bounds

/-- **The `hbaseTiming` conjunction at a post-deadline carrier.**

`movingSlotFoldAt_of_handoff` and both moving-chain record theorems
(`MovingChainExecutionRun.lean:1354,1404,1837,1943`) take exactly this triple
beside the two-slot handoff. It is pure schedule arithmetic: the fold's base
round is `q` or `q + 1`, so its predecessor is at least `q - 1`, which the
post-deadline bound puts at or after `rGST`.

The third conjunct is the caller's horizon premise, carried so that the
conclusion is literally the conjunction the consumers name. -/
theorem w4_handoffBaseTiming_after_GST
    (S : Setup V) {rho : Run V}
    {rGST gap : Round} (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
      rho.horizon) :
    0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon := by
  have hGSTdead : rGST ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hlow := (w4_handoffBaseRound_bounds S q).1
  have hqpos : 3 ≤ q := (Nat.le_add_left 3 _).trans hq
  have hrGSTq : rGST + 3 ≤ q :=
    (Nat.add_le_add_right hGSTdead 3).trans hq
  have hbase : rGST + 1 ≤ S.hc.round_of (S.hc.opening_slot q + 3) :=
    (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 3) rGST).trans
      (hrGSTq.trans hlow)
  have hpred : rGST ≤ S.hc.round_of (S.hc.opening_slot q + 3) - 1 :=
    Nat.le_sub_of_add_le hbase
  refine ⟨?_, ?_, hhor⟩
  · exact Nat.lt_of_lt_of_le (by decide : 0 < 3) (hqpos.trans hlow)
  · exact hpost.trans ((action_strictMono S).monotone hpred)

#print axioms w4_handoffBaseTiming_after_GST








/-- **The twin discharges `_of_preparedBoundaryOutput`.**

Both live record theorems (`MovingChainHandoffExportsRun.lean:1196,1769`)
carry that pin beside the handoff, reading the cache at the round action
`S.a q`. The twin's opening arm is literally it: `S.a q` and
`Protocol.confirmation_time S.E (S.hc.opening_slot q)` are the same time by
`Protocol.a_eq_confirmation_time` (`Schedule.lean:153`, `rfl`), so the two
prepared caches are the same read. This closes one of the five named
obligations the corresponding branch lists under residual item 6. -/
theorem HealedTwoSlotHandoffPrepared.preparedBoundaryOutput
    {S : Setup V} {rho : Run V}
    {q : Round} {B : Block V} {carrier : V}
    (h : HealedTwoSlotHandoffPrepared S rho q B carrier)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤
      rho.horizon) :
    ∀ u ∈ rho.honest,
      GenuineConfirmationWith
          (NamedProfile.gradeContract
            (NamedActionReads.confirmationReadAt S rho u (S.a q)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho u (S.hc.opening_slot q))
          (S.hc.opening_slot q)
          (movingSlotConfirmationOutput S rho (S.hc.opening_slot q) u) ∧
        Block.Preceq
          (movingSlotConfirmationOutput S rho (S.hc.opening_slot q) u) B := by
  intro u hu
  exact h.boundary_outputs (S.hc.opening_slot q) (Or.inl rfl) u hu hhor

#print axioms HealedTwoSlotHandoffPrepared.preparedBoundaryOutput

/-! ## Producing the twin at a post-deadline carrier -/

/-- Schedule facts at a post-deadline carrier's opening slot. -/
private theorem w4_openingSlot_pos (S : Setup V) {q : Round} (hq : 2 ≤ q) :
    0 < S.hc.opening_slot q :=
  Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_two hq)
    (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)

/-- Two rounds of schedule separate a deadline opening from a later opening. -/
private theorem w4_openingSlot_two_after (S : Setup V) {d m : Round}
    (hdm : d + 1 ≤ m) :
    S.hc.opening_slot d + 2 ≤ S.hc.opening_slot m := by
  have hstep : S.hc.opening_slot d + 2 ≤ S.hc.opening_slot (d + 1) := by
    simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left S.hc.R_ge_two (d * S.hc.R)
  exact hstep.trans (Nat.mul_le_mul_right S.hc.R hdm)

/-- **The opening arm of the twin's boundary outputs.**

At a post-deadline carrier every honest opening evaluation is genuine under
that node's own prepared contract, and its output lies below the endpoint of
the next slot. The endpoint is supplied by the one general-slot named fact the
carrier regime still lacks, the honest head equality at `opening q + 1`
(`hheadsSucc`), which is earlier's `honestProposal_voteDutyHead_eq_after_SG_healing`
(`ProposalAdoptionSafetyRun.lean:161`, red) read at that slot.

Genuineness is `genuineConfirmationAndPreceq_of_postHealingCone_all_honest`
over the opening vote cone; the order to the endpoint is
`genuineConfirmationWith_preceq_laterVoterHeads_after_GST` at `c = q - 2`,
which is exactly what the `deadline + 3 ≤ q` window buys. -/
theorem w4_openingBoundaryOutput_of_headsSucc
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hcarrier : ProposerCarrierAt S rho q)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q + 1) ≤
      rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    {D : Block V}
    (hheadsSucc : ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot q + 1) = D) :
    ∀ v ∈ rho.honest,
      GenuineConfirmationWith
          (NamedProfile.gradeContract
            (confirmationInputRead S rho v (S.hc.opening_slot q)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
          (S.hc.opening_slot q)
          (movingSlotConfirmationOutput S rho (S.hc.opening_slot q) v) ∧
        Block.Preceq
          (movingSlotConfirmationOutput S rho (S.hc.opening_slot q) v) D := by
  classical
  set Dl := fgSafetyProgressDeadline S rho rGST gap delayExtra with hDl
  set start := S.hc.opening_slot q with hstart
  have hm : Dl + 2 ≤ q := (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) Dl).trans hq
  have hqPos : 2 ≤ q := (Nat.le_add_left 2 Dl).trans hm
  have hstartPos : 0 < start := w4_openingSlot_pos S hqPos
  -- horizons
  have hconf0 : Protocol.confirmation_time S.E start ≤ rho.horizon :=
    (Int.add_le_add_right (proposal_time_mono S.E (Nat.le_succ start)) _).trans hhor
  have hvote0 : Protocol.vote_time S.E start ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E start).trans hconf0
  have hproposal0 : Protocol.proposal_time S.E start ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E start).le.trans hvote0
  have hvoteDelta : Protocol.vote_time S.E start + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E start).trans hconf0
  have hvote1 : Protocol.vote_time S.E (start + 1) ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E (start + 1)).trans hhor
  -- deadline geometry
  have hdlq : Dl + 1 ≤ q := Nat.le_of_succ_le hm
  have hdeadlineSlot : S.hc.opening_slot Dl + 1 ≤ start :=
    Nat.le_of_succ_le (w4_openingSlot_two_after S hdlq)
  have hdeadlineProposal : S.a Dl ≤ Protocol.proposal_time S.E start :=
    (action_lt_proposal_time_two_after S Dl).le.trans
      (proposal_time_mono S.E (w4_openingSlot_two_after S hdlq))
  have hdeadlineVote : S.a Dl ≤ Protocol.vote_time S.E start :=
    hdeadlineProposal.trans (proposal_time_lt_vote_time S.E start).le
  have hdeadlineRead : S.a Dl ≤ Protocol.confirmation_time S.E start :=
    hdeadlineVote.trans (vote_time_le_confirmation_time S.E start)
  have hGSTdead : rGST ≤ Dl := by
    rw [hDl]
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hpostProposal : S.E.t_GST ≤ Protocol.proposal_time S.E start :=
    hpost.trans (((action_strictMono S).monotone hGSTdead).trans hdeadlineProposal)
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E start :=
    hpostProposal.trans (proposal_time_lt_vote_time S.E start).le
  -- the three live named exports at the carrier's opening slot
  have hheads0 : ∀ v ∈ rho.honest, voterHeadAt S rho v start = P.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named
      S adm hcom hbelow hrec hdelay hpost hm hvote0 hcarrier hP
  have hcone : NamedHonestVotesCone S rho start (fun X => Block.Preceq P.erase X) :=
    honestProposal_openingVoteCone_after_SG_healing_named
      S adm hcom hm hcarrier hvote0 hP hheads0
  have hfacts := honestProposal_confirmationReadFacts_after_SG_healing_named
    S adm hcom hbelow hrec hdelay hpost hm hconf0 hcarrier hP
  -- each reader's own fork-choice root is below the opening proposal
  have hroot : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho v start).st.core.toHealing.toFG)
        P.erase := by
    intro v hv
    have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hconf0
        hdeadlineSlot (le_refl _) hvoteDelta hv hv
    have hrootHead' : Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho v start).st.core.toHealing.toFG)
        (voterHeadAt S rho v start) := by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    simpa only [hheads0 v hv] using hrootHead'
  have hlocal : ∀ v ∈ rho.honest,
      Block.Preceq
          (Protocol.get_fg_root
            (confirmationInputRead S rho v start).st.core.toHealing.toFG)
          P.erase ∧
        Block.Preceq
          (namedConfirmationAnchor S (confirmationInputRead S rho v start))
          P.erase ∧
        P.erase ∈ confTree (confirmationInputRead S rho v start).st.core :=
    fun v hv => ⟨hroot v hv, (hfacts v hv).1, (hfacts v hv).2⟩
  have hgen := genuineConfirmationAndPreceq_of_postHealingCone_all_honest
    S adm hcom hstartPos hpostVote hconf0 hcone hlocal
  -- the later-heads bound at c = q - 2
  have hc : Dl + 1 ≤ q - 2 :=
    Nat.le_sub_of_add_le (show Dl + 1 + 2 ≤ q from hq)
  have hqOne : 1 ≤ q := (by decide : (1 : Nat) ≤ 2).trans hqPos
  have hqPredOne : 1 ≤ q - 1 :=
    Nat.le_sub_of_add_le (show 1 + 1 ≤ q from hqPos)
  have hcSucc : q - 2 + 1 = q - 1 := by
    simpa only [Nat.sub_sub, Nat.add_comm, Nat.reduceAdd] using
      Nat.sub_add_cancel hqPredOne
  have hsucc : S.hc.opening_slot (q - 2 + 1) + 1 ≤ start := by
    rw [hcSucc, hstart]
    exact Nat.le_of_succ_le
      (w4_openingSlot_two_after S (Nat.sub_add_cancel hqOne).le)
  intro v hv
  obtain ⟨hgenuine, -⟩ := hgen v hv
  refine ⟨hgenuine, ?_⟩
  have hlater := genuineConfirmationWith_preceq_laterVoterHeads_after_GST
    S adm hcom hbelow hrec hdelay hpost hc hsucc hconf0 hv hgenuine
    (start + 1) (le_refl _) hvote1 v hv
  simpa only [hheadsSucc v hv] using hlater

#print axioms w4_openingBoundaryOutput_of_headsSucc

/-- **The prepared selection at any post-deadline slot, from the named head
and confirmation-read facts.**

This is P7a's route (`ProposalConfirmationPreparedLiveNamedRun.lean:18`) with
the carrier's opening slot generalised away: every ingredient it uses below
the three opening-slot exports is already general-slot. The honest vote names
come from the head equality, the reader's own fork-choice root from
`fgRoot_preceq_previousHead_through_confirmation_after_GST`, and the walk
equality from `confWalkWith_eq_of_support`. Unlike P7a it also returns the
genuineness, which is the second component `confWalkWith_eq_of_support`
already hands back. -/
theorem w4_preparedGenuineSelection_of_namedFacts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {s : Slot}
    (hs : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 2 ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {P : NamedBlock V} (hrun : RunBlock S rho P)
    (hheads : ∀ v ∈ rho.honest, voterHeadAt S rho v s = P.erase)
    (hreads : ∀ v ∈ rho.honest,
      Block.Preceq
          (namedConfirmationAnchor S (confirmationInputRead S rho v s))
          P.erase ∧
        P.erase ∈ confTree (confirmationInputRead S rho v s).st.core) :
    ∀ v ∈ rho.honest,
      GenuineConfirmationWith
        (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v s) s P.erase := by
  classical
  set Dl := fgSafetyProgressDeadline S rho rGST gap delayExtra with hDl
  have hs1 : S.hc.opening_slot Dl + 1 ≤ s := Nat.le_of_succ_le hs
  have hspos : 0 < s :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2)
      ((Nat.le_add_left 2 (S.hc.opening_slot Dl)).trans hs)
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hhor
  have hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E s).le.trans hvoteHor
  have hvoteDelta : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E s).trans hhor
  have hdeadlineProposal : S.a Dl ≤ Protocol.proposal_time S.E s :=
    (action_lt_proposal_time_two_after S Dl).le.trans (proposal_time_mono S.E hs)
  have hdeadlineVote : S.a Dl ≤ Protocol.vote_time S.E s :=
    hdeadlineProposal.trans (proposal_time_lt_vote_time S.E s).le
  have hdeadlineRead : S.a Dl ≤ Protocol.confirmation_time S.E s :=
    hdeadlineVote.trans (vote_time_le_confirmation_time S.E s)
  have hGSTdead : rGST ≤ Dl := by
    rw [hDl]
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
    hpost.trans (((action_strictMono S).monotone hGSTdead).trans hdeadlineVote)
  have hnames : NamedHonestVotesName S rho s P.erase := by
    apply honestVotesName_of_exactCone S rho s P.erase
    intro w hw hcommittee
    obtain ⟨X, hXhead, hXrun, hXemit⟩ :=
      voteDutyHead_runBlock_and_emits S adm hspos hvoteHor hw hcommittee
    exact ⟨X, by simpa only [hXhead] using hheads w hw, hXrun, hXemit⟩
  have hroot : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho v s).st.core.toHealing.toFG) P.erase := by
    intro v hv
    have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor hs1 (le_refl _)
        hvoteDelta hv hv
    have hrootHead' : Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho v s).st.core.toHealing.toFG)
        (voterHeadAt S rho v s) := by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    simpa only [hheads v hv] using hrootHead'
  intro v hv
  have hsupport := honestSupport_confVotes_after_gst_of_names
    S adm hcom hspos hpostVote hhor hrun hnames hv (hroot v hv) (hreads v hv).2
  have hvalid : Protocol.VoteSetValid S.E s
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) := by
    simpa only [confStore, tickStore] using
      voteSetValid_confLate_stateBeforeTime S adm.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E s) s
  have hcandidate : P.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s) := by
    simpa only [confStore_eq_confirmationInputRead] using (hreads v hv).2
  have hanchor' : Block.Preceq
      (confAnchorWith
        (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v s)) P.erase := by
    simpa only [confAnchorWith, namedConfirmationAnchor,
      confStore_eq_confirmationInputRead] using (hreads v hv).1
  have hpath : ∀ C : Block V,
      Block.Preceq
          (confAnchorWith
            (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
            S.E S.hc (Proofs.Optimistic.confStore S rho v s)) C →
      C ≠ confAnchorWith
          (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho v s) →
      Block.Preceq C P.erase → C ∈ confTree (Proofs.Optimistic.confStore S rho v s) := by
    have hpath' := confPath_of_candidate S hcandidate
    simpa only [confAnchorWith, namedConfirmationAnchor,
      confStore_eq_confirmationInputRead] using hpath'
  obtain ⟨hwalk, helig⟩ := confWalkWith_eq_of_support
    (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
    S.E S.hc (Proofs.Optimistic.confStore S rho v s) s rho.honest P.erase
      (by simpa only [confStore_eq_confirmationInputRead, confVotes,
        confirmationVotes] using hsupport) hvalid hanchor' hpath
  refine ⟨?_, ?_⟩
  · rw [update_confirmation_with_live_confirmed, hwalk, if_pos helig]
  · rw [hwalk]
    exact helig

#print axioms w4_preparedGenuineSelection_of_namedFacts

/-- The degenerate branch of the frozen-candidate producer, closed positively.

When the endpoint sits at or below the reader's own fork-choice root, the root
bound makes it EQUAL to that root, and the reader's frozen candidate tree then
contains it: it is processed, the finalized record is below it through the
root, and the viability band is the frontier cap in its debt form, since the
reader's own `h_max` is at most the honest supremum. -/
private theorem w4_rootCase_candidate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest)
    {s : Slot} {Dn : NamedBlock V} (hrunD : RunBlock S rho Dn)
    (hmem : Dn.erase ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).T)
    (hproc : Dn.erase ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore (s + 1))
    (hcap : honestHMaxBeforeIndex S rho
        (strictEventIndex rho (Protocol.vote_time S.E (s + 1))) ≤
      (Protocol.derive_named S.E S.cfg Dn).h + 1)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) Dn.erase)
    (_hle : Block.Preceq Dn.erase
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)) :
    Dn.erase ∈ voter_candidate_tree S.E
      (voteDutyRead S rho w (s + 1)).st.core.toHealing := by
  classical
  have hbodies : Dn ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).bodies :=
    mem_bodies_of_mem_T S adm hw hrunD (by
      simpa only [Run.storeBeforeTime] using hmem)
  have hsigma := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
    (Protocol.vote_time S.E (s + 1)) w Dn (by
      simpa only [Run.storeBeforeTime] using hbodies)
  have hmaxLe : (rho.stateBefore S
      (strictEventIndex rho (Protocol.vote_time S.E (s + 1))) w).st.h_max ≤
      honestHMaxBeforeIndex S rho
        (strictEventIndex rho (Protocol.vote_time S.E (s + 1))) := by
    have h := Finset.le_sup (s := rho.honest) (f := fun v : V =>
      (rho.stateBefore S
        (strictEventIndex rho (Protocol.vote_time S.E (s + 1))) v).st.h_max) hw
    simpa only [honestHMaxBeforeIndex] using h
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (Protocol.vote_time S.E (s + 1)) w
  have hF : Block.Preceq
      (voteDutyRead S rho w (s + 1)).st.core.F Dn.erase := by
    refine Block.preceq_trans ?_ hroot
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      (Proofs.Records.preceq_get_fg_root_of_F
        (st := (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (s + 1))).core.toHealing.toFG) hFJ)
  have hband : (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
      ((voteDutyRead S rho w (s + 1)).st.core.σ Dn.erase).h := by
    have hmaxRead : (voteDutyRead S rho w (s + 1)).st.core.h_max ≤
        (Protocol.derive_named S.E S.cfg Dn).h + 1 := by
      refine le_trans ?_ (le_trans hmaxLe hcap)
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed w]
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using (le_refl _)
    have hsigmaRead : (voteDutyRead S rho w (s + 1)).st.core.σ Dn.erase =
        Protocol.derive_named S.E S.cfg Dn := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hsigma
    rw [hsigmaRead]
    exact Nat.sub_le_iff_le_add.mpr hmaxRead
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
  have hslot : (voteDutyRead S rho w (s + 1)).st.core.toHealing.s = s + 1 := by
    simpa only [Protocol.Store.toHealing] using voteDutyRead_slot S rho w (s + 1)
  rw [hslot]
  exact ⟨⟨⟨hproc, hF⟩, Dn.erase, hproc, Block.preceq_self _, hband⟩, hroot⟩


/-- **The prepared next-vote adoption record at an honest proposal slot**
( gs, deliverable 4's assembly).

The endpoint `D` is every honest head at slot `s`, so it reaches every honest
slot-`(s + 1)` vote duty. The constructor is
`nextVoteAdoption_of_frozenCandidateAtRead_compatibleAnchor`; its anchor input
is the live general-slot
`nextVoteDutyAnchor_compatible_of_honestPreviousHead_after_SG_healing_named`
at compatibility strength, and its frozen-candidate input is routed through the
slot-`s` honest vote cone: `honestHeadsAvailableBefore_of_postHealingCone_at`
then `storeBeforeTime_mem_stamp_of_cone`, whose stamp at the support cutoff
carries to the view freeze and so puts `D` in the reader's processed tree, and
then `honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_named`.

That last producer returns a disjunction, and its degenerate branch is closed
positively rather than out: there the endpoint is at or below the
reader's own fork-choice root, so with the root bound it IS that root, and the
candidate tree then wants three things of it. Processed it already is; the
finalized record sits below it through the root; and the viability band is the
frontier cap in its debt form, since the reader's own `h_max` is at most the
honest supremum. That cap is the single remaining input, taken in the
conclusion shape of the corresponding branch's
`w4HonestFrontier_le_succ_of_heightGates`
(`HealingSurface/W4HeightSourceHistoryRun`, 790467df), so the spine feeds both
records from one place. -/
theorem w4_adoptionAt_slot_of_frontierCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {s : Slot}
    (hs : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ s)
    (hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s)
    {Dn : NamedBlock V} (hrunD : RunBlock S rho Dn)
    (hheads : ∀ v ∈ rho.honest, voterHeadAt S rho v s = Dn.erase)
    (hcone : NamedHonestVotesCone S rho s (fun X => Block.Preceq Dn.erase X))
    {carrier : V} (hcarrierHon : carrier ∈ rho.honest)
    {w : V} (hw : w ∈ rho.honest)
    (_of_frontierCap : honestHMaxBeforeIndex S rho
        (strictEventIndex rho (Protocol.vote_time S.E (s + 1))) ≤
      (Protocol.derive_named S.E S.cfg Dn).h + 1)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) Dn.erase) :
    Protocol.NamedNextVoteAdoption S rho
      (Proofs.Optimistic.confStore S rho carrier s) s Dn.erase w := by
  have hcutGamma : Protocol.support_cutoff S.E s ≤
      Protocol.vote_time S.E (s + 1) :=
    support_cutoff_le_vote_time_succ S.E s
  have havail : HonestHeadsAvailableBefore S rho s w
      (Protocol.support_cutoff S.E s) :=
    honestHeadsAvailableBefore_of_postHealingCone_at S adm.toNamedAdmissibleCore
      hw hpostVote hcutHor hcutGamma (by
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hroot) hcone
  obtain ⟨hmem, hstamp⟩ := storeBeforeTime_mem_stamp_of_cone S adm hcom
    havail hcutGamma hcone (Block.preceq_self Dn.erase)
  have hanchor := nextVoteDutyAnchor_compatible_of_honestPreviousHead_after_SG_healing_named
    S adm hcom hbelow hrec hdelay hpost hs hvoteHor hw hw
    (show Block.Preceq Dn.erase (voterHeadAt S rho w s) from by
      rw [hheads w hw]
      exact Block.preceq_self Dn.erase)
  have hstampFreeze : stampedBefore
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).timestamp_block
      (Protocol.view_freeze S.E s) Dn.erase = true := by
    rw [stampedBefore_eq_occurrenceBefore] at hstamp ⊢
    exact occurrenceBefore_mono
      (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)) hstamp
  have hproc : Dn.erase ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore (s + 1) := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨?_, Or.inl ?_⟩
    · simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.Store.toHealing] using hmem
    · simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.Store.toHealing, Nat.add_sub_cancel] using hstampFreeze
  have hsDead : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s := by
    refine Nat.le_trans ?_ hs
    have hstep : S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 2 ≤
        S.hc.opening_slot
          (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) := by
      simp only [Protocol.HealConfig.opening_slot, Nat.add_mul]
      have := S.hc.R_ge_two
      calc fgSafetyProgressDeadline S rho rGST gap delayExtra * S.hc.R + 2
          ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra * S.hc.R
            + 2 * S.hc.R := Nat.add_le_add_left (by
              simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_right 2
                (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) _
        _ = _ := rfl
    exact Nat.le_of_succ_le hstep
  have hcandidate : Dn.erase ∈ voter_candidate_tree S.E
      (voteDutyRead S rho w (s + 1)).st.core.toHealing := by
    rcases honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_named
        S adm hcom hbelow hrec hdelay hpost hsDead hvoteHor hw hw
        (show Block.Preceq Dn.erase (voterHeadAt S rho w s) from by
          rw [hheads w hw]
          exact Block.preceq_self Dn.erase) hproc with hcand | hle
    · simpa only [voterCandidateTreeAt] using hcand
    · exact w4_rootCase_candidate S adm hw hrunD hmem hproc _of_frontierCap hroot hle
  exact nextVoteAdoption_of_frozenCandidateAtRead_compatibleAnchor
    S adm hcarrierHon hpostProp hhor hw
    (by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hcandidate) hanchor

#print axioms w4_adoptionAt_slot_of_frontierCap


/-- **The twin at a post-deadline carrier.**

Everything the record needs at the carrier's opening slot is closed from the
three live named exports of `ProposalAdoptionNamedClosedRun`, and the two
facts one slot later, at `S.hc.opening_slot q + 1`, are now closed too: that
slot does not open a round, and the general-slot exports the corresponding branch and
w4-gs2 available in the same module reach it. `_of_headsSucc` is
`honestProposal_voterHeadAt_eq_after_SG_healing_named_slot` (b8248b5a) and
`_of_readsSucc` is
`honestProposal_confirmationReadFacts_after_SG_healing_named_slot`
(68dc3ed0), both instantiated at `d:= S.hc.opening_slot q`.

One pin is left. `_of_adoptionSucc` is earlier's
`nextVoteAdoption_of_commonHead_after_SG_healing`
(`PostSafetyHandoffRun.lean:34`, red) read at the prepared adoption
interface. Its constructor now exists at the strength the live producers can
feed, `nextVoteAdoption_of_frozenCandidateAtRead_compatibleAnchor`
(`RecoveryFinalityFilterRetainedAdoptionRun`), so what remains is the
assembly: the candidate membership and the anchor compatibility at the
slot-`(opening q + 2)` vote read. -/
theorem w4_healedTwoSlotHandoffPrepared_of_carrier_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hcarrier : ProposerCarrierAt S rho q)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q + 1) ≤
      rho.horizon)
    {D : NamedBlock V}
    (hD : proposedBlockAt S rho (S.hc.opening_slot q + 1) = some D)
    (_of_adoptionSucc : ∀ carrier ∈ rho.honest, ∀ w ∈ rho.honest,
      Protocol.NamedNextVoteAdoption S rho
        (Proofs.Optimistic.confStore S rho carrier (S.hc.opening_slot q + 1))
        (S.hc.opening_slot q + 1) D.erase w) :
    ∃ carrier : V, HealedTwoSlotHandoffPrepared S rho q D.erase carrier := by
  classical
  set Dl := fgSafetyProgressDeadline S rho rGST gap delayExtra with hDl
  set start := S.hc.opening_slot q with hstart
  have hm : Dl + 2 ≤ q := (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) Dl).trans hq
  have hqPos : 2 ≤ q := (Nat.le_add_left 2 Dl).trans hm
  have hdlq : Dl + 1 ≤ q := Nat.le_of_succ_le hm
  have hstartPos : 0 < start := w4_openingSlot_pos S hqPos
  have hdeadlineTwo : S.hc.opening_slot Dl + 2 ≤ start :=
    w4_openingSlot_two_after S hdlq
  have hproposal1Hor : Protocol.proposal_time S.E (start + 1) ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E (start + 1)).le.trans
      ((vote_time_le_confirmation_time S.E (start + 1)).trans hhor)
  have hrunD : RunBlock S rho D :=
    proposedBlock_runBlock S adm (Nat.succ_pos start) hcarrier.2.1
      hproposal1Hor hD
  -- The two slot-`(opening q + 1)` facts that is pins. Both are now
  -- the available general-slot exports of `ProposalAdoptionNamedClosedRun`,
  -- instantiated at `d:= S.hc.opening_slot q`.
  have hdeadlineOpen : S.hc.opening_slot (Dl + 2) ≤ start := by
    simpa only [hstart, Protocol.HealConfig.opening_slot] using
      Nat.mul_le_mul_right S.hc.R hm
  have hvote1Hor : Protocol.vote_time S.E (start + 1) ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E (start + 1)).trans hhor
  have _of_headsSucc : ∀ v ∈ rho.honest,
      voterHeadAt S rho v (start + 1) = D.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
      S adm hcom hbelow hrec hdelay hpost
      (hdeadlineOpen.trans (Nat.le_succ start)) hvote1Hor hcarrier.2.1 hD
  have _of_readsSucc : ∀ v ∈ rho.honest,
      Block.Preceq
          (namedConfirmationAnchor S
            (confirmationInputRead S rho v (start + 1))) D.erase ∧
        D.erase ∈
          confTree (confirmationInputRead S rho v (start + 1)).st.core :=
    honestProposal_confirmationReadFacts_after_SG_healing_named_slot
      S adm hcom hbelow hrec hdelay hpost hdeadlineOpen hhor hcarrier.2.1 hD
  have hgenSucc := w4_preparedGenuineSelection_of_namedFacts
    S adm hcom hbelow hrec hdelay hpost
      (hdeadlineTwo.trans (Nat.le_succ start)) hhor hrunD
      _of_headsSucc _of_readsSucc
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q)
  have hopening := w4_openingBoundaryOutput_of_headsSucc
    S adm hcom hbelow hrec hdelay hpost hq hcarrier hhor hP _of_headsSucc
  obtain ⟨carrier, hcarrierHon⟩ := honest_nonempty_of_honestCommittees hcom
  refine ⟨carrier,
    { carrier_honest := hcarrierHon
      carrier_genuine := hgenSucc carrier hcarrierHon
      boundary_outputs := ?_
      adoption := _of_adoptionSucc carrier hcarrierHon }⟩
  intro t ht v hv _
  rcases ht with rfl | rfl
  · exact hopening v hv
  · have hsel : movingSlotConfirmationOutput S rho (start + 1) v = D.erase :=
      (hgenSucc v hv).selected
    rw [hsel]
    exact ⟨hgenSucc v hv, Block.preceq_self _⟩

#print axioms w4_healedTwoSlotHandoffPrepared_of_carrier_after_GST



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
