module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalSnapshot
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# GST-zero honest-proposal canonicality

An honest slot-`(s+1)` proposer reads the whole slot-`s` raw vote bucket and
the exact subset whose heads resolve in its proposal-time tree. At GST zero,
every honest slot-`s` vote and its head have arrived by that read. Therefore a
directed honest-vote cone gives the proposer's two-view pair the same
`ConeSupport` interface already used at voter and confirmation reads.

This file first proves that proposer-side packaging. It is the counting part
of the statement that the honest proposal parent remains canonical. No
proposal-priority rule, pending object, or additional protocol mechanism is
used.

**Named-runtime proof (design note).** What survives is the
proposal-window arithmetic, the proposal-read representation producer (rebuilt
from `Availability/EvaluationStoreRun.lean`'s
`honest_represented_stateBeforeTime`, which this chain rebuilt from
`broadcast_gst_zero` and `Proofs.NamedSGArrival.honest_row_after_call`), and the
proposer two-view validity, which reads the proposer duty store only as a pool
and a tree.

**restated below.** `proposalPath_of_candidate` uses the  named store wrappers
at the proposer read. Its public scope and hypotheses are unchanged from earlier.

**Open (class d),.** Seventeen declarations are NOT
restated: `honest_vote_mem_proposer_pair`, `coneSupport_proposerDutyStore` and its
three `_of_*Cone` variants, `headsResolveIn_proposerDutyStore_of_endpointCone`,
`compatibleVoteDutyReach_of_endpointCone_before`,
`coneAndAdmissionAt_proposal_of_genuine`,
`proposalDutyAnchor_preceq_of_canonicalHistoryBefore`,
`candidateAtTick_of_heightGateHistory_honestWeightMajority`,
`proposalDutyCandidate_of_canonicalHistoryBefore`,
`endpoint_preceq_proposedParent_of_cone` and its two admitted variants,
`frontierEndpoint_preceq_proposedParent_gstZero`,
`proposedParent_descends_selectionFrontier_gstZero`,
`proposedParent_preceq_proposedBlock` and
`proposedBlock_canonicalHistoryAtProposal_gstZero`.

They rest on the retired total proposal reader `proposedBlock` and its parent
(: the named `proposedBlockAt_parent` gives the graded parent, and a proof
that needed the parent to be an ungraded `Protocol.get_head` at the tick store
open items naming Q-PR2), on `getSgRootPreceq_stateBeforeTime_of_history` and the
confirmation anchor recorded as absent in
`Availability/EvaluationStoreRun.lean`, and on the vote-duty and proposer head
equalities of. Their byte-exact earlier text is archived  at
`the compatibility layer`.
Not guessed at; not available.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The previous slot's support cutoff is before the next proposal instant. -/
theorem support_cutoff_le_proposal_time_succ (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.proposal_time E (s + 1) := by
  have hstep : Protocol.proposal_time E (s + 1) =
      Protocol.support_cutoff E s + 2 * E.Δ := by
    unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
    push_cast
    ring
  rw [hstep]
  exact le_add_of_nonneg_right
    (Int.mul_nonneg (by norm_num) (le_of_lt E.Δ_pos))

/-- The previous-round SG relay deadline is no later than the proposal duty
for the round that duty reads. -/
theorem previous_action_add_delta_le_proposal
    (S : Setup V) {s : Slot}
    (hr : 0 < S.hc.round_of s) :
    S.a (S.hc.round_of s - 1) + S.E.Δ ≤
      Protocol.proposal_time S.E s := by
  let r := S.hc.round_of s
  change 0 < r at hr
  change S.a (r - 1) + S.E.Δ ≤ Protocol.proposal_time S.E s
  have hmul : r * S.hc.R ≤ s := by
    simpa only [r, Protocol.HealConfig.round_of] using
      (Nat.div_mul_le_self s S.hc.R)
  have hr' : r - 1 + 1 = r := by
    apply Nat.sub_add_cancel
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hr)
  have hsplit : (r - 1) * S.hc.R + S.hc.R = r * S.hc.R := by
    calc
      (r - 1) * S.hc.R + S.hc.R =
          (r - 1) * S.hc.R + 1 * S.hc.R := by rw [one_mul]
      _ = (r - 1 + 1) * S.hc.R := by rw [Nat.add_mul]
      _ = r * S.hc.R := by rw [hr']
  have hslots : (r - 1) * S.hc.R + 2 ≤ s := by
    exact le_trans (Nat.add_le_add_left S.hc.R_ge_two _) (hsplit ▸ hmul)
  have hslotsInt :
      (((r - 1) * S.hc.R + 2 : Nat) : Time) ≤ (s : Time) := by
    exact_mod_cast hslots
  push_cast at hslotsInt
  unfold Setup.a Protocol.HealConfig.a Protocol.proposal_time Env.t slotStart
  simp only [Protocol.HealConfig.opening_slot]
  push_cast
  have hd0 : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  have hfactor : (0 : Time) ≤ 4 * S.E.Δ :=
    Int.mul_nonneg (by norm_num) hd0
  have hscaled := Int.mul_le_mul_of_nonneg_left hslotsInt hfactor
  have h78 : 7 * S.E.Δ ≤ 8 * S.E.Δ :=
    Int.mul_le_mul_of_nonneg_right (by decide : (7 : Time) ≤ 8) hd0
  calc
    4 * S.E.Δ * (↑(r - 1) * ↑S.hc.R) + 6 * S.E.Δ + S.E.Δ =
        4 * S.E.Δ * (↑(r - 1) * ↑S.hc.R) + 7 * S.E.Δ := by ring
    _ ≤ 4 * S.E.Δ * (↑(r - 1) * ↑S.hc.R) + 8 * S.E.Δ :=
      add_le_add (le_refl _) h78
    _ = 4 * S.E.Δ * (↑(r - 1) * ↑S.hc.R + 2) := by ring
    _ ≤ 4 * S.E.Δ * (s : Time) := hscaled


/-- The raw view read by a proposal duty has the committee validity enforced
by vote-pool ingress. -/
theorem proposerDutyStore_proposer_view_valid_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho) (s : Slot) :
    Protocol.VoteSetValid S.E ((proposerDutyStore S rho s).s - 1)
      (Protocol.proposer_view
        (proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
        (proposerDutyStore S rho s).s).toFinset := by
  have hsch := adm.toNamedScheduleWellFormed
  simpa only [proposerDutyStore, Proofs.Optimistic.tickStore,
    Proofs.Optimistic.slotOf_proposal_time] using
      voteSetValid_proposer_view_stateBeforeTime S hsch
        (S.E.proposer s) (Protocol.proposal_time S.E s) s

theorem proposerDutyStore_proposer_view_valid
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) (s : Slot) :
    Protocol.VoteSetValid S.E ((proposerDutyStore S rho s).s - 1)
      (Protocol.proposer_view
        (proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
        (proposerDutyStore S rho s).s).toFinset :=
  proposerDutyStore_proposer_view_valid_core
    S adm.toNamedAdmissibleCore s

#print axioms proposerDutyStore_proposer_view_valid_core

end Protocol
end DecoupledConsensusModel

end
