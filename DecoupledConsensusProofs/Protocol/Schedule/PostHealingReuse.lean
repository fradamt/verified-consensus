module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Objects.PostGSTSync
public import DecoupledConsensusProofs.Protocol.Schedule.CanonicalSuffixPostGSTCore

@[expose] public section

/-!
# Confirmation-kernel reuse after a healing boundary

The guarded `latest_confirmed` record is not the correct primary post-healing
surface. A pre-healing value can be incompatible with the healed chain, and
the Section 7 guard then retains that old value. Healing does not rewrite it.

The true suffix surface is instead about the `live_confirmed` values produced
by confirmation evaluations after the boundary:

* those evaluation outputs are compatible; and
* every such evaluation is genuine.

`HonestSelectionSuffixEndpoint` is the proof-only safety interface. It gives a
common upper endpoint for every actual Section 7 selection after the boundary.
The endpoint is ghost proof state, not protocol state. A post-healing frontier
induction can choose its final descendant after it has processed the finite run.

No synchrony or fault bound is used in the assembly theorem. Post-GST relay,
honest committee majority, and honest global weight majority belong only to the
producer of the endpoint and renewal facts. `BelowOneThird` is therefore not
part of this suffix interface.

**Named-runtime proof.** What survives here is the pure
boundary-window arithmetic and the two store-local anchor kernels, which read a
supplied `Protocol.Store V` and need no run vocabulary at all.

**Open (class d).** The whole suffix-endpoint interface and its producers are
NOT restated: `alignedRound_represented`, `confRepresentation_after_gst`,
`confAnchor_compatible_of_history_after_gst`,
`genuineConfirmationAndPreceq_after_gst`, `updateConfirmation_compatible_after_gst`,
`GenuineConfirmationSelectionAt`, `LiveConfirmationsFrom`,
`LiveConfirmationCompatibleFrom`, `HonestSelectionSuffixEndpointAtIndex` and
`GenuineSelectionSuffixEndpointAtIndex` with all of their algebra, seeds,
successors and time-suffix projections, and the eight
`liveConfirmationsFrom_*` / `existsSelectionSuffixEndpoint*` producers, plus
`PostHealingConfirmationContinuation`,
`HealedTwoSlotHandoff.selection_before_two_after` and
`genuineConfirmationAt_of_genuineConfirmation`.

They rest on four things this chain records as absent: the post-GST
representation producer, whose full-participation form this chain rebuilds only
at GST zero (`Availability/EvaluationStoreRun.lean`'s
`honest_represented_stateBeforeTime`); the confirmation anchor
`confAnchor_compatible_of_history`, absent in
`Availability/CanonicalHistory.lean` on the grade-batch `sole` half; and
`ConfirmationSelectionAt`'s two-value reading, false under the runtime
contract whose `confirmationSG` is `.optional (frameSGCandidate c)` — the same
gap `UserConfirmationHistoryRun.lean` records, which is what
`GenuineConfirmationSelectionAt` and the `liveConfirmations` family are built
on. Their byte-exact earlier text is archived  at
`the compatibility layer`.
Not guessed at; not available.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


theorem coneSupport_confVotes_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {tgt : Block V → Prop}
    (hnames : Proofs.HealingSurface.NamedHonestVotesCone S rho s tgt)
    {v : V} (hv : v ∈ rho.honest)
    (hres : Proofs.Optimistic.HeadsResolveIn S rho s
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.confStore S rho v s).timestamp_block) :
    Proofs.Optimistic.ConeSupport S.E (Proofs.Optimistic.confStore S rho v s).T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
      s rho.honest tgt := by
  apply Proofs.Optimistic.coneSupport_confVotes S rho hcom hnames v
  · intro u hus hval hemit harr
    exact canonicalSuffixHonestVoteCounted S adm hs hpost hhor v hv u hus hval
      hemit harr
  · exact hres


/-! ## Post-GST confirmation-anchor producers -/

/-! ### The two-duty boundary window -/

/-- The opening-slot vote used by the action-time confirmation is strictly
before the aligned-round boundary. -/
theorem opening_vote_time_lt_action
    (S : Setup V) (r : Round) :
    Protocol.vote_time S.E (S.hc.opening_slot r) < S.a r := by
  unfold Setup.a Protocol.HealConfig.a Protocol.vote_time Env.t slotStart
  have hd := S.E.Δ_pos
  have h : S.E.Δ < 6 * S.E.Δ := by
    simpa using Int.mul_lt_mul_of_pos_right (show (1 : Int) < 6 by omega) hd
  exact Int.add_lt_add_left h _

/-- The immediately following slot also votes before `a_r`; this is the
one-slot persistence handoff that healing must supply. -/
theorem next_vote_time_lt_action
    (S : Setup V) (r : Round) :
    Protocol.vote_time S.E (S.hc.opening_slot r + 1) < S.a r := by
  unfold Setup.a Protocol.HealConfig.a Protocol.vote_time Env.t slotStart
  push_cast
  have hd := S.E.Δ_pos
  ring_nf
  have h : S.E.Δ * 5 < S.E.Δ * 6 :=
    Int.mul_lt_mul_of_pos_left (show (5 : Int) < 6 by omega) hd
  exact Int.add_lt_add_right h _

/-- From the second later slot onward, vote duties are genuinely after the
aligned-round boundary and can use the generic post-GST relay kernel. -/
theorem action_lt_vote_time_two_after
    (S : Setup V) (r : Round) :
    S.a r < Protocol.vote_time S.E (S.hc.opening_slot r + 2) := by
  unfold Setup.a Protocol.HealConfig.a Protocol.vote_time Env.t slotStart
  push_cast
  have hd := S.E.Δ_pos
  ring_nf
  have h : S.E.Δ * 6 < S.E.Δ * 9 :=
    Int.mul_lt_mul_of_pos_left (show (6 : Int) < 9 by omega) hd
  exact Int.add_lt_add_right h _

/-- The only confirmation evaluations from the aligned action through the
strict prefix before the second later slot are those of the opening slot and
its immediate successor. This arithmetic fact isolates the two duties that
healing must hand to the ordinary post-GST induction. -/
theorem eq_opening_or_next_of_confirmation_in_boundary_window
    (S : Setup V) (r : Round) {s : Slot}
    (hlo : S.a r ≤ Protocol.confirmation_time S.E s)
    (hhi : Protocol.confirmation_time S.E s <
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2)) :
    s = S.hc.opening_slot r ∨ s = S.hc.opening_slot r + 1 := by
  let o := S.hc.opening_slot r
  have hlo' : Protocol.confirmation_time S.E o ≤
      Protocol.confirmation_time S.E s := by
    simpa only [Setup.a, Protocol.a_eq_confirmation_time, o] using hlo
  have hloSlots : o + 1 ≤ s + 1 := by
    apply Proofs.Optimistic.slot_le_of_support_cutoff_le S.E
    simpa only [← Protocol.confirmation_time_eq_support_cutoff_succ] using hlo'
  have hhiSlots : s + 1 ≤ o + 2 + 1 := by
    apply Proofs.Optimistic.slot_le_of_support_cutoff_le S.E
    simpa only [← Protocol.confirmation_time_eq_support_cutoff_succ] using
      (le_of_lt hhi)
  have hne : s + 1 ≠ o + 2 + 1 := by
    intro heq
    have heqTime : Protocol.confirmation_time S.E s =
        Protocol.confirmation_time S.E (o + 2) := by
      simpa only [Protocol.confirmation_time_eq_support_cutoff_succ] using
        congrArg (Protocol.support_cutoff S.E) heq
    rw [heqTime] at hhi
    exact (lt_irrefl _ hhi)
  have hhiSlots' : s + 1 < o + 2 + 1 := lt_of_le_of_ne hhiSlots hne
  have hos : o ≤ s := by
    apply Nat.le_of_succ_le_succ
    simpa only [Nat.succ_eq_add_one] using hloSlots
  have hso : s < o + 2 := by
    apply Nat.lt_of_succ_lt_succ
    simpa only [Nat.succ_eq_add_one] using hhiSlots'
  rcases Nat.eq_or_lt_of_le hos with heq | hlt
  · exact Or.inl (by simpa only [o] using heq.symm)
  · right
    have hlower : o + 1 ≤ s := Nat.succ_le_iff.mpr hlt
    have hupper : s ≤ o + 1 := by
      have hp := Nat.le_pred_of_lt hso
      simpa only [Nat.add_sub_cancel] using hp
    simpa only [o] using Nat.le_antisymm hupper hlower

end Protocol
end DecoupledConsensusModel

end
