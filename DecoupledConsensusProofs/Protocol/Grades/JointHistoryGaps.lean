module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Store.JointHistoryB4B5

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryGapsTime
open Execution Internal.NamedOutageEntry Internal.NamedJointOutage Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime JointHistoryB4B5Time
variable {V : Type} [DecidableEq V] [Fintype V]







/-! ## `Setup.a` is strictly monotone (hence injective) in the round

Needed to know that a tick event's own time `S.a r` determines `r` uniquely,
so growing the confirmation witness at one honest reader's action tick never
has to worry about a different round sharing the same tick time. -/

theorem setup_a_strictMono (S : Setup V) : StrictMono S.a := by
  intro r1 r2 hr
  show S.hc.a S.E.Δ r1 < S.hc.a S.E.Δ r2
  have hR : 0 < S.hc.R := lt_of_lt_of_le (by norm_num) S.hc.R_ge_two
  have hnat : r1 * S.hc.R < r2 * S.hc.R := (Nat.mul_lt_mul_right hR).mpr hr
  have hcast : ((r1 * S.hc.R : Nat) : Time) < ((r2 * S.hc.R : Nat) : Time) := by
    exact_mod_cast hnat
  have heq : S.hc.a S.E.Δ r2 - S.hc.a S.E.Δ r1 =
      4 * S.E.Δ * (((r2 * S.hc.R : Nat) : Time) - ((r1 * S.hc.R : Nat) : Time)) := by
    unfold Protocol.HealConfig.a Protocol.HealConfig.opening_slot
      DecoupledConsensusModel.slotStart
    push_cast
    ring
  have hpos : (0 : Time) < 4 * S.E.Δ *
      (((r2 * S.hc.R : Nat) : Time) - ((r1 * S.hc.R : Nat) : Time)) :=
    Int.mul_pos (Int.mul_pos (by norm_num) S.E.Δ_pos) (sub_pos.mpr hcast)
  have hdiff : (0 : Time) < S.hc.a S.E.Δ r2 - S.hc.a S.E.Δ r1 := by rw [heq]; exact hpos
  exact sub_pos.mp hdiff

theorem setup_a_injective (S : Setup V) {r1 r2 : Round} (h : S.a r1 = S.a r2) : r1 = r2 :=
  (setup_a_strictMono S).injective h

/-! ## Gap A2 -/


/-! ## Gap B4/B5 -/


/-! ## The SG step, conditional on the two gaps. -/


/-! ## The two unproved statements -/


/-! ## B4's former gap, now closed
`JointHistoryB4B5.capture_ready_token` does its own case split on the
orientation between the capture reader's own finalized body and the emitter's
confirmed head, using the joint history to show the two are comparable
(clause (0) `SGVoteOnHistory` for the confirmed head, clause (3) of
`LayerAHistoryOn` for the reader's own finalized body,
`ViabilityHistoryTime.named_common_chain` for the comparison). One
orientation is the original delivery route through the healthy prefix. The
other lands the confirmed head already among the reader's own held bodies
(`ViabilityHistoryTime.ancestor_body_mem`), and leaves its arrival
undated: the reader's own finalized body at the G2-domain read only dates it
before the G2-DOMAIN read, 4Δ too late
(`JointHistoryB4B5Time.early_g2_lt_domain_g2`).
The fix renews clause (3) of the joint history a second time, at the confirmed
head's own arrival DEADLINE `d = S.a k + Δ` instead of the domain read
(`d ≤ early` by `action_delta_le_early_g2`), and runs the same common-chain
split against `H` there. Both branches close with lemmas already proved in
production, no new premise: the ancestor branch reads
`ViabilityHistoryTime.ancestor_body_mem` at the earlier read directly
(`NamedBlockStamp.held_body_stampedBefore_stateBeforeTime` then dates `H`
before `d`), and the delivery branch reruns
`NamedHealthyHeadReady.healthy_head_body_at_read` with `targetRead = d`
instead of the domain read. Either way the stamp obtained at the earlier read
transports forward to the domain read unchanged
(`NamedBlockStamp.stateBefore_body_stamp_mono`: a block stamp, once written,
is never rewritten), which is what still dates `H` before `early` there. This
closes B4 with no fifth clause on the joint history and no new result-1 timing
lemma. -/


/-! ## The requested signature, grown witness

`ConfirmationOnActionRead` at the fixed witness `C` is no longer available
directly (the strict clause 4 only supplies it after possibly growing `C`
through `NamedConfirmationOnHistoryQuery`), so the public conclusion is
restated on the grown witness `C'` the same way the renewal driver needs it:
`C' ` is still in the run, still above `C`, and now dominates `source` too.
`fg_source_on_history_of` itself is unchanged, called here at `C'`. -/


end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryGapsTime

end
