module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.UserConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Schedule.CandidateSafety
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Protocol.Handlers.RetentionNamed
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationRecordOrigin

@[expose] public section

/-! # User-candidate origins and processed-block scope -/

namespace DecoupledConsensusModel
namespace Proofs
namespace UserConfirmation

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The public candidate definition is the same walk used by the handler:
unfolding `userCandidateAtIndex` exposes the named confirmation walk over the
confirmation duty's own prepared read (design note: the prior RHS read the erased
`confWalk` over an old-style `tickStore`; the named walk instead reads
`Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache)...` on the
prepared read's core store). -/
theorem userCandidateAtIndex_eq (S : Setup V) (rho : Run V) (v : V)
    (i : Nat) (time : Time) :
    userCandidateAtIndex S rho v i time =
      namedConfirmationWalk S
        (NamedActionReads.confirmationReadFrom S (rho.stateBefore S i v) time)
        (S.E.slotOf time - 1) := rfl


/-- Normalize the actual user-candidate event to one named confirmation slot.

design note: the prior conclusion equated `userCandidateAtIndex` to `confWalk S.E S.hc
(confStore S rho v s) s`, the erased walk over the prior tick-store
reconstruction. That equation is no longer available in general (Result23Shapes
Shape 10: the two anchors agree only when the confirmation read's own cache
contract selects the same SG root as the unparameterised selector, a condition
this theorem does not have). The mechanical replacement states the same
normalization directly in the named vocabulary: the walk over the confirmation
duty's own prepared read (`confirmationInputRead`).

: `UserConfirmationSelectionAt` now carries a second arm, the
SG candidate the runtime's optional selector writes when the walk fails the
gate. That value is not the walk and no green lemma relates the two, so the
normalization carries the arm forward rather than resolving it: the middle
component is the same disjunction the predicate holds, at the normalized
confirmation time. The slot and horizon components are unchanged. -/
theorem selectionAt_slot (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {v : V} {i : Nat} {C : Block V}
    (hsel : UserConfirmationSelectionAt S rho v i C) :
    ∃ s : Slot,
      rho.events[i]? = some (Event.tick v (Protocol.confirmation_time S.E s)) ∧
      (namedConfirmationWalk S (confirmationInputRead S rho v s) s = C ∨
        userSGCandidateAtIndex S rho v i (Protocol.confirmation_time S.E s) = some C) ∧
      Protocol.confirmation_time S.E s ≤ rho.horizon := by
  rcases hsel with ⟨time, hi, hpos, htime, hC⟩
  let s := S.E.slotOf time - 1
  have hk : s + 1 = S.E.slotOf time := Nat.sub_add_cancel hpos
  have hconfirmation : time = Protocol.confirmation_time S.E s := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ S.E s, hk]
    exact htime
  rw [userCandidateAtIndex_eq] at hC
  have hstate := stateBefore_tick_eq_stateBeforeTime S sch hi
  refine ⟨s, ?_, ?_, ?_⟩
  · simpa only [hconfirmation] using hi
  · rcases hC with hwalk | hsg
    · rw [hstate, hconfirmation, slotOf_confirmation_time, Nat.add_sub_cancel] at hwalk
      exact Or.inl hwalk
    · exact Or.inr (by simpa only [hconfirmation] using hsg)
  · have hhor := (sch.in_horizon (Event.tick v time) (List.mem_of_getElem? hi)).2
    simpa only [Event.time, hconfirmation] using hhor


/-- A tick that is not a confirmation tick leaves `latest_confirmed` unchanged.
Proposal, vote, and round-action subduties do not write this field.

: the bare `(nd, st, Λ)` argument triple is retired; the closed named tick
bundles them as one `NamedNodeState`, read by node identity `v` directly. The
branch reasoning is byte-identical to `Protocol.Monotone.tick_latest_preserves`
(same duty composition order), specialised to plain equality since `h` collapses
the confirmation branch outright instead of needing the `Preceq`/`compatible`
disjunction that theorem carries. -/
theorem on_tick_emit_latest_of_ne
    (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : ¬ (0 < S.E.slotOf t ∧
      t = Protocol.support_cutoff S.E (S.E.slotOf t))) :
    (on_tick_emit S v n t).1.st.latest_confirmed = n.st.latest_confirmed := by
  show (Protocol.NamedTick.tick
      (NamedProfile.gradeContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v) n.st n.record t).1.latest_confirmed =
      n.st.latest_confirmed
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
    Protocol.NamedTick.namedOps, if_neg h]
  split_ifs <;>
    simp only [attest_with_latest, propose_block_with_latest, named_goldfish_vote_with_latest]







/-! ## Candidate membership in the reading node's own tree -/

/-- The named confirmation walk is a block the reading store holds: the frame
anchor is in the tree and `Protocol.ghost` never leaves the filtered tree. -/
theorem namedConfirmationWalk_mem (S : Setup V) (n : NamedNodeState V) (s : Slot)
    (hroots : Proofs.NamedStoreRoots.RootsInTree n.st) :
    namedConfirmationWalk S n s ∈ n.st.core.T := by
  have hroot := Proofs.NamedStoreRoots.fg_root_mem n.st hroots
  have hanchor := Proofs.NamedConfirmationMembership.runtime_anchor_mem
    n.cache S.E S.hc n.st.core.toHealing
    (S.hc.round_of n.st.core.s) hroot
  exact Proofs.Records.ghost_mem_of _ _ hanchor (Proofs.Records.get_filtered_block_tree_subset _)



/-! ## The three values of one confirmation write -/





/- The same bound holds in the strict pre-time store. -/





end UserConfirmation
end Proofs
end DecoupledConsensusModel

end
