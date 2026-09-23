module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.MovingChainBase

@[expose] public section

/-!
# Structures shared by the W4 handoff triple

The handoff triple of `W4RecoverySpineRun` is stated over two records that the
three moving-chain record theorems of `MovingChainHandoffExportsRun` consume.
Those theorems are being restated over the records, so the records have
to sit BELOW the exports; the branches leaves that produce them
(`W4HandoffBoundaryRun`, `W4HealedTwoSlotHandoffRun`) import the exports and
cannot hold them.

`MovingChainHandoffRowCapBoundary` is `MovingChainHandoffBoundary`
(`MovingChainBaseRun.lean:178`) with its `frontierCap` field replaced by the
two row caps that `movingFrontierChainState_bootstrapAt_of_rowCap`
(`MovingChainBaseRun.lean:320`) actually consumes, plus the `RunBlock` and
erased-height fields that `MovingChainHandoffBoundary.toSplitBoundary` already
takes as extra arguments.

`frontierCap` is one height too strong and fails at a post-deadline carrier
(the corresponding branch's Open, design note): the round's own action justifies a new
height, the honest slot `opening_slot q + 2` proposal carries that quorum, and
every honest frontier is at `M0 + 1` before the cutoff. The project's own
recovery bound is `honestHMaxBeforeIndex ≤ C + 1` with `C` the endpoint's
height (`HealingDebtStateRun`, "one unit of frontier debt"); `frontierCap` asks
for zero debt. The row caps are true there: rows at `M0 + 1` are not emitted
until the next round's action, past the cutoff.

The eliminators kept here are the ones whose inputs stay at `MovingChainBaseRun`
level. `MovingChainHandoffBoundary.toRowCap`, the producers, and the `hold`-free
`movingBoundaryHistory_toFreeze_of_rowCap` stay in `W4HandoffBoundaryRun`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Internal.NamedRecoveryRead
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]






/-- The healed two-slot handoff, read at each node's own prepared
confirmation contract: field for field the twin of
`Protocol.HealedTwoSlotHandoff` (`HealingBoundaryRun.lean:30`).

That record pins `Protocol.GradeContract.current` in `carrier_genuine` and
`boundary_outputs`, and `Protocol.NextVoteAdoption` (whose `emit` field is
`Protocol.goldfish_vote`) in `adoption`. The selection's confirmation duty runs
the confirming node's own prepared read contract and its vote duty emits
`Protocol.NamedDuties.goldfish_vote_with` on that contract, so those three
fields are counterfactual and the original record has no producer (design note).
`HealingBoundaryRun` is untouched and the original still compiles.

The selected value of each boundary output is written as
`movingSlotConfirmationOutput` (`MovingChainSlotRun.lean:117`), which is by
definition that node's prepared `live_confirmed` and is already the vocabulary
of the record theorems' own `_of_preparedBoundaryOutput` pin.

`adoption` quantifies over every honest reader, not only the boundary
committee. earlier's producer `nextVoteAdoption_of_commonHead_after_SG_healing`
(`PostSafetyHandoffRun.lean:35`) takes only honesty of source and target and
has no committee premise, so the guard was added when the record was packed,
not when it was proved; dropping it costs the producer nothing and lets branches
w4-h1's `w4BoundaryHeads_of_adoption` reach every honest reader, which is what
the row-cap boundary's `processed` field quantifies over. Every consumer that
instantiated the narrow field at a committee member still does. -/
structure HealedTwoSlotHandoffPrepared
    (S : Setup V) (rho : Run V) (r : Round) (B : Block V)
    (carrier : V) : Prop where
  /-- The named opening-plus-one evaluator is honest. -/
  carrier_honest : carrier ∈ rho.honest
  /-- The carrier's own prepared opening-plus-one evaluation genuinely
  confirms the endpoint. -/
  carrier_genuine : GenuineConfirmationWith
    (Execution.NamedProfile.gradeContract
      (Internal.NamedRecoveryRead.confirmationInputRead S rho carrier
        (S.hc.opening_slot r + 1)).cache)
    S.E S.hc
    (Proofs.Optimistic.confStore S rho carrier (S.hc.opening_slot r + 1))
    (S.hc.opening_slot r + 1) B
  /-- Every actual honest opening or opening-plus-one evaluation is genuine
  under that node's own contract and lies below the endpoint. -/
  boundary_outputs : ∀ s : Slot,
    (s = S.hc.opening_slot r ∨ s = S.hc.opening_slot r + 1) →
      ∀ v ∈ rho.honest,
        Protocol.confirmation_time S.E s ≤ rho.horizon →
          GenuineConfirmationWith
              (Execution.NamedProfile.gradeContract
                (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
              S.E S.hc (Proofs.Optimistic.confStore S rho v s) s
              (movingSlotConfirmationOutput S rho s v) ∧
            Block.Preceq (movingSlotConfirmationOutput S rho s v) B
  /-- The carrier output reaches every honest opening-plus-two vote duty
  through the prepared accepted-forwarding interface. -/
  adoption : ∀ w ∈ rho.honest,
    Protocol.NamedNextVoteAdoption S rho
      (Proofs.Optimistic.confStore S rho carrier (S.hc.opening_slot r + 1))
      (S.hc.opening_slot r + 1) B w


/-- Verbatim copy of the private
`preceq_voterHeadAt_of_namedNextVoteAdoption`
(`SGLifetimeNamedRun.lean:38`, also duplicated at
`HandoverBootstrapPacketNamedRun.lean:38`). -/
private theorem w4_preceq_voterHeadAt_of_namedNextVoteAdoption
    (S : Setup V) {rho : Run V} {source : Protocol.Store V}
    {s : Slot} {B : Block V} {w : V}
    (heligible : Protocol.voters_count S.E (confLate S.E source s) s <
      2 * Protocol.goldfish_score S.E source.T
        (confVotes S.E source s) (confVotes S.E source s) s B)
    (hadopt : Protocol.NamedNextVoteAdoption S rho source s B w) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w (s + 1)
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using voteDutyRead_slot S rho w (s + 1)
  have hprev : st.s - 1 = s := by
    rw [hslot]
    simp
  change Block.Preceq B
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  rw [get_head_in_tree_split_with, hprev]
  simpa only [Protocol.Store.toHealing, read, st] using
    (Protocol.goldfish_fork_choice_captures_of_confirmation
      S.E st.σ st.h_max source.T st.T tree st.s
      (confEarly S.E source s) (confLate S.E source s)
      (confVotes S.E source s) votes support s
      (confNumerator S.E source s) hadopt.transport heligible
        hadopt.support_subset hadopt.anchor hadopt.path)

/-- **The twin supplies the first ordinary post-boundary honest-vote cone**,
the projection `Protocol.HealedTwoSlotHandoff.honestVotesCone_two_after`
supplies today and that the two live record exports read at
`MovingChainHandoffExportsRun.lean:2049,2272`. No committee-weight or fault
bound is used. -/
theorem HealedTwoSlotHandoffPrepared.honestVotesCone_two_after
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {r : Round} {B : Block V} {carrier : V}
    (h : HealedTwoSlotHandoffPrepared S rho r B carrier)
    (hhor : Protocol.vote_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon) :
    NamedHonestVotesCone S rho (S.hc.opening_slot r + 2)
      (fun X => Block.Preceq B X) := by
  have hCg : Protocol.GenuineConfirmation
      (contract := NamedProfile.gradeContract
        (confirmationInputRead S rho carrier
          (S.hc.opening_slot r + 1)).cache)
      S.E S.hc
      (Proofs.Optimistic.confStore S rho carrier (S.hc.opening_slot r + 1))
      (S.hc.opening_slot r + 1) B :=
    ⟨h.carrier_genuine.selected, h.carrier_genuine.genuine⟩
  have heligible := hCg.eligible
  intro w hw hcommittee
  obtain ⟨X, hXhead, hXrun, hXemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm
      (Nat.succ_pos (S.hc.opening_slot r + 1)) hhor hw hcommittee
  refine ⟨X, ?_, hXrun, hXemit⟩
  have hhead := w4_preceq_voterHeadAt_of_namedNextVoteAdoption S heligible
    (h.adoption w hw)
  simpa only [hXhead] using hhead


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
