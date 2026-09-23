module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.OutageResilience

@[expose] public section

/-! Pure core-store and arithmetic helpers retained in the default library.
the prior runtime statements and proofs are in the compatibility layer. -/


namespace DecoupledConsensusModel
namespace Internal.OutageEntryRevision
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Inclusive retained admission interval for the current support-frame round.
This is deliberately not the first affected phase's eligible input window. -/
def retainedRounds (S : Setup V) (supportRound : Round) : Finset Round :=
  (Finset.range (supportRound + 1)).filter (fun k => supportRound - S.hc.η_SG ≤ k)

/-- All actual retained raw SG projections in this interval before cutoff.
A late or unknown body does not remove a raw input from this inventory. -/
def retainedRaw (S : Setup V) (st : Protocol.Store V) (supportRound : Round)
    (cutoff : Time) (sender : V) : Finset (Protocol.SGVote V) :=
  ((retainedRounds S supportRound).biUnion st.toHealing.gradeView.sg_votes).filter
    (fun u => u.val_index = sender ∧ occurrenceBefore (st.timestamp_sg_vote u) cutoff = true)

/-- A distinct usable-input set; an unknown newer raw head does not overwrite
or remove a known older usable input. open uses the actual body and stamps. -/
def retainedReady (S : Setup V) (st : Protocol.Store V) (supportRound : Round)
    (cutoff : Time) (sender : V) : Finset (Protocol.SGVote V) :=
  (retainedRaw S st supportRound cutoff sender).filter
    (fun u => DecoupledConsensusModel.Protocol.bodyReady st.toHealing.gradeView st.F cutoff u = true)

/-- Every maximal-round input is retained in a tie; no arbitrary head is chosen. -/
def latest (inputs : Finset (Protocol.SGVote V)) : Finset (Protocol.SGVote V) :=
  inputs.filter (fun u => ∀ x ∈ inputs, x.round ≤ u.round)

/-- Coverage requires actual unique lookup. Unknown and empty heads fail this
positive coverage test; no global body witness substitutes for local open. -/
def covers (st : Protocol.Store V) (P : Block V) (u : Protocol.SGVote V) : Bool :=
  match u.confirmed.bind (Block.find? st.T) with
  | none => false
  | some B => Block.preceq P B

/-- Complete conservative stale-risk test at one reader. An unknown/empty latest
raw head is counted. All top-round ties must cover P and name the same head;
an equivocation tie cannot become a supporter by picking its favorable branch.
No retained input means no stale opponent at this read. -/
def staleAt (S : Setup V) (st : Protocol.Store V) (supportRound : Round)
    (b0 : Time) (P : Block V) (sender : V) : Bool :=
  let top := latest (retainedRaw S st supportRound b0 sender)
  decide ((∃ u ∈ top, covers st P u = false) ∨
    (∃ u ∈ top, ∃ w ∈ top, u.confirmed ≠ w.confirmed))

end Internal.OutageEntryRevision
end DecoupledConsensusModel

end
