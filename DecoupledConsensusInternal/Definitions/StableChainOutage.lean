module
public import DecoupledConsensusInternal.ModelVocabulary
public import Mathlib.Data.Finset.Max
public import DecoupledConsensusInternal.Definitions.OutageEntryRevision

@[expose] public section

/-! Pure core-store and arithmetic helpers retained in the default library.
the prior runtime statements and proofs are in the compatibility layer. -/


namespace DecoupledConsensusModel
namespace Internal.StableChainOutageDraft
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open OutageEntryRevision DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- First confirmation read after round-r phase completion, at T_r+2Delta.
G0 closes at T_r+Delta; G2 and G1 close earlier. For r>0 this is an actual
support-cutoff confirmation tick whose SG candidate has round label r. -/
def formationConfirmationTime (S : Setup V) (r : Round) : Time :=
  Protocol.support_cutoff S.E (S.hc.opening_slot r)


/-- 1190's next-round transfer, with an explicit conservative record
margin: first confirmation of s+1 plus Delta <= b0, i.e. T_(s+1)+3Delta<=b0.
This places every round-(s+1) phase and its confirmation read before b0. Waiting
until a_(s+1)+Delta would consume all eta=1,R=3 retained slack, so that stronger
margin is not used. Two-round separation s+1<roundOf(b0) suffices for R>=3.
No sufficiency or minimality proof for this transfer margin is asserted. -/
def FormationMargin (S : Setup V) (s : Round) (b0 : Time) : Prop :=
  formationConfirmationTime S (s + 1) + S.E.Δ ≤ b0

end Internal.StableChainOutageDraft
end DecoupledConsensusModel

end
