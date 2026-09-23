module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run

@[expose] public section

/-! Definitions used by the final review statements. No proof obligations are assumed here. -/

namespace DecoupledConsensusModel
namespace Proofs.Optimistic

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store the tick at `t` hands its first duty: the node's own store with the
clock and the slot written (PROTOCOL.md#the-complete-protocol). -/
def tickStore (S : Setup V) (st : Protocol.Store V) (t : Time) : Protocol.Store V :=
  { st with t := t, s := S.E.slotOf t }


/-- The store `goldfish_vote` reads at the slot-`s` vote instant
(PROTOCOL.md#the-complete-protocol): the tick's store at `t_s + Δ`.

It serves to apply `set_fresh_root` first on an opening slot; the 
replacement of §6 deleted the round decision, so the vote branch now reads the
tick's own store outright. The proposal branch does not fire at `t_s + Δ`, so
nothing stands between. The name is kept because every `VoteDuty*` statement
below is phrased over it. -/
def voteStore (S : Setup V) (st : Protocol.Store V) (s : Slot) : Protocol.Store V :=
  tickStore S st (Protocol.vote_time S.E s)

/-- The core clock/slot data at the slot-`s` vote duty. Named phase
preparation changes the cache, not this store; no proposal or confirmation
branch precedes the vote at its distinct slot phase. This is not the vote
duty's grade contract, which still uses the actual prepared cache. -/
def voteDutyStore (S : Setup V) (ρ : Run V) (w : V) (s : Slot) : Protocol.Store V :=
  voteStore S (ρ.storeBeforeTime S w (Protocol.vote_time S.E s)).core s

end Proofs.Optimistic
end DecoupledConsensusModel

end
