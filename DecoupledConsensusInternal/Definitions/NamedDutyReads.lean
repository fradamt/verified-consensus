module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedDutyReads

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! Proof-side prepared-duty projections and queries. -/
namespace DecoupledConsensusModel.Internal.NamedRecoveryRead
open Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

def proposalDutyRead (S : Setup V) (rho : Run V) (s : Slot) : NamedNodeState V :=
  proposerReadAt S rho s

def proposalDutyStore (S : Setup V) (rho : Run V) (s : Slot) : Protocol.Store V :=
  (proposalDutyRead S rho s).st.core

def voteDutyStore (S : Setup V) (rho : Run V) (v : V) (s : Slot) : Protocol.Store V :=
  (voteDutyRead S rho v s).st.core

def confirmationInputStore (S : Setup V) (rho : Run V) (v : V) (s : Slot) : Protocol.Store V :=
  (confirmationInputRead S rho v s).st.core

def actionDutyStore (S : Setup V) (rho : Run V) (v : V) (r : Round) : Protocol.Store V :=
  (actionDutyRead S rho v r).st.core

def VoteEmissionQuery (S : Setup V) (rho : Run V) : Prop :=
  NamedScheduleWellFormed S rho →
  ∀ (s : Slot) (v : V) (i : Nat), 0 < s → v ∈ rho.honest →
    rho.events[i]? = some (.tick v (Protocol.vote_time S.E s)) →
    ∀ u : GoldfishVote V,
      (NamedObject.gfVote u ∈ NamedRun.emittedAt S rho i v (Protocol.vote_time S.E s)) ↔
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract (voteDutyRead S rho v s).cache) S.E S.hc (S.node v)
        (voteDutyRead S rho v s).st).2 = some u

end DecoupledConsensusModel.Internal.NamedRecoveryRead

end
