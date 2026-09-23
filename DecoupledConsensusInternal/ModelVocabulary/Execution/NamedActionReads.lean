module
public import DecoupledConsensusModel

@[expose] public section

/-! Exact named action reads, extracted without a body change. -/
namespace DecoupledConsensusModel.Execution.NamedActionReads
open DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The round-action input after the existing confirmation duty at a_r.
This API is restricted to a round action. Exact named-tick correspondence,
including support-cutoff timing, is a proof obligation. -/
def actionReadFrom (S : Setup V) (before : NamedNodeState V) (r : Round) :
    NamedNodeState V :=
  let t := S.a r
  let n := confirmationReadFrom S before t
  let st := Protocol.NamedDuties.update_confirmation_with
    (NamedProfile.gradeContract n.cache) S.E S.hc n.st (S.E.slotOf t - 1)
  ⟨st, before.record, n.cache⟩

def actionReadAt (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    NamedNodeState V :=
  actionReadFrom S (NamedRun.stateBeforeTime S rho (S.a r) v) r


end DecoupledConsensusModel.Execution.NamedActionReads

end
