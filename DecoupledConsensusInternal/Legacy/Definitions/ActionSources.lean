module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedActionReads

@[expose] public section

/-! Actual named action observers. Definitions only. -/
namespace DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Full named read after the same-tick confirmation duty. -/
def actionReadAt (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    NamedNodeState V :=
  NamedActionReads.actionReadAt S rho v r

/-- Full prepared action read, including the cache, store, and record. -/
def actionStoreAt (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    NamedNodeState V :=
  actionReadAt S rho v r

/-- Original named row computed by the action. Actual emission requires an awake tick. -/
def actionAttestationAt (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    NamedAttestation V :=
  let n := actionReadAt S rho v r
  (Protocol.NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
    S.E S.hc (S.node v) n.st n.record).2.2

/-- The SG selector uses the cache contract of the actual action. -/
def actionSGBlockAt (S : Setup V) (rho : Run V) (v : V) (r : Round) : Block V :=
  let n := actionReadAt S rho v r
  let gc := NamedProfile.gradeContract n.cache
  let st := n.st.core.toHealing
  let k := S.hc.round_of st.s
  Protocol.get_sg_vote_with gc S.E S.hc st k
    (Protocol.grade2_block_with gc S.E S.hc st k)

/-- The FG source uses the same action store and grade contract. -/
def actionFGSource (S : Setup V) (n : NamedNodeState V) : Option (Block V) :=
  let gc := NamedProfile.gradeContract n.cache
  let st := n.st.core.toHealing
  let r := S.hc.round_of st.s
  Protocol.fg_source_with gc S.E S.hc st r
    (Protocol.grade2_block_with gc S.E S.hc st r)

/-- The source checkpoint comes from the stored named derivation. -/
def fgConfirmationWitness (S : Setup V) (n : NamedNodeState V) : Option (Block V) :=
  (actionFGSource S n).map (fun Cfg => (n.st.core.σ Cfg).T_h)

end DecoupledConsensusModel.Proofs.HealingSurface

end
