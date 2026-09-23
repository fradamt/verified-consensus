module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.LeakFairnessL1

@[expose] public section

/-! Proof-side leak-fairness helpers outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Internal.LeakFairness
open Execution Protocol
open Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

def currentProductionRecord (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.Record :=
  (rho.stateBeforeTime S (S.a r) v).Λ.legacy

def NoConflictingJustificationsAtHCurrentProduction (S : Setup V) (rho : Run V)
    (H : Height) : Prop :=
  ∀ A B : NamedBlock V, RunBlock S rho A → RunBlock S rho B →
    (Protocol.derive_named S.E S.cfg A).h_j = H →
    (Protocol.derive_named S.E S.cfg B).h_j = H →
    (Protocol.derive_named S.E S.cfg A).J.root =
      (Protocol.derive_named S.E S.cfg B).J.root

def currentProductionEffectiveLock (S : Setup V) (rho : Run V)
    (v : V) (r : Round) (source : Block V) : Option BlockId :=
  Protocol.own_lock (currentProductionRecord S rho v r)
    (currentProductionSourceState S rho v r source).h
    (actionAttestationAt S rho v r).finality_pair

def LockOnSourceAtFrontierCurrentProduction (S : Setup V) : Prop :=
  ∀ (rho : Run V) (v : V) (r : Round) (source : Block V),
    LeakFairnessExecution S rho → v ∈ rho.honest →
    currentProductionSource S rho v r = some source →
    CurrentProductionSourceAtFrontier S rho v r source →
    NoConflictingJustificationsAtHCurrentProduction S rho
      (currentProductionSourceState S rho v r source).h →
    ∀ entry : BlockId, currentProductionEffectiveLock S rho v r source = some entry →
      entry = (currentProductionSourceState S rho v r source).T_h.root

def LeakFairnessL1CurrentProductionInternal (S : Setup V) : Prop :=
  ∀ (rho : Run V) (v : V) (r : Round) (source : Block V),
    LeakFairnessExecution S rho → v ∈ rho.honest →
    currentProductionSource S rho v r = some source →
    CurrentProductionSourceAtFrontier S rho v r source →
    NoConflictingJustificationsAtHCurrentProduction S rho
      (currentProductionSourceState S rho v r source).h →
    CurrentProductionHeightContribution S rho v r source ∧
      CurrentProductionL1Protection S rho v r source

end DecoupledConsensusModel.Internal.LeakFairness

end
