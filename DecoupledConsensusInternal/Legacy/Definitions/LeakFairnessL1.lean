module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.LeakLedger
public import DecoupledConsensusInternal.Legacy.Definitions.ActionSources
public import DecoupledConsensusInternal.Legacy.Definitions.NamedEvidenceInternal
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Admissible
public import DecoupledConsensusInternal.Legacy.Assumptions.Weight

@[expose] public section

/-! Stream 5 fairness statements ( 1213).
CurrentProduction means the existing production action: current grades,
height-only timeouts and wire-only carried admission. It is not the outer
outage definition's CurrentProfile, which uses the cached-frame runtime.
No named-runtime fairness or fairness for stale-source votes is asserted.
The lock-on-source lemma below is a required conclusion, never an assumption. -/


namespace DecoupledConsensusModel
namespace Internal.LeakFairness
open Execution Protocol
open Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The exact execution families used by current-production L1 fairness.

The proof needs schedule order and no-duplicate events to identify the actual
action history, and run-scoped root collision freedom to lift erased ancestry
back to named blocks. It needs no delivery well-formedness, authenticity, or
synchrony premise. -/
structure LeakFairnessExecution (S : Setup V) (rho : Run V) : Prop where
  sorted : rho.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f)
  nodup : rho.events.Nodup
  rootCollisionFree : RootCollisionFree S rho

/-- The FG source actually selected from the action's post-confirmation store. -/
def currentProductionSource (S : Setup V) (rho : Run V) (v : V) (r : Round) : Option (Block V) :=
  actionFGSource S (actionStoreAt S rho v r)

/-- Read the source fields from that same actual store, not a supplied context. -/
def currentProductionSourceState (S : Setup V) (rho : Run V)
    (v : V) (r : Round) (source : Block V) : ChainState V :=
  (actionStoreAt S rho v r).st.core.σ source

/-- Fairness at the source frontier is the chain-stability scope, by design.
Descendant-based viability alone does not produce this explicit premise. -/
def CurrentProductionSourceAtFrontier (S : Setup V) (rho : Run V)
    (v : V) (r : Round) (source : Block V) : Prop :=
  (actionStoreAt S rho v r).st.core.h_max ≤
    (currentProductionSourceState S rho v r source).h + 1

/-- The emitted current-production row supplies a usable height contribution
at its actual source entry. No free row or signature/source callback occurs. -/
def CurrentProductionHeightContribution (S : Setup V) (rho : Run V)
    (v : V) (r : Round) (source : Block V) : Prop :=
  let state := currentProductionSourceState S rho v r source
  let row := actionAttestationAt S rho v r
  row.height_pair = .vote state.h state.T_h.root false ∨
    row.height_pair = .vote state.h state.T_h.root true

/-- The actual emitted row is carried at its source height/entry on a source
extension in the current run. Inclusion is explicit: no fairness under
censorship is claimed. All chain states are structurally derived. -/
def CarriedAtSourceEntryCurrentProduction (S : Setup V) (rho : Run V)
    (v : V) (r : Round) (source : Block V) (B : NamedBlock V) : Prop :=
  RunBlock S rho B ∧ Block.Preceq source B.parent.erase ∧
    actionAttestationAt S rho v r ∈ B.attestations ∧
    (Protocol.derive_named S.E S.cfg B.parent).h =
      (currentProductionSourceState S rho v r source).h ∧
    (Protocol.derive_named S.E S.cfg B.parent).T_h.root =
      (currentProductionSourceState S rho v r source).T_h.root

/-- Once carried at the same entry, the row sets progress before height
processing. Every same-height continuation then has zero L1 slot charge for
this validator. L2 fairness is outside this target. -/
def CurrentProductionL1Protection (S : Setup V) (rho : Run V)
    (v : V) (r : Round) (source : Block V) : Prop :=
  ∀ B : NamedBlock V, CarriedAtSourceEntryCurrentProduction S rho v r source B →
    v ∈ (Internal.LeakLedger.namedPreHeightSnapshot S.E S.cfg B).progress ∧
    ∀ C : NamedBlock V, RunBlock S rho C → Block.Preceq B.erase C.erase →
      (Protocol.derive_named S.E S.cfg C.parent).h =
        (currentProductionSourceState S rho v r source).h →
      (Internal.LeakLedger.namedBlockCharges S.E S.cfg C v).l1 = 0


/-- Public CurrentProduction fairness. SlashableBound discharges same-height
justification uniqueness through the existing 2q-W theorem. Fairness at the
frontier is the chain-stability scope, by design (user, 1240).
The frontier premise remains explicit; lock alignment and L1 protection
are proved conclusions. No head-height voting change is planned. -/
def LeakFairnessL1CurrentProduction (S : Setup V) : Prop :=
  ∀ (rho : Run V) (v : V) (r : Round) (source : Block V),
    LeakFairnessExecution S rho → SlashableBound S rho → v ∈ rho.honest →
    currentProductionSource S rho v r = some source →
    CurrentProductionSourceAtFrontier S rho v r source →
    CurrentProductionHeightContribution S rho v r source ∧
      CurrentProductionL1Protection S rho v r source

end Internal.LeakFairness
end DecoupledConsensusModel

end
