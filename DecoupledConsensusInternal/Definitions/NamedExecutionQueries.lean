module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedRun
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedAdmissible
public import DecoupledConsensusInternal.ModelVocabulary.FinalityGadget.Crossing

@[expose] public section


namespace DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Clock facts (Execution.lean rows 8.3 to 8.10) -/

/-- Twin of `on_tick_emit_time`: a tick stamps the store clock and slot. -/
def NamedTickTimeQuery (S : Setup V) : Prop :=
  ∀ (v : V) (before : NamedNodeState V) (t : Time),
    (NamedNode.tick S v before t).1.st.core.t = t ∧
    (NamedNode.tick S v before t).1.st.core.s = S.E.slotOf t

/-- Twin of `process_time`: processing an object leaves the clock and slot. -/
def NamedProcessTimeQuery (S : Setup V) : Prop :=
  ∀ (n : NamedNodeState V) (o : NamedObject V),
    (NamedNode.process S n o).st.core.t = n.st.core.t ∧
    (NamedNode.process S n o).st.core.s = n.st.core.s

/-- Twin of `foldl_step_time`: after folding events from a world, a node's
clock is its last tick time in the list, else unchanged. -/
def NamedFoldStepTimeQuery (S : Setup V) : Prop :=
  ∀ (w : NamedWorld V) (l : List (NamedEvent V)) (v : V),
    ((l.foldl (NamedWorld.step S) w) v).st.core.t =
      (Run.lastTickIn v l).getD (w v).st.core.t

/-- Twin of `store_time_eq_lastTick`: the strict prefix read's clock is the
last tick time in that prefix, zero if none. -/
def NamedStoreTimeEqLastTickQuery (S : Setup V) (rho : NamedRun V) : Prop :=
  ∀ (v : V) (i : Nat),
    (NamedRun.stateBefore S rho i v).st.core.t =
      (Run.lastTickIn v (rho.events.take i)).getD 0

/-! ## Committee-pool invariant preservation (CommitteePools.lean rows 7.1 to 7.14) -/

/-- The invariant is unchanged and stays on the erased core store. -/
abbrev CorePools (S : Setup V) (st : Protocol.Store V) : Prop :=
  Protocol.CommitteePools S.E st

def NamedTickPoolsQuery (S : Setup V) : Prop :=
  ∀ (v : V) (before : NamedNodeState V) (t : Time),
    CorePools S before.st.core → CorePools S (NamedNode.tick S v before t).1.st.core

def NamedProcessPoolsQuery (S : Setup V) : Prop :=
  ∀ (n : NamedNodeState V) (o : NamedObject V),
    CorePools S n.st.core → CorePools S (NamedNode.process S n o).st.core

/-- Twin of `WorldCommitteePools`. -/
def NamedWorldCommitteePools (S : Setup V) (w : NamedWorld V) : Prop :=
  ∀ v : V, CorePools S (w v).st.core

def NamedWorldInitPoolsQuery (S : Setup V) : Prop :=
  NamedWorldCommitteePools S (NamedWorld.init : NamedWorld V)

def NamedWorldStepPoolsQuery (S : Setup V) : Prop :=
  ∀ (w : NamedWorld V) (e : NamedEvent V),
    NamedWorldCommitteePools S w → NamedWorldCommitteePools S (NamedWorld.step S w e)

/-- Twins of `stateBefore`, `stateAt`, `stateBeforeTime`, `final`. -/
def NamedRunPoolsQuery (S : Setup V) (rho : NamedRun V) : Prop :=
  (∀ (i : Nat) (v : V), CorePools S (NamedRun.stateBefore S rho i v).st.core) ∧
  (∀ (t : Time) (v : V), CorePools S (NamedRun.readAt S rho t v).st.core) ∧
  (∀ (t : Time) (v : V), CorePools S (NamedRun.stateBeforeTime S rho t v).st.core) ∧
  (∀ v : V, CorePools S (NamedRun.final S rho v).st.core)

end DecoupledConsensusModel.Execution

end
