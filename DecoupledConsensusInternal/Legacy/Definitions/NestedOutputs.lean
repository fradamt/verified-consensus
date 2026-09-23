module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedRun
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

/-! # The three user-facing chains nest at every read

Addendum 34 22. The statement is unconditional: it has no fault bound,
no synchrony hypothesis, and no honesty hypothesis. -/



namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- earlier result (addendum 34 22): the three user-facing chains nest at
every read of every node, finalized ⪯ stable ⪯ confirmed. Unconditional: it
holds by construction of the accessors, for every run and every node, honest or
not. -/
def NestedOutputs (S : Setup V) : Prop :=
  ∀ (rho : NamedRun V) (v : V) (t : Time),
    let st := (NamedRun.readAt S rho t v).st.core
    Block.Preceq st.F (Protocol.get_stable st) ∧
      Block.Preceq (Protocol.get_stable st) (Protocol.get_confirmed st)

end Internal
end DecoupledConsensusModel

end
