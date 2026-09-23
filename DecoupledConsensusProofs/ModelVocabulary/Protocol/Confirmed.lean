module
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Pairs
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Blocks
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Time
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Weights
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Env
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.Objects
public import DecoupledConsensusProofs.ModelVocabulary.FinalityGadget.ChainState
public import DecoupledConsensusProofs.ModelVocabulary.FinalityGadget.Transition
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.Store
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.ForkChoice
public import DecoupledConsensusProofs.ModelVocabulary.MajoritySG.Objects
public import DecoupledConsensusProofs.ModelVocabulary.MajoritySG.ForkChoice
public import DecoupledConsensusProofs.ModelVocabulary.FGForkChoice.Finality
public import DecoupledConsensusProofs.ModelVocabulary.Healing.Schedule
public import DecoupledConsensusProofs.ModelVocabulary.Healing.Action
public import DecoupledConsensusProofs.ModelVocabulary.Protocol.Store
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusModel.Protocol.Store

@[expose] public section

/-! # The three user-facing chains

The store exposes three outputs, nested by construction: finalized (`Σ.F`),
stable (`get_stable`), confirmed (`get_confirmed`). Addendum 34 22
.
-/



namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V]


/-- The stable record sits at or below the confirmation record (addendum 34,
). This is a REGIME fact, not a run invariant of
`update_confirmation_with`: when an eligible Goldfish head replaces a
conflicting old confirmation record while the stable record kept an older value
on that old branch — `advance_confirmed` keeps an ancestor candidate — the two
records diverge. The safety regime excludes it, because honest Goldfish heads
extend the SG root; the handler alone does not.

It is the stable/raw-record compatibility that replaces the prior finality/raw-record
compatibility now that `get_confirmed` falls back on `get_stable`. Under the
safety regime every honest node's read satisfies it, from SG-root canonicity of
honest Goldfish heads; that is a follow-up statement and discharges the
hypotheses that carry this predicate. -/
def StableBelowConfirmed (st : Store V) : Prop :=
  Block.Preceq st.latest_stable st.latest_confirmed

/-! The three chains nest by construction, `F ⪯ get_stable ⪯ get_confirmed`.
That is `DecoupledConsensusProofs.NestedOutputsRun`, one layer up: reflexivity
and transitivity of `Block.preceq` live in `DecoupledConsensusProofs.Ancestry`,
which the model layer cannot import. -/

end Protocol
end DecoupledConsensusModel

end
