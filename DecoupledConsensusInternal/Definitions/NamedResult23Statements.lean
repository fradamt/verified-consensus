module
public import DecoupledConsensusInternal.ModelVocabulary

public import DecoupledConsensusInternal.Definitions.NamedConfirmationWalk
public import DecoupledConsensusInternal.Definitions.NamedCertificates
public import DecoupledConsensusInternal.Definitions.NamedDerived
public import DecoupledConsensusInternal.Definitions.ConfirmationScore

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Internal

open Execution NamedRecoveryRead Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
## Shape 2 — named finalized-root computation query

Old site: `DecoupledConsensusProofs/HealingSurface/UserConfirmationGenesisRun.lean:156`,
the `simp only [Safety.derived_state_node, Safety.process_height_events_F,
Safety.afterFin_F, Safety.foldBlock_J, Safety.foldBlock_F,
Safety.derived_state_genesis,...]` that closes
`finalized_eq_genesis_before_first_confirmation`
(UserConfirmationGenesisRun.lean:122).

Destination namespace: `DecoupledConsensusModel.Internal`
(next to `NamedFinalizedAt`, `Definitions/NamedEvidence.lean`).
Destination module: `Definitions/NamedEvidence.lean`.
-/

/-- Q-E3: the named derivation of a block whose only ancestor is genesis
finalizes genesis. This is the named replacement for the
`derived_state_node`/`foldBlock_F`/`derived_state_genesis` simp set: the two
arms the genesis argument needs, read off `derive_named` rather than
`derived_state`. -/
def NamedShallowFinalizedRootQuery (E : Env V) (cfg : HeightConfig) : Prop :=
  (derive_named E cfg (NamedBlock.genesis : NamedBlock V)).F = Block.genesis ∧
    ∀ C : NamedBlock V, NamedBlock.parent? C = some NamedBlock.genesis →
      (derive_named E cfg C).F = Block.genesis

/-!
## Shape 4 — the named confirmation anchor

Old header: `DecoupledConsensusProofs/Availability/Main.lean:136`

```lean
def confAnchor (E: Env V) (hc: HealConfig) (st: Protocol.Store V): Block V:=
  Protocol.get_sg_root E hc st.toHealing (hc.round_of st.s)
```

Destination namespace: `DecoupledConsensusModel.Internal`
(the anchor is contract-parameterised, so it lives with the named walk, not with
the profile-independent `conf*` layer).
Destination module: `Definitions/NamedConfirmationWalk.lean`.

This is exactly the anchor `namedConfirmationWalk` (NamedConfirmationWalk.lean:29-30)
inlines; giving it a name is what lets `EvaluationStoreOk`'s two reach clauses,
`EvaluationReaches`'s two reach clauses, `confRoot_preceq_confAnchor`,
`confEligible_confWalk_iff` and `live_confirmed_eq` be restated.
-/

/-- The SG root of a prepared read under the contract that read's own duty
uses: the named twin of `confAnchor`. -/
def namedConfirmationAnchor (S : Setup V) (n : NamedNodeState V) : Block V :=
  Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing (S.hc.round_of n.st.core.s)

/-- The confirmation anchor of `v`'s slot-`s` confirmation input read. -/
def confirmationAnchorAt (S : Setup V) (ρ : Run V) (v : V) (s : Slot) : Block V :=
  namedConfirmationAnchor S (confirmationInputRead S ρ v s)



-- Shape 11 support: `NamedJustifiedAt` now lives in `NamedDerived.lean`
-- as `Internal.NamedJustifiedAt` (imported above); dropped from this file.

end Internal
end DecoupledConsensusModel

end
