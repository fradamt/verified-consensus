module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedEvidenceInternal
public import DecoupledConsensusInternal.Definitions.Evidence
public import DecoupledConsensusInternal.Definitions.LeakLedger
public import DecoupledConsensusInternal.Definitions.NamedCertificates
public import DecoupledConsensusInternal.Definitions.ProposalSources

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! Proof-side named evidence queries outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Internal
open Protocol Execution
variable {V : Type} [DecidableEq V] [Fintype V]

namespace LeakLedger

def namedLedger (E : Env V) (cfg : HeightConfig) : NamedBlock V → V → LayerCharges
  | .genesis, _ => LayerCharges.zero
  | C@(.node p _ _ _ _ _ _), v =>
    LayerCharges.add (namedLedger E cfg p v) (namedBlockCharges E cfg C v)

end LeakLedger

def proposedBlockErased (S : Setup V) (rho : Execution.Run V) (s : Slot) : Option (Block V) :=
  (Statements.Instantiation.proposedBlockAt S rho s).map NamedBlock.erase

def NamedDerivationAgreesWithoutTimeoutsQuery (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ C : NamedBlock V,
    (∀ a ∈ named_chain_attestations C, a.height_pair.properTarget = true ∨
      a.height_pair = .empty) →
    derive_named E cfg C = derived_state E cfg C.erase

def NamedFinalizedPrefixQuery (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ (C : NamedBlock V) (p : NamedBlock V), NamedBlock.parent? C = some p →
    Block.Preceq (derive_named E cfg p).F (derive_named E cfg C).F

end DecoupledConsensusModel.Internal

end
