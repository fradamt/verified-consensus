module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusModel.Objects.NamedBlocks
public import DecoupledConsensusInternal.ModelVocabulary.FinalityGadget.Crossing
public import DecoupledConsensusModel.Objects.NamedBlocks

@[expose] public section

/-!
# Named crossing witness and entry-matching timeout quorum 

Under the targeted rule a height row is `(h, T, timeout)` and counts on a
chain only when `T` is that chain's entry at `h`. the prior `CrossingWitness`
let a timeout row cross any chain at its height; the named witness requires
every row of the quorum, target or timeout, to name the crossing entry.

Safety direction: `NamedCrossingWitness` implies the prior `CrossingWitness`
on the erased rows (a named timeout erases to a height-only timeout), so
every old consequence of a crossing (`finalized_preceq_of_height_lt` and
its twelve healing sites) is inherited by weakening. Liveness direction:
the producers of a crossing are restated here and proved anew.
-/


namespace DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A quorum of named rows all naming entry `X` at height `h`, with `X` below `B`. -/
def NamedCrossingWitness (E : Env V) (A : Finset (NamedAttestation V)) (h : Height)
    (B : Block V) : Prop :=
  ∃ (Q : Finset V) (X : Block V), E.electorate.IsQuorum Q ∧
    Block.preceq X B = true ∧
    ∀ i ∈ Q, ∃ a ∈ A, a.val_index = i ∧ a.height_pair.matchesEntry h X.root = true

/-- A quorum of named timeout rows at height `H` naming entry `T`. -/
def NamedTimeoutQuorumAt (E : Env V) (H : Height) (T : BlockId)
    (ats : List (NamedAttestation V)) : Prop :=
  ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
    ∀ i ∈ Q, ∃ a ∈ ats, a.val_index = i ∧ a.height_pair = .vote H T true

/-- A quorum of named target rows at height `H` naming entry `T`. -/
def NamedTargetQuorumAt (E : Env V) (H : Height) (T : BlockId)
    (ats : List (NamedAttestation V)) : Prop :=
  ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
    ∀ i ∈ Q, ∃ a ∈ ats, a.val_index = i ∧ a.height_pair = .vote H T false

/-- The full named rows carried by a chain (the named twin of `chain_attestations`). -/
def named_chain_attestations : NamedBlock V → Finset (NamedAttestation V)
  | .genesis => ∅
  | .node p _ _ _ _ ats _ => named_chain_attestations p ∪ ats.toFinset

/-- The targeted fold over one block's rows, exactly as the named transition
stages it: slot written first, rows folded, latest block written last. -/
def foldNamedBlock (σ : ChainState V) (B : NamedBlock V) : ChainState V :=
  fold_rows (TimeoutBinding.targeted V) σ B.erase B.attestations



/-- Q-C1: erasure weakens a named crossing to the previous crossing. -/
def NamedCrossingErasesQuery (E : Env V) (A : Finset (NamedAttestation V)) (h : Height)
    (B : Block V) : Prop :=
  NamedCrossingWitness E A h B →
    Protocol.CrossingWitness E (A.image NamedAttestation.erase) h B

/-- Q-C2: a named derived height above `h ≥ 1` has a named crossing at `h`. -/
def NamedHeightCrossingQuery (E : Env V) (cfg : HeightConfig) (h : Height) : Prop :=
  1 ≤ h → ∀ C : NamedBlock V, h < (derive_named E cfg C).h →
    NamedCrossingWitness E (named_chain_attestations C) h C.erase

/-- Q-C3: a matching timeout quorum on a mature entry advances the height by one.
The entry match `σ.T_h.root = T` is the new hypothesis; the previous lemma had none. -/
def NamedTimeoutQuorumCrossesQuery (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ (σ : ChainState V) (B : NamedBlock V) (H : Height) (T : BlockId),
    σ.h = H → σ.T_h.root = T →
    σ.T_h.slot + cfg.timeoutDelay ≤ B.erase.slot →
    NamedTimeoutQuorumAt E H T B.attestations →
    (named_transition E cfg σ B).h = H + 1

/-- Q-C4: a matching target quorum advances the height and sets target participation. -/
def NamedTargetQuorumCrossesQuery (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ (σ : ChainState V) (B : NamedBlock V) (H : Height) (T : BlockId),
    σ.h = H → σ.T_h.root = T →
    NamedTargetQuorumAt E H T B.attestations →
    (named_transition E cfg σ B).h = H + 1

/-- Q-C5: a mismatching row adds no height bit (the unified test, spec Addendum E). -/
def MismatchAddsNothingQuery (_E : Env V) : Prop :=
  ∀ (σ : ChainState V) (a : NamedAttestation V),
    a.height_pair.matchesEntry σ.h σ.T_h.root = false →
    (process_attestation_with (TimeoutBinding.targeted V) σ a).progress = σ.progress ∧
    (process_attestation_with (TimeoutBinding.targeted V) σ a).target_participation =
      σ.target_participation

end DecoupledConsensusModel.Protocol

end
