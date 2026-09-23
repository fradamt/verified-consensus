module
public import DecoupledConsensusModel
public import DecoupledConsensusInternal.ModelVocabulary.Substrate.Weights

@[expose] public section

/-! Proof-free witness definitions shared by statement and proof modules. -/

namespace DecoupledConsensusModel

namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def CrossingWitness (E : Env V) (A : Finset (CombinedAttestation V)) (h : Height)
    (B : Block V) : Prop :=
  ∃ (Q : Finset V) (X : Block V), E.electorate.IsQuorum Q ∧
    Block.preceq X B = true ∧
    ∀ i ∈ Q, ∃ a ∈ A, a.val_index = i ∧
      (a.height_pair = HeightPair.target h X.root ∨
        a.height_pair = HeightPair.timeout h)

end Protocol

namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def CommitteePools (E : Env V) (st : Protocol.Store V) : Prop :=
  ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k →
    u.val_index ∈ E.committee k

end Protocol

end DecoupledConsensusModel

end
