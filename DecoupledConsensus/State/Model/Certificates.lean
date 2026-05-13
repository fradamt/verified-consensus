import DecoupledConsensus.State.Model.StateMachine

namespace DecoupledConsensus

/-! # Accountable Safety Model: certificates

External certificate and structural slashability predicates.
These are model/spec predicates; their properties are proved in proof modules. -/

variable {n : ℕ}

open scoped Block

/-! ### Vote-tracking infrastructure

For the main-safety lemma, we need to extract concrete votes from quorums in state.
`votesIncluded` flattens the embedded vote payloads along a chain. The model
treats those payloads as the structural evidence; if a concrete protocol adds
working signatures, this evidence is exactly what signatures authenticate. -/

/-- All votes included in any block of the chain (oldest first). -/
def votesIncluded {n : ℕ} :
    ∀ {B : Block n}, Chain n B → List (Vote n)
  | _, .genesis => []
  | _, @Chain.extend _ parent c bid newSlot votes _ =>
      votesIncluded c ++ (Block.mk bid parent newSlot votes).votes

/-- A quorum of validators contributed finalize commitments for block `C` at
    height `h_f`. This is proof/certificate data, not protocol state. -/
def FinalizeQuorumWitness (votes : List (Vote n)) (C : Block n) (h_f : ℕ) : Prop :=
  ∃ Q : Finset (Validator n), IsQuorumStrict n Q ∧
    ∀ i ∈ Q, ∃ v ∈ votes, v.validator = i ∧
      v.finalize = some (h_f, C.id)

/-- A quorum of validators justified block `C` at height `h_f`. -/
def JustifyQuorumWitness (votes : List (Vote n)) (C : Block n) (h_f : ℕ) : Prop :=
  ∃ Q : Finset (Validator n), IsQuorumStrict n Q ∧
    ∀ i ∈ Q, ∃ v ∈ votes, v.validator = i ∧
      v.target = some C.id ∧ v.height = h_f

/-- Certificate attached to the event "the state variable `F` was set to `C`
    at height `h_f`". The height is witness/certificate data used to state
    finality externally; it is not stored in `State`.

    For non-genesis finality, the certificate records:
    - a finalize quorum for `(C, h_f)`;
    - the justification quorum that made `C` eligible for finality at `h_f`;
    - the height-closed block-state fact `σ[C].h = h_f`;
    - that the witnessing chain has advanced past `h_f`. -/
def FinalizedCertificate {n : ℕ} {B : Block n}
    (chain : Chain n B) (C : Block n) (h_f : ℕ) (hC : C ≼ B) : Prop :=
  (h_f = 0 ∧ C = Block.genesis) ∨
    (h_f > 0 ∧
      FinalizeQuorumWitness (votesIncluded chain) C h_f ∧
      JustifyQuorumWitness (votesIncluded chain) C h_f ∧
      (stateOf (chain.subchain hC)).h = h_f ∧
      (stateOf chain).h > h_f)

/-! ## Slashing aggregate -/

/-- A validator is slashable if two conflicting votes with that validator field
    appear in chain histories. This is the structural accountability conclusion;
    a concrete signature layer can authenticate the vote payloads externally. -/
def IsSlashable (i : Validator n) : Prop :=
  ∃ B₁ : Block n, ∃ chain₁ : Chain n B₁,
  ∃ B₂ : Block n, ∃ chain₂ : Chain n B₂,
  ∃ a ∈ votesIncluded chain₁, ∃ b ∈ votesIncluded chain₂,
    a.validator = i ∧ b.validator = i ∧ Vote.Slashable a b

/-- "At least `f + 1` slashable validators" — strictly more than the
    adversary budget `f`, i.e., the safety property is broken accountably.
    This is the literal `card ≥ f + 1` form under the BFT convention
    `n = 3 * f + 1`. -/
def AtLeastFThirdSlashable (f : ℕ) : Prop :=
  ∃ S : Finset (Validator n), S.card ≥ f + 1 ∧ ∀ i ∈ S, IsSlashable i

end DecoupledConsensus
