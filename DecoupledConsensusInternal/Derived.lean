module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.Evidence
public import DecoupledConsensusInternal.Roots

@[expose] public section

/-!
# P1 substrate — derived chain states and slashing evidence
(design note P1; PROTOCOL.md#the-complete-protocol)

The chain-level objects `P1` is stated over. Everything here is a definition:
this library states, it never proves (`conventions.md:4`, extended by
`the design note:29–30`).

Three shapes are forced here.

* **The chain state is derived from the block, not read from a store.**
  "`σ[B] = state_transition(σ[B.parent], B)` is a deterministic function of the
  chain ending at `B`" (PROTOCOL.md#the-complete-protocol). `derived_state` is that
  function, folded structurally from `ChainState.initial` at genesis — which is
  the value the model's total `σ[·]` map already gives genesis
  (modeling-choices row 3). No store appears in the statement of P1.
* **The evidence set is the carried attestations of the chain.** `Σ.σ[·]` is
  written only by `on_block`, and the only attestations any transition
  folds are `B.attestations` for blocks `B` on the chain
  (PROTOCOL.md#the-complete-protocol); nothing else can move a chain state. So
  `chain_attestations` is the whole evidence pool of a derived state.
* **Slashing evidence names the two histories that expose it.** E1 and E2 are
  relations on two occurrences, so a witness draws one occurrence from each
  side's carried attestations, with `a = b` permitted — "the conflicting
  occurrences can be in one attestation" (PROTOCOL.md#the-complete-protocol). The scoped form is
  the conclusion, the pool form is the hypothesis, and the conversion runs one
  way; see the evidence section below.
-/

namespace DecoupledConsensusModel
namespace Internal

open Protocol (ChainState HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The derived chain state (PROTOCOL.md#the-complete-protocol) -/

/-! ## Slashing evidence — scoped and unscoped (PROTOCOL.md#the-complete-protocol)
The previous formalization's discipline, restated (
§1.4, §1.6). Two forms of the same notion:
* **scoped** — `SlashableBetween`, naming the two evidence sets that expose the
  conflict, one witness drawn from each. This is the *conclusion* form: a caller
  gets the histories that convict, not merely the fact that someone is
  convictable.
* **unscoped** — the evidence sets existentially closed. This is the previous repo's
  *hypothesis* form, and it **does not proof**: see `SlashableAnywhere`.
The conversion runs one way only, scoped to unscoped, and never back.
-/

/-- P1 `i` is slashable **within** one evidence pool: both witnesses drawn from
the same set (PROTOCOL.md#the-complete-protocol). The pool-scoped analogue of the previous repo's
unscoped `IsSlashable`, and the form a store-facing hypothesis can use, because
the pool is a real object rather than an existential over constructible
blocks. -/
def SlashableIn (A : Finset (CombinedAttestation V)) (i : V) : Prop :=
  SlashableBetween A A i

/-- P1 the literal proof of the previous repo's unscoped `IsSlashable`
(`Certificates.lean:87`): the histories existentially closed over.
**Degenerate in this model, and stated only to record that.**
`Proofs.slashableAnywhere_of_any` proves it holds of *every* validator: `Block`
is a free inductive (`Substrate/Blocks.lean:88`) carrying an unconstrained
attestation list and no authentication step, so two one-block histories
convicting any `i` can always be written down. A `¬`-of-this hypothesis would
therefore be `False`, and any statement taking it would be vacuous. Store-facing
hypotheses use `NoSlashableWeightIn` over a real pool instead (choices P1.2). -/
def SlashableAnywhere (i : V) : Prop :=
  ∃ B₁ B₂ : Block V, SlashableBetween (chain_attestations B₁) (chain_attestations B₂) i

/-- P1 slashable weight `2q − W` **within** one evidence pool. -/
def HasSlashableWeightIn (E : Env V) (A : Finset (CombinedAttestation V)) : Prop :=
  ∃ S : Finset V, HasIntersectionWeight E S ∧ ∀ i ∈ S, SlashableIn A i

/-- P1 no slashable weight in a pool: the **hypothesis** form, for statements
that consume accountability rather than produce it (`accountable-safety-port.md`
§1.6). Pool-scoped, not existentially closed — see `SlashableAnywhere`. -/
def NoSlashableWeightIn (E : Env V) (A : Finset (CombinedAttestation V)) : Prop :=
  ¬ HasSlashableWeightIn E A

/-! ## The sharp E1 carrier (PROTOCOL.md#the-complete-protocol) -/

/-- P1 one validator's **E1** evidence against **one fixed finality pair**: `i`
signed `p` on one side and a height pair conflicting with `p` on the other
(PROTOCOL.md#the-complete-protocol).

The pair is a **parameter**, deliberately: `HasE1WeightAt` binds it outside the
signer set, so every counted signer convicts against the *same* `⟨h, T⟩`. Making
it an inner existential — `∀ i ∈ S, ∃ hᵢ` — is a strictly weaker claim, and is
the bug the weighted repo's first review caught
(§4). -/
def E1EvidenceForPair (p : FinalityPair) (A₁ A₂ : Finset (CombinedAttestation V))
    (i : V) : Prop :=
  ∃ a ∈ A₁, ∃ b ∈ A₂, a.val_index = i ∧ b.val_index = i ∧
    a.finality_pair = some p ∧
    Protocol.conflictsWithFinality b.height_pair p = true

/-- P1 at least `2q − W` weight has E1 evidence against the **one** pair `p`
(PROTOCOL.md#the-complete-protocol).

Quantifier order, outermost first: `p`, then `∃ S`, then `∀ i ∈ S`. -/
def HasE1WeightAt (E : Env V) (p : FinalityPair)
    (A₁ A₂ : Finset (CombinedAttestation V)) : Prop :=
  ∃ S : Finset V, HasIntersectionWeight E S ∧ ∀ i ∈ S, E1EvidenceForPair p A₁ A₂ i



/-- P1/U one validator's **E2** evidence against **one fixed height and pair of
roots** (PROTOCOL.md#the-complete-protocol).

The mirror of `E1EvidenceForPair`, with the same quantifier discipline: `h`, `T₁`
and `T₂` are parameters, bound outside the signer set by `HasE2WeightAt`, so
every counted signer convicts at the *same* height for the *same* two roots. -/
def E2EvidenceAtHeight (h : Height) (T₁ T₂ : BlockId)
    (A₁ A₂ : Finset (CombinedAttestation V)) (i : V) : Prop :=
  ∃ a ∈ A₁, ∃ b ∈ A₂, a.val_index = i ∧ b.val_index = i ∧
    a.height_pair = HeightPair.target h T₁ ∧ b.height_pair = HeightPair.target h T₂

/-- P1/U at least `2q − W` weight has E2 evidence at the one height `h` against
the two roots (PROTOCOL.md#the-complete-protocol). Quantifier order, outermost
first: `h`, `T₁`, `T₂`, then `∃ S`, then `∀ i ∈ S`. -/
def HasE2WeightAt (E : Env V) (h : Height) (T₁ T₂ : BlockId)
    (A₁ A₂ : Finset (CombinedAttestation V)) : Prop :=
  ∃ S : Finset V, HasIntersectionWeight E S ∧
    ∀ i ∈ S, E2EvidenceAtHeight h T₁ T₂ A₁ A₂ i

/-! ## Agreement with the store map (PROTOCOL.md#the-complete-protocol) -/


/-- P1/P6 the store's `Σ.σ[·]` agrees with the derived state on every processed
block (PROTOCOL.md#the-complete-protocol).

`on_block` computes `σ[B]` incrementally from `Σ.σ[B.parent]`, so the two
coincide only when the parent's entry was itself computed — which is the
dependency-complete contract (O8), not a property of the handler. Stated here as
the bridge P1's store-level corollary needs; it is a future lemma, not a
definitional fact. -/
def DerivedStateAgrees (E : Env V) (cfg : HeightConfig) (st : Protocol.Store V) : Prop :=
  ∀ B ∈ st.T, st.σ B = derived_state E cfg B

end Internal
end DecoupledConsensusModel

end
