module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.FinalizationBridge
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier
public import DecoupledConsensusProofs.Execution.OutageProvenance

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace Bridges

open Internal Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The finalization half -/

/-- **The store's finalized block is recomputed on a body the store retains.**
The named form of `Protocol.StoreFinalizationOnChain` at a strict pre-time read.
No admissibility premise: `Proofs.NamedRuntime.stateBeforeTime_invariants` is local.
The height bound is a free extra the named carrier already proves. -/
theorem storeFinalizationOnChain_stateBeforeTime (S : Setup V) (rho : NamedRun V)
    (t : Time) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBeforeTime S rho t v).st.bodies ∧
      (derive_named S.E S.cfg D).F = (NamedRun.stateBeforeTime S rho t v).st.core.F ∧
      (derive_named S.E S.cfg D).h_F < (NamedRun.stateBeforeTime S rho t v).st.core.h_max :=
  NamedFinalizationBridge.finalization_carrier_stateBeforeTime S rho t v

/-- Index form of `storeFinalizationOnChain_stateBeforeTime`. -/
theorem storeFinalizationOnChain_stateBefore (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
      (derive_named S.E S.cfg D).F = (NamedRun.stateBefore S rho i v).st.core.F ∧
      (derive_named S.E S.cfg D).h_F < (NamedRun.stateBefore S rho i v).st.core.h_max :=
  NamedFinalizationBridge.finalization_carrier_stateBefore S rho i v

/-! ## 2. The justification half -/


/-- **The named on-chain justification predicate** ( 1636 crosswalk,
addendum 35 ). The named twin of `Proofs.Bridges.StoreJustificationOnChain`: the
store's justified block and its height are recomputed on a body the store
actually retains, never on an erasure. -/
def NamedStoreJustificationOnChain (S : Setup V) (st : Protocol.NamedStore V) : Prop :=
  ∃ D ∈ st.bodies, (derive_named S.E S.cfg D).J = st.core.J ∧
    (derive_named S.E S.cfg D).h_j = st.core.h_j


/-- **The store's justified block is recomputed on a body the store retains.**
The named form of `Proofs.Bridges.StoreJustificationOnChain`, same premise set. -/
theorem storeJustificationOnChain_stateBeforeTime (S : Setup V) (rho : NamedRun V)
    (t : Time) (v : V) :
    NamedStoreJustificationOnChain S (NamedRun.stateBeforeTime S rho t v).st :=
  NamedJustificationCarrier.justification_carrier_stateBeforeTime S rho t v

theorem storeJustificationOnChain_readAt (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    NamedStoreJustificationOnChain S (NamedRun.readAt S rho t v).st :=
  NamedJustificationCarrier.justification_carrier_readAt S rho t v





/-- Index form of the justification carrier. -/
theorem storeJustificationOnChain_stateBefore (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) :
    NamedStoreJustificationOnChain S (NamedRun.stateBefore S rho i v).st :=
  NamedJustificationCarrier.justification_carrier_stateBefore S rho i v





/-- **The named provenance pair**. `Proofs.Bridges.Provenance` is the
finalization and justification halves together, because `update_finality`
writes both from the same chain state in the same call. This is its named
form, and like its halves it takes no premise. -/
def NamedProvenance (S : Setup V) (st : Protocol.NamedStore V) : Prop :=
  (∃ D ∈ st.bodies, (derive_named S.E S.cfg D).F = st.core.F ∧
      (derive_named S.E S.cfg D).h_F < st.core.h_max) ∧
    NamedStoreJustificationOnChain S st


theorem namedProvenance_stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    NamedProvenance S (NamedRun.stateBefore S rho i v).st :=
  ⟨NamedFinalizationBridge.finalization_carrier_stateBefore S rho i v,
    storeJustificationOnChain_stateBefore S rho i v⟩

theorem namedProvenance_stateBeforeTime (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    NamedProvenance S (NamedRun.stateBeforeTime S rho t v).st :=
  ⟨NamedFinalizationBridge.finalization_carrier_stateBeforeTime S rho t v,
    storeJustificationOnChain_stateBeforeTime S rho t v⟩

theorem namedProvenance_readAt (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    NamedProvenance S (NamedRun.readAt S rho t v).st :=
  ⟨NamedFinalizationBridge.finalization_carrier_readAt S rho t v,
    storeJustificationOnChain_readAt S rho t v⟩


/-! ## 3. Carried honest rows are past emissions -/

/-- **A carried honest row was emitted, at its own action, no later than the
block that carries it was processed.** The named form of
`Proofs.Bridges.carriedArePastEmissions_of_admissible` for a processed block. It takes
`NamedUnforgeable` alone, not a full admissible core. -/
theorem carriedArePastEmissions_of_processes (S : Setup V) (rho : NamedRun V)
    (auth : NamedUnforgeable S rho)
    {receiver : V} {B : NamedBlock V} {a : NamedAttestation V} {t : Time}
    (hB : NamedRun.processes S rho receiver (.block B) t)
    (ha : a ∈ B.attestations) (hHon : a.val_index ∈ rho.honest) :
    S.a a.round ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) :=
  NamedOutageProvenance.honest_carried_row_emission S rho auth hB ha hHon

/-- The admissible-core form of `carriedArePastEmissions_of_processes`. -/
theorem carriedArePastEmissions_of_admissibleCore (S : Setup V) {rho : NamedRun V}
    (adm : NamedAdmissibleCore S rho)
    {receiver : V} {B : NamedBlock V} {a : NamedAttestation V} {t : Time}
    (hB : NamedRun.processes S rho receiver (.block B) t)
    (ha : a ∈ B.attestations) (hHon : a.val_index ∈ rho.honest) :
    S.a a.round ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) :=
  carriedArePastEmissions_of_processes S rho adm.toNamedUnforgeable hB ha hHon

/-- **A held honest row was accepted earlier and emitted at its own action.**
The held-row form, for a row already in the reader's own SG rows. -/
theorem heldArePastEmissions_of_admissibleCore (S : Setup V) {rho : NamedRun V}
    (adm : NamedAdmissibleCore S rho) (i : Nat) (receiver : V)
    {a : NamedAttestation V}
    (ha : a ∈ (NamedRun.stateBefore S rho i receiver).st.sg_rows a.round)
    (hHon : a.val_index ∈ rho.honest) :
    ∃ j : Nat, j < i ∧ ∃ t : Time,
      NamedRun.acceptsAt S rho j receiver (.attest a) t ∧
      S.a a.round ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) :=
  NamedOutageProvenance.honest_held_row_emission S rho adm.toNamedUnforgeable i receiver ha hHon


/-! ## 4. Carried rows of an ancestor, erased -/

/-- **A row carried by an ancestor of a named block is in the erased block's
chain attestations.** The erasure of `chain_attestations`: `NamedBlock.erase`
maps a node's rows pointwise and keeps its parent, and `chain_attestations`
unions a node's rows with its parent's, so the two commute along the chain. -/
theorem erase_mem_chain_attestations (D : NamedBlock V) :
    ∀ carrier : NamedBlock V, NamedBlock.Preceq carrier D →
      ∀ a : NamedAttestation V, a ∈ carrier.attestations →
        a.erase ∈ chain_attestations D.erase := by
  induction D with
  | genesis =>
    intro carrier hc a ha
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hc
    subst hc
    simp only [NamedBlock.attestations, List.not_mem_nil] at ha
  | node p sl r gv sup rows pr ih =>
    intro carrier hc a ha
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hc
    show a.erase ∈ chain_attestations
      (Block.node p.erase sl r gv sup (rows.map NamedAttestation.erase) pr)
    simp only [chain_attestations, Finset.mem_union]
    rcases hc with rfl | hcp
    · exact Or.inl (List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨a, by simpa only [NamedBlock.attestations] using ha, rfl⟩))
    · exact Or.inr (ih carrier hcp a ha)

#print axioms erase_mem_chain_attestations

#print axioms storeFinalizationOnChain_stateBeforeTime
#print axioms storeFinalizationOnChain_stateBefore
#print axioms storeJustificationOnChain_stateBeforeTime
#print axioms storeJustificationOnChain_stateBefore
#print axioms namedProvenance_stateBefore
#print axioms carriedArePastEmissions_of_processes
#print axioms carriedArePastEmissions_of_admissibleCore
#print axioms heldArePastEmissions_of_admissibleCore

end Bridges
end Proofs
end DecoupledConsensusModel

end
