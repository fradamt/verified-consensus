module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.Certificates
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open DecoupledConsensusModel.Execution

/-! ## Symmetry of the two symmetric notions (PROTOCOL.md#the-complete-protocol) -/

section Symmetry

variable {V : Type} [DecidableEq V]

/-- §1 compatibility is symmetric (PROTOCOL.md#the-complete-protocol). -/
theorem compatible_comm {B C : Block V} (h : Block.compatible B C = true) :
    Block.compatible C B = true := by
  simp only [Block.compatible, Bool.or_eq_true] at h ⊢
  exact h.symm

/-- P1 root injectivity is inherited by a smaller scope (PROTOCOL.md#the-complete-protocol). -/
theorem RootInjectiveBelow.mono {S S' : Finset (Block V)}
    (h : Execution.RootInjectiveBelow S')
    (hs : S ⊆ S') : Execution.RootInjectiveBelow S := by
  intro A C hA hC hr
  obtain ⟨B, hB, hAB⟩ := hA
  obtain ⟨B', hB', hCB'⟩ := hC
  exact h A C ⟨B, hs hB, hAB⟩ ⟨B', hs hB', hCB'⟩ hr

/-- P1 root injectivity is symmetric in the two tips (PROTOCOL.md#the-complete-protocol). The
old `idInjectiveOnAncestors_sym` (`accountable-safety-port.md` §2 node 3). -/
theorem rootInjectiveOnAncestors_symm {B₁ B₂ : Block V}
    (h : Execution.RootInjectiveOnAncestors B₁ B₂) :
    Execution.RootInjectiveOnAncestors B₂ B₁ :=
  RootInjectiveBelow.mono h (by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_insert_self _ _)

/-- P1 the pair-pinned E1 carrier read in the **other** pool order
(PROTOCOL.md#the-complete-protocol).

`e1Fields` tests each side's finality pair against the other's height pair, so
one occurrence of `Slashable` covers both orientations; only the pair-pinned
carrier is directional. This is the conversion the strict-order branch of the
composition needs. -/
theorem slashableBetween_of_e1EvidenceForPair_swap {p : FinalityPair}
    {A₁ A₂ : Finset (CombinedAttestation V)} {i : V}
    (h : E1EvidenceForPair p A₂ A₁ i) : SlashableBetween A₁ A₂ i := by
  obtain ⟨a, ha, b, hb, hav, hbv, hfp, hcf⟩ := h
  refine ⟨b, hb, a, ha, hbv, hav, ?_⟩
  have h1 : Protocol.e1Slashable b a = true := by
    simp only [Protocol.e1Slashable, Protocol.sameValidator,
      Protocol.e1Fields, hfp, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, Option.elim]
    exact ⟨by rw [hbv, hav], Or.inr hcf⟩
  change Protocol.slashable b a = true
  simp only [Protocol.slashable, h1, Bool.true_or]

variable [Fintype V]

/-- P1 the same, aggregated (PROTOCOL.md#the-complete-protocol). -/
theorem hasSlashableWeightBetween_of_hasE1WeightAt_swap {E : Env V} {p : FinalityPair}
    {A₁ A₂ : Finset (CombinedAttestation V)} (h : HasE1WeightAt E p A₂ A₁) :
    HasSlashableWeightBetween E A₁ A₂ := by
  obtain ⟨S, hw, hev⟩ := h
  exact ⟨S, hw, fun i hi => slashableBetween_of_e1EvidenceForPair_swap (hev i hi)⟩

/-- P1 slashable weight survives pool growth (PROTOCOL.md#the-complete-protocol). -/
theorem hasSlashableWeightBetween_mono {E : Env V}
    {A₁ A₂ A₁' A₂' : Finset (CombinedAttestation V)}
    (h : HasSlashableWeightBetween E A₁ A₂) (h₁ : A₁ ⊆ A₁') (h₂ : A₂ ⊆ A₂') :
    HasSlashableWeightBetween E A₁' A₂' := by
  obtain ⟨S, hw, hev⟩ := h
  refine ⟨S, hw, fun i hi => ?_⟩
  obtain ⟨a, ha, b, hb, hav, hbv, hs⟩ := hev i hi
  exact ⟨a, h₁ ha, b, h₂ hb, hav, hbv, hs⟩

end Symmetry

/-! ## The named/erased evidence crosswalk (PROTOCOL.md#the-complete-protocol)

Erasure is valid in exactly one direction here: a **named** row carried by a
named ancestor is evidence held by the **erased** tip, and an entry-naming
named row erases to a row that convicts. The reverse — recomputing chain state
across erasure — is not valid, which is why `Internal.ChainAccountableSafety` is
stated over `derive_named` and proved in `Protocol.NamedMain`.

These two lemmas are the whole crosswalk, and they live here because they need
nothing from the named derivation: only `NamedBlock.erase` and
`NamedAttestation.erase`.
-/

section NamedCrosswalk

variable {V : Type} [DecidableEq V]

/-- P1 a named row carried by a named ancestor is evidence of the erased tip
(PROTOCOL.md#the-complete-protocol).

`NamedBlock.erase` maps a node's row list pointwise, and
`Proofs.NamedWire.erase_preceq` carries named ancestry to erased ancestry, so
`chain_attestations` of the erased tip already holds every erased row of every
named ancestor. -/
theorem named_row_erase_mem {tip carrier : NamedBlock V} {a : NamedAttestation V}
    (hc : NamedBlock.Preceq carrier tip) (ha : a ∈ carrier.attestations) :
    a.erase ∈ chain_attestations tip.erase := by
  refine chain_attestations_mono (Proofs.NamedWire.erase_preceq hc) ?_
  cases carrier with
  | genesis => simp only [NamedBlock.attestations, List.not_mem_nil] at ha
  | node p s r votes support rows proposer =>
    exact mem_chain_attestations_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)

omit [DecidableEq V] in
/-- P1 an entry-naming named row erases to a row that conflicts with any
finality pair at the same height on a different root (PROTOCOL.md#the-complete-protocol).

Both annotations convict: a proper target erases to `.target h X`, which
conflicts because the roots differ; a timeout erases to `.timeout h`, which
conflicts on the height alone. The targeted rule makes the timeout row name the
entry too, and that extra content is **not** needed here — the argument is the
old one. -/
theorem conflictsWithFinality_erase_of_matchesEntry {a : NamedAttestation V}
    {h : Height} {X T : BlockId} (hm : a.height_pair.matchesEntry h X = true)
    (hne : X ≠ T) :
    Protocol.conflictsWithFinality a.erase.height_pair ⟨h, T⟩ = true := by
  have hbe : a.erase.height_pair = a.height_pair.erase := rfl
  rw [hbe]
  cases hp : a.height_pair with
  | empty =>
    rw [hp] at hm
    simp only [NamedHeightPair.matchesEntry] at hm
    exact absurd hm Bool.false_ne_true
  | vote height entry timeout =>
    rw [hp] at hm
    simp only [NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    cases timeout <;>
      simp [NamedHeightPair.erase, Protocol.conflictsWithFinality, hne]

end NamedCrosswalk

/-! ## The oriented core (PROTOCOL.md#the-complete-protocol) -/


/-! ## The headline statements (PROTOCOL.md#the-complete-protocol) -/


/-! ## The store-level corollary (PROTOCOL.md#the-complete-protocol) -/

section HealingStore

variable {V : Type} [DecidableEq V] [Fintype V]



/-- P1 the store's finalization is realized by a processed block's **derived**
state (PROTOCOL.md#the-complete-protocol).

The missing link of the store corollary, and it is not free. -/
def StoreFinalizationOnChain (E : Env V) (cfg : HeightConfig)
    (st : Protocol.Store V) : Prop :=
  ∃ B ∈ st.T, (derived_state E cfg B).F = st.F

/-- P1 a processed block's evidence is the store's evidence
(PROTOCOL.md#the-complete-protocol). -/
theorem chain_attestations_subset_store {W : Type} [DecidableEq W]
    {st : Protocol.Store W} {B : Block W} (hB : B ∈ st.T) :
    chain_attestations B ⊆ store_attestations st :=
  Finset.subset_biUnion_of_mem chain_attestations hB



end HealingStore


end Protocol
end DecoupledConsensusModel

end
