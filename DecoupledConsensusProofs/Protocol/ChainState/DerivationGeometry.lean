module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.NamedStore
public import DecoupledConsensusProofs.Protocol.ChainState.Chain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records

@[expose] public section

/-! Structural geometry of the named derivation, split out of
`NamedStoreRoots` so that the optimistic action layer can use it. The two
consumers sit on opposite sides of `NamedAdmission`, so they cannot share
that module. Nothing here is an execution or authenticity claim. -/
namespace DecoupledConsensusModel.Proofs.NamedDerivationGeometry
open DecoupledConsensusModel Protocol
variable {V Row : Type} [DecidableEq V]

/-- The checked single-row context theorem lifts through any actual bound
row fold, including the targeted named-row specialization. -/
theorem fold_context_fields (binding : TimeoutBinding V Row)
    (rows : List Row) (st : ChainState V) :
    let out := rows.foldl (process_attestation_with binding) st
    out.L = st.L ∧ out.h = st.h ∧ out.T_h = st.T_h ∧ out.J = st.J ∧
      out.h_j = st.h_j ∧ out.F = st.F ∧ out.h_F = st.h_F := by
  induction rows generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons row rows ih =>
    have one := TimeoutBindingDefaults.process_context_fields binding st row
    have rest := ih (process_attestation_with binding st row)
    exact ⟨rest.1.trans one.1, rest.2.1.trans one.2.1,
      rest.2.2.1.trans one.2.2.1, rest.2.2.2.1.trans one.2.2.2.1,
      rest.2.2.2.2.1.trans one.2.2.2.2.1,
      rest.2.2.2.2.2.1.trans one.2.2.2.2.2.1,
      rest.2.2.2.2.2.2.trans one.2.2.2.2.2.2⟩

/-- The only ancestry premise is the local extension of the previous latest block.
The named derivation below supplies it from its real structural parent. -/
theorem chainOrder_fold_rows (binding : TimeoutBinding V Row) (st : ChainState V)
    (geometry : Block V) (rows : List Row) (h : Protocol.ChainOrder st)
    (hL : Block.Preceq st.L geometry) : Protocol.ChainOrder (fold_rows binding st geometry rows) := by
  have fields := fold_context_fields binding rows { st with s := geometry.slot }
  refine {
    target_preceq_latest := ?_
    justified_preceq_target := ?_
    finalized_preceq_justified := ?_
    heights_ordered := ?_
    justified_below_height := ?_ }
  · change Block.Preceq (rows.foldl (process_attestation_with binding)
      { st with s := geometry.slot }).T_h geometry
    rw [fields.2.2.1]
    exact Block.preceq_trans h.target_preceq_latest hL
  · change Block.Preceq (rows.foldl (process_attestation_with binding)
      { st with s := geometry.slot }).J
      (rows.foldl (process_attestation_with binding) { st with s := geometry.slot }).T_h
    rw [fields.2.2.2.1, fields.2.2.1]
    exact h.justified_preceq_target
  · change Block.Preceq (rows.foldl (process_attestation_with binding)
      { st with s := geometry.slot }).F
      (rows.foldl (process_attestation_with binding) { st with s := geometry.slot }).J
    rw [fields.2.2.2.2.2.1, fields.2.2.2.1]
    exact h.finalized_preceq_justified
  · change (rows.foldl (process_attestation_with binding) { st with s := geometry.slot }).h_F ≤
      (rows.foldl (process_attestation_with binding) { st with s := geometry.slot }).h_j
    rw [fields.2.2.2.2.2.2, fields.2.2.2.2.1]
    exact h.heights_ordered
  · change (rows.foldl (process_attestation_with binding) { st with s := geometry.slot }).h_j <
      (rows.foldl (process_attestation_with binding) { st with s := geometry.slot }).h
    rw [fields.2.2.2.2.1, fields.2.1]
    exact h.justified_below_height

variable [Fintype V]

private theorem height_events_latest (E : Env V) (cfg : HeightConfig) (st : ChainState V) :
    (process_height_events E cfg st).L = st.L := by
  rw [Protocol.process_height_events_eq]
  split_ifs <;> simp only [advance_height, Protocol.afterFin_L]

theorem named_transition_latest (E : Env V) (cfg : HeightConfig)
    (st : ChainState V) (B : NamedBlock V) : (named_transition E cfg st B).L = B.erase := by
  unfold named_transition transition_rows
  rw [height_events_latest]
  rfl

theorem derive_named_latest (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (derive_named E cfg B).L = B.erase := by
  cases B with
  | genesis => rfl
  | node parent slot root votes support rows proposer =>
    exact named_transition_latest E cfg (derive_named E cfg parent) _

/-- Actual named derivation has the usual ancestor and height order. The
proof never equates it with compatibility derivation on B.erase. -/
theorem chainOrder_derive_named (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    Protocol.ChainOrder (derive_named E cfg B) := by
  induction B with
  | genesis => exact Protocol.chainOrder_initial
  | node parent slot root votes support rows proposer ih =>
    rw [BlockProcessingDefaults.derive_named_node]
    unfold named_transition transition_rows
    apply Protocol.chainOrder_process_height_events E cfg
    apply chainOrder_fold_rows (TimeoutBinding.targeted V) _ _ _ ih
    rw [derive_named_latest]
    exact Protocol.preceq_node parent.erase slot root votes support
      (rows.map NamedAttestation.erase) proposer

theorem derive_named_anchors_preceq (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    Block.Preceq (derive_named E cfg B).F B.erase ∧
      Block.Preceq (derive_named E cfg B).J B.erase := by
  have h := chainOrder_derive_named E cfg B
  refine ⟨?_, ?_⟩
  · simpa only [derive_named_latest] using h.finalized_preceq_latest
  · simpa only [derive_named_latest] using
      Block.preceq_trans h.justified_preceq_target h.target_preceq_latest

omit [Fintype V] in
private theorem named_parent_geometry (B : NamedBlock V) :
    Block.Preceq B.parent.erase B.erase := by
  cases B with
  | genesis => exact Block.preceq_self _
  | node parent slot root votes support rows proposer =>
    exact Protocol.preceq_node parent.erase slot root votes support
      (rows.map NamedAttestation.erase) proposer

/-- The named transition's justification is an ancestor of the body. -/
theorem transition_justification_ancestor (E : Env V) (cfg : HeightConfig)
    (B : NamedBlock V) :
    Block.Preceq (named_transition E cfg (derive_named E cfg B.parent) B).J B.erase := by
  have hfold := chainOrder_fold_rows (TimeoutBinding.targeted V)
    (derive_named E cfg B.parent) B.erase B.attestations
    (chainOrder_derive_named E cfg B.parent)
    (by rw [derive_named_latest]; exact named_parent_geometry B)
  have h := Protocol.chainOrder_process_height_events E cfg hfold
  have hJ := Block.preceq_trans h.justified_preceq_target h.target_preceq_latest
  change Block.Preceq (named_transition E cfg (derive_named E cfg B.parent) B).J
    (named_transition E cfg (derive_named E cfg B.parent) B).L at hJ
  rwa [named_transition_latest] at hJ

/-- Scoped named parent closure supplies actual geometry ancestor membership. -/
theorem core_ancestor_mem (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (h : Proofs.NamedStore.Coherent E cfg st) {X Y : Block V}
    (hX : X ∈ st.core.T) (hYX : Block.Preceq Y X) : Y ∈ st.core.T := by
  have hclosed : ∀ C ∈ st.core.T, C.parent? = none ∨ C.parent ∈ st.core.T := by
    intro C hC
    rw [h.1] at hC ⊢
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hC
    right
    rw [Proofs.NamedWire.erase_parent]
    exact Finset.mem_image_of_mem NamedBlock.erase (h.2.2.1.2 N hN)
  exact Proofs.Records.mem_of_preceq hclosed Y X hX hYX
end DecoupledConsensusModel.Proofs.NamedDerivationGeometry

end
