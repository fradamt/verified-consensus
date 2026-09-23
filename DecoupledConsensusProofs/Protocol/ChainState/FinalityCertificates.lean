module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.MatchingProgress
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedFinalityCertificates
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem named_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

omit [Fintype V] in
private theorem named_extend {A parent : NamedBlock V} (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (h : NamedBlock.Preceq A parent) :
    NamedBlock.Preceq A (.node parent s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

-- Existence inside this full recursive chain, not injectivity of erase.
omit [Fintype V] in
private theorem erased_ancestor_lift (B : NamedBlock V) {raw : Block V}
    (h : Block.Preceq raw B.erase) :
    ∃ A : NamedBlock V, NamedBlock.Preceq A B ∧ A.erase = raw := by
  induction B with
  | genesis =>
    have hr : raw = Block.genesis := by
      simpa only [Block.Preceq, Block.preceq, NamedBlock.erase, decide_eq_true_eq] using h
    subst raw
    exact ⟨.genesis, named_self _, rfl⟩
  | node parent s root votes support rows proposer ih =>
    let B := NamedBlock.node parent s root votes support rows proposer
    have hcases : raw = B.erase ∨ Block.Preceq raw parent.erase := by
      simpa only [B, NamedBlock.erase, Block.Preceq, Block.preceq,
        Bool.or_eq_true, decide_eq_true_eq] using h
    rcases hcases with heq | hp
    · exact ⟨B, named_self B, heq.symm⟩
    · obtain ⟨A, hA, hErase⟩ := ih hp
      exact ⟨A, named_extend s root votes support rows proposer hA, hErase⟩

omit [Fintype V] in
private theorem chain_parent_subset (parent : NamedBlock V) (slot : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (a : NamedAttestation V) (ha : NamedMatchingProgress.OnNamedChain parent a) :
    NamedMatchingProgress.OnNamedChain
      (.node parent slot root votes support rows proposer) a := by
  obtain ⟨carrier, hc, hrow⟩ := ha
  exact ⟨carrier, named_extend slot root votes support rows proposer hc, hrow⟩

omit [Fintype V] in
private theorem own_rows (B : NamedBlock V) (a : NamedAttestation V)
    (ha : a ∈ B.attestations) : NamedMatchingProgress.OnNamedChain B a :=
  ⟨B, named_self B, ha⟩

-- The pair is the current J/h_j, not the current entry T_h/h.
private def FinalizeRows (pool : NamedAttestation V → Prop) (st : ChainState V) : Prop :=
  ∀ signer ∈ st.finalize, ∃ a : NamedAttestation V, pool a ∧
    a.val_index = signer ∧ a.finality_pair = some ⟨st.h_j, st.J.root⟩

omit [DecidableEq V] [Fintype V] in
private theorem rows_empty (pool : NamedAttestation V → Prop) (st : ChainState V)
    (hEmpty : st.finalize = ∅) : FinalizeRows pool st := by
  intro signer hs
  rw [hEmpty] at hs
  simp at hs

omit [DecidableEq V] [Fintype V] in
private theorem rows_mono (pool next : NamedAttestation V → Prop) (st : ChainState V)
    (h : FinalizeRows pool st) (hsub : ∀ a, pool a → next a) : FinalizeRows next st := by
  intro signer hs
  obtain ⟨a, ha, hv, hp⟩ := h signer hs
  exact ⟨a, hsub a ha, hv, hp⟩

omit [DecidableEq V] [Fintype V] in
private theorem rows_congr (pool : NamedAttestation V → Prop) (st next : ChainState V)
    (h : FinalizeRows pool st) (hJ : next.J = st.J) (hhj : next.h_j = st.h_j)
    (hFinalize : next.finalize = st.finalize) : FinalizeRows pool next := by
  intro signer hs
  rw [hFinalize] at hs
  rw [hhj, hJ]
  exact h signer hs

omit [Fintype V] in
private theorem rows_process (pool : NamedAttestation V → Prop)
    (st : ChainState V) (a : NamedAttestation V) (ha : pool a) (h : FinalizeRows pool st) :
    FinalizeRows pool (process_attestation_with (TimeoutBinding.targeted V) st a) := by
  intro signer hs
  have fields := TimeoutBindingDefaults.process_context_fields (TimeoutBinding.targeted V) st a
  rw [fields.2.2.2.2.1, fields.2.2.2.1]
  rw [TargetedTimeoutBinding.process_finality_eq] at hs
  rcases Protocol.mem_finalize_process_attestation hs with hold | ⟨hSigner, hPair⟩
  · exact h signer hold
  · exact ⟨a, ha, by simpa only [NamedAttestation.erase] using hSigner.symm,
      by simpa only [NamedAttestation.erase] using hPair⟩

omit [Fintype V] in
private theorem rows_fold (pool : NamedAttestation V → Prop)
    (rows : List (NamedAttestation V)) (st : ChainState V)
    (hrows : ∀ a ∈ rows, pool a) (h : FinalizeRows pool st) :
    FinalizeRows pool
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V)) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (fun b hb => hrows b (List.mem_cons_of_mem a hb))
      (rows_process pool st a (hrows a (List.mem_cons_self ..)) h)

omit [Fintype V] in
private theorem rows_fold_block (pool : NamedAttestation V → Prop)
    (st : ChainState V) (B : NamedBlock V)
    (hrows : ∀ a ∈ B.attestations, pool a) (h : FinalizeRows pool st) :
    FinalizeRows pool
      (fold_rows (TimeoutBinding.targeted V) st B.erase B.attestations) := by
  have hf := rows_fold pool B.attestations { st with s := B.erase.slot } hrows
    (rows_congr pool st _ h rfl rfl rfl)
  exact rows_congr pool _ _ hf rfl rfl rfl

private theorem rows_height_events (E : Env V) (cfg : HeightConfig)
    (pool : NamedAttestation V → Prop) (st : ChainState V) (h : FinalizeRows pool st) :
    FinalizeRows pool (process_height_events E cfg st) := by
  have hAfter := rows_congr pool st (Protocol.afterFin E st) h
    (Protocol.afterFin_J E) (Protocol.afterFin_h_j E) (Protocol.afterFin_finalize E)
  rw [Protocol.process_height_events_eq]
  split_ifs
  · exact rows_empty pool _ rfl
  · exact rows_congr pool _ _ hAfter rfl rfl rfl
  · exact hAfter

private theorem derive_finalize_rows (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    FinalizeRows (NamedMatchingProgress.OnNamedChain B) (derive_named E cfg B) := by
  induction B with
  | genesis => exact rows_empty _ _ rfl
  | node parent slot root votes support rows proposer ih =>
    change FinalizeRows _ (process_height_events E cfg
      (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
        (NamedBlock.node parent slot root votes support rows proposer).erase rows))
    apply rows_height_events
    apply rows_fold_block
    · exact own_rows _
    · exact rows_mono _ _ _ ih
        (chain_parent_subset parent slot root votes support rows proposer)

private theorem folded_finalize_rows (E : Env V) (cfg : HeightConfig)
    (parent : NamedBlock V) (slot : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    let B := NamedBlock.node parent slot root votes support rows proposer
    FinalizeRows (NamedMatchingProgress.OnNamedChain B)
      (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent) B.erase rows) := by
  apply rows_fold_block
  · exact own_rows _
  · exact rows_mono _ _ _ (derive_finalize_rows E cfg parent)
      (chain_parent_subset parent slot root votes support rows proposer)

omit [Fintype V] in
private theorem fold_finality_fields (st : ChainState V) (B : NamedBlock V) :
    (fold_rows (TimeoutBinding.targeted V) st B.erase B.attestations).F = st.F ∧
    (fold_rows (TimeoutBinding.targeted V) st B.erase B.attestations).h_F = st.h_F := by
  have fields := Proofs.NamedStoreRoots.fold_context_fields (TimeoutBinding.targeted V)
    B.attestations { st with s := B.erase.slot }
  exact ⟨fields.2.2.2.2.2.1, fields.2.2.2.2.2.2⟩

private def RowQuorum (E : Env V) (pool : NamedAttestation V → Prop)
    (pair : FinalityPair) : Prop :=
  ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
    ∀ signer ∈ Q, ∃ a : NamedAttestation V, pool a ∧
      a.val_index = signer ∧ a.finality_pair = some pair

private theorem quorum_mono (E : Env V) (pool next : NamedAttestation V → Prop)
    (pair : FinalityPair) (h : RowQuorum E pool pair)
    (hsub : ∀ a, pool a → next a) : RowQuorum E next pair := by
  obtain ⟨Q, hQ, hw⟩ := h
  refine ⟨Q, hQ, ?_⟩
  intro signer hs
  obtain ⟨a, ha, hv, hp⟩ := hw signer hs
  exact ⟨a, hsub a ha, hv, hp⟩

private theorem certificate_step (E : Env V) (cfg : HeightConfig)
    (pool : NamedAttestation V → Prop) (st : ChainState V) (h : FinalizeRows pool st) :
    ((process_height_events E cfg st).F = st.F ∧
      (process_height_events E cfg st).h_F = st.h_F) ∨
    RowQuorum E pool
      ⟨(process_height_events E cfg st).h_F, (process_height_events E cfg st).F.root⟩ := by
  by_cases hf : finalityReady E st = true
  · right
    refine ⟨st.finalize, Protocol.isQuorum_of_finalityReady E hf, ?_⟩
    intro signer hs
    obtain ⟨a, ha, hv, hp⟩ := h signer hs
    refine ⟨a, ha, hv, ?_⟩
    rw [Protocol.process_height_events_h_F, Protocol.process_height_events_F,
      Protocol.afterFin_h_F, Protocol.afterFin_F, if_pos hf, if_pos hf]
    exact hp
  · left
    constructor
    · rw [Protocol.process_height_events_F, Protocol.afterFin_F, if_neg hf]
    · rw [Protocol.process_height_events_h_F, Protocol.afterFin_h_F, if_neg hf]

theorem finalized_zero_is_genesis (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
    (hz : (derive_named E cfg D).h_F = 0) :
    (derive_named E cfg D).F = Block.genesis := by
  induction D with
  | genesis => rfl
  | node parent slot root votes support rows proposer ih =>
    let B := NamedBlock.node parent slot root votes support rows proposer
    let folded := fold_rows (TimeoutBinding.targeted V)
      (derive_named E cfg parent) B.erase B.attestations
    change (process_height_events E cfg folded).h_F = 0 at hz
    change (process_height_events E cfg folded).F = Block.genesis
    rw [Protocol.process_height_events_h_F, Protocol.afterFin_h_F] at hz
    rw [Protocol.process_height_events_F, Protocol.afterFin_F]
    split_ifs at hz ⊢ with hf
    · have hlt := Protocol.lt_of_finalityReady E hf
      rw [hz] at hlt
      exact False.elim (Nat.not_lt_zero _ hlt)
    · have hFields := fold_finality_fields (derive_named E cfg parent) B
      change folded.F = Block.genesis
      rw [hFields.1]
      exact ih (hFields.2.symm.trans hz)

private theorem nonzero_rows_certificate (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
    (hnz : (derive_named E cfg D).h_F ≠ 0) :
    RowQuorum E (NamedMatchingProgress.OnNamedChain D)
      ⟨(derive_named E cfg D).h_F, (derive_named E cfg D).F.root⟩ := by
  induction D with
  | genesis => exact False.elim (hnz rfl)
  | node parent slot root votes support rows proposer ih =>
    let B := NamedBlock.node parent slot root votes support rows proposer
    let folded := fold_rows (TimeoutBinding.targeted V)
      (derive_named E cfg parent) B.erase B.attestations
    have hRows := folded_finalize_rows E cfg parent slot root votes support rows proposer
    have hFields := fold_finality_fields (derive_named E cfg parent) B
    change (process_height_events E cfg folded).h_F ≠ 0 at hnz
    change RowQuorum E (NamedMatchingProgress.OnNamedChain B)
      ⟨(process_height_events E cfg folded).h_F, (process_height_events E cfg folded).F.root⟩
    rcases certificate_step E cfg _ folded hRows with ⟨hF, hhF⟩ | hCert
    · rw [hhF, hF, hFields.2, hFields.1]
      have hParent : (derive_named E cfg parent).h_F ≠ 0 := by
        intro hz
        exact hnz (hhF.trans (hFields.2.trans hz))
      exact quorum_mono E _ _ _ (ih hParent)
        (chain_parent_subset parent slot root votes support rows proposer)
    · exact hCert

theorem finality_certificate (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
    (hnz : (derive_named E cfg D).h_F ≠ 0) :
    ∃ F : NamedBlock V, NamedBlock.Preceq F D ∧
      F.erase = (derive_named E cfg D).F ∧
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
        ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
          NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
          a.val_index = signer ∧
          a.finality_pair = some ⟨(derive_named E cfg D).h_F, F.root⟩ := by
  obtain ⟨F, hFD, hErase⟩ := erased_ancestor_lift D
    (Proofs.NamedStoreRoots.derive_named_anchors_preceq E cfg D).1
  have hRoot : (derive_named E cfg D).F.root = F.root :=
    (congrArg Block.root hErase).symm.trans (Proofs.NamedWire.erase_root F)
  obtain ⟨Q, hQ, hw⟩ := nonzero_rows_certificate E cfg D hnz
  refine ⟨F, hFD, hErase, Q, hQ, ?_⟩
  intro signer hs
  obtain ⟨a, ⟨carrier, hcarrier, hrow⟩, hv, hp⟩ := hw signer hs
  exact ⟨carrier, a, hcarrier, hrow, hv, by simpa only [hRoot] using hp⟩

theorem height_crossing (E : Env V) (cfg : HeightConfig) (C : NamedBlock V)
    (h : Height) (hpos : 1 ≤ h) (hlt : h < (derive_named E cfg C).h) :
    ∃ X : NamedBlock V, NamedBlock.Preceq X C ∧
      (derive_named E cfg X).h = h ∧
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
        ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
          NamedBlock.Preceq carrier C ∧ a ∈ carrier.attestations ∧
          a.val_index = signer ∧ a.height_pair.matchesEntry h X.root = true := by
  induction C with
  | genesis =>
    change h < 1 at hlt
    exact False.elim ((Nat.not_lt_of_ge hpos) hlt)
  | node parent slot root votes support rows proposer ih =>
    let B := NamedBlock.node parent slot root votes support rows proposer
    by_cases hp : h < (derive_named E cfg parent).h
    · obtain ⟨X, hX, hXh, Q, hQ, hw⟩ := ih hp
      refine ⟨X, named_extend slot root votes support rows proposer hX, hXh, Q, hQ, ?_⟩
      intro signer hs
      obtain ⟨carrier, a, hc, ha, hv, hm⟩ := hw signer hs
      exact ⟨carrier, a, named_extend slot root votes support rows proposer hc, ha, hv, hm⟩
    · have hParent : (derive_named E cfg parent).h = h := by
        rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg parent slot root
          votes support rows proposer with hStay | hAdvance
        · rw [hStay] at hlt
          exact False.elim (hp hlt)
        · rw [hAdvance] at hlt
          exact Nat.le_antisymm (Nat.le_of_not_gt hp) (Nat.le_of_lt_succ hlt)
      have hAdvance : (derive_named E cfg B).h ≠ (derive_named E cfg parent).h := by
        intro heq
        change h < (derive_named E cfg B).h at hlt
        rw [heq, hParent] at hlt
        exact (Nat.lt_irrefl h) hlt
      obtain ⟨X, hX, hErase, hXh⟩ := Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg parent
      have hRoot : (derive_named E cfg parent).T_h.root = X.root :=
        (congrArg Block.root hErase).symm.trans (Proofs.NamedWire.erase_root X)
      obtain ⟨Q, hQ, hw⟩ := NamedMatchingProgress.crossing_matching_quorum E cfg
        parent slot root votes support rows proposer hAdvance
      refine ⟨X, named_extend slot root votes support rows proposer hX,
        hXh.trans hParent, Q, hQ, ?_⟩
      intro signer hs
      obtain ⟨carrier, a, hc, ha, hv, hm⟩ := hw signer hs
      exact ⟨carrier, a, hc, ha, hv, by simpa only [hParent, hRoot] using hm⟩

end DecoupledConsensusModel.Proofs.NamedFinalityCertificates

end
