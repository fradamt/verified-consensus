module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.MatchingProgress
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedJustificationCertificates
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

-- The pool retains the full original row and its proper-target flag.
private def TargetRows (pool : NamedAttestation V → Prop) (st : ChainState V) : Prop :=
  ∀ signer ∈ st.target_participation, ∃ a : NamedAttestation V, pool a ∧
    a.val_index = signer ∧ a.height_pair = .vote st.h st.T_h.root false

omit [DecidableEq V] [Fintype V] in
private theorem rows_empty (pool : NamedAttestation V → Prop) (st : ChainState V)
    (hEmpty : st.target_participation = ∅) : TargetRows pool st := by
  intro signer hs
  rw [hEmpty] at hs
  simp at hs

omit [DecidableEq V] [Fintype V] in
private theorem rows_mono (pool next : NamedAttestation V → Prop) (st : ChainState V)
    (h : TargetRows pool st) (hsub : ∀ a, pool a → next a) : TargetRows next st := by
  intro signer hs
  obtain ⟨a, ha, hv, hp⟩ := h signer hs
  exact ⟨a, hsub a ha, hv, hp⟩

omit [DecidableEq V] [Fintype V] in
private theorem rows_congr (pool : NamedAttestation V → Prop) (st next : ChainState V)
    (h : TargetRows pool st) (hh : next.h = st.h) (hT : next.T_h = st.T_h)
    (hTarget : next.target_participation = st.target_participation) : TargetRows pool next := by
  intro signer hs
  rw [hTarget] at hs
  rw [hh, hT]
  exact h signer hs

omit [DecidableEq V] [Fintype V] in
private theorem matching_proper_vote (a : NamedAttestation V) (h : Height) (root : BlockId)
    (hm : (a.height_pair.matchesEntry h root && a.height_pair.properTarget) = true) :
    a.height_pair = .vote h root false := by
  cases hp : a.height_pair with
  | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
  | vote k entry timeout =>
    cases timeout with
    | false =>
      have heq : k = h ∧ entry = root := by
        simpa [hp, NamedHeightPair.matchesEntry, NamedHeightPair.properTarget] using hm
      rcases heq with ⟨rfl, rfl⟩
      rfl
    | true => simp [hp, NamedHeightPair.properTarget] at hm

omit [Fintype V] in
private theorem rows_process (pool : NamedAttestation V → Prop)
    (st : ChainState V) (a : NamedAttestation V) (ha : pool a) (h : TargetRows pool st) :
    TargetRows pool (process_attestation_with (TimeoutBinding.targeted V) st a) := by
  intro signer hs
  have fields := TimeoutBindingDefaults.process_context_fields (TimeoutBinding.targeted V) st a
  rw [fields.2.1, fields.2.2.1]
  rw [(TargetedTimeoutBinding.process_height_fields st a).2] at hs
  split_ifs at hs with hm
  · rcases Finset.mem_insert.mp hs with heq | hold
    · exact ⟨a, ha, heq.symm, matching_proper_vote a st.h st.T_h.root hm⟩
    · exact h signer hold
  · exact h signer hs

omit [Fintype V] in
private theorem rows_fold (pool : NamedAttestation V → Prop)
    (rows : List (NamedAttestation V)) (st : ChainState V)
    (hrows : ∀ a ∈ rows, pool a) (h : TargetRows pool st) :
    TargetRows pool
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V)) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (fun b hb => hrows b (List.mem_cons_of_mem a hb))
      (rows_process pool st a (hrows a (List.mem_cons_self ..)) h)

omit [Fintype V] in
private theorem rows_fold_block (pool : NamedAttestation V → Prop)
    (st : ChainState V) (B : NamedBlock V)
    (hrows : ∀ a ∈ B.attestations, pool a) (h : TargetRows pool st) :
    TargetRows pool
      (fold_rows (TimeoutBinding.targeted V) st B.erase B.attestations) := by
  have hf := rows_fold pool B.attestations { st with s := B.erase.slot } hrows
    (rows_congr pool st _ h rfl rfl rfl)
  exact rows_congr pool _ _ hf rfl rfl rfl

private theorem rows_height_events (E : Env V) (cfg : HeightConfig)
    (pool : NamedAttestation V → Prop) (st : ChainState V) (h : TargetRows pool st) :
    TargetRows pool (process_height_events E cfg st) := by
  have hAfter := rows_congr pool st (Protocol.afterFin E st) h
    (Protocol.afterFin_h E) (Protocol.afterFin_T_h E) (Protocol.afterFin_target_participation E)
  rw [Protocol.process_height_events_eq]
  split_ifs
  · exact rows_empty pool _ rfl
  · exact rows_empty pool _ rfl
  · exact hAfter

private theorem derive_target_rows (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    TargetRows (NamedMatchingProgress.OnNamedChain B) (derive_named E cfg B) := by
  induction B with
  | genesis => exact rows_empty _ _ rfl
  | node parent slot root votes support rows proposer ih =>
    change TargetRows _ (process_height_events E cfg
      (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
        (NamedBlock.node parent slot root votes support rows proposer).erase rows))
    apply rows_height_events
    apply rows_fold_block
    · exact own_rows _
    · exact rows_mono _ _ _ ih
        (chain_parent_subset parent slot root votes support rows proposer)

private theorem folded_target_rows (E : Env V) (cfg : HeightConfig)
    (parent : NamedBlock V) (slot : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    let B := NamedBlock.node parent slot root votes support rows proposer
    TargetRows (NamedMatchingProgress.OnNamedChain B)
      (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent) B.erase rows) := by
  apply rows_fold_block
  · exact own_rows _
  · exact rows_mono _ _ _ (derive_target_rows E cfg parent)
      (chain_parent_subset parent slot root votes support rows proposer)

omit [Fintype V] in
private theorem fold_justification_fields (st : ChainState V) (B : NamedBlock V) :
    (fold_rows (TimeoutBinding.targeted V) st B.erase B.attestations).J = st.J ∧
    (fold_rows (TimeoutBinding.targeted V) st B.erase B.attestations).h_j = st.h_j ∧
    (fold_rows (TimeoutBinding.targeted V) st B.erase B.attestations).h = st.h := by
  have fields := Proofs.NamedStoreRoots.fold_context_fields (TimeoutBinding.targeted V)
    B.attestations { st with s := B.erase.slot }
  exact ⟨fields.2.2.2.1, fields.2.2.2.2.1, fields.2.1⟩

private theorem justification_pair_cases (E : Env V) (cfg : HeightConfig) (st : ChainState V) :
    ((process_height_events E cfg st).J = st.J ∧
      (process_height_events E cfg st).h_j = st.h_j) ∨
    ((process_height_events E cfg st).J = st.T_h ∧
      (process_height_events E cfg st).h_j = st.h) := by
  rw [Protocol.process_height_events_eq]
  split_ifs
  · right
    exact ⟨Protocol.afterFin_T_h E, Protocol.afterFin_h E⟩
  · left
    exact ⟨Protocol.afterFin_J E, Protocol.afterFin_h_j E⟩
  · left
    exact ⟨Protocol.afterFin_J E, Protocol.afterFin_h_j E⟩

private def RowQuorum (E : Env V) (pool : NamedAttestation V → Prop)
    (h : Height) (root : BlockId) : Prop :=
  ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
    ∀ signer ∈ Q, ∃ a : NamedAttestation V, pool a ∧
      a.val_index = signer ∧ a.height_pair = .vote h root false

private theorem quorum_mono (E : Env V) (pool next : NamedAttestation V → Prop)
    (height : Height) (root : BlockId) (h : RowQuorum E pool height root)
    (hsub : ∀ a, pool a → next a) : RowQuorum E next height root := by
  obtain ⟨Q, hQ, hw⟩ := h
  refine ⟨Q, hQ, ?_⟩
  intro signer hs
  obtain ⟨a, ha, hv, hp⟩ := hw signer hs
  exact ⟨a, hsub a ha, hv, hp⟩

private theorem certificate_step (E : Env V) (cfg : HeightConfig)
    (pool : NamedAttestation V → Prop) (st : ChainState V) (h : TargetRows pool st) :
    ((process_height_events E cfg st).J = st.J ∧
      (process_height_events E cfg st).h_j = st.h_j) ∨
    RowQuorum E pool (process_height_events E cfg st).h_j
      (process_height_events E cfg st).J.root := by
  have hAfter := rows_congr pool st (Protocol.afterFin E st) h
    (Protocol.afterFin_h E) (Protocol.afterFin_T_h E) (Protocol.afterFin_target_participation E)
  rw [Protocol.process_height_events_eq]
  split_ifs with ht hp
  · right
    refine ⟨(Protocol.afterFin E st).target_participation,
      Protocol.isQuorum_of_targetReady E ht, ?_⟩
    intro signer hs
    exact hAfter signer hs
  · left
    exact ⟨Protocol.afterFin_J E, Protocol.afterFin_h_j E⟩
  · left
    exact ⟨Protocol.afterFin_J E, Protocol.afterFin_h_j E⟩

/-- Zero justification height names genesis, for the actual named derivation. -/
theorem justified_zero_is_genesis (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
    (hz : (derive_named E cfg D).h_j = 0) :
    (derive_named E cfg D).J = Block.genesis := by
  induction D with
  | genesis => rfl
  | node parent slot root votes support rows proposer ih =>
    let B := NamedBlock.node parent slot root votes support rows proposer
    let folded := fold_rows (TimeoutBinding.targeted V)
      (derive_named E cfg parent) B.erase B.attestations
    have hFields := fold_justification_fields (derive_named E cfg parent) B
    change (process_height_events E cfg folded).h_j = 0 at hz
    change (process_height_events E cfg folded).J = Block.genesis
    rcases justification_pair_cases E cfg folded with ⟨hJ, hhj⟩ | ⟨_, hhj⟩
    · rw [hJ, hFields.1]
      exact ih (hFields.2.1.symm.trans (hhj.symm.trans hz))
    · have hpos : 0 < (derive_named E cfg parent).h :=
        (Nat.zero_le _).trans_lt
          (Proofs.NamedStoreRoots.chainOrder_derive_named E cfg parent).justified_below_height
      have hzero : (derive_named E cfg parent).h = 0 :=
        hFields.2.2.symm.trans (hhj.symm.trans hz)
      exact False.elim ((Nat.ne_of_gt hpos) hzero)

private theorem nonzero_rows_certificate (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
    (hnz : (derive_named E cfg D).h_j ≠ 0) :
    RowQuorum E (NamedMatchingProgress.OnNamedChain D)
      (derive_named E cfg D).h_j (derive_named E cfg D).J.root := by
  induction D with
  | genesis => exact False.elim (hnz rfl)
  | node parent slot root votes support rows proposer ih =>
    let B := NamedBlock.node parent slot root votes support rows proposer
    let folded := fold_rows (TimeoutBinding.targeted V)
      (derive_named E cfg parent) B.erase B.attestations
    have hRows := folded_target_rows E cfg parent slot root votes support rows proposer
    have hFields := fold_justification_fields (derive_named E cfg parent) B
    change (process_height_events E cfg folded).h_j ≠ 0 at hnz
    change RowQuorum E (NamedMatchingProgress.OnNamedChain B)
      (process_height_events E cfg folded).h_j (process_height_events E cfg folded).J.root
    rcases certificate_step E cfg _ folded hRows with ⟨hJ, hhj⟩ | hCert
    · rw [hhj, hJ, hFields.2.1, hFields.1]
      have hParent : (derive_named E cfg parent).h_j ≠ 0 := by
        intro hz
        exact hnz (hhj.trans (hFields.2.1.trans hz))
      exact quorum_mono E _ _ _ _ (ih hParent)
        (chain_parent_subset parent slot root votes support rows proposer)
    · exact hCert

/-- A nonzero named justification carries an original false-flag target row
for every signer in its quorum, on this same full recursive chain. -/
theorem justification_certificate (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
    (hnz : (derive_named E cfg D).h_j ≠ 0) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J D ∧
      J.erase = (derive_named E cfg D).J ∧
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
        ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
          NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
          a.val_index = signer ∧
          a.height_pair = .vote (derive_named E cfg D).h_j J.root false := by
  obtain ⟨J, hJD, hErase⟩ := erased_ancestor_lift D
    (Proofs.NamedStoreRoots.derive_named_anchors_preceq E cfg D).2
  have hRoot : (derive_named E cfg D).J.root = J.root :=
    (congrArg Block.root hErase).symm.trans (Proofs.NamedWire.erase_root J)
  obtain ⟨Q, hQ, hw⟩ := nonzero_rows_certificate E cfg D hnz
  refine ⟨J, hJD, hErase, Q, hQ, ?_⟩
  intro signer hs
  obtain ⟨a, ⟨carrier, hcarrier, hrow⟩, hv, hp⟩ := hw signer hs
  exact ⟨carrier, a, hcarrier, hrow, hv, by simpa only [hRoot] using hp⟩

end DecoupledConsensusModel.Proofs.NamedJustificationCertificates

end
