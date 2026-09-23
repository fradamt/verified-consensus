module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.StoreRoots
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding
public import DecoupledConsensusProofs.Protocol.ChainState.Certificates

@[expose] public section

/-! Local matching-progress witnesses from actual full named rows.
The pool predicates are proof-local. No checkpoint callback, runtime source
observation, honest-quorum assumption, or new protocol definition is used. -/
namespace DecoupledConsensusModel.Proofs.NamedMatchingProgress
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

def OnNamedChain (B : NamedBlock V) (a : NamedAttestation V) : Prop :=
  ∃ carrier : NamedBlock V, NamedBlock.Preceq carrier B ∧ a ∈ carrier.attestations

def MatchingWitnesses (pool : NamedAttestation V → Prop) (st : ChainState V) : Prop :=
  st.target_participation ⊆ st.progress ∧
  ∀ signer ∈ st.progress, ∃ a, pool a ∧ a.val_index = signer ∧
    a.height_pair.matchesEntry st.h st.T_h.root = true

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
-- Preserve the frozen public instance parameters.
theorem targeted_progress_origin (st : ChainState V) (a : NamedAttestation V)
    (signer : V)
    (h : signer ∈ (process_attestation_with (TimeoutBinding.targeted V) st a).progress) :
    signer ∈ st.progress ∨
      signer = a.val_index ∧ a.height_pair.matchesEntry st.h st.T_h.root = true := by
  rw [(TargetedTimeoutBinding.process_height_fields st a).1] at h
  split_ifs at h with hm
  · rcases Finset.mem_insert.mp h with heq | hold
    · exact Or.inr ⟨heq, hm⟩
    · exact Or.inl hold
  · exact Or.inl h

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
-- Preserve the frozen public instance parameters.

omit [DecidableEq V] [Fintype V] in
private theorem witnesses_empty (pool : NamedAttestation V → Prop) (st : ChainState V)
    (ht : st.target_participation = ∅) (hp : st.progress = ∅) : MatchingWitnesses pool st := by
  refine ⟨by rw [ht]; exact Finset.empty_subset _, ?_⟩
  intro signer hs
  rw [hp] at hs
  simp at hs

omit [DecidableEq V] [Fintype V] in
private theorem witnesses_mono (pool next : NamedAttestation V → Prop) (st : ChainState V)
    (h : MatchingWitnesses pool st) (hsub : ∀ a, pool a → next a) : MatchingWitnesses next st := by
  refine ⟨h.1, ?_⟩
  intro signer hs
  obtain ⟨a, ha, hv, hm⟩ := h.2 signer hs
  exact ⟨a, hsub a ha, hv, hm⟩

omit [DecidableEq V] [Fintype V] in
private theorem witnesses_congr (pool : NamedAttestation V → Prop) (st next : ChainState V)
    (h : MatchingWitnesses pool st) (hh : next.h = st.h) (ht : next.T_h = st.T_h)
    (hTarget : next.target_participation = st.target_participation)
    (hProgress : next.progress = st.progress) : MatchingWitnesses pool next := by
  refine ⟨?_, ?_⟩
  · rw [hTarget, hProgress]; exact h.1
  · intro signer hs
    rw [hProgress] at hs
    rw [hh, ht]
    exact h.2 signer hs

set_option linter.unusedFintypeInType false in
-- Calls the frozen public Fintype-parameterized progress lemma.
private theorem witnesses_process (pool : NamedAttestation V → Prop)
    (st : ChainState V) (a : NamedAttestation V) (ha : pool a) (h : MatchingWitnesses pool st) :
    MatchingWitnesses pool (process_attestation_with (TimeoutBinding.targeted V) st a) := by
  have fields := TargetedTimeoutBinding.process_height_fields st a
  have context := TimeoutBindingDefaults.process_context_fields (TimeoutBinding.targeted V) st a
  refine ⟨?_, ?_⟩
  · intro signer hs
    rw [fields.2] at hs
    rw [fields.1]
    have hsubset := h.1
    split_ifs at hs ⊢ <;> simp_all only [Bool.and_eq_true, Finset.mem_insert]
    all_goals aesop
  · intro signer hs
    rw [context.2.1, context.2.2.1]
    rcases targeted_progress_origin st a signer hs with hold | ⟨heq, hm⟩
    · exact h.2 signer hold
    · exact ⟨a, ha, heq.symm, hm⟩

set_option linter.unusedFintypeInType false in
-- Calls the frozen public Fintype-parameterized progress lemma.
private theorem witnesses_fold (pool : NamedAttestation V → Prop)
    (rows : List (NamedAttestation V)) (st : ChainState V)
    (hrows : ∀ a ∈ rows, pool a) (h : MatchingWitnesses pool st) :
    MatchingWitnesses pool
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V)) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (fun b hb => hrows b (List.mem_cons_of_mem a hb))
      (witnesses_process pool st a (hrows a (List.mem_cons_self ..)) h)

set_option linter.unusedFintypeInType false in
-- Calls the frozen public Fintype-parameterized progress lemma.
private theorem witnesses_fold_block (pool : NamedAttestation V → Prop)
    (st : ChainState V) (B : NamedBlock V)
    (hrows : ∀ a ∈ B.attestations, pool a) (h : MatchingWitnesses pool st) :
    MatchingWitnesses pool (fold_rows (TimeoutBinding.targeted V) st B.erase B.attestations) := by
  have hf := witnesses_fold pool B.attestations { st with s := B.erase.slot } hrows
    (witnesses_congr pool st _ h rfl rfl rfl rfl)
  exact witnesses_congr pool _ _ hf rfl rfl rfl rfl

private theorem witnesses_height_events (E : Env V) (cfg : HeightConfig)
    (pool : NamedAttestation V → Prop) (st : ChainState V) (h : MatchingWitnesses pool st) :
    MatchingWitnesses pool (process_height_events E cfg st) := by
  have hf := witnesses_congr pool st (Protocol.afterFin E st) h
    (Protocol.afterFin_h E) (Protocol.afterFin_T_h E)
    (Protocol.afterFin_target_participation E) (Protocol.afterFin_progress E)
  rw [Protocol.process_height_events_eq]
  split_ifs
  · exact witnesses_empty pool _
      Protocol.advance_height_target_participation Protocol.advance_height_progress
  · exact witnesses_empty pool _
      Protocol.advance_height_target_participation Protocol.advance_height_progress
  · exact hf

omit [Fintype V] in
private theorem named_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

omit [Fintype V] in
private theorem chain_parent_subset (parent : NamedBlock V) (slot : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (a : NamedAttestation V) (ha : OnNamedChain parent a) :
    OnNamedChain (.node parent slot root votes support rows proposer) a := by
  obtain ⟨carrier, hc, hrow⟩ := ha
  refine ⟨carrier, ?_, hrow⟩
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr hc

omit [Fintype V] in
private theorem own_rows_on_chain (B : NamedBlock V) (a : NamedAttestation V)
    (ha : a ∈ B.attestations) : OnNamedChain B a := ⟨B, named_self B, ha⟩

theorem derive_matching_witnesses (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    MatchingWitnesses (OnNamedChain B) (derive_named E cfg B) := by
  induction B with
  | genesis => exact witnesses_empty _ _ rfl rfl
  | node parent slot root votes support rows proposer ih =>
    change MatchingWitnesses _ (process_height_events E cfg
      (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
        (NamedBlock.node parent slot root votes support rows proposer).erase rows))
    apply witnesses_height_events
    apply witnesses_fold_block
    · exact own_rows_on_chain _
    · exact witnesses_mono _ _ _ ih
        (chain_parent_subset parent slot root votes support rows proposer)

theorem crossing_matching_quorum (E : Env V) (cfg : HeightConfig)
    (parent : NamedBlock V) (slot : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (hAdvance : (derive_named E cfg (.node parent slot root votes support rows proposer)).h ≠
      (derive_named E cfg parent).h) :
    ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
      ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
        NamedBlock.Preceq carrier (.node parent slot root votes support rows proposer) ∧
        a ∈ carrier.attestations ∧ a.val_index = signer ∧
        a.height_pair.matchesEntry (derive_named E cfg parent).h
          (derive_named E cfg parent).T_h.root = true := by
  let B := NamedBlock.node parent slot root votes support rows proposer
  let folded := fold_rows (TimeoutBinding.targeted V)
    (derive_named E cfg parent) B.erase B.attestations
  have hw : MatchingWitnesses (OnNamedChain B) folded := by
    apply witnesses_fold_block
    · exact own_rows_on_chain B
    · exact witnesses_mono _ _ _ (derive_matching_witnesses E cfg parent)
        (chain_parent_subset parent slot root votes support rows proposer)
  have hc := Proofs.NamedStoreRoots.fold_context_fields (TimeoutBinding.targeted V) B.attestations
    { derive_named E cfg parent with s := B.erase.slot }
  have hh : folded.h = (derive_named E cfg parent).h := hc.2.1
  have ht : folded.T_h = (derive_named E cfg parent).T_h := hc.2.2.1
  rcases Protocol.height_advance_step E cfg hw.1 with hstay | ⟨_, hquorum⟩
  · exact False.elim (hAdvance (hstay.trans hh))
  · refine ⟨folded.progress, hquorum, ?_⟩
    intro signer hsigner
    obtain ⟨a, ⟨carrier, hcarrier, hrow⟩, hval, hmatch⟩ := hw.2 signer hsigner
    exact ⟨carrier, a, hcarrier, hrow, hval, by simpa only [hh, ht] using hmatch⟩



#print axioms targeted_progress_origin
#print axioms derive_matching_witnesses
#print axioms crossing_matching_quorum
end DecoupledConsensusModel.Proofs.NamedMatchingProgress

end
