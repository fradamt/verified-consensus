module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.StoreRoots

@[expose] public section

/-! Local named height-entry algebra. All state values come from
derive_named and the actual targeted row fold. No runtime, source-compatibility,
prefix-protection, or JointAt premise is used. -/
namespace DecoupledConsensusModel.Proofs.NamedEntryHeight
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


omit [Fintype V] in
private theorem fold_height (binding : TimeoutBinding V (NamedAttestation V))
    (st : ChainState V) (geometry : Block V) (rows : List (NamedAttestation V)) :
    (fold_rows binding st geometry rows).h = st.h :=
  (Proofs.NamedStoreRoots.fold_context_fields binding rows { st with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem fold_entry (binding : TimeoutBinding V (NamedAttestation V))
    (st : ChainState V) (geometry : Block V) (rows : List (NamedAttestation V)) :
    (fold_rows binding st geometry rows).T_h = st.T_h :=
  (Proofs.NamedStoreRoots.fold_context_fields binding rows { st with s := geometry.slot }).2.2.1

/-- Every actual named block either retains its height and entry together,
or advances one height and makes this block its new entry. -/
theorem transition_height_entry_cases (E : Env V) (cfg : HeightConfig)
    (st : ChainState V) (B : NamedBlock V) :
    ((named_transition E cfg st B).h = st.h ∧ (named_transition E cfg st B).T_h = st.T_h) ∨
    ((named_transition E cfg st B).h = st.h + 1 ∧
      (named_transition E cfg st B).T_h = B.erase) := by
  unfold named_transition transition_rows
  rw [Protocol.process_height_events_eq]
  split_ifs
  · right
    constructor
    · rw [Protocol.advance_height_h, Protocol.afterFin_h, fold_height]
    · rw [Protocol.advance_height_T_h, Protocol.afterFin_L]
      rfl
  · right
    constructor
    · rw [Protocol.advance_height_h, Protocol.afterFin_h, fold_height]
    · rw [Protocol.advance_height_T_h, Protocol.afterFin_L]
      rfl
  · left
    constructor
    · rw [Protocol.afterFin_h, fold_height]
    · rw [Protocol.afterFin_T_h, fold_entry]

theorem derive_node_height_cases (E : Env V) (cfg : HeightConfig)
    (parent : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    let B := NamedBlock.node parent s root votes support rows proposer
    (derive_named E cfg B).h = (derive_named E cfg parent).h ∨
      (derive_named E cfg B).h = (derive_named E cfg parent).h + 1 := by
  rcases transition_height_entry_cases E cfg (derive_named E cfg parent)
    (.node parent s root votes support rows proposer) with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Heights are monotone along full named ancestry; erasure injectivity is
not assumed and the previous derived_state function is not used. -/
theorem derive_height_mono (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) : (derive_named E cfg A).h ≤ (derive_named E cfg B).h := by
  induction B with
  | genesis =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    subst A
    exact le_refl _
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact le_refl _
    · have hle := ih hparent
      rcases derive_node_height_cases E cfg parent s root votes support rows proposer with h | h
      · rw [h]; exact hle
      · rw [h]; exact hle.trans (Nat.le_succ _)

/-- Each geometry entry is the erasure of an actual full named ancestor at
the same derived height. This avoids applying derive_named to an erased block. -/
theorem entry_ancestor_same_height (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    ∃ entry : NamedBlock V, NamedBlock.Preceq entry B ∧
      entry.erase = (derive_named E cfg B).T_h ∧
      (derive_named E cfg entry).h = (derive_named E cfg B).h := by
  induction B with
  | genesis => exact ⟨.genesis, named_self _, rfl, rfl⟩
  | node parent s root votes support rows proposer ih =>
    rcases transition_height_entry_cases E cfg (derive_named E cfg parent)
      (.node parent s root votes support rows proposer) with hstay | hnew
    · obtain ⟨entry, he, hentry, hheight⟩ := ih
      exact ⟨entry, named_extend s root votes support rows proposer he,
        hentry.trans hstay.2.symm, hheight.trans hstay.1.symm⟩
    · exact ⟨.node parent s root votes support rows proposer, named_self _, hnew.2.symm, rfl⟩

theorem entry_geometry_ancestor (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    Block.Preceq (derive_named E cfg B).T_h B.erase := by
  obtain ⟨entry, hentry, he, _⟩ := entry_ancestor_same_height E cfg B
  rw [← he]
  exact Proofs.NamedWire.erase_preceq hentry

/-- Equality of child and parent height forces equality of their entries. -/
theorem node_entry_eq_of_height_eq (E : Env V) (cfg : HeightConfig)
    (parent : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (hh : (derive_named E cfg (.node parent s root votes support rows proposer)).h =
      (derive_named E cfg parent).h) :
    (derive_named E cfg (.node parent s root votes support rows proposer)).T_h =
      (derive_named E cfg parent).T_h := by
  rcases transition_height_entry_cases E cfg (derive_named E cfg parent)
    (.node parent s root votes support rows proposer) with hstay | hnew
  · exact hstay.2
  · have hstep := hnew.1
    change (derive_named E cfg (.node parent s root votes support rows proposer)).h =
      (derive_named E cfg parent).h + 1 at hstep
    exact False.elim (Nat.succ_ne_self _ (hstep.symm.trans hh))

theorem entry_eq_on_plateau (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hh : (derive_named E cfg A).h = (derive_named E cfg B).h) :
    (derive_named E cfg A).T_h = (derive_named E cfg B).T_h := by
  induction B with
  | genesis =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    subst A
    rfl
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · rfl
    · have hlow := derive_height_mono E cfg hparent
      have hhigh := derive_height_mono E cfg
        (named_extend s root votes support rows proposer (named_self parent))
      have hparentHeight : (derive_named E cfg parent).h =
          (derive_named E cfg (.node parent s root votes support rows proposer)).h := by
        exact le_antisymm hhigh (hh ▸ hlow)
      exact (ih hparent (hh.trans hparentHeight.symm)).trans
        (node_entry_eq_of_height_eq E cfg parent s root votes support rows proposer
          hparentHeight.symm).symm


#print axioms transition_height_entry_cases
#print axioms derive_node_height_cases
#print axioms derive_height_mono
#print axioms entry_ancestor_same_height
#print axioms entry_geometry_ancestor
#print axioms node_entry_eq_of_height_eq
#print axioms entry_eq_on_plateau
end DecoupledConsensusModel.Proofs.NamedEntryHeight

end
