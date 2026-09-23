module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusProofs.Protocol.Handlers.BlockProcessingDefaults

@[expose] public section

/-! Named block-prefix coherence. The scoped erasure uniqueness
is produced by fresh geometry insertion, not assumed globally. DerivedView
binds each stored body's actual full row history to its cached chain state.
This is not an actual named event runtime or an authenticity theorem. -/
namespace DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open Protocol
open BlockProcessingDefaults
variable {V : Type} [DecidableEq V] [Fintype V]

def TreeView (st : Protocol.NamedStore V) : Prop :=
  st.core.T = st.bodies.image NamedBlock.erase

def ErasureUnique (st : Protocol.NamedStore V) : Prop :=
  ∀ A ∈ st.bodies, ∀ B ∈ st.bodies, A.erase = B.erase → A = B

def NamedParentClosed (st : Protocol.NamedStore V) : Prop :=
  NamedBlock.genesis ∈ st.bodies ∧ ∀ B ∈ st.bodies, B.parent ∈ st.bodies

def PoolView (st : Protocol.NamedStore V) : Prop :=
  ∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase

def DerivedView (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) : Prop :=
  ∀ B ∈ st.bodies, st.core.σ B.erase = derive_named E cfg B

def Coherent (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) : Prop :=
  TreeView st ∧ ErasureUnique st ∧ NamedParentClosed st ∧ PoolView st ∧ DerivedView E cfg st

/-- The initial named body is exactly genesis; both row pools are empty. -/
theorem coherent_initial (E : Env V) (cfg : HeightConfig) :
    Coherent E cfg (Protocol.NamedStore.initial : Protocol.NamedStore V) := by
  simp [Coherent, TreeView, ErasureUnique, NamedParentClosed, PoolView, DerivedView,
    Protocol.NamedStore.initial, Protocol.Store.init, NamedBlock.erase, NamedBlock.parent,
    derive_named]

theorem coherent_clock (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (t : Time) (h : Coherent E cfg st) : Coherent E cfg (setClock E st t) := h

omit [Fintype V] in
theorem commit_core (before : Protocol.NamedStore V) (after : Protocol.Store V) (B : NamedBlock V) :
    (commitBlock before after B).core = after := by
  unfold commitBlock
  split_ifs <;> rfl

omit [Fintype V] in
theorem commit_rows (before : Protocol.NamedStore V) (after : Protocol.Store V) (B : NamedBlock V) :
    (commitBlock before after B).sg_rows = before.sg_rows := by
  unfold commitBlock
  split_ifs <;> rfl

omit [Fintype V] in
/-- The geometry commit and named-body commit are the same insertion. -/
theorem commit_tree_view (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) (hTree : TreeView before)
    (hCases : after.T = before.core.T ∨ after.T = insert B.erase before.core.T) :
    TreeView (commitBlock before after B) := by
  unfold commitBlock
  split_ifs with hf
  · change after.T = (insert B before.bodies).image NamedBlock.erase
    rw [Finset.image_insert, ← hTree]
    rcases hCases with hOld | hNew
    · exact False.elim (hf.1 (by rw [← hOld]; exact hf.2))
    · exact hNew
  · change after.T = before.bodies.image NamedBlock.erase
    rw [← hTree]
    rcases hCases with hOld | hNew
    · exact hOld
    · have hB : B.erase ∈ before.core.T := by
        by_contra hnot
        apply hf
        exact ⟨hnot, by rw [hNew]; exact Finset.mem_insert_self _ _⟩
      rw [hNew, Finset.insert_eq_of_mem hB]

omit [Fintype V] in
/-- Scoped uniqueness is maintained by rejecting occupied geometry, without
any global injectivity theorem for the erasure function. -/
theorem commit_erasure_unique (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) (hTree : TreeView before) (hUnique : ErasureUnique before) :
    ErasureUnique (commitBlock before after B) := by
  unfold commitBlock
  split_ifs with hf
  · intro A hA C hC he
    rcases Finset.mem_insert.mp hA with hAB | hAold
    · rcases Finset.mem_insert.mp hC with hCB | hCold
      · exact hAB.trans hCB.symm
      · have hBC : B.erase = C.erase := by rw [← hAB]; exact he
        exact False.elim (hf.1 (by
          rw [hBC, hTree]
          exact Finset.mem_image_of_mem NamedBlock.erase hCold))
    · rcases Finset.mem_insert.mp hC with hCB | hCold
      · have hAB : A.erase = B.erase := by rw [← hCB]; exact he
        exact False.elim (hf.1 (by
          rw [← hAB, hTree]
          exact Finset.mem_image_of_mem NamedBlock.erase hAold))
      · exact hUnique A hAold C hCold he
  · exact hUnique

omit [Fintype V] in
theorem commit_parent_closed (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) (hParent : NamedParentClosed before) (hp : B.parent ∈ before.bodies) :
    NamedParentClosed (commitBlock before after B) := by
  unfold commitBlock
  split_ifs
  · refine ⟨Finset.mem_insert_of_mem hParent.1, ?_⟩
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact Finset.mem_insert_of_mem hp
    · exact Finset.mem_insert_of_mem (hParent.2 C hC)
  · exact hParent

omit [Fintype V] in
theorem commit_pool_view (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) (hPool : PoolView before) (hVotes : after.sg_votes = before.core.sg_votes) :
    PoolView (commitBlock before after B) := by
  intro r
  rw [commit_core, commit_rows, hVotes]
  exact hPool r

/-- The new cache entry and all retained old cache entries keep their exact
named derivations. No root-only metadata lookup is used. -/
theorem commit_derived_view (E : Env V) (cfg : HeightConfig)
    (before : Protocol.NamedStore V) (after : Protocol.Store V) (B : NamedBlock V)
    (hDerived : DerivedView E cfg before)
    (hOld : ∀ C ∈ before.bodies, after.σ C.erase = before.core.σ C.erase)
    (hNew : B.erase ∉ before.core.T → B.erase ∈ after.T →
      after.σ B.erase = derive_named E cfg B) :
    DerivedView E cfg (commitBlock before after B) := by
  unfold commitBlock
  split_ifs with hf
  · intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact hNew hf.1 hf.2
    · exact (hOld C hC).trans (hDerived C hC)
  · intro C hC
    exact (hOld C hC).trans (hDerived C hC)

/-- The actual named block prefix preserves all five coherence properties.
Its only premise is the previous local invariant, supplied at initialization. -/
theorem coherent_process_block (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) (h : Coherent E cfg st) :
    Coherent E cfg (process_block_core E hc cfg st B) := by
  by_cases hp : B.parent ∈ st.bodies
  · rcases h with ⟨hTree, hUnique, hParent, hPool, hDerived⟩
    let buildState := fun parentState => named_transition E cfg parentState B
    let after := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B.erase buildState) hc st.core B.erase
    have hCases : after.T = st.core.T ∨ after.T = insert B.erase st.core.T :=
      checked_tree_cases E hc st.core B.erase buildState
    have hVotes : after.sg_votes = st.core.sg_votes :=
      checked_sg_votes E hc st.core B.erase buildState
    have hOld : ∀ C ∈ st.bodies, after.σ C.erase = st.core.σ C.erase := by
      intro C hC
      apply checked_old_state E hc st.core B.erase C.erase buildState
      rw [hTree]
      exact Finset.mem_image_of_mem NamedBlock.erase hC
    have hNew : B.erase ∉ st.core.T → B.erase ∈ after.T →
        after.σ B.erase = derive_named E cfg B := by
      intro hfresh hmem
      have hne : B ≠ NamedBlock.genesis := by
        intro heq
        subst B
        apply hfresh
        rw [hTree]
        exact Finset.mem_image_of_mem NamedBlock.erase hParent.1
      have hstate := checked_fresh_state E hc st.core B.erase buildState hfresh hmem
      change after.σ B.erase = named_transition E cfg (st.core.σ B.erase.parent) B at hstate
      rw [Proofs.NamedWire.erase_parent, hDerived B.parent hp] at hstate
      rw [derive_named_of_not_genesis E cfg B hne]
      exact hstate
    change Coherent E cfg (if B.parent ∉ st.bodies then st else commitBlock st after B)
    rw [if_neg (not_not.mpr hp)]
    exact ⟨commit_tree_view st after B hTree hCases,
      commit_erasure_unique st after B hTree hUnique,
      commit_parent_closed st after B hParent hp,
      commit_pool_view st after B hPool hVotes,
      commit_derived_view E cfg st after B hDerived hOld hNew⟩
  · simpa only [process_block_core, if_pos hp] using h


/-- An existing erasure never replaces the retained named metadata. -/
theorem existing_geometry_keeps_bodies (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hB : B.erase ∈ st.core.T) : (process_block_core E hc cfg st B).bodies = st.bodies := by
  by_cases hp : B.parent ∈ st.bodies
  · simp [process_block_core, commitBlock, hB, hp]
  · simp [process_block_core, hp]

#print axioms coherent_initial
#print axioms coherent_clock
#print axioms commit_core
#print axioms commit_rows
#print axioms commit_tree_view
#print axioms commit_erasure_unique
#print axioms commit_parent_closed
#print axioms commit_pool_view
#print axioms commit_derived_view
#print axioms coherent_process_block
#print axioms existing_geometry_keeps_bodies
end DecoupledConsensusModel.Proofs.NamedStore

end
