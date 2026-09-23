module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.Admission
public import DecoupledConsensusProofs.Protocol.ChainState.Chain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records

@[expose] public section

/-! Structural named-store root producers follow derive_named and the
actual targeted row processor. RootsInTree is a local invariant seeded at
initialization and preserved by clock, named block processing and F1.
No compatibility derived-state equality or global erasure injectivity is used. -/
namespace DecoupledConsensusModel.Proofs.NamedStoreRoots
open DecoupledConsensusModel Protocol
variable {V Row : Type} [DecidableEq V]


/- The structural geometry lemmas now live in `NamedDerivationGeometry`;
they are re-exported here so that existing references keep resolving. -/
export NamedDerivationGeometry (fold_context_fields chainOrder_fold_rows
  named_transition_latest derive_named_latest chainOrder_derive_named
  derive_named_anchors_preceq core_ancestor_mem transition_justification_ancestor)

variable [Fintype V]



/-- The two mutable store roots need a separate local invariant: Coherent
alone constrains bodies and sigma, not arbitrary top-level F and J values. -/
def RootsInTree (st : Protocol.NamedStore V) : Prop :=
  st.core.F ∈ st.core.T ∧ st.core.J ∈ st.core.T

def Invariant (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) : Prop :=
  Proofs.NamedStore.Coherent E cfg st ∧ RootsInTree st

omit [Fintype V] in
theorem roots_initial : RootsInTree (Protocol.NamedStore.initial : Protocol.NamedStore V) := by
  constructor <;> exact Finset.mem_singleton_self _

theorem roots_clock (E : Env V) (st : Protocol.NamedStore V) (t : Time)
    (h : RootsInTree st) : RootsInTree (Protocol.NamedStore.setClock E st t) := h

omit [Fintype V] in
private theorem update_finality_J_mem (st : Protocol.Store V) (sigma : ChainState V)
    (hJ : st.J ∈ st.T) (hNew : sigma.J ∈ st.T) :
    (Protocol.update_finality st sigma).J ∈ (Protocol.update_finality st sigma).T := by
  rw [Proofs.update_finality_T]
  rcases Proofs.Records.update_finality_J_cases st sigma with h | h
  · rw [h]; exact hJ
  · rw [h]; exact hNew

private theorem raw_F_mem (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) (hF : st.F ∈ st.T) :
    (Protocol.on_block_using E st B buildState).F ∈
      (Protocol.on_block_using E st B buildState).T := by
  simp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact hF
    | (apply finalizedInTree_update_finality
       rw [foldl_on_goldfish_vote_checked_F E, Proofs.foldl_on_goldfish_vote_checked_T E]
       exact Finset.mem_insert_of_mem hF)

private theorem raw_J_mem (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) (hJ : st.J ∈ st.T)
    (hBuilt : (buildState (st.σ B.parent)).J ∈ insert B st.T) :
    (Protocol.on_block_using E st B buildState).J ∈
      (Protocol.on_block_using E st B buildState).T := by
  simp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact hJ
    | (apply update_finality_J_mem
       · rw [(coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).J_eq,
           Proofs.foldl_on_goldfish_vote_checked_T E]
         exact Finset.mem_insert_of_mem hJ
       · rw [(coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).σ_eq,
           Proofs.foldl_on_goldfish_vote_checked_T E]
         simpa using hBuilt)

/-- Actual block-core processing preserves both roots. The named-parent guard
supplies parent lookup, while targeted derivation supplies the new J ancestor. -/
theorem roots_process_block_core (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hCoherent : Proofs.NamedStore.Coherent E cfg st) (hRoots : RootsInTree st) :
    RootsInTree (Protocol.NamedStore.process_block_core E hc cfg st B) := by
  by_cases hp : B.parent ∈ st.bodies
  · have hParentCore : B.erase.parent ∈ st.core.T := by
      rw [Proofs.NamedWire.erase_parent, hCoherent.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hp
    have hclosed : ∀ X ∈ insert B.erase st.core.T,
        X.parent? = none ∨ X.parent ∈ insert B.erase st.core.T := by
      intro X hX
      rcases Finset.mem_insert.mp hX with rfl | hOld
      · exact Or.inr (Finset.mem_insert_of_mem hParentCore)
      · have hImage : X ∈ st.bodies.image NamedBlock.erase := by rwa [← hCoherent.1]
        obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hImage
        right
        apply Finset.mem_insert_of_mem
        rw [Proofs.NamedWire.erase_parent, hCoherent.1]
        exact Finset.mem_image_of_mem NamedBlock.erase (hCoherent.2.2.1.2 N hN)
    have hBuilt : (named_transition E cfg (st.core.σ B.erase.parent) B).J ∈
        insert B.erase st.core.T := by
      rw [Proofs.NamedWire.erase_parent, hCoherent.2.2.2.2 B.parent hp]
      exact Proofs.Records.mem_of_preceq hclosed _ B.erase (Finset.mem_insert_self _ _)
        (transition_justification_ancestor E cfg B)
    change RootsInTree (if B.parent ∉ st.bodies then st else
      Protocol.NamedStore.commitBlock st
        (Protocol.on_block_checked_using
          (fun current => Protocol.on_block_using E current B.erase
            (fun parentState => named_transition E cfg parentState B)) hc st.core B.erase) B)
    rw [if_neg (not_not.mpr hp)]
    unfold RootsInTree
    rw [NamedStore.commit_core]
    dsimp only [Protocol.on_block_checked_using]
    split_ifs
    · exact ⟨raw_F_mem E st.core B.erase _ hRoots.1,
        raw_J_mem E st.core B.erase _ hRoots.2 hBuilt⟩
    · exact hRoots
  · simpa only [Protocol.NamedStore.process_block_core, if_pos hp] using hRoots

omit [Fintype V] in
theorem roots_admit_row (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (h : RootsInTree st) :
    RootsInTree (Protocol.NamedAdmission.admit_row hc st row) := by
  unfold RootsInTree
  rw [NamedAdmission.admit_row_core]
  simpa only [(coreEq_on_sg_vote hc st.core row.erase).F_eq,
    (coreEq_on_sg_vote hc st.core row.erase).J_eq, on_sg_vote_T] using h

omit [Fintype V] in
theorem roots_admit_rows (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : RootsInTree st) :
    RootsInTree (Protocol.NamedAdmission.admit_rows hc st rows) := by
  induction rows generalizing st with
  | nil => exact h
  | cons row rows ih =>
    exact ih (Protocol.NamedAdmission.admit_row hc st row) (roots_admit_row hc st row h)

omit [Fintype V] in
theorem roots_admit_carried (admission : Protocol.CarriedAdmission)
    (hc : Protocol.HealConfig) (before after : Protocol.NamedStore V) (B : NamedBlock V)
    (h : RootsInTree after) :
    RootsInTree (Protocol.NamedAdmission.admit_carried admission hc before after B) := by
  cases admission with
  | alsoCarried =>
    dsimp only [Protocol.NamedAdmission.admit_carried]
    split_ifs
    · exact roots_admit_rows hc after B.attestations h
    · exact h

theorem roots_on_block_with (admission : Protocol.CarriedAdmission)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) (h : Invariant E cfg st) :
    RootsInTree (Protocol.NamedAdmission.on_block_with admission E hc cfg st B) :=
  roots_admit_carried admission hc st _ B (roots_process_block_core E hc cfg st B h.1 h.2)

omit [Fintype V] in
theorem fg_root_mem (st : Protocol.NamedStore V) (h : RootsInTree st) :
    Protocol.get_fg_root st.core.toHealing.toFG ∈ st.core.T := by
  unfold Protocol.get_fg_root
  split_ifs
  · exact h.2
  · exact h.1

theorem invariant_initial (E : Env V) (cfg : HeightConfig) :
    Invariant E cfg (Protocol.NamedStore.initial : Protocol.NamedStore V) :=
  ⟨NamedStore.coherent_initial E cfg, roots_initial⟩

theorem invariant_clock (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (t : Time) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedStore.setClock E st t) :=
  ⟨NamedStore.coherent_clock E cfg st t h.1, roots_clock E st t h.2⟩

theorem invariant_admit_row (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (row : NamedAttestation V) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedAdmission.admit_row hc st row) :=
  ⟨NamedAdmission.coherent_admit_row E hc cfg st row h.1, roots_admit_row hc st row h.2⟩

theorem invariant_on_block_with (admission : Protocol.CarriedAdmission)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedAdmission.on_block_with admission E hc cfg st B) :=
  ⟨NamedAdmission.coherent_on_block admission E hc cfg st B h.1,
    roots_on_block_with admission E hc cfg st B h⟩



#print axioms fold_context_fields
#print axioms chainOrder_fold_rows
#print axioms named_transition_latest
#print axioms derive_named_latest
#print axioms chainOrder_derive_named
#print axioms derive_named_anchors_preceq
#print axioms core_ancestor_mem
#print axioms roots_initial
#print axioms roots_clock
#print axioms roots_process_block_core
#print axioms roots_admit_row
#print axioms roots_admit_rows
#print axioms roots_admit_carried
#print axioms roots_on_block_with
#print axioms fg_root_mem
#print axioms invariant_initial
#print axioms invariant_clock
#print axioms invariant_admit_row
#print axioms invariant_on_block_with
end DecoupledConsensusModel.Proofs.NamedStoreRoots

end
