module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Duties.Proposals
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent

@[expose] public section

/-! Direct core equations and local invariant preservation for named
duties. Proposal uses poolAndCarried rows and alsoCarried admission.
Lookup success and the scheduler are separate consumers of these results. -/
namespace DecoupledConsensusModel.Proofs.NamedDuties
open Protocol.NamedDuties
variable {V : Type} [DecidableEq V] [Fintype V]

theorem goldfish_vote_core (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (goldfish_vote_with gc E hc nd st).1.core =
      (Protocol.goldfish_vote_with gc E hc nd st.core).1 := rfl


theorem goldfish_vote_metadata (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (goldfish_vote_with gc E hc nd st).1.bodies = st.bodies ∧
      (goldfish_vote_with gc E hc nd st).1.sg_rows = st.sg_rows := ⟨rfl, rfl⟩

theorem confirmation_core (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (update_confirmation_with gc E hc st s).core =
      Protocol.update_confirmation_with gc E hc st.core s := rfl

theorem confirmation_metadata (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (update_confirmation_with gc E hc st s).bodies = st.bodies ∧
      (update_confirmation_with gc E hc st s).sg_rows = st.sg_rows := ⟨rfl, rfl⟩

private theorem coherent_replace_core (E : Env V) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (core : Protocol.Store V)
    (h : Proofs.NamedStore.Coherent E cfg st) (hT : core.T = st.core.T)
    (hSigma : core.σ = st.core.σ) (hSG : core.sg_votes = st.core.sg_votes) :
    Proofs.NamedStore.Coherent E cfg { st with core := core } := by
  rcases h with ⟨hTree, hUnique, hParent, hPool, hDerived⟩
  refine ⟨?_, hUnique, hParent, ?_, ?_⟩
  · change core.T = st.bodies.image NamedBlock.erase
    rw [hT]
    exact hTree
  · intro r
    change core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase
    rw [hSG]
    exact hPool r
  · intro B hB
    change core.σ B.erase = Protocol.derive_named E cfg B
    rw [hSigma]
    exact hDerived B hB

private theorem checked_sg_votes (E : Env V) (st : Protocol.Store V)
    (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st vote).sg_votes = st.sg_votes := by
  simp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> rfl

theorem coherent_goldfish_vote (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Proofs.NamedStore.Coherent E cfg st) :
    Proofs.NamedStore.Coherent E cfg (goldfish_vote_with gc E hc nd st).1 := by
  dsimp only [goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact coherent_replace_core E cfg st _ h
      (on_goldfish_vote_checked_T E st.core _)
      (coreEq_on_goldfish_vote_checked E st.core _).σ_eq
      (checked_sg_votes E st.core _)
  · exact h

theorem coherent_confirmation (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (s : Slot) (h : Proofs.NamedStore.Coherent E cfg st) :
    Proofs.NamedStore.Coherent E cfg (update_confirmation_with gc E hc st s) :=
  coherent_replace_core E cfg st _ h rfl rfl rfl

theorem roots_goldfish_vote (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Proofs.NamedStoreRoots.RootsInTree st) :
    Proofs.NamedStoreRoots.RootsInTree (goldfish_vote_with gc E hc nd st).1 :=
  NamedProposalParent.roots_goldfish_vote_with gc E hc nd st h

theorem roots_confirmation (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot)
    (h : Proofs.NamedStoreRoots.RootsInTree st) :
    Proofs.NamedStoreRoots.RootsInTree (update_confirmation_with gc E hc st s) :=
  NamedProposalParent.roots_update_confirmation_with gc E hc st s h

theorem invariant_goldfish_vote (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Proofs.NamedStoreRoots.Invariant E cfg st) :
    Proofs.NamedStoreRoots.Invariant E cfg (goldfish_vote_with gc E hc nd st).1 :=
  ⟨coherent_goldfish_vote gc E hc cfg nd st h.1, roots_goldfish_vote gc E hc nd st h.2⟩

theorem invariant_confirmation (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (s : Slot) (h : Proofs.NamedStoreRoots.Invariant E cfg st) :
    Proofs.NamedStoreRoots.Invariant E cfg (update_confirmation_with gc E hc st s) :=
  ⟨coherent_confirmation gc E hc cfg st s h.1, roots_confirmation gc E hc st s h.2⟩

/-- F1 is fixed at alsoCarried; F2 is fixed at poolAndCarried in the read. -/
theorem propose_some (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Protocol.NamedActions.proposal_with gc .poolAndCarried E hc nd st = some B) :
    propose_block_with gc E hc cfg nd st =
      (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B, some B) := by
  simp only [propose_block_with, h]

theorem propose_none (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Protocol.NamedActions.proposal_with gc .poolAndCarried E hc nd st = none) :
    propose_block_with gc E hc cfg nd st = (st, none) := by
  simp only [propose_block_with, h]



theorem attest_core (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (attest_with gc E hc nd st record).1.core = Protocol.on_sg_vote hc st.core
      (Protocol.NamedActions.round_action_with gc E hc nd st.core.toHealing record).2.erase :=
  NamedAdmission.admit_row_core hc st _


#print axioms goldfish_vote_core
#print axioms goldfish_vote_metadata
#print axioms confirmation_metadata
#print axioms coherent_goldfish_vote
#print axioms coherent_confirmation
#print axioms roots_goldfish_vote
#print axioms roots_confirmation
#print axioms invariant_goldfish_vote
#print axioms invariant_confirmation
#print axioms propose_some
#print axioms propose_none
#print axioms attest_core
end DecoupledConsensusModel.Proofs.NamedDuties

end
