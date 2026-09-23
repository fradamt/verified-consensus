module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.NamedDuties

@[expose] public section

/-! Local confirmation membership. The existing Proofs.NamedStoreRoots.Invariant
is unchanged. A separate predicate tracks both retained confirmation values
through named handlers and concrete current/frame contracts. -/
namespace DecoupledConsensusModel.Proofs.NamedConfirmationMembership
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]


/-- The STABLE record joined the predicate with addendum 34 26 (
): the confirmation duty now floors the confirmation record on the stable
record, and the floor's third arm writes the stable record itself, so the
confirmation value's membership no longer follows from the arm alone. -/
def Confirmed (st : Protocol.Store V) : Prop :=
  st.live_confirmed ∈ st.T ∧ st.latest_confirmed ∈ st.T ∧ st.latest_stable ∈ st.T

def Invariant (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V) : Prop :=
  Proofs.NamedStoreRoots.Invariant E cfg st ∧ Confirmed st.core

omit [Fintype V] in
private theorem confirmed_finality (st : Protocol.Store V) (sigma : ChainState V)
    (h : Confirmed st) : Confirmed (Protocol.update_finality st sigma) := by
  dsimp only [Protocol.update_finality]
  split_ifs <;> exact h

private theorem confirmed_gf_checked (E : Env V) (st : Protocol.Store V)
    (vote : GoldfishVote V) (h : Confirmed st) :
    Confirmed (Protocol.on_goldfish_vote_checked E st vote) := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact h

private theorem confirmed_gf_fold (E : Env V) (st : Protocol.Store V)
    (votes : List (GoldfishVote V)) (h : Confirmed st) :
    Confirmed (votes.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction votes generalizing st with
  | nil => exact h
  | cons vote votes ih => exact ih _ (confirmed_gf_checked E st vote h)

private theorem confirmed_raw_block (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) (h : Confirmed st) :
    Confirmed (Protocol.on_block_using E st B buildState) := by
  dsimp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact h
    | (apply confirmed_finality
       apply confirmed_gf_fold
       exact ⟨Finset.mem_insert_of_mem h.1, Finset.mem_insert_of_mem h.2.1,
         Finset.mem_insert_of_mem h.2.2⟩)

theorem confirmed_process_block_core (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Confirmed st.core) :
    Confirmed (Protocol.NamedStore.process_block_core E hc cfg st B).core := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs <;> first
    | exact h
    | (rw [NamedStore.commit_core]
       dsimp only [Protocol.on_block_checked_using]
       split_ifs
       · exact confirmed_raw_block E st.core B.erase _ h
       · exact h)

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
-- Retain the frozen public Fintype parameter.
theorem confirmed_admit_row (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (h : Confirmed st.core) :
    Confirmed (Protocol.NamedAdmission.admit_row hc st row).core := by
  rw [NamedAdmission.admit_row_core]
  dsimp only [Protocol.on_sg_vote]
  split_ifs <;> exact h

set_option linter.unusedFintypeInType false in
-- Retain the frozen public Fintype parameter.
theorem confirmed_admit_rows (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : Confirmed st.core) :
    Confirmed (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons row rows ih => exact ih _ (confirmed_admit_row hc st row h)

theorem confirmed_on_block_with (admission : Protocol.CarriedAdmission)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) (h : Confirmed st.core) :
    Confirmed (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core := by
  have hcore := confirmed_process_block_core E hc cfg st B h
  cases admission with
  | alsoCarried =>
    dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
    split_ifs
    · exact confirmed_admit_rows hc _ B.attestations hcore
    · exact hcore

/-- Both anchors belong to the processed tree at the actual supplied store. -/
theorem runtime_anchor_mem (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round)
    (hroot : Protocol.get_fg_root st.toFG ∈ st.T) :
    ((DecoupledConsensusModel.Protocol.frameContract cache).read E hc st r).anchor ∈ st.T := by
  exact NamedProposalParent.frame_anchor_mem E hc st r
    (DecoupledConsensusModel.Protocol.readFrame cache st r).g1 hroot

theorem runtime_Q2_mem (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round)
    (B : Block V) (h : ((DecoupledConsensusModel.Protocol.frameContract cache).read E hc st r).Q2 = some B) :
    B ∈ st.T := by
  change DecoupledConsensusModel.Protocol.grade2Block st (DecoupledConsensusModel.Protocol.readFrame cache st r) =
    some B at h
  unfold DecoupledConsensusModel.Protocol.grade2Block at h
  split_ifs at h
  · obtain ⟨root, _, hp⟩ := Option.bind_eq_some_iff.mp h
    exact Proofs.Records.get_filtered_block_tree_subset st.toFG
      (NamedProposalParent.activePrefix_mem _ root B hp)

theorem frame_confirmation_candidate_mem (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (s : Slot)
    (B : Block V) (h : DecoupledConsensusModel.Protocol.frameSGCandidate cache E hc st s = some B) :
    B ∈ st.T := by
  obtain ⟨root, _, hp⟩ := Option.bind_eq_some_iff.mp h
  exact Proofs.Records.get_filtered_block_tree_subset st.toFG
    (NamedProposalParent.activePrefix_mem _ root B hp)

omit [Fintype V] in
private theorem advance_mem (st : Protocol.Store V) (candidate : Block V)
    (hold : st.latest_confirmed ∈ st.T) (hnew : candidate ∈ st.T) :
    Protocol.advance_confirmed st.latest_confirmed candidate ∈ st.T := by
  unfold Protocol.advance_confirmed
  split_ifs <;> assumption

omit [Fintype V] in

/-- 26's three-way floor writes one of three values that are already in
the tree: the confirmation arm, the prior record, or the stable record. -/
private theorem floor_mem {st : Protocol.Store V} {stable confirmed : Block V}
    (hstable : stable ∈ st.T) (hconfirmed : confirmed ∈ st.T)
    (hold : st.latest_confirmed ∈ st.T) :
    Protocol.floor_on_stable stable confirmed st.latest_confirmed ∈ st.T := by
  unfold Protocol.floor_on_stable
  split_ifs <;> assumption

/-- Internal generic helper. Selected current/frame calls below discharge
both selector obligations; arbitrary grade contracts are not assumed safe. -/
private theorem confirmed_update_of_members (gc : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot)
    (h : Confirmed st) (hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T)
    (hanchor : (gc.read E hc st.toHealing (hc.round_of st.s)).anchor ∈ st.T)
    (hstableRoot : ∀ G, gc.stableRoot E hc st.toHealing (hc.round_of st.s) = some G →
      G ∈ st.T)
    (hcandidate : match gc.confirmationSG with
      | .optional select => ∀ B, select E hc st.toHealing s = some B → B ∈ st.T) :
    Confirmed (Protocol.update_confirmation_with gc E hc st s) := by
  have hwalk (score : Block V → Nat) (eligible : Block V → Bool) :
      Protocol.ghost (Protocol.get_sg_root_with gc E hc st.toHealing (hc.round_of st.s))
        (Protocol.get_filtered_block_tree st.toHealing.toFG) score eligible ∈ st.T :=
    Proofs.Records.ghost_mem_of score eligible hanchor (Proofs.Records.get_filtered_block_tree_subset _)
  have hstable : (match gc.stableRoot E hc st.toHealing (hc.round_of st.s) with
      | some G => Protocol.advance_confirmed st.latest_stable G
      | none => st.latest_stable) ∈ st.T := by
    cases hg : gc.stableRoot E hc st.toHealing (hc.round_of st.s) with
    | none => exact h.2.2
    | some G =>
      show Protocol.advance_confirmed st.latest_stable G ∈ st.T
      unfold Protocol.advance_confirmed
      split_ifs
      · exact h.2.2
      · exact hstableRoot G hg
  unfold Confirmed
  dsimp only [Protocol.update_confirmation_with]
  refine ⟨?_, ?_, hstable⟩
  · split_ifs <;> first | exact hroot | exact hwalk _ _
  · -- The floor writes the confirmation arm, the previous record, or the stable one.
    refine floor_mem hstable ?_ h.2.1
    cases hp : gc.confirmationSG with
    | optional select =>
      simp only [hp] at hcandidate ⊢
      split_ifs
      · exact advance_mem st _ h.2.1 (hwalk _ _)
      · cases hs : select E hc st.toHealing s with
        | none => exact h.2.1
        | some B => exact advance_mem st B h.2.1 (hcandidate B hs)

theorem confirmed_update (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot)
    (hroots : Proofs.NamedStoreRoots.RootsInTree st) (h : Confirmed st.core) :
    Confirmed (Protocol.NamedDuties.update_confirmation_with
      (DecoupledConsensusModel.Protocol.frameContract cache) E hc st s).core := by
  apply confirmed_update_of_members _ E hc st.core s h
    (Proofs.NamedStoreRoots.fg_root_mem st hroots)
    (runtime_anchor_mem cache E hc st.core.toHealing _ (Proofs.NamedStoreRoots.fg_root_mem st hroots))
  · 
    intro G hG
    change DecoupledConsensusModel.Protocol.frameStableRoot cache E hc st.core.toHealing
        (hc.round_of st.core.s) = some G at hG
    unfold DecoupledConsensusModel.Protocol.frameStableRoot at hG
    cases hslot : (DecoupledConsensusModel.Protocol.readFrame cache st.core.toHealing
        (hc.round_of st.core.s)).g2.bind id with
    | none =>
        rw [hslot] at hG
        simp at hG
        exact hG ▸ Proofs.NamedStoreRoots.fg_root_mem st hroots
    | some raw =>
        rw [hslot] at hG
        cases hactive : DecoupledConsensusModel.Protocol.activePrefix
            (Protocol.get_filtered_block_tree st.core.toHealing.toFG) raw with
        | none =>
            simp [Option.bind, hactive] at hG
            exact hG ▸ Proofs.NamedStoreRoots.fg_root_mem st hroots
        | some Q =>
            simp [Option.bind, hactive] at hG
            have hQG : Q = G := hG
            subst G
            exact Proofs.Records.get_filtered_block_tree_subset st.core.toHealing.toFG
              (NamedProposalParent.activePrefix_mem _ raw Q hactive)
  · exact frame_confirmation_candidate_mem cache E hc st.core.toHealing s

theorem invariant_initial (E : Env V) (cfg : HeightConfig) :
    Invariant E cfg (Protocol.NamedStore.initial : Protocol.NamedStore V) :=
  ⟨Proofs.NamedStoreRoots.invariant_initial E cfg,
    Finset.mem_singleton_self _, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩

theorem invariant_clock (E : Env V) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (t : Time) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedStore.setClock E st t) :=
  ⟨Proofs.NamedStoreRoots.invariant_clock E cfg st t h.1, h.2⟩


theorem invariant_admit_row (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (row : NamedAttestation V) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedAdmission.admit_row hc st row) :=
  ⟨Proofs.NamedStoreRoots.invariant_admit_row E hc cfg st row h.1, confirmed_admit_row hc st row h.2⟩

theorem invariant_on_block_with (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedAdmission.on_block_with admission E hc cfg st B) :=
  ⟨Proofs.NamedStoreRoots.invariant_on_block_with admission E hc cfg st B h.1,
    confirmed_on_block_with admission E hc cfg st B h.2⟩

theorem invariant_goldfish_vote (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1 := by
  refine ⟨NamedDuties.invariant_goldfish_vote gc E hc cfg nd st h.1, ?_⟩
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact confirmed_gf_checked E st.core _ h.2
  · exact h.2

theorem invariant_update (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (s : Slot) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedDuties.update_confirmation_with
      (DecoupledConsensusModel.Protocol.frameContract cache) E hc st s) :=
  ⟨NamedDuties.invariant_confirmation _ E hc cfg st s h.1,
    confirmed_update cache E hc st s h.1.2 h.2⟩

theorem invariant_propose (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact invariant_on_block_with .alsoCarried E hc cfg st _ h

theorem invariant_attest (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (h : Invariant E cfg st) :
    Invariant E cfg (Protocol.NamedDuties.attest_with gc E hc nd st record).1 :=
  invariant_admit_row E hc cfg st _ h

omit [Fintype V] in
private theorem currentSGVote_mem (st : Protocol.NamedStore V) (grades : Protocol.GradeRead V)
    (hancestor : ∀ B, Block.Preceq B st.core.live_confirmed → B ∈ st.core.T)
    (hroot : Protocol.get_fg_root st.core.toHealing.toFG ∈ st.core.T)
    (hanchor : grades.anchor ∈ st.core.T)
    (hQ2 : ∀ B, grades.Q2 = some B → B ∈ st.core.T) :
    Protocol.currentSGVote st.core.toHealing grades ∈ st.core.T := by
  unfold Protocol.currentSGVote
  split
  · rename_i B hB
    exact hancestor B (Proofs.Engine.deepest_clear_preceq hB)
  · split
    · rename_i q hq
      exact hQ2 q hq
    · split_ifs <;> assumption

/-- Actual current/frame SG selection returns a retained body. No value is
reconstructed from an erased FG row, and the SG head is not the FG source. -/
theorem sg_head_mem (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (h : Invariant E cfg st) :
    let gc := DecoupledConsensusModel.Protocol.frameContract cache
    let r := hc.round_of st.core.s
    Protocol.get_sg_vote_with gc E hc st.core.toHealing r
      (Protocol.grade2_block_with gc E hc st.core.toHealing r) ∈ st.core.T := by
  have hroot := Proofs.NamedStoreRoots.fg_root_mem st h.1.2
  have hanchor := runtime_anchor_mem cache E hc st.core.toHealing
    (hc.round_of st.core.s) hroot
  have hQ2 := runtime_Q2_mem cache E hc st.core.toHealing (hc.round_of st.core.s)
  have hancestor : ∀ B, Block.Preceq B st.core.live_confirmed → B ∈ st.core.T := by
    intro B hB
    exact Proofs.NamedStoreRoots.core_ancestor_mem E cfg st h.1.1 h.2.1 hB
  exact currentSGVote_mem st _ hancestor hroot hanchor hQ2

/-- The shared attestation read carries this exact stored head root. This
local producer is ready for the future computed post-confirmation binding. -/
theorem attestation_input_head (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : Invariant E cfg st) :
    ∃ H ∈ st.core.T,
      (Protocol.attestation_input_with (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc nd st.core.toHealing).confirmed = some H.root :=
  ⟨_, sg_head_mem cache E hc cfg st h, rfl⟩

#print axioms confirmed_process_block_core
#print axioms confirmed_admit_row
#print axioms confirmed_admit_rows
#print axioms confirmed_on_block_with
#print axioms runtime_anchor_mem
#print axioms runtime_Q2_mem
#print axioms frame_confirmation_candidate_mem
#print axioms confirmed_update
#print axioms invariant_initial
#print axioms invariant_clock
#print axioms invariant_admit_row
#print axioms invariant_on_block_with
#print axioms invariant_goldfish_vote
#print axioms invariant_update
#print axioms sg_head_mem
#print axioms attestation_input_head
end DecoupledConsensusModel.Proofs.NamedConfirmationMembership

end
