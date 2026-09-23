module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.FrameStoreRoot
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound

@[expose] public section



namespace DecoupledConsensusModel.Proofs.NamedFinalizedViable
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The block body, over an arbitrary builder -/

/-- The named twin of `finalizedViable_on_block`: same proof, but the written
entry comes from whatever builder the caller supplies. -/
theorem viable_on_block_using (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V) (h : FinalizedViable st) :
    FinalizedViable (Protocol.on_block_using E st B build) := by
  rcases NamedJustificationBound.raw_eq_or_accepted E st B build with hid | hacc
  · rw [hid]
    exact h
  obtain ⟨u, huT, huF, _huJ, _huhj, humax, husigma, hfresh, hFB, hres⟩ := hacc
  rw [hres]
  have hu : FinalizedViable u := by
    obtain ⟨hFT, W, hW, hFW, hh⟩ := (finalizedViable_iff st).mp h
    have hWB : W ≠ B := fun hEq => hfresh (hEq ▸ hW)
    rw [finalizedViable_iff, huT, husigma, huF, humax]
    exact ⟨Finset.mem_insert_of_mem hFT, W, Finset.mem_insert_of_mem hW, hFW, by
      simpa only [if_neg hWB] using hh⟩
  refine finalizedViable_update_finality u (u.σ B) ?_ rfl ?_ hu
  · rw [huT]
    exact Finset.mem_insert_self _ _
  · rw [huF]
    exact hFB

/-! ## 2. The named handlers -/

private theorem viable_process_core (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs <;> first
    | exact h
    | (rw [NamedStore.commit_core]
       dsimp only [Protocol.on_block_checked_using]
       split_ifs
       · exact viable_on_block_using S.E st.core B.erase _ h
       · exact h)

omit [Fintype V] in
private theorem viable_row (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  exact finalizedViable_of_eq (on_sg_vote_T hc st.core a.erase)
    (coreEq_on_sg_vote hc st.core a.erase).σ_eq
    (coreEq_on_sg_vote hc st.core a.erase).F_eq
    (on_sg_vote_h_max hc st.core a.erase) h

omit [Fintype V] in
private theorem viable_rows (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (viable_row hc st a h)

private theorem viable_block_with (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h : FinalizedViable st.core) :
    FinalizedViable
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core := by
  have hcore := viable_process_core S st B h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact viable_rows S.hc _ B.attestations hcore
  · exact hcore

private theorem viable_clock (S : Setup V) (st : Protocol.NamedStore V) (t : Time)
    (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedStore.setClock S.E st t).core :=
  finalizedViable_of_eq rfl rfl rfl rfl h

private theorem viable_confirmation (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core :=
  FrameStoreRoot.finalizedViable_confirmation_with gc S st.core s h

private theorem viable_vote (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core :=
  FrameStoreRoot.finalizedViable_goldfish_with gc S nd st.core h

private theorem viable_propose (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : FinalizedViable st.core) :
    FinalizedViable
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact viable_block_with S st _ h

private theorem viable_attest (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1.core :=
  viable_row S.hc st _ h

private theorem viable_tick (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 : FinalizedViable st0.core := viable_clock S st t h
  have h1 : FinalizedViable st1.core := by
    dsimp only [st1]
    split_ifs
    · exact viable_propose gc S nd st0 h0
    · exact h0
  have h2 : FinalizedViable st2.core := by
    dsimp only [st2]
    split_ifs
    · exact viable_vote gc S nd st1 h1
    · exact h1
  have h3 : FinalizedViable st3.core := by
    dsimp only [st3]
    split_ifs
    · exact viable_confirmation gc S st2 (s - 1) h2
    · exact h2
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact viable_attest gc S nd st3 record h3
  · exact h3

private theorem node_tick_viable (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : FinalizedViable n.st.core) :
    FinalizedViable (Execution.NamedNode.tick S v n t).1.st.core :=
  viable_tick (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v)
    n.st n.record t h

private theorem node_process_viable (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (h : FinalizedViable n.st.core) :
    FinalizedViable (Execution.NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact viable_block_with S n.st B h
  | gfVote u =>
    exact finalizedViable_of_eq (on_goldfish_vote_checked_T S.E n.st.core u)
      (coreEq_on_goldfish_vote_checked S.E n.st.core u).σ_eq
      (coreEq_on_goldfish_vote_checked S.E n.st.core u).F_eq
      (on_goldfish_vote_checked_h_max S.E n.st.core u) h
  | attest a => exact viable_row S.hc n.st a h

omit [Fintype V] in
private theorem initial_viable (v : V) :
    FinalizedViable (NamedWorld.init v : NamedNodeState V).st.core := by
  rw [finalizedViable_iff]
  exact ⟨Finset.mem_singleton_self _, Block.genesis, Finset.mem_singleton_self _,
    Block.preceq_self _, Nat.sub_le _ _⟩

private theorem world_viable (S : Setup V) (w : NamedWorld V) (e : NamedEvent V)
    (h : ∀ v, FinalizedViable (w v).st.core) :
    ∀ v, FinalizedViable (NamedWorld.step S w e v).st.core := by
  intro v
  cases e with
  | tick u t =>
    by_cases hv : v = u
    · subst u
      simpa only [NamedWorld.step, Function.update_self] using node_tick_viable S v (w v) t (h v)
    · simpa only [NamedWorld.step, Function.update_of_ne hv] using h v
  | deliver u o t =>
    by_cases hv : v = u
    · subst u
      simpa only [NamedWorld.step, Function.update_self] using
        node_process_viable S (w v) o (h v)
    · simpa only [NamedWorld.step, Function.update_of_ne hv] using h v

private theorem fold_viable (S : Setup V) (events : List (NamedEvent V)) (w : NamedWorld V)
    (h : ∀ v, FinalizedViable (w v).st.core) :
    ∀ v, FinalizedViable (events.foldl (NamedWorld.step S) w v).st.core := by
  induction events generalizing w with
  | nil => exact h
  | cons e events ih => exact ih _ (world_viable S w e h)

/-! ## 3. The exports

`FinalizedViable` at every named read, with no premise. -/


theorem finalizedViable_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    FinalizedViable (rho.stateBeforeTime S t v).st.core :=
  fold_viable S _ NamedWorld.init initial_viable v

theorem finalizedViable_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    FinalizedViable (Run.readAt S rho t v).st.core :=
  fold_viable S _ NamedWorld.init initial_viable v

theorem finalizedViable_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    FinalizedViable (Run.stateAt S rho t v).st.core :=
  finalizedViable_readAt S rho t v




#print axioms viable_on_block_using
#print axioms finalizedViable_stateBeforeTime

end DecoupledConsensusModel.Proofs.NamedFinalizedViable

end
