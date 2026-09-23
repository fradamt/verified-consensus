module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OutageInputs

@[expose] public section

/-! First numeric named-store slice. Bounds and frontier monotonicity
come from actual closed handlers and folds. No numeric invariant, observed
source, network condition, or finalization certificate is an outer premise. -/
namespace DecoupledConsensusModel.Proofs.NamedNumericStore
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

def HeightsBounded (S : Setup V) (st : Protocol.NamedStore V) : Prop :=
  ∀ B ∈ st.bodies, (derive_named S.E S.cfg B).h ≤ st.core.h_max

private def CoreBound (st : Protocol.Store V) : Prop :=
  ∀ B ∈ st.T, (st.σ B).h ≤ st.h_max

private def CoreStep (before after : Protocol.Store V) : Prop :=
  before.h_max ≤ after.h_max ∧ (CoreBound before → CoreBound after)

omit [DecidableEq V] [Fintype V] in
private theorem step_refl (st : Protocol.Store V) : CoreStep st st := ⟨le_refl _, id⟩

omit [DecidableEq V] [Fintype V] in
private theorem step_trans {a b c : Protocol.Store V} (hab : CoreStep a b) (hbc : CoreStep b c) :
    CoreStep a c := ⟨hab.1.trans hbc.1, fun h => hbc.2 (hab.2 h)⟩

omit [Fintype V] in
private theorem finality_max (st : Protocol.Store V) (sigma : ChainState V) :
    (Protocol.update_finality st sigma).h_max = max st.h_max sigma.h := by
  dsimp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
private theorem finality_bound (st : Protocol.Store V) (sigma : ChainState V)
    (h : ∀ B ∈ st.T, (st.σ B).h ≤ max st.h_max sigma.h) :
    CoreBound (Protocol.update_finality st sigma) := by
  dsimp only [Protocol.update_finality]
  split_ifs <;> exact h

private theorem gf_fields (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V) :
    let out := Protocol.on_goldfish_vote_checked E st u
    out.T = st.T ∧ out.σ = st.σ ∧ out.h_max = st.h_max := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

private theorem gf_fold_fields (E : Env V) (st : Protocol.Store V) (votes : List (GoldfishVote V)) :
    let out := votes.foldl (Protocol.on_goldfish_vote_checked E) st
    out.T = st.T ∧ out.σ = st.σ ∧ out.h_max = st.h_max := by
  induction votes generalizing st with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons u votes ih =>
    have h := ih (Protocol.on_goldfish_vote_checked E st u)
    have one := gf_fields E st u
    exact ⟨h.1.trans one.1, h.2.1.trans one.2.1, h.2.2.trans one.2.2⟩

private theorem raw_block_step (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V) :
    CoreStep st (Protocol.on_block_using E st B build) := by
  dsimp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact step_refl st
    | (constructor
       · rw [finality_max, (gf_fold_fields E _ B.gf_votes).2.2]
         exact Nat.le_max_left _ _
       · intro h
         apply finality_bound
         rw [(gf_fold_fields E _ B.gf_votes).1,
           (gf_fold_fields E _ B.gf_votes).2.1, (gf_fold_fields E _ B.gf_votes).2.2]
         intro C hC
         by_cases hCB : C = B
         · subst C
           exact Nat.le_max_right _ _
         · simp only [if_neg hCB]
           exact (h C ((Finset.mem_insert.mp hC).resolve_left hCB)).trans (Nat.le_max_left _ _))

private theorem named_core_step (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    CoreStep st.core (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs <;> first
    | exact step_refl st.core
    | (rw [NamedStore.commit_core]
       dsimp only [Protocol.on_block_checked_using]
       split_ifs
       · exact raw_block_step S.E st.core B.erase _
       · exact step_refl st.core)

omit [Fintype V] in
private theorem row_step (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    CoreStep st.core (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  dsimp only [Protocol.on_sg_vote]
  split_ifs <;> exact ⟨le_refl _, id⟩

omit [Fintype V] in
private theorem rows_step (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    CoreStep st.core (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact step_refl _
  | cons a rows ih => exact step_trans (row_step hc st a) (ih _)

private theorem block_step (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    CoreStep st.core
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core := by
  have hc := named_core_step S st B
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact step_trans hc (rows_step S.hc _ B.attestations)
  · exact hc

private theorem gf_step (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V) :
    CoreStep st (Protocol.on_goldfish_vote_checked E st u) := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact ⟨le_refl _, id⟩

private theorem clock_step (E : Env V) (st : Protocol.NamedStore V) (t : Time) :
    CoreStep st.core (Protocol.NamedStore.setClock E st t).core := ⟨le_refl _, id⟩

private theorem confirmation_step (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) :
    CoreStep st.core (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core :=
  ⟨le_refl _, id⟩

private theorem propose_step (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    CoreStep st.core (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact step_refl _
  · exact block_step S st _

private theorem vote_step (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    CoreStep st.core (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact gf_step S.E st.core _
  · exact step_refl _

private theorem attest_step (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) :
    CoreStep st.core (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1.core :=
  row_step S.hc st _

private theorem tick_step (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    CoreStep st.core (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h01 : CoreStep st0.core st1.core := by
    dsimp only [st1]
    split_ifs
    · exact propose_step gc S nd st0
    · exact step_refl _
  have h12 : CoreStep st1.core st2.core := by
    dsimp only [st2]
    split_ifs
    · exact vote_step gc S nd st1
    · exact step_refl _
  have h23 : CoreStep st2.core st3.core := by
    dsimp only [st3]
    split_ifs
    · exact confirmation_step gc S st2 (s - 1)
    · exact step_refl _
  have h03 := step_trans (clock_step S.E st t) (step_trans h01 (step_trans h12 h23))
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact step_trans h03 (attest_step gc S nd st3 record)
  · exact h03

private theorem node_tick_step (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    CoreStep n.st.core (Execution.NamedNode.tick S v n t).1.st.core :=
  tick_step (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v) n.st n.record
    t

private theorem node_process_step (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    CoreStep n.st.core (Execution.NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact block_step S n.st B
  | gfVote u => exact gf_step S.E n.st.core u
  | attest a => exact row_step S.hc n.st a

private theorem world_step (S : Setup V) (w : NamedWorld V) (e : NamedEvent V) (v : V) :
    CoreStep (w v).st.core (NamedWorld.step S w e v).st.core := by
  cases e with
  | tick u t =>
    by_cases h : v = u
    · subst u
      simpa only [NamedWorld.step, Function.update_self] using node_tick_step S v (w v) t
    · simpa only [NamedWorld.step, Function.update_of_ne h] using step_refl (w v).st.core
  | deliver u o t =>
    by_cases h : v = u
    · subst u
      simpa only [NamedWorld.step, Function.update_self] using node_process_step S (w v) o
    · simpa only [NamedWorld.step, Function.update_of_ne h] using step_refl (w v).st.core

omit [Fintype V] in
private theorem initial_bound (v : V) :
    CoreBound (NamedWorld.init v : NamedNodeState V).st.core := by
  intro B hB
  have he : B = Block.genesis := Finset.mem_singleton.mp hB
  subst B
  exact le_refl _

private theorem fold_bound (S : Setup V) (events : List (NamedEvent V)) (w : NamedWorld V)
    (h : ∀ v, CoreBound (w v).st.core) :
    ∀ v, CoreBound (events.foldl (NamedWorld.step S) w v).st.core := by
  induction events generalizing w with
  | nil => exact h
  | cons e events ih => exact ih _ (fun v => (world_step S w e v).2 (h v))

private theorem named_bound (S : Setup V) (st : Protocol.NamedStore V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreBound st.core) : HeightsBounded S st := by
  intro B hB
  have hmem : B.erase ∈ st.core.T := by
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hB
  have hb := h B.erase hmem
  rw [hco.2.2.2.2 B hB] at hb
  exact hb

theorem heights_bounded_stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    HeightsBounded S (NamedRun.stateBefore S rho i v).st :=
  named_bound S _ (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
    (fold_bound S (rho.events.take i) NamedWorld.init initial_bound v)

theorem heights_bounded_stateBeforeTime (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    HeightsBounded S (NamedRun.stateBeforeTime S rho t v).st :=
  named_bound S _ (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
    (fold_bound S _ NamedWorld.init initial_bound v)

theorem heights_bounded_readAt (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    HeightsBounded S (NamedRun.readAt S rho t v).st :=
  named_bound S _ (Proofs.NamedRuntime.readAt_invariants S rho t v).1.1.1
    (fold_bound S _ NamedWorld.init initial_bound v)



theorem stateBefore_hmax_mono (S : Setup V) (rho : NamedRun V) (v : V)
    {i j : Nat} (hij : i ≤ j) :
    (NamedRun.stateBefore S rho i v).st.core.h_max ≤
      (NamedRun.stateBefore S rho j v).st.core.h_max := by
  have hs (k : Nat) : (NamedRun.stateBefore S rho k v).st.core.h_max ≤
      (NamedRun.stateBefore S rho (k + 1) v).st.core.h_max := by
    rw [Proofs.NamedRuntime.stateBefore_succ]
    cases he : rho.events[k]? with
    | none => simp only [Option.toList_none, List.foldl_nil, le_refl]
    | some e =>
      simpa only [Option.toList_some, List.foldl_cons, List.foldl_nil] using
        (world_step S (NamedRun.stateBefore S rho k) e v).1
  exact (monotone_nat_of_le_succ hs) hij

end DecoupledConsensusModel.Proofs.NamedNumericStore

end
