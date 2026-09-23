module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.ActionSources
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxMonotone
public import DecoupledConsensusProofs.Protocol.Schedule.Alignment
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry

@[expose] public section

/-!
# Low event-indexed `h_max` core

This module owns the store/tree invariants, exact event-prefix frontiers, and
height interpolation used by raw progress and recovery. It has no recovery
height, healing suffix, or termination assumption.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Exact maximum witness -/

def HMaxInTree (st : Protocol.Store V) : Prop :=
  ∃ B ∈ st.T, st.h_max ≤ (st.σ B).h




/-! ## Action-store field facts -/



namespace HealingSurface

/-! ## Exact action read -/


/-! ## Processed-tree height bounds -/

/-- Every processed block is at or below the store's recorded maximum height. -/
def TreeHeightsLeHMax (st : Protocol.Store V) : Prop :=
  ∀ B ∈ st.T, (st.σ B).h ≤ st.h_max

omit [Fintype V] in
/-- The initial store satisfies the processed-height upper bound. -/
theorem treeHeightsLeHMax_init :
    TreeHeightsLeHMax (Protocol.Store.init : Protocol.Store V) := by
  intro B hB
  simp only [Protocol.Store.init, Finset.mem_singleton] at hB
  subst B
  rfl

omit [Fintype V] in
/-- `update_finality` changes neither the processed tree nor its state map and
sets the resulting bound to `max st.h_max sigma.h`. -/
theorem treeHeightsLeHMax_update_finality_of_max
    (st : Protocol.Store V) (sigma : Protocol.ChainState V)
    (h : ∀ B ∈ st.T, (st.σ B).h ≤ max st.h_max sigma.h) :
    TreeHeightsLeHMax (Protocol.update_finality st sigma) := by
  intro B hB
  rw [Proofs.update_finality_T] at hB
  rw [update_finality_σ]
  have hle := h B hB
  simp only [Protocol.update_finality]
  split_ifs <;> exact hle


omit [DecidableEq V] [Fintype V] in
/-- Carry the height bound across a handler that preserves the three fields. -/
theorem treeHeightsLeHMax_of_eq {st st' : Protocol.Store V}
    (hT : st'.T = st.T) (hSigma : st'.σ = st.σ)
    (hMax : st'.h_max = st.h_max) (h : TreeHeightsLeHMax st) :
    TreeHeightsLeHMax st' := by
  intro B hB
  rw [hT] at hB
  rw [hSigma, hMax]
  exact h B hB



private theorem treeHeightsLeHMax_on_block_using
    (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V)
    (h : TreeHeightsLeHMax st) :
    TreeHeightsLeHMax (Protocol.on_block_using E st B buildState) := by
  by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · simpa [Protocol.on_block_using, hfirst] using h
  by_cases hadmit : Block.preceq st.F B = true
  · by_cases hproposer : B.proposer? = some (E.proposer B.slot)
    · by_cases hparent : B.parent.slot < B.slot
      · let state := buildState (st.σ B.parent)
        let stored : Protocol.Store V :=
          { st with
            σ := fun C => if C = B then state else st.σ C
            T := insert B st.T
            timestamp_block := fun C =>
              if C = B then some (st.t : Stamp) else st.timestamp_block C }
        let unpacked : Protocol.Store V :=
          B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored
        have hon : Protocol.on_block_using E st B buildState =
            Protocol.update_finality unpacked (unpacked.σ B) := by
          simp [Protocol.on_block_using, hfirst, hadmit, hproposer, hparent,
            unpacked, stored, state]
        rw [hon]
        apply treeHeightsLeHMax_update_finality_of_max
        intro C hC
        have hT : unpacked.T = insert B st.T := by
          simp only [unpacked, stored, Proofs.foldl_on_goldfish_vote_checked_T]
        rw [hT] at hC
        rcases Finset.mem_insert.mp hC with hCB | hCT
        · subst C
          have hSigma : unpacked.σ B = state := by
            simp only [unpacked, stored,
              (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes stored).σ_eq,
              if_pos]
          have hMax : unpacked.h_max = st.h_max := by
            simp only [unpacked, stored, foldl_on_goldfish_vote_checked_h_max]
          rw [hSigma, hMax]
          exact Nat.le_max_right _ _
        · have hBnot : B ∉ st.T := by
            intro hBT
            exact hfirst (Or.inr (Or.inl hBT))
          have hCBne : C ≠ B := by
            intro hEq
            apply hBnot
            exact hEq ▸ hCT
          have hSigma : unpacked.σ C = st.σ C := by
            simp only [unpacked, stored,
              (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes stored).σ_eq,
              if_neg hCBne]
          have hMax : unpacked.h_max = st.h_max := by
            simp only [unpacked, stored, foldl_on_goldfish_vote_checked_h_max]
          rw [hSigma, hMax]
          exact (h C hCT).trans (Nat.le_max_left _ _)
      · simpa [Protocol.on_block_using, hfirst, hadmit, hproposer, hparent] using h
    · simpa [Protocol.on_block_using, hfirst, hadmit, hproposer] using h
  · simpa [Protocol.on_block_using, hfirst, hadmit] using h

private theorem treeHeightsLeHMax_on_block_checked_using
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (B : Block V)
    (handle : Protocol.Store V → Protocol.Store V)
    (hhandle : TreeHeightsLeHMax st → TreeHeightsLeHMax (handle st))
    (h : TreeHeightsLeHMax st) :
    TreeHeightsLeHMax (Protocol.on_block_checked_using handle hc st B) := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle h
  · exact h

private theorem process_block_core_treeHeightsLeHMax
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : TreeHeightsLeHMax st.core) :
    TreeHeightsLeHMax (Protocol.NamedStore.process_block_core E hc cfg st B).core := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  · rw [commitBlock_core]
    exact treeHeightsLeHMax_on_block_checked_using hc st.core B.erase _
      (fun h' => treeHeightsLeHMax_on_block_using E st.core B.erase _ h') h
  · exact h

private theorem admit_row_treeHeightsLeHMax
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (a : NamedAttestation V)
    (h : TreeHeightsLeHMax st.core) :
    TreeHeightsLeHMax (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [admit_row_core]
  intro B hB
  rw [on_sg_vote_T hc st.core a.erase] at hB
  rw [(coreEq_on_sg_vote hc st.core a.erase).σ_eq, on_sg_vote_h_max]
  exact h B hB

private theorem admit_rows_treeHeightsLeHMax (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      TreeHeightsLeHMax st.core →
        TreeHeightsLeHMax (Protocol.NamedAdmission.admit_rows hc st rows).core
  | [], _, h => h
  | a :: rows, st, h =>
      admit_rows_treeHeightsLeHMax hc rows (Protocol.NamedAdmission.admit_row hc st a)
        (admit_row_treeHeightsLeHMax hc st a h)

private theorem admit_carried_treeHeightsLeHMax
    (admission : Protocol.CarriedAdmission) (hc : Protocol.HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V)
    (h : TreeHeightsLeHMax after.core) :
    TreeHeightsLeHMax (Protocol.NamedAdmission.admit_carried admission hc before after B).core := by
  cases admission with
  | alsoCarried =>
      dsimp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_treeHeightsLeHMax hc B.attestations after h
      · exact h

private theorem on_block_with_treeHeightsLeHMax
    (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : TreeHeightsLeHMax st.core) :
    TreeHeightsLeHMax (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core :=
  admit_carried_treeHeightsLeHMax admission hc st _ B
    (process_block_core_treeHeightsLeHMax E hc cfg st B h)

private theorem propose_block_with_treeHeightsLeHMax
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : TreeHeightsLeHMax st.core) :
    TreeHeightsLeHMax (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact on_block_with_treeHeightsLeHMax .alsoCarried E hc cfg st _ h

private theorem goldfish_vote_with_treeHeightsLeHMax
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : TreeHeightsLeHMax st.core) :
    TreeHeightsLeHMax (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · intro B hB
    rw [on_goldfish_vote_checked_T] at hB
    rw [(coreEq_on_goldfish_vote_checked E st.core _).σ_eq, on_goldfish_vote_checked_h_max]
    exact h B hB
  · exact h

private theorem update_confirmation_with_treeHeightsLeHMax
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (s : Slot) (h : TreeHeightsLeHMax st.core) :
    TreeHeightsLeHMax (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core :=
  h

private theorem attest_with_treeHeightsLeHMax
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (h : TreeHeightsLeHMax st.core) :
    TreeHeightsLeHMax (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core :=
  admit_row_treeHeightsLeHMax hc st _ h

private theorem tick_treeHeightsLeHMax
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : TreeHeightsLeHMax st.core) :
    TreeHeightsLeHMax (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core := by
  refine named_tick_preserves (fun st' => TreeHeightsLeHMax st'.core) gc E hc cfg nd
    ?_ ?_ ?_ ?_ st record t h
  · intro st' h'; exact propose_block_with_treeHeightsLeHMax gc E hc cfg nd st' h'
  · intro st' h'; exact goldfish_vote_with_treeHeightsLeHMax gc E hc nd st' h'
  · intro st' s h'; exact update_confirmation_with_treeHeightsLeHMax gc E hc st' s h'
  · intro st' record' h'; exact attest_with_treeHeightsLeHMax gc E hc nd st' record' h'

private theorem node_tick_treeHeightsLeHMax
    (S : Setup V) (v : V) (n : NodeState V) (t : Time) (h : TreeHeightsLeHMax n.st.core) :
    TreeHeightsLeHMax (NamedNode.tick S v n t).1.st.core :=
  tick_treeHeightsLeHMax (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
    S.E S.hc S.cfg (S.node v) n.st n.record t h

private theorem node_process_treeHeightsLeHMax
    (S : Setup V) (n : NodeState V) (o : Object V) (h : TreeHeightsLeHMax n.st.core) :
    TreeHeightsLeHMax (NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact on_block_with_treeHeightsLeHMax .alsoCarried S.E S.hc S.cfg n.st B h
  | gfVote u =>
      show TreeHeightsLeHMax (Protocol.on_goldfish_vote_checked S.E n.st.core u)
      intro C hC
      rw [on_goldfish_vote_checked_T] at hC
      rw [(coreEq_on_goldfish_vote_checked S.E n.st.core u).σ_eq, on_goldfish_vote_checked_h_max]
      exact h C hC
  | attest a => exact admit_row_treeHeightsLeHMax S.hc n.st a h

private theorem worldStep_treeHeightsLeHMax
    (S : Setup V) (w : World V) (e : Event V) (v : V) (h : TreeHeightsLeHMax (w v).st.core) :
    TreeHeightsLeHMax ((World.step S w e) v).st.core := by
  cases e with
  | tick u t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact node_tick_treeHeightsLeHMax S v (w v) t h
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact h
  | deliver u o t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact node_process_treeHeightsLeHMax S (w v) o h
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact h

private theorem foldlWorld_treeHeightsLeHMax
    (S : Setup V) (v : V) (events : List (Event V)) (w : World V)
    (h : TreeHeightsLeHMax (w v).st.core) :
    TreeHeightsLeHMax ((events.foldl (World.step S) w) v).st.core := by
  induction events generalizing w with
  | nil => exact h
  | cons e events ih =>
      exact ih (w := World.step S w e) (worldStep_treeHeightsLeHMax S w e v h)

private theorem stateBefore_treeHeightsLeHMax
    (S : Setup V) (rho : Run V) (v : V) (i : Nat) :
    TreeHeightsLeHMax (rho.stateBefore S i v).st.core := by
  unfold Run.stateBefore
  exact foldlWorld_treeHeightsLeHMax S v (rho.events.take i) NamedWorld.init
    treeHeightsLeHMax_init

private theorem stateBeforeTime_treeHeightsLeHMax
    (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    TreeHeightsLeHMax (rho.storeBeforeTime S v t).core := by
  unfold Run.storeBeforeTime NamedRun.stateBeforeTime
  exact foldlWorld_treeHeightsLeHMax S v _ NamedWorld.init treeHeightsLeHMax_init



/-- The same upper bound holds in the exact post-confirmation store read by a
round action. `actionStoreAt` now reads a full named node state
(`NamedActionReads.actionReadAt`), not a bare store ( restatement),
so the conclusion is read at `.st.core`; its confirmation-duty write is
unconditional (no branch, unlike the retired bare `attestStore`), so the T/σ/
h_max agreement with the pre-action read is definitional. -/
theorem treeHeightsLeHMax_actionStore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) :
    TreeHeightsLeHMax (actionStoreAt S rho v r).st.core := by
  have hpre : TreeHeightsLeHMax (rho.stateBeforeTime S (S.a r) v).st.core :=
    stateBeforeTime_treeHeightsLeHMax S rho v (S.a r)
  have hT : (actionStoreAt S rho v r).st.core.T =
      (rho.stateBeforeTime S (S.a r) v).st.core.T := rfl
  have hσ : (actionStoreAt S rho v r).st.core.σ =
      (rho.stateBeforeTime S (S.a r) v).st.core.σ := rfl
  have hmax : (actionStoreAt S rho v r).st.core.h_max =
      (rho.stateBeforeTime S (S.a r) v).st.core.h_max := rfl
  exact treeHeightsLeHMax_of_eq hT hσ hmax hpre


/-! ### One event raises the stored maximum by at most one -/

omit [Fintype V] in
/-- The one writer of `h_max` stores the maximum with the incoming height. -/
theorem update_finality_h_max_eq
    (st : Protocol.Store V) (sigma : Protocol.ChainState V) :
    (Protocol.update_finality st sigma).h_max = max st.h_max sigma.h := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl




private theorem named_transition_h_le_succ
    (E : Env V) (cfg : Protocol.HeightConfig) (B : NamedBlock V)
    (sigma : Protocol.ChainState V) :
    (Protocol.named_transition E cfg sigma B).h ≤ sigma.h + 1 := by
  have hfold : (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) sigma
      B.erase B.attestations).h = sigma.h := by
    unfold Protocol.fold_rows
    exact (NamedDerivationGeometry.fold_context_fields
      (Protocol.TimeoutBinding.targeted V) B.attestations
      { sigma with s := B.erase.slot }).2.1
  unfold Protocol.named_transition Protocol.transition_rows
  rw [Protocol.process_height_events_eq]
  split_ifs
  · rw [Protocol.advance_height_h, Protocol.afterFin_h, hfold]
  · rw [Protocol.advance_height_h, Protocol.afterFin_h, hfold]
  · rw [Protocol.afterFin_h, hfold]
    exact Nat.le_succ _

private theorem on_block_using_h_max_le_succ
    (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V)
    (hbuild : ∀ parentState, (buildState parentState).h ≤ parentState.h + 1)
    (hbound : TreeHeightsLeHMax st) :
    (Protocol.on_block_using E st B buildState).h_max ≤ st.h_max + 1 := by
  by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · simp [Protocol.on_block_using, hfirst]
  by_cases hadmit : Block.preceq st.F B = true
  · by_cases hproposer : B.proposer? = some (E.proposer B.slot)
    · by_cases hparent : B.parent.slot < B.slot
      · let state := buildState (st.σ B.parent)
        let stored : Protocol.Store V :=
          { st with
            σ := fun C => if C = B then state else st.σ C
            T := insert B st.T
            timestamp_block := fun C =>
              if C = B then some (st.t : Stamp) else st.timestamp_block C }
        let unpacked := B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored
        have hon : Protocol.on_block_using E st B buildState =
            Protocol.update_finality unpacked (unpacked.σ B) := by
          simp [Protocol.on_block_using, hfirst, hadmit, hproposer, hparent,
            unpacked, stored, state]
        have hparentT : B.parent ∈ st.T := by
          by_contra hnot
          exact hfirst (Or.inr (Or.inr hnot))
        have hstate : state.h ≤ st.h_max + 1 :=
          (hbuild (st.σ B.parent)).trans
            (Nat.add_le_add_right (hbound B.parent hparentT) 1)
        have hSigma : unpacked.σ B = state := by
          simp only [unpacked, stored,
            (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes stored).σ_eq,
            if_pos]
        have hMax : unpacked.h_max = st.h_max := by
          simp only [unpacked, stored, foldl_on_goldfish_vote_checked_h_max]
        rw [hon, update_finality_h_max_eq, hSigma, hMax]
        exact Nat.max_le.mpr ⟨Nat.le_succ _, hstate⟩
      · simp [Protocol.on_block_using, hfirst, hadmit, hproposer, hparent]
    · simp [Protocol.on_block_using, hfirst, hadmit, hproposer]
  · simp [Protocol.on_block_using, hfirst, hadmit]

private theorem on_block_checked_using_h_max_le_succ
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (B : Block V)
    (handle : Protocol.Store V → Protocol.Store V)
    (hhandle : TreeHeightsLeHMax st → (handle st).h_max ≤ st.h_max + 1)
    (hbound : TreeHeightsLeHMax st) :
    (Protocol.on_block_checked_using handle hc st B).h_max ≤ st.h_max + 1 := by
  simp only [Protocol.on_block_checked_using]
  split_ifs with hvalid
  · exact hhandle hbound
  · exact Nat.le_succ _

private theorem process_block_core_h_max_le_succ
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hbound : TreeHeightsLeHMax st.core) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.h_max ≤ st.core.h_max + 1 := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  · rw [commitBlock_core]
    exact on_block_checked_using_h_max_le_succ hc st.core B.erase _
      (fun h' => on_block_using_h_max_le_succ E st.core B.erase _
        (named_transition_h_le_succ E cfg B) h') hbound
  · exact Nat.le_succ _

private theorem admit_row_h_max_eq
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (a : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st a).core.h_max = st.core.h_max := by
  rw [admit_row_core, on_sg_vote_h_max]

private theorem admit_rows_h_max_eq (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      (Protocol.NamedAdmission.admit_rows hc st rows).core.h_max = st.core.h_max
  | [], _ => rfl
  | a :: rows, st =>
      (admit_rows_h_max_eq hc rows (Protocol.NamedAdmission.admit_row hc st a)).trans
        (admit_row_h_max_eq hc st a)

private theorem on_block_with_h_max_le_succ
    (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hbound : TreeHeightsLeHMax st.core) :
    (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.h_max ≤
      st.core.h_max + 1 := by
  have hb := process_block_core_h_max_le_succ E hc cfg st B hbound
  cases admission with
  | alsoCarried =>
      dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
      split_ifs
      · rw [admit_rows_h_max_eq]
        exact hb
      · exact hb

private theorem propose_block_with_h_max_le_succ
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hbound : TreeHeightsLeHMax st.core) :
    (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.h_max ≤
      st.core.h_max + 1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact Nat.le_succ _
  · exact on_block_with_h_max_le_succ .alsoCarried E hc cfg st _ hbound

private theorem goldfish_vote_with_h_max_eq
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.h_max = st.core.h_max := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_h_max E st.core _
  · rfl

private theorem update_confirmation_with_h_max_eq'
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.h_max = st.core.h_max :=
  rfl


private theorem attest_with_h_max_eq
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.h_max = st.core.h_max :=
  admit_row_h_max_eq hc st _

private theorem tick_h_max_le_succ
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (hbound : TreeHeightsLeHMax st.core) :
    (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.h_max ≤ st.core.h_max + 1 := by
  have hbound0 : TreeHeightsLeHMax (Protocol.NamedStore.setClock E st t).core := hbound
  have hprop : (Protocol.NamedDuties.propose_block_with gc E hc cfg nd
      (Protocol.NamedStore.setClock E st t)).1.core.h_max ≤ st.core.h_max + 1 :=
    propose_block_with_h_max_le_succ gc E hc cfg nd (Protocol.NamedStore.setClock E st t) hbound0
  dsimp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps]
  split_ifs <;>
    simp only [goldfish_vote_with_h_max_eq, update_confirmation_with_h_max_eq',
      attest_with_h_max_eq] <;>
    first
      | exact Nat.le_succ _
      | exact hprop

private theorem node_tick_h_max_le_succ
    (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    (hbound : TreeHeightsLeHMax n.st.core) :
    (NamedNode.tick S v n t).1.st.core.h_max ≤ n.st.core.h_max + 1 :=
  tick_h_max_le_succ (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
    S.E S.hc S.cfg (S.node v) n.st n.record t hbound

private theorem node_process_h_max_le_succ
    (S : Setup V) (n : NodeState V) (o : Object V)
    (hbound : TreeHeightsLeHMax n.st.core) :
    (NamedNode.process S n o).st.core.h_max ≤ n.st.core.h_max + 1 := by
  cases o with
  | block B => exact on_block_with_h_max_le_succ .alsoCarried S.E S.hc S.cfg n.st B hbound
  | gfVote u =>
      show (Protocol.on_goldfish_vote_checked S.E n.st.core u).h_max ≤ n.st.core.h_max + 1
      rw [on_goldfish_vote_checked_h_max]
      exact Nat.le_succ _
  | attest a =>
      show (Protocol.NamedAdmission.admit_row S.hc n.st a).core.h_max ≤ n.st.core.h_max + 1
      rw [admit_row_h_max_eq]
      exact Nat.le_succ _

/-- One world event raises one node's local maximum by at most one. -/
theorem worldStep_h_max_le_succ
    (S : Setup V) (w : World V) (e : Event V) (v : V)
    (hbound : TreeHeightsLeHMax (w v).st.core) :
    ((World.step S w e) v).st.h_max ≤ (w v).st.h_max + 1 := by
  cases e with
  | tick u t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact node_tick_h_max_le_succ S v (w v) t hbound
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact Nat.le_succ _
  | deliver u o t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact node_process_h_max_le_succ S (w v) o hbound
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact Nat.le_succ _


/-- One actual event-prefix step raises one node's maximum by at most one.
`del` is no longer load-bearing (: the run is rebuilt through the
named duty chain directly, not `Proofs.Bridges.depReachable_of_admissible`) but is
kept so every existing call site's argument shape still applies. -/
theorem stateBefore_hMax_le_succ
    (S : Setup V) {rho : Run V} (del : DeliveryWellFormed S rho)
    (v : V) (i : Nat) :
    (rho.stateBefore S (i + 1) v).st.h_max ≤
      (rho.stateBefore S i v).st.h_max + 1 := by
  have htree : TreeHeightsLeHMax (rho.stateBefore S i v).st.core :=
    stateBefore_treeHeightsLeHMax S rho v i
  have hstep : rho.stateBefore S (i + 1) =
      (rho.events[i]?.toList).foldl (World.step S)
        (rho.stateBefore S i) := by
    unfold Run.stateBefore NamedRun.stateBefore
    rw [List.take_add_one, List.foldl_append]
  rcases hevent : rho.events[i]? with _ | e
  · rw [hstep, hevent]
    exact Nat.le_succ _
  · rw [hstep, hevent]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil]
    exact worldStep_h_max_le_succ S (rho.stateBefore S i) e v htree

/-! ## One-edge and intermediate-height facts -/

/-! ## The height bound -/


/-! ## Exact-height interpolation on one chain -/


/-! ## Event-index and time-index frontiers -/

/-! ### Pointwise and honest event-prefix frontiers -/

/-- An honest node's local event-prefix maximum is below the honest frontier. -/
theorem localHMax_le_honestHMaxBeforeIndex
    (S : Setup V) (rho : Run V) (n : Nat) {v : V}
    (hv : v ∈ rho.honest) :
    (rho.stateBefore S n v).st.h_max ≤ honestHMaxBeforeIndex S rho n := by
  simpa only [honestHMaxBeforeIndex] using
    (Finset.le_sup
      (f := fun w => (rho.stateBefore S n w).st.h_max) hv)

/-- The honest event-prefix frontier is monotone across arbitrary indices. -/
theorem honestHMaxBeforeIndex_mono
    (S : Setup V) (rho : Run V) {n m : Nat} (hnm : n ≤ m) :
    honestHMaxBeforeIndex S rho n ≤ honestHMaxBeforeIndex S rho m := by
  unfold honestHMaxBeforeIndex
  apply Finset.sup_le
  intro v hv
  exact (stateBefore_hMax_mono S rho v hnm).trans
    (Finset.le_sup
      (f := fun w => (rho.stateBefore S m w).st.h_max) hv)

/-- One world event raises the honest event-prefix frontier by at most one. -/
theorem honestHMaxBeforeIndex_succ_le
    (S : Setup V) {rho : Run V} (del : DeliveryWellFormed S rho) (i : Nat) :
    honestHMaxBeforeIndex S rho (i + 1) ≤
      honestHMaxBeforeIndex S rho i + 1 := by
  unfold honestHMaxBeforeIndex
  apply Finset.sup_le
  intro v hv
  exact (stateBefore_hMax_le_succ S del v i).trans
    (Nat.add_le_add_right
      (Finset.le_sup
        (f := fun w => (rho.stateBefore S i w).st.h_max) hv) 1)

/-! ### Exact strict and inclusive time indices -/

/-- Number of run events strictly before `t`. -/
def strictEventIndex (rho : Run V) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time < t))).length

/-- Number of run events at or before `t`. -/
def inclusiveEventIndex (rho : Run V) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).length

omit [DecidableEq V] [Fintype V] in
/-- Strict event cursors are monotone in their time cutoff. -/
theorem strictEventIndex_mono
    (rho : Run V) {t u : Time} (htu : t ≤ u) :
    strictEventIndex rho t ≤ strictEventIndex rho u := by
  unfold strictEventIndex
  exact (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact lt_of_lt_of_le he htu)).length_le

omit [DecidableEq V] [Fintype V] in
/-- Inclusive event cursors are monotone in their time cutoff. -/
theorem inclusiveEventIndex_mono
    (rho : Run V) {t u : Time} (htu : t ≤ u) :
    inclusiveEventIndex rho t ≤ inclusiveEventIndex rho u := by
  unfold inclusiveEventIndex
  exact (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact he.trans htu)).length_le

omit [DecidableEq V] [Fintype V] in
/-- Every event strictly before a time is also at or before that time. -/
theorem strictEventIndex_le_inclusiveEventIndex
    (rho : Run V) (t : Time) :
    strictEventIndex rho t ≤ inclusiveEventIndex rho t := by
  unfold strictEventIndex inclusiveEventIndex
  exact (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact le_of_lt he)).length_le

/-- A strict time read is exactly the corresponding event-prefix read. -/
theorem stateBeforeTime_eq_stateBefore_strictEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho) (t : Time) :
    NamedRun.stateBeforeTime S rho t = rho.stateBefore S (strictEventIndex rho t) := by
  simpa only [strictEventIndex] using
    Proofs.Optimistic.stateBeforeTime_eq_take S sch t

/-- An inclusive time read is exactly the corresponding event-prefix read. -/
theorem stateAt_eq_stateBefore_inclusiveEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho) (t : Time) :
    NamedRun.readAt S rho t = rho.stateBefore S (inclusiveEventIndex rho t) := by
  simpa only [inclusiveEventIndex] using Proofs.Optimistic.stateAt_eq_take S sch t

/-- FGStore projection of the exact strict time-index conversion. -/
theorem storeBeforeTime_eq_stateBefore_strictEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (t : Time) :
    rho.storeBeforeTime S v t =
      (rho.stateBefore S (strictEventIndex rho t) v).st := by
  unfold Run.storeBeforeTime
  rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex S sch t) v]

/-- FGStore projection of the exact inclusive time-index conversion. -/
theorem storeAt_eq_stateBefore_inclusiveEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (t : Time) :
    rho.storeAt S v t =
      (rho.stateBefore S (inclusiveEventIndex rho t) v).st := by
  unfold Run.storeAt
  rw [congrFun (stateAt_eq_stateBefore_inclusiveEventIndex S sch t) v]


omit [DecidableEq V] [Fintype V] in
/-- The exact strict index at `t` is the exact inclusive index at `t - 1`. -/
theorem strictEventIndex_eq_inclusiveEventIndex_pred
    (rho : Run V) (t : Time) :
    strictEventIndex rho t = inclusiveEventIndex rho (t - 1) := by
  have hfilter :
      (fun e : Event V => decide (e.time < t)) =
        (fun e : Event V => decide (e.time ≤ t - 1)) := by
    funext e
    exact Bool.decide_congr (Int.le_sub_one_iff).symm
  unfold strictEventIndex inclusiveEventIndex
  rw [hfilter]

/-- A strict world read at `t` is exactly the inclusive world read at
`t - 1`. -/
theorem stateBeforeTime_eq_stateAt_pred
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho) (t : Time) :
    NamedRun.stateBeforeTime S rho t = NamedRun.readAt S rho (t - 1) := by
  rw [stateBeforeTime_eq_stateBefore_strictEventIndex S sch,
    stateAt_eq_stateBefore_inclusiveEventIndex S sch,
    strictEventIndex_eq_inclusiveEventIndex_pred]

/-- The public inclusive frontier is the indexed frontier at the exact
inclusive event cursor. -/
theorem honestHMaxAt_eq_honestHMaxBeforeIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho) (t : Time) :
    honestHMaxAt S rho t =
      honestHMaxBeforeIndex S rho (inclusiveEventIndex rho t) := by
  unfold honestHMaxAt honestHMaxBeforeIndex
  refine Finset.sup_congr rfl (fun v _ => ?_)
  rw [Run.storeAt, congrFun (stateAt_eq_stateBefore_inclusiveEventIndex S sch t) v]

/-- The public inclusive honest frontier is monotone in time. -/
theorem honestHMaxAt_mono
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t u : Time} (htu : t ≤ u) :
    honestHMaxAt S rho t ≤ honestHMaxAt S rho u := by
  unfold honestHMaxAt
  apply Finset.sup_le
  intro v hv
  exact (stateAt_h_max_mono S sch v htu).trans
    (Finset.le_sup (f := fun w => (rho.storeAt S w u).h_max) hv)

/-- A strict pre-time local maximum is below its inclusive value at the same
time. -/
theorem storeBeforeTime_hMax_le_storeAt
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (t : Time) :
    (rho.storeBeforeTime S v t).h_max ≤ (rho.storeAt S v t).h_max := by
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch,
    storeAt_eq_stateBefore_inclusiveEventIndex S sch]
  exact stateBefore_hMax_mono S rho v
    (strictEventIndex_le_inclusiveEventIndex rho t)

/-- A strict pre-time local maximum is monotone in its time argument. -/
theorem storeBeforeTime_hMax_mono
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) {t u : Time} (htu : t ≤ u) :
    (rho.storeBeforeTime S v t).h_max ≤
      (rho.storeBeforeTime S v u).h_max := by
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch,
    storeBeforeTime_eq_stateBefore_strictEventIndex S sch]
  exact stateBefore_hMax_mono S rho v (strictEventIndex_mono rho htu)

/-! ### Honest witnesses and the least exact crossing -/

/-- A strict rise of the honest indexed frontier is attained by one honest
local store. -/
theorem exists_honest_localHMax_gt_of_lt_honestHMaxBeforeIndex
    (S : Setup V) (rho : Run V) (n : Nat) (H : Height)
    (hlt : H < honestHMaxBeforeIndex S rho n) :
    ∃ v ∈ rho.honest, H < (rho.stateBefore S n v).st.h_max := by
  by_contra hnone
  have hsup : honestHMaxBeforeIndex S rho n ≤ H := by
    unfold honestHMaxBeforeIndex
    apply Finset.sup_le
    intro v hv
    exact Nat.le_of_not_gt (fun hgt => hnone ⟨v, hv, hgt⟩)
  exact (Nat.not_lt_of_ge hsup) hlt

/-- A successor-valued honest frontier has an honest local store at that exact
successor height. -/
theorem exists_honest_localHMax_eq_of_honestHMaxBeforeIndex_eq_succ
    (S : Setup V) (rho : Run V) (n : Nat) (H : Height)
    (heq : honestHMaxBeforeIndex S rho n = H + 1) :
    ∃ v ∈ rho.honest, (rho.stateBefore S n v).st.h_max = H + 1 := by
  have hlt : H < honestHMaxBeforeIndex S rho n := by
    rw [heq]
    exact Nat.lt_succ_self H
  obtain ⟨v, hv, hlocal⟩ :=
    exists_honest_localHMax_gt_of_lt_honestHMaxBeforeIndex
      S rho n H hlt
  have hupper :=
    (localHMax_le_honestHMaxBeforeIndex S rho n hv).trans_eq heq
  have hlower : H + 1 ≤ (rho.stateBefore S n v).st.h_max :=
    Nat.succ_le_iff.mpr hlocal
  exact ⟨v, hv, Nat.le_antisymm hupper hlower⟩

/-- A bounded frontier crossing has a least event cursor. The cursor strictly
advances past `start`, every earlier cursor remains at most `H`, and the
one-event upper bound makes the first crossing height exactly `H + 1`. -/
theorem exists_least_honestHMaxBeforeIndex_crossing
    (S : Setup V) {rho : Run V} (del : DeliveryWellFormed S rho)
    {start stop : Nat} {H : Height}
    (hstartStop : start ≤ stop)
    (hstart : honestHMaxBeforeIndex S rho start ≤ H)
    (hstop : H < honestHMaxBeforeIndex S rho stop) :
    ∃ first : Nat,
      start < first ∧ first ≤ stop ∧
        (∀ j : Nat, start ≤ j → j < first →
          honestHMaxBeforeIndex S rho j ≤ H) ∧
        honestHMaxBeforeIndex S rho first = H + 1 := by
  classical
  have hne : start ≠ stop := by
    intro heq
    subst stop
    exact (Nat.not_lt_of_ge hstart) hstop
  have hstartLtStop : start < stop :=
    lt_of_le_of_ne hstartStop hne
  let P : Nat → Prop := fun k =>
    start < k ∧ k ≤ stop ∧ H < honestHMaxBeforeIndex S rho k
  have hex : ∃ k, P k :=
    ⟨stop, hstartLtStop, le_rfl, hstop⟩
  let first : Nat := Nat.find hex
  have hspec : P first := Nat.find_spec hex
  have hbelow : ∀ j : Nat, start ≤ j → j < first →
      honestHMaxBeforeIndex S rho j ≤ H := by
    intro j hstartJ hjFirst
    rcases eq_or_lt_of_le hstartJ with hEq | hstartJ'
    · subst j
      exact hstart
    · by_contra hnot
      have hgt : H < honestHMaxBeforeIndex S rho j :=
        Nat.lt_of_not_ge hnot
      have hjFind : j < Nat.find hex := by
        simpa only [first] using hjFirst
      have hnotP : ¬ P j := Nat.find_min hex hjFind
      apply hnotP
      exact ⟨hstartJ', (Nat.le_of_lt hjFirst).trans hspec.2.1, hgt⟩
  have hfirstPos : 0 < first :=
    lt_of_le_of_lt (Nat.zero_le start) hspec.1
  have hpredStart : start ≤ first - 1 := by omega
  have hpredLt : first - 1 < first := by omega
  have hpred : honestHMaxBeforeIndex S rho (first - 1) ≤ H :=
    hbelow (first - 1) hpredStart hpredLt
  have hstep :=
    honestHMaxBeforeIndex_succ_le S del (first - 1)
  have hpredSucc : first - 1 + 1 = first := by omega
  rw [hpredSucc] at hstep
  have hupper : honestHMaxBeforeIndex S rho first ≤ H + 1 :=
    hstep.trans (Nat.add_le_add_right hpred 1)
  have hlower : H + 1 ≤ honestHMaxBeforeIndex S rho first :=
    Nat.succ_le_iff.mpr hspec.2.2
  exact ⟨first, hspec.1, hspec.2.1, hbelow,
    Nat.le_antisymm hupper hlower⟩

/-! ## Emitted height-pair bounds -/

/-! ## 1. Honest height-pair emissions are below the moving frontier -/

/-- Each honest local frontier is below the honest maximum. -/
theorem localHMax_le_honestHMaxAt
    (S : Setup V) (rho : Run V) (t : Time) {v : V}
    (hv : v ∈ rho.honest) :
    (rho.storeAt S v t).h_max ≤ honestHMaxAt S rho t := by
  simpa only [honestHMaxAt] using
    (Finset.le_sup (f := fun w => (rho.storeAt S w t).h_max) hv)



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
