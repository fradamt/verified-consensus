module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone

@[expose] public section

/-!
# Run-level monotonicity of `h_max`

The final Section 7 store never lowers `h_max`. This neutral module contains
only that transition and run-prefix fact. It has no recovery horizon and no
termination measure.
-/

namespace DecoupledConsensusModel
namespace Proofs
open Protocol (ChainState)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- `on_goldfish_vote` does not write `Σ.h_max`. -/
theorem on_goldfish_vote_h_max (st : Protocol.Store V) (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote st vote).h_max = st.h_max := by
  unfold Protocol.on_goldfish_vote
  split_ifs <;> rfl

/-- The checked runtime guard also preserves `Σ.h_max`. -/
theorem on_goldfish_vote_checked_h_max (E : Env V) (st : Protocol.Store V)
    (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st vote).h_max = st.h_max := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_h_max st vote
  · rfl


/-- The checked carried-vote fold preserves `Σ.h_max`. -/
theorem foldl_on_goldfish_vote_checked_h_max (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).h_max = st.h_max := by
  induction l generalizing st with
  | nil => rfl
  | cons u us ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_h_max]

omit [Fintype V] in
/-- `on_sg_vote` does not write `Σ.h_max`. -/
theorem on_sg_vote_h_max (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).h_max = st.h_max := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl


omit [Fintype V] in
/-- `update_finality` never lowers `Σ.h_max`; its only write is a maximum. -/
theorem update_finality_h_max_mono (st : Protocol.Store V) (sigma : ChainState V) :
    st.h_max ≤ (Protocol.update_finality st sigma).h_max := by
  simp only [Protocol.update_finality]
  split_ifs <;> exact Nat.le_max_left _ _

namespace HealingSurface



private theorem on_block_using_h_max_mono (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    st.h_max ≤ (Protocol.on_block_using E st B buildState).h_max := by
  simp only [Protocol.on_block_using]
  split_ifs <;> try exact Nat.le_refl _
  let stored : Protocol.Store V :=
    { st with
      σ := fun C => if C = B then buildState (st.σ B.parent) else st.σ C
      T := insert B st.T
      timestamp_block := fun C =>
        if C = B then some (st.t : Stamp) else st.timestamp_block C }
  let unpacked := B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored
  change st.h_max ≤ (Protocol.update_finality unpacked (unpacked.σ B)).h_max
  have hu : unpacked.h_max = st.h_max := by
    simp only [unpacked, foldl_on_goldfish_vote_checked_h_max, stored]
  rw [← hu]
  exact update_finality_h_max_mono _ _

private theorem on_block_checked_using_h_max_mono (handle : Protocol.Store V → Protocol.Store V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (B : Block V)
    (hhandle : st.h_max ≤ (handle st).h_max) :
    st.h_max ≤ (Protocol.on_block_checked_using handle hc st B).h_max := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle
  · exact Nat.le_refl _

private theorem commitBlock_h_max (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock before after B).h_max = after.h_max := by
  show (Protocol.NamedStore.commitBlock before after B).core.h_max = after.h_max
  rw [commitBlock_core]

private theorem process_block_core_h_max_mono (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    st.h_max ≤ (Protocol.NamedStore.process_block_core E hc cfg st B).h_max := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  · rw [commitBlock_h_max]
    exact on_block_checked_using_h_max_mono _ hc st.core B.erase
      (on_block_using_h_max_mono E st.core B.erase _)
  · exact Nat.le_refl _

private theorem admit_row_h_max (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st a).h_max = st.h_max := by
  show (Protocol.NamedAdmission.admit_row hc st a).core.h_max = st.h_max
  rw [admit_row_core]
  exact on_sg_vote_h_max hc st.core a.erase

private theorem admit_rows_h_max (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      (Protocol.NamedAdmission.admit_rows hc st rows).h_max = st.h_max
  | [], _ => rfl
  | a :: rows, st =>
      (admit_rows_h_max hc rows (Protocol.NamedAdmission.admit_row hc st a)).trans
        (admit_row_h_max hc st a)

private theorem admit_carried_h_max (admission : Protocol.CarriedAdmission)
    (hc : Protocol.HealConfig) (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission hc before after B).h_max = after.h_max := by
  cases admission with
  | alsoCarried =>
      dsimp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_h_max hc B.attestations after
      · rfl

private theorem on_block_with_h_max_mono (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    st.h_max ≤ (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).h_max := by
  dsimp only [Protocol.NamedAdmission.on_block_with]
  rw [admit_carried_h_max]
  exact process_block_core_h_max_mono E hc cfg st B

private theorem propose_block_with_h_max_mono (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    st.h_max ≤ (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.h_max := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact Nat.le_refl _
  · exact on_block_with_h_max_mono .alsoCarried E hc cfg st _

private theorem goldfish_vote_with_h_max_mono (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    st.h_max ≤ (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.h_max := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact le_of_eq (on_goldfish_vote_checked_h_max E st.core _).symm
  · exact Nat.le_refl _

private theorem update_confirmation_with_h_max_mono (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    st.h_max ≤ (Protocol.NamedDuties.update_confirmation_with gc E hc st s).h_max :=
  Nat.le_refl _

private theorem attest_with_h_max_mono (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    st.h_max ≤ (Protocol.NamedDuties.attest_with gc E hc nd st record).1.h_max :=
  le_of_eq (admit_row_h_max hc st _).symm

/-- The named tick, run through the generalized clock-staging combinator: fix
`P st':= st.h_max ≤ st'.h_max` at the tick's own starting store and discharge
each of its four duties plus the clock stamp. -/
private theorem tick_h_max_mono (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    st.h_max ≤ (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.h_max := by
  refine named_tick_preserves (fun st' => st.h_max ≤ st'.h_max) gc E hc cfg nd
    ?_ ?_ ?_ ?_ st record t (Nat.le_refl _)
  · intro st' h; exact h.trans (propose_block_with_h_max_mono gc E hc cfg nd st')
  · intro st' h; exact h.trans (goldfish_vote_with_h_max_mono gc E hc nd st')
  · intro st' s h; exact h.trans (update_confirmation_with_h_max_mono gc E hc st' s)
  · intro st' record' h; exact h.trans (attest_with_h_max_mono gc E hc nd st' record')

private theorem node_tick_h_max_mono (S : Setup V) (v : V) (n : NodeState V) (t : Time) :
    n.st.h_max ≤ (NamedNode.tick S v n t).1.st.h_max :=
  tick_h_max_mono (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
    S.E S.hc S.cfg (S.node v) n.st n.record t

private theorem node_process_h_max_mono (S : Setup V) (n : NodeState V) (o : Object V) :
    n.st.h_max ≤ (NamedNode.process S n o).st.h_max := by
  cases o with
  | block B => exact on_block_with_h_max_mono .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u => exact le_of_eq (on_goldfish_vote_checked_h_max S.E n.st.core u).symm
  | attest a => exact le_of_eq (admit_row_h_max S.hc n.st a).symm

/-- One Section 7 world event never lowers one node's `h_max`. -/
private theorem worldStep_h_max_mono (S : Setup V) (w : World V)
    (e : Event V) (v : V) :
    (w v).st.h_max ≤ ((World.step S w e) v).st.h_max := by
  cases e with
  | tick u t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact node_tick_h_max_mono S v (w v) t
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact le_rfl
  | deliver u o t =>
      by_cases hu : u = v
      · subst u
        simp only [NamedWorld.step, Function.update_self]
        exact node_process_h_max_mono S (w v) o
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        exact le_rfl

/-- Folding a later event suffix never lowers one node's `h_max`. -/
private theorem foldlWorld_h_max_mono (S : Setup V) (v : V)
    (events : List (Event V)) (w : World V) :
    (w v).st.h_max ≤
      ((events.foldl (World.step S) w) v).st.h_max := by
  induction events generalizing w with
  | nil => exact le_rfl
  | cons e events ih =>
      exact (worldStep_h_max_mono S w e v).trans
        (ih (w := World.step S w e))

/-- A node's `h_max` is monotone between two inclusive store reads. -/
theorem stateAt_h_max_mono (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V)
    {t u : Time} (htu : t ≤ u) :
    (rho.storeAt S v t).h_max ≤
      (rho.storeAt S v u).h_max := by
  obtain ⟨events, hevents⟩ := Protocol.stateAt_eq_foldl S sch htu
  simp only [Run.storeAt, hevents]
  exact foldlWorld_h_max_mono S v events (NamedRun.readAt S rho t)

/-! ## Actual event-prefix fold -/

/-- One world event never lowers one node's `h_max`, in event-index form. -/
theorem stateBefore_hMax_mono_succ
    (S : Setup V) (rho : Run V) (v : V) (i : Nat) :
    (rho.stateBefore S i v).st.h_max ≤
      (rho.stateBefore S (i + 1) v).st.h_max := by
  have hstep : rho.stateBefore S (i + 1) =
      (rho.events[i]?.toList).foldl (World.step S)
        (rho.stateBefore S i) := by
    unfold Run.stateBefore NamedRun.stateBefore
    rw [List.take_add_one, List.foldl_append]
  rcases hevent : rho.events[i]? with _ | e
  · rw [hstep, hevent]
    exact le_rfl
  · rw [hstep, hevent]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil]
    exact worldStep_h_max_mono S _ e v

/-- A node's `h_max` is monotone across arbitrary event-prefix indices. -/
theorem stateBefore_hMax_mono
    (S : Setup V) (rho : Run V) (v : V) {n m : Nat} (hnm : n ≤ m) :
    (rho.stateBefore S n v).st.h_max ≤
      (rho.stateBefore S m v).st.h_max := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
      exact ih.trans (by
        simpa only [Nat.succ_eq_add_one] using
          stateBefore_hMax_mono_succ S rho v m)

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
