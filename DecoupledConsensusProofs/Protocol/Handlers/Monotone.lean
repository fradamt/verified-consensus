module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Execution
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationPolicy

@[expose] public section

/-!
# User-record persistence from compatibility

The user record retains an ancestor candidate and replaces other candidates.
It can recover from a conflicting history. Monotonicity therefore follows
from compatibility in a safety regime, rather than from the update alone.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## `Σ.latest_confirmed` is written by `update_confirmation` alone

The same seven-lemma shape as row C1's clock pack (`Proofs/Execution.lean`):
each handler either returns its input or returns a record update that does not
name the field. -/

omit [Fintype V] in
/-- §5.2 `update_finality` does not write `Σ.latest_confirmed`
(PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_latest (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §7.2 `on_goldfish_vote` does not write `Σ.latest_confirmed`
(PROTOCOL.md#the-complete-protocol). -/
theorem on_goldfish_vote_latest (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- The checked runtime handler also preserves `Σ.latest_confirmed`. -/
theorem on_goldfish_vote_checked_latest (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_latest st u
  · rfl


/-- The checked carried-vote fold preserves `Σ.latest_confirmed`. -/
theorem foldl_on_goldfish_vote_checked_latest (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).latest_confirmed =
      st.latest_confirmed := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_latest]

omit [Fintype V] in
/-- §7.2 `on_sg_vote` does not write `Σ.latest_confirmed`
(PROTOCOL.md#the-complete-protocol). -/
theorem on_sg_vote_latest (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl


omit [Fintype V] in

/-- **Addendum 34 26's three-way floor keeps a recorded prefix.** The
write is the confirmation arm when it extends the new stable record, the prior
record while that still does, and the stable record only when the prior record has
left its chain. Each arm keeps a prefix the prior record held: the first by the
arm's own rule, the second outright, and the third because the branch condition
`¬ (stable ⪯ old)` rules out `stable ≺ B ⪯ old`, so compatibility leaves
`B ⪯ stable`. The record is never retracted below a value it held, which is what
this file's chain rests on. -/
theorem preceq_floor {B old arm stable : Block V}
    (hold : Block.Preceq B old)
    (harm : Block.compatible B arm = true → Block.Preceq B arm)
    (hcompat : Block.compatible B (Protocol.floor_on_stable stable arm old) = true) :
    Block.Preceq B (Protocol.floor_on_stable stable arm old) := by
  unfold Protocol.floor_on_stable at hcompat ⊢
  split_ifs at hcompat ⊢ with h1 h2
  · exact harm hcompat
  · exact hold
  · rcases (show Block.Preceq B stable ∨ Block.Preceq stable B by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompat) with hBs | hsB
    · exact hBs
    · exact absurd (Block.preceq_trans hsB hold) h2

theorem on_block_using_latest (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [update_finality_latest, foldl_on_goldfish_vote_checked_latest]

theorem on_block_checked_using_latest (handle : Protocol.Store V → Protocol.Store V)
    (hc : HealConfig) (st : Protocol.Store V) (B : Block V)
    (hhandle : (handle st).latest_confirmed = st.latest_confirmed) :
    (Protocol.on_block_checked_using handle hc st B).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle
  · rfl

private theorem commitBlock_latest (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock before after B).latest_confirmed = after.latest_confirmed := by
  simp only [Protocol.NamedStore.commitBlock]
  split_ifs <;> rfl

theorem process_block_core_latest (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  all_goals first
    | rfl
    | (rw [commitBlock_latest]
       exact on_block_checked_using_latest _ hc st.core B.erase
         (on_block_using_latest E st.core B.erase _))

theorem admit_row_latest (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> exact on_sg_vote_latest hc st.core row.erase

private theorem foldl_admit_row_latest (hc : HealConfig)
    (l : List (NamedAttestation V)) (st : Protocol.NamedStore V) :
    (l.foldl (Protocol.NamedAdmission.admit_row hc) st).latest_confirmed =
      st.latest_confirmed := by
  induction l generalizing st with
  | nil => rfl
  | cons row l ih => rw [List.foldl_cons, ih, admit_row_latest]

theorem admit_rows_latest (hc : HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).latest_confirmed = st.latest_confirmed :=
  foldl_admit_row_latest hc rows st

theorem admit_carried_latest (admission : Protocol.CarriedAdmission) (hc : HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission hc before after B).latest_confirmed =
      after.latest_confirmed := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_latest hc after B.attestations
      · rfl

theorem on_block_with_latest (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedAdmission.on_block_with]
  rw [admit_carried_latest]
  exact process_block_core_latest E hc cfg st B

theorem propose_block_with_latest (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedDuties.propose_block_with]
  cases Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => rfl
  | some B => exact on_block_with_latest .alsoCarried E hc cfg st B

theorem goldfish_vote_with_latest (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    (Protocol.goldfish_vote_with contract E hc nd st).1.latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_latest E st _
  · rfl

theorem named_goldfish_vote_with_latest (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedDuties.goldfish_vote_with]
  exact goldfish_vote_with_latest contract E hc nd st.core

theorem attest_with_latest (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).1.latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedDuties.attest_with]
  exact admit_row_latest hc st _

/-! Generalizes `update_confirmation_latest_preserves` over an arbitrary grade
contract's optional confirmation-SG selector. -/
theorem update_confirmation_with_latest_preserves (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (st : Protocol.Store V) (s : Slot) {B : Block V}
    (hold : Block.Preceq B st.latest_confirmed)
    (hcompat : Block.compatible B
      (Protocol.update_confirmation_with contract E hc st s).latest_confirmed = true) :
    Block.Preceq B (Protocol.update_confirmation_with contract E hc st s).latest_confirmed := by
  simp only [Protocol.update_confirmation_with] at hcompat ⊢
  
  -- so the arm-by-arm argument moves inside `preceq_floor`'s middle premise.
  refine preceq_floor hold ?_ hcompat
  intro harm
  cases hmode : contract.confirmationSG with
  | optional select =>
      simp only [hmode] at harm ⊢
      split_ifs at harm ⊢ with helig
      · exact Proofs.ConfirmationPolicy.prefix_preceq_advance_of_result_compatible hold harm
      · cases hsel : select E hc st.toHealing s with
        | some candidate =>
            simp only [hsel] at harm ⊢
            exact Proofs.ConfirmationPolicy.prefix_preceq_advance_of_result_compatible hold harm
        | none =>
            simp only [hsel] at harm ⊢
            exact hold

theorem named_update_confirmation_with_latest_preserves (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (st : Protocol.NamedStore V) (s : Slot) {B : Block V}
    (hold : Block.Preceq B st.latest_confirmed)
    (hcompat : Block.compatible B
      (Protocol.NamedDuties.update_confirmation_with contract E hc st s).latest_confirmed =
        true) :
    Block.Preceq B
      (Protocol.NamedDuties.update_confirmation_with contract E hc st s).latest_confirmed := by
  simp only [Protocol.NamedDuties.update_confirmation_with] at hcompat ⊢
  exact update_confirmation_with_latest_preserves contract E hc st.core s hold hcompat

/-- Local restatement of `Proofs.NamedTick.tick_computed_duties` (not imported:
that file's cone loops back to this one through `Protocol.Sync`/`Main`).
Byte-identical to the original, against the same Model-level primitives, so
the proof script is unchanged. -/
private theorem named_tick_computed_duties (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    Protocol.NamedTick.tick gc E hc cfg nd st record t =
      let s := E.slotOf t
      let st0 := Protocol.NamedStore.setClock E st t
      let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
      let proposalDue := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
      let st1 := if proposalDue then proposed.1 else st0
      let emitted1 := if proposalDue then
        match proposed.2 with
        | none => []
        | some B => [NamedObject.block B]
      else []
      let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
      let voteDue := 0 < s ∧ t = Protocol.vote_time E s
      let st2 := if voteDue then voted.1 else st1
      let emitted2 := if voteDue then voted.2.toList.map NamedObject.gfVote else []
      let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
        Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
      if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        let attested := Protocol.NamedDuties.attest_with gc E hc nd st3 record
        (attested.1, attested.2.1, emitted1 ++ emitted2 ++ [NamedObject.attest attested.2.2])
      else (st3, record, emitted1 ++ emitted2) := by
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps,
    Protocol.NamedStore.setClock]
  unfold Protocol.TickScheduler.runWith.match_1 named_tick_computed_duties.match_1
  rfl

/-- The closed named tick composes its concrete duty calls in the same order
as `NamedFinalityMonotone.tick_F`, threaded for compatibility instead of plain
growth: every duty but confirmation preserves the record outright, and
confirmation's own argument is the generalized `update_confirmation_with`
result above. -/
theorem tick_latest_preserves (gc : Protocol.GradeContract V) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) {B : Block V}
    (hold : Block.Preceq B st.latest_confirmed)
    (hcompat : Block.compatible B
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.latest_confirmed = true) :
    Block.Preceq B (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.latest_confirmed := by
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time E s then
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
    Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  have hout : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1 =
      (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc E hc nd st3 record).1 else st3) := by
    rw [named_tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  have h1 : st1.latest_confirmed = st.latest_confirmed := by
    dsimp only [st1, st0]
    split_ifs
    · rw [propose_block_with_latest]; rfl
    · rfl
  have h2 : st2.latest_confirmed = st1.latest_confirmed := by
    dsimp only [st2]
    split_ifs
    · exact named_goldfish_vote_with_latest gc E hc nd st1
    · rfl
  rw [hout] at hcompat ⊢
  have hcompat3 : Block.compatible B st3.latest_confirmed = true := by
    split_ifs at hcompat with hattest
    · rwa [attest_with_latest] at hcompat
    · exact hcompat
  have hold3 : Block.Preceq B st3.latest_confirmed := by
    dsimp only [st3]
    split_ifs with hif
    · refine named_update_confirmation_with_latest_preserves gc E hc st2 (s - 1)
        (by rw [h2, h1]; exact hold) ?_
      dsimp only [st3] at hcompat3
      rwa [if_pos hif] at hcompat3
    · rw [h2, h1]; exact hold
  split_ifs with hattest
  · rw [attest_with_latest]; exact hold3
  · exact hold3

/-- The full named tick preserves the same prefix; the phase-preparation
cache and the frame-based grade contract play no role beyond fixing `gc`. -/
theorem node_tick_latest_preserves (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {B : Block V} (hold : Block.Preceq B n.st.latest_confirmed)
    (hcompat : Block.compatible B (NamedNode.tick S v n t).1.st.latest_confirmed = true) :
    Block.Preceq B (NamedNode.tick S v n t).1.st.latest_confirmed :=
  tick_latest_preserves (NamedProfile.gradeContract
    (onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
    S.E S.hc S.cfg (S.node v) n.st n.record t hold hcompat

/-- Object processing leaves the user record unchanged. -/
theorem node_process_latest (S : Setup V) (n : NodeState V) (o : Object V) :
    (NamedNode.process S n o).st.latest_confirmed = n.st.latest_confirmed := by
  cases o with
  | block B => exact on_block_with_latest .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u => exact on_goldfish_vote_checked_latest S.E n.st.core u
  | attest a => exact admit_row_latest S.hc n.st a

/-- No other step can remove a recorded prefix. -/
theorem step_latest_preserves (S : Setup V) (w : World V) (e : Event V) (v : V)
    {B : Block V} (hold : Block.Preceq B (w v).st.latest_confirmed)
    (hcompat : Block.compatible B ((NamedWorld.step S w e) v).st.latest_confirmed = true) :
    Block.Preceq B ((NamedWorld.step S w e) v).st.latest_confirmed := by
  cases e with
  | tick u t =>
      by_cases hu : u = v
      · subst hu
        simp only [NamedWorld.step, Function.update_self] at hcompat ⊢
        exact node_tick_latest_preserves S _ _ _ hold hcompat
      · simpa only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)] using hold
  | deliver u o t =>
      by_cases hu : u = v
      · subst hu
        simpa only [NamedWorld.step, Function.update_self, node_process_latest] using hold
      · simpa only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)] using hold

/-! ## The schedule: `[0, t]` is a prefix of `[0, t']` -/

/-- Sortedness by `Event.key` is sortedness by time: the key is lexicographic on
`(time, phase)` (`Props/Execution/Event.lean`). -/
theorem pairwise_time_le (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ) :
    ρ.events.Pairwise (fun e f => e.time ≤ f.time) := by
  refine sch.sorted.imp ?_
  intro e f h
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

omit [DecidableEq V] [Fintype V] in

/-- In a time-sorted list the events of `[0, t]` are a prefix of the events of
`[0, t']` for `t ≤ t'`. Once an event is past `t`, so is every later one, so the
earlier filter open items where the later one continues. -/
theorem filter_time_prefix {t t' : Time} (h : t ≤ t') :
    ∀ (l : List (Event V)), l.Pairwise (fun e f => e.time ≤ f.time) →
      l.filter (fun e => decide (e.time ≤ t)) <+:
        l.filter (fun e => decide (e.time ≤ t'))
  | [], _ => by simp
  | a :: l, hs => by
      rw [List.pairwise_cons] at hs
      by_cases ha : a.time ≤ t
      · have ha' : a.time ≤ t' := le_trans ha h
        rw [List.filter_cons_of_pos (by simpa using ha),
          List.filter_cons_of_pos (by simpa using ha')]
        obtain ⟨m, hm⟩ := filter_time_prefix h l hs.2
        exact ⟨m, by rw [List.cons_append, hm]⟩
      · have hnil : l.filter (fun e => decide (e.time ≤ t)) = [] := by
          refine List.filter_eq_nil_iff.mpr ?_
          intro f hf hcon
          exact ha (le_trans (hs.1 f hf) (by simpa using hcon))
        rw [List.filter_cons_of_neg (by simpa using ha), hnil]
        exact List.nil_prefix

/-- `Run.stateAt` at `t'` is `Run.stateAt` at `t` continued: the schedule is
sorted, so the later world is the earlier one folded over the events of
`(t, t']`. -/
theorem stateAt_eq_foldl (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {t t' : Time} (h : t ≤ t') :
    ∃ m : List (Event V),
      NamedRun.readAt S ρ t' = m.foldl (NamedWorld.step S) (NamedRun.readAt S ρ t) := by
  obtain ⟨m, hm⟩ := filter_time_prefix h ρ.events (pairwise_time_le S sch)
  refine ⟨m, ?_⟩
  simp only [NamedRun.readAt]
  rw [← hm, List.foldl_append]


private theorem time_filter_eq_take (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (t : Time) :
    rho.events.filter (fun e => decide (e.time ≤ t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  apply List.prefix_iff_eq_take.mp
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise (fun e f hk hf => by
    simp only [decide_eq_true_eq] at hf ⊢
    exact (Proofs.Bridges.time_le_of_key_le hk).trans hf) _ sch.sorted]
  exact List.takeWhile_prefix _

private theorem stateAt_time_prefix (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (t : Time) :
    NamedRun.readAt S rho t =
      rho.stateBefore S (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  unfold NamedRun.readAt Run.stateBefore NamedRun.stateBefore
  rw [← time_filter_eq_take S sch t]

private theorem time_le_of_index_lt_filter (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {t : Time} {i : Nat} {e : Event V}
    (hi : i < (rho.events.filter (fun e => decide (e.time ≤ t))).length)
    (he : rho.events[i]? = some e) : e.time ≤ t := by
  have hmem : e ∈ rho.events.filter (fun e => decide (e.time ≤ t)) := by
    rw [time_filter_eq_take S sch t]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi]; exact he)
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

private theorem index_lt_filter_of_time_le (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {t : Time} {i : Nat} {e : Event V}
    (he : rho.events[i]? = some e) (ht : e.time ≤ t) :
    i < (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  have hmem : e ∈ rho.events.filter (fun e => decide (e.time ≤ t)) :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? he, by simpa only [decide_eq_true_eq] using ht⟩
  rw [time_filter_eq_take S sch t] at hmem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  have hjlt : j < (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    rw [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hjlt] at hj
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp (by rw [hie, hje])
  simpa only [hij] using hjlt

/-- An interval without this node's ticks preserves its user record. -/
theorem latest_at_prefix_eq_of_no_tick (S : Setup V) (rho : Run V) (v : V)
    {m : Nat} :
    ∀ n : Nat, m ≤ n →
      (∀ j e, m ≤ j → j < n → rho.events[j]? = some e →
        ∀ t : Time, e ≠ Event.tick v t) →
      (rho.stateBefore S n v).st.latest_confirmed =
        (rho.stateBefore S m v).st.latest_confirmed := by
  intro n
  induction n with
  | zero => intro hm _; rw [Nat.le_zero.mp hm]
  | succ n ih =>
      intro hm h
      by_cases hmn : m ≤ n
      · rw [← ih hmn (fun j e h1 h2 h3 => h j e h1 (Nat.lt_succ_of_lt h2) h3)]
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : rho.events[n]? with
        | none => simp
        | some e =>
            have hne := h n e hmn (Nat.lt_succ_self n) hn
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e with
            | tick u t =>
                by_cases huv : u = v
                · exact False.elim (hne t (by rw [huv]))
                · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
            | deliver u o t =>
                by_cases huv : u = v
                · subst huv
                  simp only [NamedWorld.step, Function.update_self, node_process_latest]
                · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
      · have heq : m = n + 1 := by omega
        subst m
        rfl

/-- After a node's tick, its record already equals the inclusive time read.
Sortedness and unique events exclude another same-node tick at that time. -/
theorem latest_after_tick_eq_storeAt (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (Event.tick v t)) :
    (rho.stateBefore S (i + 1) v).st.latest_confirmed =
      (rho.storeAt S v t).latest_confirmed := by
  have hi := index_lt_filter_of_time_le S sch he (show (Event.tick v t).time ≤ t by rfl)
  rw [Run.storeAt, stateAt_time_prefix S sch t]
  symm
  apply latest_at_prefix_eq_of_no_tick S rho v _ (Nat.succ_le_of_lt hi)
  intro j e hij hj he' t' heq
  subst e
  have hle : t' ≤ t := time_le_of_index_lt_filter S sch hj he'
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he'
  have hkey := (List.pairwise_iff_getElem.mp sch.sorted) i j hil hjl (by omega)
  rw [hie, hje] at hkey
  have hge : t ≤ t' := Proofs.Bridges.time_le_of_key_le hkey
  have htt : t' = t := le_antisymm hle hge
  subst t'
  have hij' : i = j :=
    (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp (by rw [hie, hje])
  omega

/-- A recorded prefix persists through a finite event interval when each
later tick's result is compatible with it. -/
theorem latest_prefix_preserved (S : Setup V) (rho : Run V) (v : V)
    {B : Block V} {m : Nat}
    (hold : Block.Preceq B (rho.stateBefore S m v).st.latest_confirmed) :
    ∀ n : Nat, m ≤ n →
      (∀ i t, m ≤ i → i < n → rho.events[i]? = some (Event.tick v t) →
        Block.compatible B (rho.stateBefore S (i + 1) v).st.latest_confirmed = true) →
      Block.Preceq B (rho.stateBefore S n v).st.latest_confirmed := by
  intro n
  induction n with
  | zero => intro hm _; simpa only [Nat.le_zero.mp hm] using hold
  | succ n ih =>
      intro hm hcompat
      by_cases hmn : m ≤ n
      · have hprev := ih hmn (fun i t hmi hin he =>
          hcompat i t hmi (Nat.lt_succ_of_lt hin) he)
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : rho.events[n]? with
        | none => simpa using hprev
        | some e =>
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e with
            | tick u t =>
                by_cases huv : u = v
                · subst huv
                  apply step_latest_preserves S _ (.tick u t) u hprev
                  simpa only [Run.stateBefore, NamedRun.stateBefore, List.take_add_one, hn,
                    List.foldl_append, Option.toList, List.foldl_cons, List.foldl_nil] using
                    hcompat n t hmn (Nat.lt_succ_self n) hn
                · simpa only [NamedWorld.step, Function.update_of_ne (Ne.symm huv)] using hprev
            | deliver u o t =>
                by_cases huv : u = v
                · subst huv
                  simpa only [NamedWorld.step, Function.update_self, node_process_latest]
                    using hprev
                · simpa only [NamedWorld.step, Function.update_of_ne (Ne.symm huv)] using hprev
      · have heq : m = n + 1 := by omega
        subst m
        exact hold

/-- Agreement throughout a time interval gives monotonicity of its user
records. The update cannot replace a record by its own strict ancestor. -/
theorem latest_confirmed_mono_of_agreement (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V) {t t' : Time} (htt' : t ≤ t')
    {t0 : Time} (hcompat : ConfirmationCompatibleFrom S rho t0)
    (hv : v ∈ rho.honest) (ht : t0 ≤ t) :
    Block.Preceq (rho.storeAt S v t).latest_confirmed
      (rho.storeAt S v t').latest_confirmed := by
  have hmle := (filter_time_prefix htt' rho.events (pairwise_time_le S sch)).length_le
  simp only [Run.storeAt]
  rw [stateAt_time_prefix S sch t, stateAt_time_prefix S sch t']
  apply latest_prefix_preserved S rho v (Block.preceq_self _) _ hmle
  intro i time hmi _hin he
  have htimeHor : time ≤ rho.horizon :=
    (sch.in_horizon _ (List.mem_of_getElem? he)).2
  have hafter : t < time := by
    by_contra hnot
    have hlt := index_lt_filter_of_time_le S sch he
      (show (Event.tick v time).time ≤ t from le_of_not_gt hnot)
    exact (Nat.not_lt_of_ge hmi) hlt
  rw [latest_after_tick_eq_storeAt S sch he]
  have h := hcompat v hv v hv t time ht (ht.trans hafter.le)
    (hafter.le.trans htimeHor) htimeHor
  simpa only [Run.storeAt, stateAt_time_prefix S sch t] using h

/-- Interval form retained for callers with an explicit finite read horizon. -/
theorem latest_confirmed_mono (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V) {t t' : Time} (htt' : t ≤ t')
    {t0 : Time} (hcompat : ConfirmationCompatibleFrom S rho t0)
    (hv : v ∈ rho.honest) (ht : t0 ≤ t) (_hhor : t' ≤ rho.horizon) :
    Block.Preceq (rho.storeAt S v t).latest_confirmed
      (rho.storeAt S v t').latest_confirmed :=
  latest_confirmed_mono_of_agreement S sch v htt' hcompat hv ht

/-- The public monotonicity conclusion follows from interval agreement. -/
theorem confirmationMonotoneFrom (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (t0 : Time)
    (hcompat : ConfirmationCompatibleFrom S rho t0) :
    ConfirmationMonotoneFrom S rho t0 :=
  fun v hv _ _ ht htt' hhor => latest_confirmed_mono S sch v htt' hcompat hv ht hhor

end Protocol
end DecoupledConsensusModel

end
