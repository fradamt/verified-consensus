module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Objects.PerHeight
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordCore
public import DecoupledConsensusProofs.Protocol.Schedule.Alignment
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Engine
public import DecoupledConsensusModel.Protocol.Duties.Proposals
public import DecoupledConsensusModel.Protocol.ValidatorClient
public import DecoupledConsensusModel.Protocol.Tick

@[expose] public section

/-!
# The run-to-record bridge, and L4's honest core end to end
(`the design` §9 L4; `the design notes` §5;
PROTOCOL.md#the-complete-protocol)

`RecordCore.lean` proved everything clause (e) needs **about one record**. This
file supplies the missing sentence — *a validator's record evolves only by its
own `create_attestation` calls, from `Record.initial`* — and closes
`Internal.HealingSurface.HonestNoDoubleTarget`, hence L4, hence
`Internal.AlignedRound`'s deleted clause (e).

## Named-run proof 

The engine's own record is `Protocol.NamedRecord` now, read through
`.legacy` for every bare `Record` fact (`LockCompatible`, `target`, `lock`);
the emitted row is a `NamedAttestation`, read through `.erase` wherever the
bare `CombinedAttestation`/`HeightPair` facts apply. The single writer is
`Protocol.NamedActions.round_action_with contract E hc nd st record`, which
`NamedRecord.create` routes through the unchanged prior `create_attestation`
(`Protocol.NamedRecord`'s doc comment: "the prior client makes all pair
decisions and updates its record once"). `round_action_shape` below is the
named-run replacement for the earlier `protocol_attest_shape` and exposes
exactly that fact, at any grade contract, without resolving which contract the
engine happens to run.

The tick itself is `Execution.NamedNode.tick S v n t`, a named `NodeState`
in, a named `NodeState × List Object` out — the record and cache travel with
the store instead of being separate parameters. `on_tick_emit_attest_shape`
decomposes it exactly as the retired `Proofs.Optimistic.on_tick_emit_attest_shape`
did, via a local restatement of `Proofs.NamedTick.tick_computed_duties` (that
file's dependency `Proofs.NamedActions.lean` has no `.olean` built on this run's
frontier, so a single-file compile cannot import it; `Optimistic/Alignment.lean`
and three other files in this cone keep the identical private copy for the
same reason).

## Why it is one induction and not a redesign

Three facts about the execution layer do all the work, and none of them is new:

* `NodeState.process` never touches the record — "only `attest` writes it, and
  `attest` runs inside the tick" (`Execution/Node.lean`). Deliveries are inert.
* `World.step` reaches `v`'s entry only at `v`'s own events. Everyone else's
  ticks are inert too.
* `on_tick_emit`'s attest branch returns the named round action's own output —
  so the record after any tick is either unchanged or one `round_action_with`
  step on.

So the two invariants `RecordCore` needs travel by the induction
`Proofs.HealingLemmas.Schedule.stateBefore_sg_pool_subset` already runs for the SG
bucket: `LockCompatible` is preserved and `Λ.legacy.target` only grows.

## The shape of the conclusion

`targetsAt` reads both pairs (through `.erase`), so the argument covers both
with two monotone record fields:

* a **height pair** target is recorded *after* release
  (`create_attestation_saves`), which needs `LockCompatible` at the emitting record;
* a **finality pair** target is written to `Λ.legacy.lock` after release
  (`emits_finality_locked`). Rule B permits the target entry to remain empty.

The target and lock entries keep their first nonempty values. A later target
must agree with either an existing target or an existing lock. Therefore, two
emissions at one height name one target. The same-tick case is not an ordering
argument: the emission list carries at most one attestation
(`on_tick_emit_attest_shape`), and one attestation never conflicts with itself
(`height_pair_no_self_E1`).

For L8, the exact bridge fact is the finality lock write. Rule B removes the prior
claim that every finality voter already had a height-target row. The named
`FinalityTargetHeightSource` residual states where availability proofs still
need that earlier row.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record create_attestation finality_pair record_attestation)
open Protocol (HealConfig)
open Internal
open Execution
open Proofs.Records (LockCompatible)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. Record-layer glue: `Protocol.NamedActions.round_action_with` erasure
. Byte-identical in spirit to
`HMaxCoreRun.lean`'s `encodeHeight_erase_current`/`round_action_current_erase`,
kept generic in the grade contract since nothing here depends on which one the
engine runs. -/

omit [DecidableEq V] [Fintype V] in
private theorem erase_finality_pair (a : NamedAttestation V) :
    a.erase.finality_pair = a.finality_pair := rfl

/-- Erasure agreement for one named signing call, at any contract (
): the general-purpose bridge `Proofs.NamedRecord.create_erases` sits
in a proof file with no `.olean` built on this run's frontier (its dependency
`SlashableBoundRun.lean` is itself unported), so a single-file compile cannot
import it; this is the same proof, reached through the model-layer
definitions alone. -/
private theorem encodeHeight_erase_of (record : Record)
    (fields : Option (Height × BlockId × Bool)) (fp : Option FinalityPair) :
    (Protocol.NamedRecord.encodeHeight fields
      (Protocol.height_pair record fields fp)).erase =
      Protocol.height_pair record fields fp := by
  rcases Proofs.Engine.height_pair_cases (Λ := record) fields fp with he | ⟨h, entry, nu, hf, hp⟩
  · simp [Protocol.NamedRecord.encodeHeight, he, NamedHeightPair.erase]
  · rcases hp with ht | ht <;> rw [ht, hf] <;> rfl

/-- **: the named round action's output is exactly the prior bare
`create_attestation`'s, at the emitter's own record.** The named-run
replacement for the earlier `protocol_attest_shape`: both components, so the
record and the attestation are read off one application, at any contract. -/
private theorem round_action_shape (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V)
    (record : Protocol.NamedRecord) :
    ∃ (r : Round) (c : Option BlockId) (f : Option (Height × BlockId × Bool))
      (h_j : Height) (J : BlockId) (h_F : Height),
      (Protocol.NamedActions.round_action_with contract E hc nd st record).1.legacy =
        (create_attestation record.legacy nd.val_index r c f h_j J h_F).1 ∧
      (Protocol.NamedActions.round_action_with contract E hc nd st record).2.erase =
        (create_attestation record.legacy nd.val_index r c f h_j J h_F).2 := by
  refine ⟨_, _, _, _, _, _, rfl, ?_⟩
  simp only [Protocol.NamedActions.round_action_with, Protocol.with_attestation_input,
    Protocol.NamedRecord.create, Protocol.NamedRecord.legacyCreate,
    Protocol.NamedActions.creatorInput, Protocol.NamedRecord.encodeRow,
    NamedAttestation.erase, create_attestation, encodeHeight_erase_of]

/-! ## 1. One tick (PROTOCOL.md#the-complete-protocol) -/

private theorem on_tick_emit_record_eq (S : Setup V) (v : V) (n : NodeState V) (t : Time) :
    (on_tick_emit S v n t).1.record =
      (Protocol.NamedTick.tick
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).2.1 := rfl

private theorem on_tick_emit_snd_eq (S : Setup V) (v : V) (n : NodeState V) (t : Time) :
    (on_tick_emit S v n t).2 =
      (Protocol.NamedTick.tick
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).2.2 := rfl

/-- Local restatement of `Proofs.NamedTick.tick_computed_duties` (that file's
Proofs-layer cone is unbuilt in this worktree; `Optimistic/Alignment.lean`,
`HealingSurface/ActionRun.lean`, `Availability/Pool.lean` and
`Availability/Monotone.lean` keep the identical private copy for the same
reason). Byte-identical to the Model-level scheduler, so the proof script is
unchanged. -/
private theorem named_tick_computed_duties (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
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
        | some B => [Object.block B]
      else []
      let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
      let voteDue := 0 < s ∧ t = Protocol.vote_time E s
      let st2 := if voteDue then voted.1 else st1
      let emitted2 := if voteDue then voted.2.toList.map Object.gfVote else []
      let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
        Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
      if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        let attested := Protocol.NamedDuties.attest_with gc E hc nd st3 record
        (attested.1, attested.2.1, emitted1 ++ emitted2 ++ [Object.attest attested.2.2])
      else (st3, record, emitted1 ++ emitted2) := by
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps,
    Protocol.NamedStore.setClock]
  unfold Protocol.TickScheduler.runWith.match_1 named_tick_computed_duties.match_1
  rfl

/-- §7.2 one tick's attest branch, decomposed: a list `pre` with no attest
object, and either nothing more (record unchanged) or exactly the named round
action's own row appended (record advances by that one action). The named-run
replacement for the retired `Proofs.Optimistic.on_tick_emit_attest_shape`. -/
private theorem on_tick_emit_attest_shape (S : Setup V) (v : V) (n : NodeState V) (t : Time) :
    ∃ (st3 : Protocol.NamedStore V) (gc : Protocol.GradeContract V) (pre : List (Object V)),
      (∀ o ∈ pre, ∀ a : NamedAttestation V, o ≠ Object.attest a) ∧
      (((on_tick_emit S v n t).1.record = n.Λ ∧ (on_tick_emit S v n t).2 = pre) ∨
       ((on_tick_emit S v n t).1.record =
          (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
            st3.core.toHealing n.Λ).1 ∧
        (on_tick_emit S v n t).2 = pre ++
          [Object.attest (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
            st3.core.toHealing n.Λ).2])) := by
  have hrec := on_tick_emit_record_eq S v n t
  have hsnd := on_tick_emit_snd_eq S v n t
  rw [named_tick_computed_duties] at hrec hsnd
  set gc := NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) with hgcdef
  set s := S.E.slotOf t with hsdef
  set st0 := Protocol.NamedStore.setClock S.E n.st t with hst0def
  set proposed := Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0
    with hproposeddef
  set proposalDue := 0 < s ∧ t = Protocol.proposal_time S.E s ∧
    S.E.proposer s = (S.node v).val_index with hproposalDuedef
  set st1 := if proposalDue then proposed.1 else st0 with hst1def
  set emitted1 : List (Object V) := if proposalDue then
    (match proposed.2 with | none => [] | some B => [Object.block B]) else [] with hemitted1def
  set voted := Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1 with hvoteddef
  set voteDue := 0 < s ∧ t = Protocol.vote_time S.E s with hvoteDuedef
  set st2 := if voteDue then voted.1 else st1 with hst2def
  set emitted2 : List (Object V) := if voteDue then voted.2.toList.map Object.gfVote else []
    with hemitted2def
  set st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
    with hst3def
  have hpre : ∀ o ∈ emitted1 ++ emitted2, ∀ a : NamedAttestation V,
      o ≠ Object.attest a := by
    intro o ho a
    rcases List.mem_append.mp ho with h1 | h1
    · rw [hemitted1def] at h1
      split_ifs at h1 with hpd
      · rcases hpm : proposed.2 with _ | B
        · simp [hpm] at h1
        · simp only [hpm, List.mem_singleton] at h1
          simp [h1]
      · simp at h1
    · rw [hemitted2def] at h1
      split_ifs at h1 with hvd
      · obtain ⟨w, -, hw⟩ := List.mem_map.mp h1
        simp [← hw]
      · simp at h1
  by_cases hcond : t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
      (S.node v).awake (S.hc.round_of st3.core.s) = true
  · rw [if_pos hcond] at hrec hsnd
    exact ⟨st3, gc, emitted1 ++ emitted2, hpre, Or.inr ⟨hrec, hsnd⟩⟩
  · rw [if_neg hcond] at hrec hsnd
    exact ⟨st3, gc, emitted1 ++ emitted2, hpre, Or.inl ⟨hrec, hsnd⟩⟩

/-- §5.3 `LockCompatible` survives a tick (PROTOCOL.md#the-complete-protocol). -/
theorem lockCompatible_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    (hla : LockCompatible n.Λ.legacy) :
    LockCompatible (on_tick_emit S v n t).1.record.legacy := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, -⟩
  · rw [hrec]; exact hla
  · rw [hrec]
    obtain ⟨r, c, f, h_j, J, h_F, hleg, -⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    rw [hleg]
    exact lockCompatible_create_attestation hla _ r c f h_j J h_F

/-- §5.3 The stored target survives a tick (PROTOCOL.md#the-complete-protocol). -/
theorem target_mono_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} {T : BlockId} (hs : n.Λ.legacy.target h = some T) :
    (on_tick_emit S v n t).1.record.legacy.target h = some T := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, -⟩
  · rw [hrec]; exact hs
  · rw [hrec]
    obtain ⟨r, c, f, h_j, J, h_F, hleg, -⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    rw [hleg]
    simp only [create_attestation]
    exact record_attestation_target_mono _ _ hs

/-- §5.3 The stored lock keeps an existing lock through a valid tick. -/
theorem lock_mono_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} {T : BlockId} (hs : n.Λ.legacy.lock h = some T) :
    (on_tick_emit S v n t).1.record.legacy.lock h = some T := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, -⟩
  · rw [hrec]; exact hs
  · rw [hrec]
    obtain ⟨r, c, f, h_j, J, h_F, hleg, -⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    rw [hleg]
    exact create_attestation_lock_mono hs _ r c f h_j J h_F

/-- §7.2 a delivery never touches the record (`Execution/Node.lean`). -/
theorem process_record (S : Setup V) (n : NodeState V) (o : Object V) :
    (NamedNode.process S n o).Λ = n.Λ := by
  cases o <;> rfl

/-! ## 2. Along the run

Both inductions are `Proofs.HealingLemmas.Schedule.stateBefore_sg_pool_subset`'s, at
the record instead of the SG bucket. -/

/-- **`LockCompatible` holds at every point of every honest record**
(PROTOCOL.md#the-complete-protocol). Established at `Record.initial` and preserved
by every event: deliveries are inert, other validators' ticks are inert, and the
node's own tick is one named round action. -/
theorem stateBefore_lockCompatible (S : Setup V) (ρ : Run V) (v : V) :
    ∀ i : Nat, LockCompatible (ρ.stateBefore S i v).Λ.legacy := by
  intro i
  induction i with
  | zero => exact Proofs.Records.lockCompatible_initial
  | succ i ih =>
    have hstep : ρ.stateBefore S (i + 1) =
        (ρ.events[i]?.toList).foldl (World.step S) (ρ.stateBefore S i) := by
      unfold Run.stateBefore NamedRun.stateBefore
      rw [List.take_add_one, List.foldl_append]
    rw [hstep]
    rcases hev : ρ.events[i]? with _ | e
    · exact ih
    · cases e with
      | tick u t =>
        by_cases hu : u = v
        · subst hu
          simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_self]
          exact lockCompatible_on_tick_emit S u _ t ih
        · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_of_ne (Ne.symm hu)]
          exact ih
      | deliver u o t =>
        by_cases hu : u = v
        · subst hu
          simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_self]
          rw [process_record]
          exact ih
        · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_of_ne (Ne.symm hu)]
          exact ih

/-- **The stored target only grows along a run** (PROTOCOL.md#the-complete-protocol). The
write-once guard, lifted from one fold to the whole event list. -/
theorem stateBefore_target_mono (S : Setup V) (ρ : Run V) (v : V) {h : Height}
    {T : BlockId} {i : Nat} :
    ∀ j : Nat, i ≤ j → (ρ.stateBefore S i v).Λ.legacy.target h = some T →
      (ρ.stateBefore S j v).Λ.legacy.target h = some T := by
  intro j
  induction j with
  | zero => intro hj; rw [Nat.le_zero.mp hj]; exact id
  | succ j ih =>
    intro hj hs
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hprev := ih (Nat.lt_succ_iff.mp hlt) hs
      have hstep : ρ.stateBefore S (j + 1) =
          (ρ.events[j]?.toList).foldl (World.step S) (ρ.stateBefore S j) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rw [hstep]
      rcases hev : ρ.events[j]? with _ | e
      · exact hprev
      · cases e with
        | tick u t =>
          by_cases hu : u = v
          · subst hu
            simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_self]
            exact target_mono_on_tick_emit S u _ t hprev
          · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_of_ne (Ne.symm hu)]
            exact hprev
        | deliver u o t =>
          by_cases hu : u = v
          · subst hu
            simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_self]
            rw [process_record]
            exact hprev
          · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_of_ne (Ne.symm hu)]
            exact hprev
    · exact (Nat.le_antisymm hj hge) ▸ hs

/-- **The stored lock keeps its first value along a run.** The finality-pair
guard prevents a later named round action from replacing it with a different
target. -/
theorem stateBefore_lock_mono (S : Setup V) (ρ : Run V) (v : V) {h : Height}
    {T : BlockId} {i : Nat} :
    ∀ j : Nat, i ≤ j → (ρ.stateBefore S i v).Λ.legacy.lock h = some T →
      (ρ.stateBefore S j v).Λ.legacy.lock h = some T := by
  intro j
  induction j with
  | zero => intro hj; rw [Nat.le_zero.mp hj]; exact id
  | succ j ih =>
    intro hj hs
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hprev := ih (Nat.lt_succ_iff.mp hlt) hs
      have hstep : ρ.stateBefore S (j + 1) =
          (ρ.events[j]?.toList).foldl (World.step S) (ρ.stateBefore S j) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rw [hstep]
      rcases hev : ρ.events[j]? with _ | e
      · exact hprev
      · cases e with
        | tick u t =>
          by_cases hu : u = v
          · subst hu
            simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_self]
            exact lock_mono_on_tick_emit S u _ t hprev
          · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_of_ne (Ne.symm hu)]
            exact hprev
        | deliver u o t =>
          by_cases hu : u = v
          · subst hu
            simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_self]
            rw [process_record]
            exact hprev
          · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
              Function.update_of_ne (Ne.symm hu)]
            exact hprev
    · exact (Nat.le_antisymm hj hge) ▸ hs

/-! ## 3. What an emission leaves behind -/

/-- The record after the tick at index `i` is the tick's own output. -/
theorem stateBefore_succ_record (S : Setup V) (ρ : Run V) {v : V} {t : Time}
    {i : Nat} (hi : ρ.events[i]? = some (Event.tick v t)) :
    (ρ.stateBefore S (i + 1) v).Λ =
      (on_tick_emit S v (ρ.stateBefore S i v) t).1.record := by
  have hval : ρ.stateBefore S (i + 1) v =
      (on_tick_emit S v (ρ.stateBefore S i v) t).1 := by
    have hfold : ρ.stateBefore S (i + 1) =
        (ρ.events[i]?.toList).foldl (World.step S) (ρ.stateBefore S i) := by
      unfold Run.stateBefore NamedRun.stateBefore
      rw [List.take_add_one, List.foldl_append]
    rw [hfold, hi]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
      Function.update_self]
  rw [hval]

/-- **Every emitted height-pair target is recorded by the record the tick
leaves behind** (PROTOCOL.md#the-complete-protocol). -/
theorem emits_height_target_recorded (S : Setup V) (ρ : Run V)
    {v : V} {t : Time} {i : Nat}
    {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {T : BlockId} (hT : a.erase.height_pair = HeightPair.target h T) :
    (ρ.stateBefore S (i + 1) v).Λ.legacy.target h = some T := by
  obtain ⟨st3, gc, pre, hpre, hcase⟩ := on_tick_emit_attest_shape S v (ρ.stateBefore S i v) t
  rw [stateBefore_succ_record S ρ hi]
  rcases hcase with ⟨-, hsnd⟩ | ⟨hrec, hsnd⟩
  · rw [hsnd] at ha
    exact absurd rfl (hpre (Object.attest a) ha a)
  · rw [hrec]
    rw [hsnd] at ha
    obtain ⟨r, c, f, h_j, J, h_F, hleg, herase⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing (ρ.stateBefore S i v).Λ
    have h'' : a = (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
        st3.core.toHealing (ρ.stateBefore S i v).Λ).2 := by
      rcases List.mem_append.mp ha with h' | h'
      · exact absurd rfl (hpre (Object.attest a) h' a)
      · rw [List.mem_singleton] at h'
        injection h'
    rw [hleg]
    exact create_attestation_saves (ρ.stateBefore S i v).Λ.legacy
      (stateBefore_lockCompatible S ρ v i) (S.node v).val_index r c f h_j J h_F
      (by rw [← herase, ← h'']; exact hT)

/-- A nonempty finality pair writes its target to the lock before release. -/
theorem emits_finality_locked (S : Setup V) (ρ : Run V)
    {v : V} {t : Time} {i : Nat}
    {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {J : BlockId} (hfp : a.finality_pair = some ⟨h, J⟩) :
    (ρ.stateBefore S (i + 1) v).Λ.legacy.lock h = some J := by
  obtain ⟨st3, gc, pre, hpre, hcase⟩ := on_tick_emit_attest_shape S v (ρ.stateBefore S i v) t
  rw [stateBefore_succ_record S ρ hi]
  rcases hcase with ⟨-, hsnd⟩ | ⟨hrec, hsnd⟩
  · rw [hsnd] at ha
    exact absurd rfl (hpre (Object.attest a) ha a)
  · rw [hrec]
    rw [hsnd] at ha
    obtain ⟨r, c, f, h_j, T, h_F, hleg, herase⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing (ρ.stateBefore S i v).Λ
    have h'' : a = (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
        st3.core.toHealing (ρ.stateBefore S i v).Λ).2 := by
      rcases List.mem_append.mp ha with h' | h'
      · exact absurd rfl (hpre (Object.attest a) h' a)
      · rw [List.mem_singleton] at h'
        injection h'
    rw [hleg]
    simp only [create_attestation]
    rw [record_attestation_lock_eq_own_lock]
    have hfp' : Protocol.finality_pair (ρ.stateBefore S i v).Λ.legacy h_j T h_F =
        some ⟨h, J⟩ := by
      have hstep1 : a.erase = (create_attestation (ρ.stateBefore S i v).Λ.legacy
          (S.node v).val_index r c f h_j T h_F).2 := by rw [h'']; exact herase
      have hstep2 : a.finality_pair =
          Protocol.finality_pair (ρ.stateBefore S i v).Λ.legacy h_j T h_F := by
        rw [← erase_finality_pair a, hstep1]
        simp only [create_attestation]
      rw [← hstep2]
      exact hfp
    simp [Protocol.own_lock, hfp']

/-- Every target emitted by either pair leaves an empty-or-matching target
entry. The finality-pair arm can be empty under RULE B. -/
theorem emits_target_compatible (S : Setup V) (ρ : Run V)
    {v : V} {t : Time} {i : Nat}
    {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {T : BlockId} (hT : T ∈ targetsAt a.erase h) :
    (ρ.stateBefore S (i + 1) v).Λ.legacy.target h = none ∨
      (ρ.stateBefore S (i + 1) v).Λ.legacy.target h = some T := by
  rcases hT with hheight | hfinality
  · exact Or.inr (emits_height_target_recorded S ρ hi ha hheight)
  · have hlock := emits_finality_locked S ρ hi ha hfinality
    exact (stateBefore_lockCompatible S ρ v (i + 1) h T hlock).2

/-- Proof-layer compatibility alias for the Rule B residual statement. -/
abbrev FinalityTargetHeightSource (S : Setup V) (ρ : Run V) :=
  Internal.FinalityTargetHeightSource S ρ

/-! ## 4. L4's honest core, end to end -/

/-- **A later emission agrees with the record** — the step the ordering argument
turns on. -/
theorem emits_target_eq_of_record (S : Setup V) (ρ : Run V) {v : V} {t : Time}
    {i : Nat} {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {T X : BlockId} (hs : (ρ.stateBefore S i v).Λ.legacy.target h = some X)
    (hT : T ∈ targetsAt a.erase h) : T = X := by
  have hsucc := emits_target_compatible S ρ hi ha hT
  have hmono : (ρ.stateBefore S (i + 1) v).Λ.legacy.target h = some X :=
    stateBefore_target_mono S ρ v (i + 1) (Nat.le_succ i) hs
  rcases hsucc with hnone | hsame
  · rw [hmono] at hnone
    contradiction
  · rw [hsame] at hmono
    exact Option.some_inj.mp hmono

/-- A target emitted while the record already has a lock at that height agrees
with the lock. -/
theorem emits_target_eq_of_lock (S : Setup V) (ρ : Run V) {v : V} {t : Time}
    {i : Nat} {a : NamedAttestation V} (hi : ρ.events[i]? = some (Event.tick v t))
    (ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2)
    {h : Height} {T X : BlockId} (hs : (ρ.stateBefore S i v).Λ.legacy.lock h = some X)
    (hT : T ∈ targetsAt a.erase h) : T = X := by
  have hlock : (ρ.stateBefore S (i + 1) v).Λ.legacy.lock h = some X := by
    rw [stateBefore_succ_record S ρ hi]
    exact lock_mono_on_tick_emit S v _ t hs
  rcases hT with hheight | hfinality
  · have htarget := emits_height_target_recorded S ρ hi ha hheight
    have hcompat := (stateBefore_lockCompatible S ρ v (i + 1) h X hlock).2
    rcases hcompat with hnone | hsame
    · rw [htarget] at hnone
      contradiction
    · rw [htarget] at hsame
      exact Option.some_inj.mp hsame
  · have hnewLock := emits_finality_locked S ρ hi ha hfinality
    rw [hlock] at hnewLock
    exact (Option.some_inj.mp hnewLock).symm

/-- **`Internal.HealingSurface.HonestNoDoubleTarget`, proved**
(`the design` §9 L4, honest half; `Internal.AlignedRound`'s deleted clause
(e); `the design notes` §5).

No honest validator ever emits two different nonempty targets at one height. The
ordering argument is over event indices: the earlier emission records its target,
`target` is write-once from there, and the later emission must agree with it. The
same-index case is not an ordering argument — one tick emits at most one
attestation, and one attestation never conflicts with itself
(`height_pair_no_self_E1`).

**This pays the ledger §5 escalation in full.** `Internal.AlignedRound`'s rev. 4
rationale for deleting clause (e) — "it is a theorem" — is backed again, and L4
is complete: `perHeightCompletability_of` now composes with this and nothing is
assumed. -/
theorem honestNoDoubleTarget (S : Setup V) (ρ : Run V) :
    Internal.HealingSurface.HonestNoDoubleTarget S ρ := by
  rintro v - a a' t t' ⟨i, hi, ha⟩ ⟨j, hj, ha'⟩ h T T' hT hT'
  rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
  · rcases hT with hheight | hfinality
    · exact (emits_target_eq_of_record S ρ hj ha'
        (stateBefore_target_mono S ρ v j hlt
          (emits_height_target_recorded S ρ hi ha hheight)) hT').symm
    · exact (emits_target_eq_of_lock S ρ hj ha'
        (stateBefore_lock_mono S ρ v j hlt
          (emits_finality_locked S ρ hi ha hfinality)) hT').symm
  · rw [hj, Option.some_inj, NamedEvent.tick.injEq] at hi
    obtain ⟨-, ht⟩ := hi
    subst ht
    have ha : Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t').2 := ha
    have ha' : Object.attest a' ∈ (on_tick_emit S v (ρ.stateBefore S i v) t').2 := ha'
    obtain ⟨st3, gc, pre, hpre, hcase⟩ :=
      on_tick_emit_attest_shape S v (ρ.stateBefore S i v) t'
    rcases hcase with ⟨-, hsnd⟩ | ⟨-, hsnd⟩
    · rw [hsnd] at ha
      exact absurd rfl (hpre (Object.attest a) ha a)
    · rw [hsnd] at ha ha'
      have hmem : ∀ b : NamedAttestation V, Object.attest b ∈ pre ++
          [Object.attest (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
            st3.core.toHealing (ρ.stateBefore S i v).Λ).2] →
          b = (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
            st3.core.toHealing (ρ.stateBefore S i v).Λ).2 := by
        intro b hb
        rcases List.mem_append.mp hb with h' | h'
        · exact absurd rfl (hpre (Object.attest b) h' b)
        · rw [List.mem_singleton] at h'
          injection h'
      have hA := hmem a ha
      have hA' := hmem a' ha'
      subst hA
      subst hA'
      obtain ⟨r, c, f, h_j, J, h_F, -, herase⟩ :=
        round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing (ρ.stateBefore S i v).Λ
      rw [herase] at hT hT'
      rcases hT with hT | hT <;> rcases hT' with hT' | hT'
      · rw [hT] at hT'
        simp only [HeightPair.target.injEq, true_and] at hT'
        exact hT'
      · exact create_attestation_no_self_E1 _ _ _ _ _ _ _ _ hT hT'
      · exact (create_attestation_no_self_E1 _ _ _ _ _ _ _ _ hT' hT).symm
      · rw [hT] at hT'
        exact congrArg FinalityPair.target (Option.some_inj.mp hT')
  · rcases hT' with hheight | hfinality
    · exact emits_target_eq_of_record S ρ hi ha
        (stateBefore_target_mono S ρ v i hgt
          (emits_height_target_recorded S ρ hj ha' hheight)) hT
    · exact emits_target_eq_of_lock S ρ hi ha
        (stateBefore_lock_mono S ρ v i hgt
          (emits_finality_locked S ρ hj ha' hfinality)) hT

/-- **L4, complete** (`the design` §9 L4). The arithmetic was proved in
`PerHeight.lean`; the honest core is now a theorem, so the lemma stands on
`BelowOneThird` alone. -/
theorem perHeightCompletability (S : Setup V) {ρ : Run V}
    (hfb : BelowOneThird S ρ.honest) :
    Internal.HealingSurface.PerHeightCompletability S ρ :=
  perHeightCompletability_of S hfb (honestNoDoubleTarget S ρ)

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
