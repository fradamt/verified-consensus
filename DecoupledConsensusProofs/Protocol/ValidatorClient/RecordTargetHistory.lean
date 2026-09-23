module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Bridge

@[expose] public section

/-!
# Run provenance for anti-slashing record targets

A target entry in a node's local anti-slashing record can be introduced only by
that node's own action attestation. These facts depend only on the record writer,
the protocol tick, and the event prefix.

## Named-run proof (design note)

`on_tick_emit` is now `Execution.NamedNode.tick`, a named `NodeState` in
and a named `NodeState × List Object` out (`Execution/Node.lean`). The emitted
row is a `NamedAttestation`, read through `.erase` wherever the bare
`CombinedAttestation`/`HeightPair` facts apply ('s Rows note); the plain
`Record`/`CombinedAttestation`/`record_attestation`/`create_attestation` layer
underneath is unchanged, so the two record-layer lemmas below proof with no
statement change at all.

The existence direction this file needs — a fresh record entry came from some
emitted attestation — is the converse of `Proofs.HealingSurface.Bridge`'s
`emits_height_target_recorded`/`emits_finality_locked` (emission to record).
That file's own case split (`on_tick_emit_attest_shape`) and the record/erasure
identity (`round_action_shape`) are `private`, so this file keeps a byte-for-byte
local copy, exactly as `Optimistic/Alignment.lean`, `HealingSurface/ActionRun.lean`,
`Availability/Pool.lean` and `Availability/Monotone.lean` already do for the
identical `named_tick_computed_duties` restatement (that file's dependency
`Proofs.NamedActions.lean` has no `.olean` built on this run's frontier, so a
single-file compile cannot import it).
-/



namespace DecoupledConsensusModel
namespace Protocol

open Protocol (Record create_attestation finality_pair record_attestation)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- If `record_attestation` introduces a fresh target entry, the attestation's
height pair is the matching nonempty target. -/
theorem record_attestation_target_introduced {Λ : Record}
    {a : CombinedAttestation V} {h : Height} {T : BlockId}
    (hpre : Λ.target h = none)
    (hpost : (record_attestation Λ a).target h = some T) :
    a.height_pair = HeightPair.target h T := by
  simp only [record_attestation] at hpost
  cases hfp : a.finality_pair <;> cases hhp : a.height_pair <;>
    simp_all [Record.with_lock, Record.with_timeout]
  all_goals
    split at hpost
    · rename_i hfresh
      simp only [Record.with_target] at hpost
      split at hpost
      · rename_i heq
        exact ⟨heq.symm, Option.some.inj hpost⟩
      · rw [hpre] at hpost
        contradiction
    · rw [hpre] at hpost
      contradiction

omit [DecidableEq V] [Fintype V] in
/-- If `record_attestation` introduces a fresh lock entry, the attestation's
finality pair is that entry, at its own height.

`Λ.lock` is written only by the finality-pair prefix of `record_attestation`;
the height-pair suffix writes `target` and `timeout`, and both leave `lock`
alone. -/
theorem record_attestation_lock_introduced {Λ : Record}
    {a : CombinedAttestation V} {h : Height} {T : BlockId}
    (hpre : Λ.lock h = none)
    (hpost : (record_attestation Λ a).lock h = some T) :
    a.finality_pair = some ⟨h, T⟩ := by
  cases hfp : a.finality_pair with
  | none =>
      have hunchanged : (record_attestation Λ a).lock h = Λ.lock h := by
        simp only [record_attestation, hfp]
        split <;> first | rfl | (split <;> rfl)
      rw [hunchanged, hpre] at hpost
      exact absurd hpost (by simp)
  | some p =>
      have hlock : (record_attestation Λ a).lock h =
          (Λ.with_lock p.height p.target).lock h := by
        simp only [record_attestation, hfp]
        split <;> first | rfl | (split <;> rfl)
      rw [hlock] at hpost
      by_cases hne : h = p.height
      · subst hne
        rw [Proofs.Records.with_lock_self] at hpost
        have hT : p.target = T := Option.some.inj hpost
        subst hT
        cases p
        rfl
      · rw [Proofs.Records.with_lock_ne hne, hpre] at hpost
        exact absurd hpost (by simp)



omit [DecidableEq V] [Fintype V] in
private theorem erase_finality_pair (a : NamedAttestation V) :
    a.erase.finality_pair = a.finality_pair := rfl

omit [DecidableEq V] [Fintype V] in
private theorem encodeHeight_erase_of (record : Record)
    (fields : Option (Height × BlockId × Bool)) (fp : Option FinalityPair) :
    (Protocol.NamedRecord.encodeHeight fields
      (Protocol.height_pair record fields fp)).erase =
      Protocol.height_pair record fields fp := by
  rcases Proofs.Engine.height_pair_cases (Λ := record) fields fp with he | ⟨h, entry, nu, hf, hp⟩
  · simp [Protocol.NamedRecord.encodeHeight, he, NamedHeightPair.erase]
  · rcases hp with ht | ht <;> rw [ht, hf] <;> rfl

/-- The named round action's output is exactly the previous bare `create_attestation`'s,
at the emitter's own record, at any grade contract. -/
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

/-- One tick's attest branch, decomposed: a list `pre` with no attest object,
and either nothing more (record unchanged) or exactly the named round action's
own row appended (record advances by that one action). -/
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

/-- If one tick introduces a fresh target entry, that tick emits the matching
height-pair attestation. -/
theorem on_tick_emit_target_introduced (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} {T : BlockId}
    (hpre : n.Λ.legacy.target h = none)
    (hpost : (on_tick_emit S v n t).1.record.legacy.target h = some T) :
    ∃ a : NamedAttestation V,
      Object.attest a ∈ (on_tick_emit S v n t).2 ∧
        a.erase.height_pair = HeightPair.target h T := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, hsnd⟩
  · rw [hrec] at hpost
    exact absurd hpost (by rw [hpre]; simp)
  · obtain ⟨r, c, f, h_j, J, h_F, hleg, herase⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    refine ⟨(Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
        st3.core.toHealing n.Λ).2, ?_, ?_⟩
    · rw [hsnd]
      exact List.mem_append_right pre (List.mem_singleton_self _)
    · rw [herase]
      have hcreated :
          (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).1.target h =
            some T := by
        rw [← hleg, ← hrec]
        exact hpost
      have hfold :
          (record_attestation n.Λ.legacy
              (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).2).target h =
            some T := by
        simpa only [create_attestation] using hcreated
      exact record_attestation_target_introduced hpre hfold

/-- If one tick introduces a fresh lock entry, that tick emits the matching
finality pair. -/
theorem on_tick_emit_lock_introduced (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} {T : BlockId}
    (hpre : n.Λ.legacy.lock h = none)
    (hpost : (on_tick_emit S v n t).1.record.legacy.lock h = some T) :
    ∃ a : NamedAttestation V,
      Object.attest a ∈ (on_tick_emit S v n t).2 ∧
        a.finality_pair = some ⟨h, T⟩ := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, hsnd⟩
  · rw [hrec] at hpost
    exact absurd hpost (by rw [hpre]; simp)
  · obtain ⟨r, c, f, h_j, J, h_F, hleg, herase⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    refine ⟨(Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
        st3.core.toHealing n.Λ).2, ?_, ?_⟩
    · rw [hsnd]
      exact List.mem_append_right pre (List.mem_singleton_self _)
    · rw [← erase_finality_pair, herase]
      have hcreated :
          (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).1.lock h =
            some T := by
        rw [← hleg, ← hrec]
        exact hpost
      have hfold :
          (record_attestation n.Λ.legacy
              (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).2).lock h =
            some T := by
        simpa only [create_attestation] using hcreated
      exact record_attestation_lock_introduced hpre hfold

/-- Every target present in a node record at event prefix `n` came from a
strictly earlier local tick that emitted a matching nonempty height pair.

The execution semantics runs the protocol duty for every tick event, so this
statement is valid for every node. An honesty premise is therefore not needed.
The event witness is stronger than a bare `Run.emits` witness because it also
records that the introducing tick has index less than `n`. -/
theorem recordTarget_emission_before (S : Setup V) (ρ : Run V) (v : V) :
    ∀ (n : Nat) {h : Height} {T : BlockId},
      (ρ.stateBefore S n v).Λ.legacy.target h = some T →
        ∃ (i : Nat), i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
          ρ.events[i]? = some (Event.tick v t) ∧
            Object.attest a ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2 ∧
            a.erase.height_pair = HeightPair.target h T := by
  intro n
  induction n with
  | zero =>
      intro h T htarget
      exact absurd htarget (by
        simp [Run.stateBefore, NamedRun.stateBefore, List.take_zero, List.foldl_nil,
          NamedWorld.init, NamedNode.initial, Protocol.NamedRecord.initial,
          Record.initial])
  | succ n ih =>
      intro h T htarget
      cases hpre : (ρ.stateBefore S n v).Λ.legacy.target h with
      | some X =>
          have hmono : (ρ.stateBefore S (n + 1) v).Λ.legacy.target h = some X :=
            Proofs.HealingSurface.stateBefore_target_mono S ρ v (n + 1)
              (Nat.le_succ n) hpre
          have hXT : X = T := by
            rw [htarget] at hmono
            exact (Option.some.inj hmono).symm
          subst hXT
          obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ := ih hpre
          exact ⟨i, Nat.lt_succ_of_lt hi, t, a, hevent, hemitted, hpair⟩
      | none =>
          have hstep : ρ.stateBefore S (n + 1) =
              (ρ.events[n]?.toList).foldl (World.step S)
                (ρ.stateBefore S n) := by
            unfold Run.stateBefore NamedRun.stateBefore
            rw [List.take_add_one, List.foldl_append]
          rcases hevent : ρ.events[n]? with _ | e
          · rw [hstep, hevent] at htarget
            simp only [Option.toList, List.foldl_nil] at htarget
            exact absurd htarget (by rw [hpre]; simp)
          · cases e with
            | tick u t =>
                by_cases huv : u = v
                · subst u
                  have hpost :
                      (on_tick_emit S v (ρ.stateBefore S n v) t).1.record.legacy.target h =
                        some T := by
                    rw [← Proofs.HealingSurface.stateBefore_succ_record S ρ hevent]
                    exact htarget
                  obtain ⟨a, hemitted, hpair⟩ :=
                    on_tick_emit_target_introduced S v (ρ.stateBefore S n v) t hpre hpost
                  exact ⟨n, Nat.lt_succ_self n, t, a, hevent, hemitted, hpair⟩
                · rw [hstep, hevent] at htarget
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                    World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)] at htarget
                  exact absurd htarget (by rw [hpre]; simp)
            | deliver u o t =>
                by_cases huv : u = v
                · subst u
                  rw [hstep, hevent] at htarget
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                    World.step, NamedWorld.step, Function.update_self] at htarget
                  rw [Proofs.HealingSurface.process_record] at htarget
                  exact absurd htarget (by rw [hpre]; simp)
                · rw [hstep, hevent] at htarget
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                    World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)] at htarget
                  exact absurd htarget (by rw [hpre]; simp)

end Protocol
end DecoupledConsensusModel

end
