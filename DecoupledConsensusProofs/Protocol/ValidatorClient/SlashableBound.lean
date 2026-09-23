module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordFresh

@[expose] public section

/-!
# Honest execution non-slashability support

This file proves the record and emission facts that rule out self-slashing in
the final Section 7 execution. Honest attestations are emitted only by the
final `on_tick_emit`, whose `Lambda` component starts at `Record.initial`,
changes only through `create_attestation`, and is updated before the
attestation is released.

The generic accountable-bound bridge is packaged separately in
`SlashableBoundBridgeRun`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record create_attestation finality_pair height_pair
  record_attestation)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- A finality pair cannot coexist with a timeout pair at the same height in
one attestation produced by `create_attestation`. -/
theorem create_attestation_no_self_timeout
    (Lambda : Record) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) {h : Height} {T : BlockId}
    (hfp : (create_attestation Lambda val_index r confirmed fields h_j J h_F).2.finality_pair =
      some ⟨h, T⟩) :
    (create_attestation Lambda val_index r confirmed fields h_j J h_F).2.height_pair ≠
      HeightPair.timeout h := by
  simp only [create_attestation] at hfp ⊢
  have htimeout : Lambda.timeout h = false := by
    simp only [finality_pair] at hfp
    split at hfp
    · split at hfp
      · rename_i hguard
        simp only [Option.some.injEq] at hfp
        have hh : h_j = h := congrArg FinalityPair.height hfp
        subst h_j
        exact hguard.2.1
      · contradiction
    · contradiction
  rw [hfp]
  cases fields with
  | none => simp [height_pair]
  | some f =>
      obtain ⟨g, X, nu⟩ := f
      by_cases hgh : g = h
      · subst g
        simp only [height_pair, htimeout, Bool.false_eq_true,
          Protocol.own_lock, ↓reduceIte]
        split <;> simp
      · simp only [height_pair]
        split
        · simp_all
        · cases hl : Protocol.own_lock Lambda g (some ⟨h, T⟩) with
          | some locked =>
              by_cases heq : locked = X <;> simp [heq]
          | none =>
              cases ht : Lambda.target g with
              | some recorded =>
                  by_cases heq : recorded = X <;> simp [heq, hgh]
              | none =>
                  by_cases hnu : nu = true <;> simp [hnu, hgh]

/-- The record state established by one emitted finality pair. -/
def FinalitySafeAt (Lambda : Record) (h : Height) (T : BlockId) : Prop :=
  Lambda.timeout h = false ∧ Lambda.lock h = some T

omit [DecidableEq V] [Fintype V] in
private theorem slashableBound_record_attestation_lock
    (Lambda : Record) (a : CombinedAttestation V)
    {h : Height} {T : BlockId} (hfp : a.finality_pair = some ⟨h, T⟩) :
    (record_attestation Lambda a).lock h = some T := by
  simp only [record_attestation, hfp]
  cases a.height_pair with
  | empty => simp [Record.with_lock]
  | timeout g => simp [Record.with_lock, Record.with_timeout]
  | target g X =>
      by_cases hs : Lambda.target g = none <;>
        simp [Record.with_lock, Record.with_target, hs]

omit [DecidableEq V] [Fintype V] in
/-- A finality pair can be emitted only while its height has not timed out. -/
theorem finality_pair_timeout_false {Lambda : Record} {h_j h_F : Height}
    {J : BlockId} {h : Height} {T : BlockId}
    (hfp : finality_pair Lambda h_j J h_F = some ⟨h, T⟩) :
    Lambda.timeout h = false := by
  simp only [finality_pair] at hfp
  split at hfp
  · split at hfp
    · rename_i hguard
      simp only [Option.some.injEq] at hfp
      have hh : h_j = h := congrArg FinalityPair.height hfp
      subst h_j
      exact hguard.2.1
    · contradiction
  · contradiction

omit [DecidableEq V] [Fintype V] in
/-- A safe finality record determines the lock read by the next height pair,
including when that next attestation also contains a finality pair. -/
theorem own_lock_eq_of_finalitySafeAt {Lambda : Record} {h : Height}
    {T : BlockId} (hsafe : FinalitySafeAt Lambda h T)
    (h_j : Height) (J : BlockId) (h_F : Height) :
    Protocol.own_lock Lambda h (finality_pair Lambda h_j J h_F) = some T := by
  rcases hsafe with ⟨-, hlock⟩
  cases hfp : finality_pair Lambda h_j J h_F with
  | none => simpa [Protocol.own_lock] using hlock
  | some p =>
      by_cases hph : p.height = h
      · have hpTarget : p.target = T := by
          have hguard := (finality_pair_record_conditions hfp).2.2
          rw [hph, hlock] at hguard
          rcases hguard with hnone | hsame
          · contradiction
          · exact (Option.some.inj hsame).symm
        simp [Protocol.own_lock, hph, hpTarget]
      · simp [Protocol.own_lock, hph, hlock]

omit [DecidableEq V] [Fintype V] in
/-- Once a record is finality-safe at `h`, the next valid height rule cannot
emit a timeout at `h`. -/
theorem height_pair_ne_timeout_of_finalitySafeAt {Lambda : Record}
    {h : Height} {T : BlockId} (hsafe : FinalitySafeAt Lambda h T)
    (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    height_pair Lambda fields (finality_pair Lambda h_j J h_F) ≠
      HeightPair.timeout h := by
  exact height_pair_ne_timeout_of_own_lock hsafe.1
    (own_lock_eq_of_finalitySafeAt hsafe h_j J h_F)

omit [DecidableEq V] [Fintype V] in
/-- An emitted finality pair establishes the complete safe record state at its
height before release. -/
theorem create_attestation_finalitySafeAt
    (Lambda : Record) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) {h : Height} {T : BlockId}
    (hfp : (create_attestation Lambda val_index r confirmed fields h_j J h_F).2.finality_pair =
      some ⟨h, T⟩) :
    FinalitySafeAt
      (create_attestation Lambda val_index r confirmed fields h_j J h_F).1 h T := by
  have hfp' : finality_pair Lambda h_j J h_F = some ⟨h, T⟩ := by
    simpa only [create_attestation] using hfp
  have htimeout : Lambda.timeout h = false := finality_pair_timeout_false hfp'
  have hne := create_attestation_no_self_timeout Lambda val_index r confirmed fields
    h_j J h_F hfp
  refine ⟨?_, ?_⟩
  · simp only [create_attestation]
    exact record_attestation_timeout_false_of_ne _ htimeout hne
  · simp only [create_attestation]
    exact slashableBound_record_attestation_lock Lambda _ hfp'

omit [DecidableEq V] [Fintype V] in
/-- Once established, `FinalitySafeAt` is preserved by every later valid
`create_attestation` call. -/
theorem create_attestation_finalitySafeAt_mono
    (Lambda : Record) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) {h : Height} {T : BlockId}
    (hsafe : FinalitySafeAt Lambda h T) :
    FinalitySafeAt
      (create_attestation Lambda val_index r confirmed fields h_j J h_F).1 h T := by
  rcases hsafe with ⟨htimeout, hlock⟩
  have hne :
      (create_attestation Lambda val_index r confirmed fields h_j J h_F).2.height_pair ≠
        HeightPair.timeout h := by
    simpa only [create_attestation] using
      height_pair_ne_timeout_of_finalitySafeAt
        ⟨htimeout, hlock⟩ fields h_j J h_F
  refine ⟨?_, ?_⟩
  · simp only [create_attestation]
    exact record_attestation_timeout_false_of_ne _ htimeout hne
  · simp only [create_attestation]
    rw [record_attestation_lock_eq_own_lock]
    exact own_lock_eq_of_finalitySafeAt ⟨htimeout, hlock⟩ h_j J h_F

omit [DecidableEq V] [Fintype V] in
/-- Recording a timeout pair sets the matching timeout bit. -/
theorem record_attestation_timeout_true (Lambda : Record)
    (a : CombinedAttestation V) {h : Height}
    (hhp : a.height_pair = HeightPair.timeout h) :
    (record_attestation Lambda a).timeout h = true := by
  simp [record_attestation, hhp, Record.with_lock, Record.with_timeout]



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
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V)
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
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
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

/-! ## The final Section 7 tick -/

/-- Every attestation in one final Section 7 tick is the attestation returned by
one `create_attestation` call on the tick's input record, at the emitter's own
record, and the tick returns that call's updated retained record. -/
theorem on_tick_emit_attestation_created (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {a : NamedAttestation V}
    (hmem : Object.attest a ∈ (on_tick_emit S v n t).2) :
    ∃ (r : Round) (confirmed : Option BlockId)
      (fields : Option (Height × BlockId × Bool))
      (h_j : Height) (J : BlockId) (h_F : Height),
      a.erase = (create_attestation n.Λ.legacy (S.node v).val_index r confirmed fields
          h_j J h_F).2 ∧
        (on_tick_emit S v n t).1.record.legacy =
          (create_attestation n.Λ.legacy (S.node v).val_index r confirmed fields
            h_j J h_F).1 := by
  obtain ⟨st3, gc, pre, hpre, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨-, hsnd⟩ | ⟨hrec, hsnd⟩
  · rw [hsnd] at hmem
    exact absurd rfl (hpre (Object.attest a) hmem a)
  · rw [hsnd] at hmem
    rcases List.mem_append.mp hmem with h | h
    · exact absurd rfl (hpre (Object.attest a) h a)
    · rw [List.mem_singleton] at h
      have ha : a = (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
          st3.core.toHealing n.Λ).2 := by injection h
      obtain ⟨r, c, f, h_j, J, h_F, hleg, herase⟩ :=
        round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
      exact ⟨r, c, f, h_j, J, h_F, by rw [ha, herase], by rw [hrec, hleg]⟩

/-- A finality pair emitted by one final Section 7 tick establishes the safe
record state at that height in the tick's output. -/
theorem on_tick_emit_finalitySafeAt_of_mem (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {a : NamedAttestation V} {h : Height} {T : BlockId}
    (hmem : Object.attest a ∈ (on_tick_emit S v n t).2)
    (hfp : a.finality_pair = some ⟨h, T⟩) :
    FinalitySafeAt (on_tick_emit S v n t).1.record.legacy h T := by
  obtain ⟨r, confirmed, fields, h_j, J, h_F, herase, hleg⟩ :=
    on_tick_emit_attestation_created S v n t hmem
  have hcreated : (create_attestation n.Λ.legacy (S.node v).val_index r confirmed fields
      h_j J h_F).2.finality_pair = some ⟨h, T⟩ := by
    rw [← herase]; exact hfp
  rw [hleg]
  exact create_attestation_finalitySafeAt n.Λ.legacy (S.node v).val_index r confirmed
    fields h_j J h_F hcreated

/-- A timeout pair emitted by one final Section 7 tick sets the matching bit in
the tick's output record. -/
theorem on_tick_emit_timeout_true_of_mem (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {a : NamedAttestation V} {h : Height}
    (hmem : Object.attest a ∈ (on_tick_emit S v n t).2)
    (hhp : a.erase.height_pair = HeightPair.timeout h) :
    (on_tick_emit S v n t).1.record.legacy.timeout h = true := by
  obtain ⟨r, confirmed, fields, h_j, J, h_F, herase, hleg⟩ :=
    on_tick_emit_attestation_created S v n t hmem
  have hcreated : (create_attestation n.Λ.legacy (S.node v).val_index r confirmed fields
      h_j J h_F).2.height_pair = HeightPair.timeout h := by
    rw [← herase]; exact hhp
  rw [hleg]
  change (record_attestation n.Λ.legacy
    (create_attestation n.Λ.legacy (S.node v).val_index r confirmed fields h_j J h_F).2).timeout h
      = true
  apply record_attestation_timeout_true
  exact hcreated

/-- `FinalitySafeAt` survives one final Section 7 tick. -/
theorem finalitySafeAt_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} {T : BlockId} (hsafe : FinalitySafeAt n.Λ.legacy h T) :
    FinalitySafeAt (on_tick_emit S v n t).1.record.legacy h T := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, -⟩
  · rw [hrec]; exact hsafe
  · rw [hrec]
    obtain ⟨r, confirmed, fields, h_j, J, h_F, hleg, -⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    rw [hleg]
    exact create_attestation_finalitySafeAt_mono n.Λ.legacy (S.node v).val_index r confirmed
      fields h_j J h_F hsafe

/-! ## The event-prefix record -/

/-- `FinalitySafeAt` is monotone along a validator's event-prefix record. -/
theorem stateBefore_finalitySafeAt_mono (S : Setup V) (rho : Run V) (v : V)
    {h : Height} {T : BlockId} {i : Nat} :
    ∀ j : Nat, i ≤ j → FinalitySafeAt (rho.stateBefore S i v).Λ.legacy h T →
      FinalitySafeAt (rho.stateBefore S j v).Λ.legacy h T := by
  intro j
  induction j with
  | zero =>
      intro hj
      rw [Nat.le_zero.mp hj]
      exact id
  | succ j ih =>
      intro hj hsafe
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · have hprev := ih (Nat.lt_succ_iff.mp hlt) hsafe
        have hstep : rho.stateBefore S (j + 1) =
            (rho.events[j]?.toList).foldl (World.step S) (rho.stateBefore S j) := by
          unfold Run.stateBefore NamedRun.stateBefore
          rw [List.take_add_one, List.foldl_append]
        rw [hstep]
        rcases hevent : rho.events[j]? with _ | e
        · exact hprev
        · cases e with
          | tick u t =>
              by_cases huv : u = v
              · subst u
                simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                  World.step, NamedWorld.step, Function.update_self]
                exact finalitySafeAt_on_tick_emit S v _ t hprev
              · simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                  World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
                exact hprev
          | deliver u o t =>
              by_cases huv : u = v
              · subst u
                simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                  World.step, NamedWorld.step, Function.update_self]
                rw [process_record]
                exact hprev
              · simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                  World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
                exact hprev
      · exact (Nat.le_antisymm hj hge) ▸ hsafe

/-- An emitted finality pair establishes `FinalitySafeAt` in the record after
its tick. -/
theorem emitted_finalitySafeAt (S : Setup V) (rho : Run V)
    {v : V} {t : Time} {i : Nat} {a : NamedAttestation V}
    (hi : rho.events[i]? = some (Event.tick v t))
    (hmem : Object.attest a ∈ (on_tick_emit S v (rho.stateBefore S i v) t).2)
    {h : Height} {T : BlockId} (hfp : a.finality_pair = some ⟨h, T⟩) :
    FinalitySafeAt (rho.stateBefore S (i + 1) v).Λ.legacy h T := by
  rw [stateBefore_succ_record S rho hi]
  exact on_tick_emit_finalitySafeAt_of_mem S v _ t hmem hfp

/-- An emitted timeout pair sets the timeout bit in the record after its tick. -/
theorem emitted_timeout_true (S : Setup V) (rho : Run V)
    {v : V} {t : Time} {i : Nat} {a : NamedAttestation V}
    (hi : rho.events[i]? = some (Event.tick v t))
    (hmem : Object.attest a ∈ (on_tick_emit S v (rho.stateBefore S i v) t).2)
    {h : Height} (hhp : a.erase.height_pair = HeightPair.timeout h) :
    (rho.stateBefore S (i + 1) v).Λ.legacy.timeout h = true := by
  rw [stateBefore_succ_record S rho hi]
  exact on_tick_emit_timeout_true_of_mem S v _ t hmem hhp

/-- No two protocol emissions by one validator can contain a finality pair and
a timeout pair at the same height, in either event order. -/
theorem no_timeout_against_finality (S : Setup V) (rho : Run V)
    {v : V} {a b : NamedAttestation V} {ta tb : Time}
    (ha : rho.emits S v (Object.attest a) ta)
    (hb : rho.emits S v (Object.attest b) tb)
    {h : Height} {T : BlockId} (hfp : a.finality_pair = some ⟨h, T⟩)
    (hhp : b.erase.height_pair = HeightPair.timeout h) : False := by
  obtain ⟨i, hi, hai⟩ := ha
  obtain ⟨j, hj, hbj⟩ := hb
  have hsafe := emitted_finalitySafeAt S rho hi hai hfp
  have htimeout := emitted_timeout_true S rho hj hbj hhp
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · have hsafe' := stateBefore_finalitySafeAt_mono S rho v
      (i := i + 1) (j + 1) (by omega) hsafe
    rw [hsafe'.1] at htimeout
    contradiction
  · rw [hsafe.1] at htimeout
    contradiction
  · have htimeout' := stateBefore_timeout_mono S rho v
      (h := h) (i := j + 1) (i + 1) (by omega) htimeout
    rw [hsafe.1] at htimeout'
    contradiction

/-! ## Honest emission non-slashability -/

/-- The already-proved target-history theorem applies to any two emissions of
an admissible run. Admissibility is used only to recover that the emitting tick
belongs to the run's honest set. -/
theorem emitted_targets_eq_of_admissibleCore (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) {v : V} {a b : NamedAttestation V}
    {ta tb : Time} (ha : rho.emits S v (Object.attest a) ta)
    (hb : rho.emits S v (Object.attest b) tb) {h : Height} {T U : BlockId}
    (hT : T ∈ targetsAt a.erase h) (hU : U ∈ targetsAt b.erase h) : T = U := by
  obtain ⟨i, hi, hai⟩ := ha
  have hmem : Event.tick v ta ∈ rho.events := List.mem_of_getElem? hi
  have hv : v ∈ rho.honest := adm.honest_only _ hmem
  exact honestNoDoubleTarget S rho v hv a b ta tb ⟨i, hi, hai⟩ hb
    h T U hT hU

/-- A height pair from one honest protocol emission does not conflict with a
finality pair from another emission by the same validator. -/
theorem conflictsWithFinality_false_of_admissibleCore (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) {v : V} {a b : NamedAttestation V}
    {ta tb : Time} (ha : rho.emits S v (Object.attest a) ta)
    (hb : rho.emits S v (Object.attest b) tb) {p : FinalityPair}
    (hfp : a.finality_pair = some p) :
    Protocol.conflictsWithFinality b.erase.height_pair p = false := by
  obtain ⟨h, T⟩ := p
  cases hhp : b.erase.height_pair with
  | empty => simp [Protocol.conflictsWithFinality]
  | timeout g =>
      by_cases hgh : g = h
      · subst g
        exact False.elim (no_timeout_against_finality S rho ha hb hfp hhp)
      · simp [Protocol.conflictsWithFinality, hgh]
  | target g U =>
      by_cases hgh : g = h
      · subst g
        have hTU : T = U := emitted_targets_eq_of_admissibleCore S adm ha hb
          (Or.inr hfp) (Or.inl hhp)
        simp [Protocol.conflictsWithFinality, hTU]
      · simp [Protocol.conflictsWithFinality, hgh]

/-- Two height pairs from honest protocol emissions do not form E2 evidence. -/
theorem e2Fields_false_of_admissibleCore (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) {v : V} {a b : NamedAttestation V}
    {ta tb : Time} (ha : rho.emits S v (Object.attest a) ta)
    (hb : rho.emits S v (Object.attest b) tb) :
    Protocol.e2Fields a.erase b.erase = false := by
  cases hpa : a.erase.height_pair with
  | empty => simp [Protocol.e2Fields, hpa]
  | timeout h => simp [Protocol.e2Fields, hpa]
  | target h T =>
      cases hpb : b.erase.height_pair with
      | empty => simp [Protocol.e2Fields, hpa, hpb]
      | timeout g => simp [Protocol.e2Fields, hpa, hpb]
      | target g U =>
          by_cases hgh : h = g
          · subst g
            have hTU : T = U := emitted_targets_eq_of_admissibleCore S adm ha hb
              (Or.inl hpa) (Or.inl hpb)
            simp [Protocol.e2Fields, hpa, hpb, hTU]
          · simp [Protocol.e2Fields, hpa, hpb, hgh]






end HealingSurface
end Proofs
end DecoupledConsensusModel

end
