module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordTargetHistory

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record create_attestation height_pair own_lock record_attestation)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The timeout writer -/

omit [DecidableEq V] [Fintype V] in
/-- A true timeout entry remains true after `record_attestation`. -/
theorem record_attestation_timeout_mono {Lambda : Record}
    (a : CombinedAttestation V) {h : Height}
    (htrue : Lambda.timeout h = true) :
    (record_attestation Lambda a).timeout h = true := by
  simp only [record_attestation]
  cases a.finality_pair <;> cases a.height_pair <;>
    simp_all [Record.with_lock, Record.with_timeout, Record.with_target]
  all_goals split <;> simp_all

omit [DecidableEq V] [Fintype V] in
/-- If `record_attestation` changes a timeout entry from false to true, the
attestation contains the matching timeout height pair. -/
theorem record_attestation_timeout_introduced {Lambda : Record}
    {a : CombinedAttestation V} {h : Height}
    (hpre : Lambda.timeout h = false)
    (hpost : (record_attestation Lambda a).timeout h = true) :
    a.height_pair = HeightPair.timeout h := by
  simp only [record_attestation] at hpost
  cases hfp : a.finality_pair <;> cases hhp : a.height_pair <;>
    simp_all [Record.with_lock, Record.with_timeout, Record.with_target]
  all_goals split at hpost <;> simp_all



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

/-! ## 2. One tick and the run prefix -/

/-- A true timeout entry survives one protocol tick. -/
theorem timeout_mono_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height} (hs : n.Λ.legacy.timeout h = true) :
    (on_tick_emit S v n t).1.record.legacy.timeout h = true := by
  obtain ⟨st3, gc, pre, -, hcase⟩ := on_tick_emit_attest_shape S v n t
  rcases hcase with ⟨hrec, -⟩ | ⟨hrec, -⟩
  · rw [hrec]; exact hs
  · rw [hrec]
    obtain ⟨r, c, f, h_j, J, h_F, hleg, -⟩ :=
      round_action_shape gc S.E S.hc (S.node v) st3.core.toHealing n.Λ
    rw [hleg]
    simp only [create_attestation]
    exact record_attestation_timeout_mono _ hs

/-- If one tick introduces a timeout entry, that tick emits the matching
timeout-pair attestation. -/
theorem on_tick_emit_timeout_introduced (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {h : Height}
    (hpre : n.Λ.legacy.timeout h = false)
    (hpost : (on_tick_emit S v n t).1.record.legacy.timeout h = true) :
    ∃ a : NamedAttestation V,
      Object.attest a ∈ (on_tick_emit S v n t).2 ∧
        a.erase.height_pair = HeightPair.timeout h := by
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
          (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).1.timeout h =
            true := by
        rw [← hleg, ← hrec]
        exact hpost
      have hfold :
          (record_attestation n.Λ.legacy
              (create_attestation n.Λ.legacy (S.node v).val_index r c f h_j J h_F).2).timeout h =
            true := by
        simpa only [create_attestation] using hcreated
      exact record_attestation_timeout_introduced hpre hfold

/-- Timeout entries only grow along an execution prefix. -/
theorem stateBefore_timeout_mono (S : Setup V) (rho : Run V) (v : V)
    {h : Height} {i : Nat} :
    ∀ j : Nat, i ≤ j → (rho.stateBefore S i v).Λ.legacy.timeout h = true →
      (rho.stateBefore S j v).Λ.legacy.timeout h = true := by
  intro j
  induction j with
  | zero =>
      intro hj
      rw [Nat.le_zero.mp hj]
      exact id
  | succ j ih =>
      intro hj htrue
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · have hprev := ih (Nat.lt_succ_iff.mp hlt) htrue
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
                simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                  NamedWorld.step, Function.update_self]
                exact timeout_mono_on_tick_emit S v _ t hprev
              · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                  NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
                exact hprev
          | deliver u o t =>
              by_cases huv : u = v
              · subst u
                simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                  NamedWorld.step, Function.update_self]
                rw [process_record]
                exact hprev
              · simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                  NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
                exact hprev
      · exact (Nat.le_antisymm hj hge) ▸ htrue

/-- Every true timeout entry at prefix `n` came from a strictly earlier local
tick that emitted the matching timeout pair. -/
theorem recordTimeout_emission_before (S : Setup V) (rho : Run V) (v : V) :
    ∀ (n : Nat) {h : Height},
      (rho.stateBefore S n v).Λ.legacy.timeout h = true →
        ∃ (i : Nat), i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
          rho.events[i]? = some (Event.tick v t) ∧
            Object.attest a ∈ (on_tick_emit S v (rho.stateBefore S i v) t).2 ∧
            a.erase.height_pair = HeightPair.timeout h := by
  intro n
  induction n with
  | zero =>
      intro h htimeout
      exact absurd htimeout (by
        simp [Run.stateBefore, NamedRun.stateBefore, List.take_zero, List.foldl_nil,
          NamedWorld.init, NamedNode.initial, Protocol.NamedRecord.initial,
          Record.initial])
  | succ n ih =>
      intro h htimeout
      cases hpre : (rho.stateBefore S n v).Λ.legacy.timeout h with
      | true =>
          obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ := ih hpre
          exact ⟨i, Nat.lt_succ_of_lt hi, t, a, hevent, hemitted, hpair⟩
      | false =>
          have hstep : rho.stateBefore S (n + 1) =
              (rho.events[n]?.toList).foldl (World.step S)
                (rho.stateBefore S n) := by
            unfold Run.stateBefore NamedRun.stateBefore
            rw [List.take_add_one, List.foldl_append]
          rcases hevent : rho.events[n]? with _ | e
          · rw [hstep, hevent] at htimeout
            simp only [Option.toList, List.foldl_nil] at htimeout
            exact absurd htimeout (by rw [hpre]; simp)
          · cases e with
            | tick u t =>
                by_cases huv : u = v
                · subst u
                  have hpost :
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.record.legacy.timeout h =
                        true := by
                    rw [← stateBefore_succ_record S rho hevent]
                    exact htimeout
                  obtain ⟨a, hemitted, hpair⟩ :=
                    on_tick_emit_timeout_introduced S v (rho.stateBefore S n v) t hpre hpost
                  exact ⟨n, Nat.lt_succ_self n, t, a, hevent, hemitted, hpair⟩
                · rw [hstep, hevent] at htimeout
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                    World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)] at htimeout
                  exact absurd htimeout (by rw [hpre]; simp)
            | deliver u o t =>
                by_cases huv : u = v
                · subst u
                  rw [hstep, hevent] at htimeout
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                    World.step, NamedWorld.step, Function.update_self] at htimeout
                  rw [process_record] at htimeout
                  exact absurd htimeout (by rw [hpre]; simp)
                · rw [hstep, hevent] at htimeout
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                    World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)] at htimeout
                  exact absurd htimeout (by rw [hpre]; simp)

/-! ## 3. A locally unused height is fresh -/

/-- All three anti-slashing fields have their initial value at one height. -/
def RecordFreshAt (Lambda : Record) (H : Height) : Prop :=
  Lambda.target H = none ∧ Lambda.timeout H = false ∧ Lambda.lock H = none

/-- No attestation emitted by `v` before event prefix `n` has a nonempty height
pair at `H`. The statement covers both `.target H _` and `.timeout H`. -/
def NoLocalHeightPairBefore (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) (H : Height) : Prop :=
  ∀ {i : Nat} {t : Time} {a : NamedAttestation V},
    i < n →
      rho.events[i]? = some (Event.tick v t) →
      Object.attest a ∈ (on_tick_emit S v (rho.stateBefore S i v) t).2 →
      a.erase.height_pair.height? ≠ some H




/-! ## 4. Fresh timeout selection -/

omit [DecidableEq V] [Fintype V] in
/-- At a fresh height, `nu = true` selects the timeout row even when this same
attestation carries a finality pair, provided that pair is at another height. -/
theorem height_pair_timeout_of_fresh_of_finality_height_ne
    {Lambda : Record} {H : Height} {T : BlockId} {p : FinalityPair}
    (hfresh : RecordFreshAt Lambda H) (hne : p.height ≠ H) :
    height_pair Lambda (some (H, T, true)) (some p) = HeightPair.timeout H := by
  rcases hfresh with ⟨htarget, htimeout, hlock⟩
  simp [height_pair, own_lock, htimeout, hlock, htarget, hne]

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
