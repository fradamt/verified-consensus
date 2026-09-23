module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.ModelVocabulary.Execution.NamedRun
public import DecoupledConsensusProofs.Protocol.Grades.NamedNode
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotone
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges

@[expose] public section

/-! Basic facts for the one named event fold. Local store, record and clipping
invariants hold from fixed initialization. Time-prefix equations use explicit
list order and uniqueness, not a supplied execution view or receipt premise. -/
namespace DecoupledConsensusModel.Proofs.NamedRuntime
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- These are local predicates with checked initial and transition producers. -/
def NodeInvariant (S : Setup V) (n : NamedNodeState V) : Prop :=
  Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st ∧
  NamedTickRecord.Invariant n.record ∧ DecoupledConsensusModel.Protocol.clipCache n.st.core.F n.cache = n.cache

theorem initial_invariant (S : Setup V) (v : V) : NodeInvariant S (NamedWorld.init v) :=
  ⟨(NamedNode.initial_invariants S).1, (NamedNode.initial_invariants S).2,
    NamedNode.cache_clipped_initial⟩

private theorem node_tick_invariant (S : Setup V) (v : V) (n : NamedNodeState V)
    (t : Time) (h : NodeInvariant S n) :
    NodeInvariant S (Execution.NamedNode.tick S v n t).1 :=
  ⟨NamedNode.confirmation_invariant_tick S v n t h.1,
    NamedNode.record_invariant_tick S v n t h.2.1, NamedNode.cache_clipped_tick S v n t⟩

private theorem node_process_invariant (S : Setup V) (n : NamedNodeState V)
    (o : NamedObject V) (h : NodeInvariant S n) :
    NodeInvariant S (Execution.NamedNode.process S n o) :=
  ⟨(NamedNode.invariants_process S n o h.1 h.2.1).1,
    (NamedNode.invariants_process S n o h.1 h.2.1).2, NamedNode.cache_clipped_process S n o⟩

theorem step_tick (S : Setup V) (w : NamedWorld V) (v : V) (t : Time) :
    NamedWorld.step S w (.tick v t) v = (Execution.NamedNode.tick S v (w v) t).1 := by
  simp only [NamedWorld.step, Function.update_self]

theorem step_deliver (S : Setup V) (w : NamedWorld V) (v : V) (o : NamedObject V) (t : Time) :
    NamedWorld.step S w (.deliver v o t) v = Execution.NamedNode.process S (w v) o := by
  simp only [NamedWorld.step, Function.update_self]

theorem step_other (S : Setup V) (w : NamedWorld V) (e : NamedEvent V) (v : V)
    (h : v ≠ e.node) : NamedWorld.step S w e v = w v := by
  cases e <;> exact Function.update_of_ne h _ _

private theorem step_invariant (S : Setup V) (w : NamedWorld V) (e : NamedEvent V)
    (h : ∀ v, NodeInvariant S (w v)) : ∀ v, NodeInvariant S (NamedWorld.step S w e v) := by
  intro v
  by_cases hv : v = e.node
  · cases e with
    | tick u t =>
      change v = u at hv
      subst v
      rw [step_tick]
      exact node_tick_invariant S u (w u) t (h u)
    | deliver u o t =>
      change v = u at hv
      subst v
      rw [step_deliver]
      exact node_process_invariant S (w u) o (h u)
  · rw [step_other S w e v hv]
    exact h v

private theorem fold_invariant (S : Setup V) (events : List (NamedEvent V)) :
    ∀ w : NamedWorld V, (∀ v, NodeInvariant S (w v)) →
      ∀ v, NodeInvariant S (events.foldl (NamedWorld.step S) w v) := by
  induction events with
  | nil => intro w h; exact h
  | cons e events ih =>
    intro w h
    exact ih _ (step_invariant S w e h)

theorem stateBefore_zero (S : Setup V) (rho : NamedRun V) :
    NamedRun.stateBefore S rho 0 = NamedWorld.init := rfl

theorem stateBefore_succ (S : Setup V) (rho : NamedRun V) (i : Nat) :
    NamedRun.stateBefore S rho (i + 1) =
      (rho.events[i]?.toList).foldl (NamedWorld.step S) (NamedRun.stateBefore S rho i) := by
  unfold NamedRun.stateBefore
  rw [List.take_add_one, List.foldl_append]

theorem stateBefore_tick (S : Setup V) (rho : NamedRun V) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    NamedRun.stateBefore S rho (i + 1) v =
      (Execution.NamedNode.tick S v (NamedRun.stateBefore S rho i v) t).1 := by
  rw [stateBefore_succ, hi]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, step_tick]

theorem stateBefore_deliver (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {o : NamedObject V} {t : Time}
    (hi : rho.events[i]? = some (.deliver v o t)) :
    NamedRun.stateBefore S rho (i + 1) v =
      Execution.NamedNode.process S (NamedRun.stateBefore S rho i v) o := by
  rw [stateBefore_succ, hi]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, step_deliver]

theorem stateBefore_other (S : Setup V) (rho : NamedRun V) {i : Nat} {e : NamedEvent V}
    (hi : rho.events[i]? = some e) (v : V) (hv : v ≠ e.node) :
    NamedRun.stateBefore S rho (i + 1) v = NamedRun.stateBefore S rho i v := by
  rw [stateBefore_succ, hi]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, step_other S _ e v hv]

theorem stateBefore_invariants (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    NodeInvariant S (NamedRun.stateBefore S rho i v) :=
  fold_invariant S (rho.events.take i) NamedWorld.init (initial_invariant S) v

theorem stateBeforeTime_invariants (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    NodeInvariant S (NamedRun.stateBeforeTime S rho t v) :=
  fold_invariant S _ NamedWorld.init (initial_invariant S) v

theorem readAt_invariants (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    NodeInvariant S (NamedRun.readAt S rho t v) :=
  fold_invariant S _ NamedWorld.init (initial_invariant S) v






omit [DecidableEq V] [Fintype V] in
theorem objects_of_delivery (rho : NamedRun V) {i : Nat} {v : V} {o : NamedObject V} {t : Time}
    (hi : rho.events[i]? = some (.deliver v o t)) : o ∈ NamedRun.objects rho := by
  exact List.mem_filterMap.mpr ⟨.deliver v o t, List.mem_of_getElem? hi, rfl⟩

theorem directBlock_of_delivery (S : Setup V) (rho : NamedRun V)
    {i : Nat} {v : V} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (.deliver v (.block B) t)) :
    NamedRun.directBlockInRun S rho B := Or.inl (objects_of_delivery rho hi)

theorem directBlock_of_prefix (S : Setup V) (rho : NamedRun V) {v : V}
    (hv : v ∈ rho.honest) (i : Nat) {B : NamedBlock V}
    (hB : B ∈ (NamedRun.stateBefore S rho i v).st.bodies) :
    NamedRun.directBlockInRun S rho B := Or.inr ⟨v, hv, i, hB⟩

omit [Fintype V] in
private theorem named_preceq_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

omit [Fintype V] in
private theorem named_preceq_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) : NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
    have hB : B = .genesis := by simpa [NamedBlock.Preceq, NamedBlock.preceq] using hBC
    simpa only [← hB] using hAB
  | node p s root gf support rows proposer ih =>
    have hcases : B = .node p s root gf support rows proposer ∨ NamedBlock.Preceq B p := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] using hBC
    rcases hcases with hEq | hParent
    · simpa only [← hEq] using hAB
    · change (decide (A = .node p s root gf support rows proposer) ||
        NamedBlock.preceq A p) = true
      simp only [Bool.or_eq_true]
      exact Or.inr (ih hParent)

theorem blockInRun_of_direct (S : Setup V) (rho : NamedRun V) {B : NamedBlock V}
    (h : NamedRun.directBlockInRun S rho B) : NamedRun.blockInRun S rho B :=
  ⟨B, h, named_preceq_self B⟩

theorem blockInRun_of_ancestor (S : Setup V) (rho : NamedRun V) {A B : NamedBlock V}
    (hB : NamedRun.blockInRun S rho B) (hAB : NamedBlock.Preceq A B) :
    NamedRun.blockInRun S rho A := by
  obtain ⟨C, hC, hBC⟩ := hB
  exact ⟨C, hC, named_preceq_trans hAB hBC⟩



private theorem step_F_mono (S : Setup V) (w : NamedWorld V) (e : NamedEvent V) (v : V) :
    Block.Preceq (w v).st.core.F (NamedWorld.step S w e v).st.core.F := by
  by_cases hv : v = e.node
  · cases e with
    | tick u t =>
      change v = u at hv
      subst v
      rw [step_tick]
      exact NamedFinalityMonotone.node_tick_F S u (w u) t
    | deliver u o t =>
      change v = u at hv
      subst v
      rw [step_deliver]
      exact NamedFinalityMonotone.node_process_F S (w u) o
  · rw [step_other S w e v hv]
    exact Block.preceq_self _

theorem stateBefore_F_mono (S : Setup V) (rho : NamedRun V) (v : V)
    {i j : Nat} (hij : i ≤ j) :
    Block.Preceq (NamedRun.stateBefore S rho i v).st.core.F
      (NamedRun.stateBefore S rho j v).st.core.F := by
  induction j, hij using Nat.le_induction with
  | base => exact Block.preceq_self _
  | succ j hij ih =>
    apply Block.preceq_trans ih
    rw [stateBefore_succ]
    cases he : rho.events[j]? with
    | none => exact Block.preceq_self _
    | some e => exact step_F_mono S _ e v

/-- The clock reads only the local tick or the preceding local clock. -/
theorem step_clock_eq (S : Setup V) (w : NamedWorld V) (e : NamedEvent V) (v : V) :
    (NamedWorld.step S w e v).st.core.t =
      match e with
      | .tick u t => if v = u then t else (w v).st.core.t
      | .deliver _ _ _ => (w v).st.core.t := by
  cases e with
  | tick u t =>
    dsimp only
    by_cases hv : v = u
    · subst v
      simp only [step_tick]
      exact (Proofs.NamedNode.tick_clock S u (w u) t).1
    · rw [step_other S w (.tick u t) v hv, if_neg hv]
  | deliver u o t =>
    by_cases hv : v = u
    · subst v
      rw [step_deliver]
      exact (Proofs.NamedNode.process_clock S (w u) o).1
    · exact congrArg (fun n : NamedNodeState V => n.st.core.t)
        (step_other S w (.deliver u o t) v hv)

omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_mem_take (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i : Nat} {f : NamedEvent V} (hf : rho.events[i]? = some f)
    (e : NamedEvent V) (he : e ∈ rho.events.take i) : e.time ≤ f.time := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hf
  have hsplit : rho.events = rho.events.take i ++ f :: rho.events.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i rho.events]
    rw [List.drop_eq_getElem_cons hi, hget]
  have hp := hsorted
  rw [hsplit] at hp
  exact time_le_of_key_le ((List.pairwise_append.mp hp).2.2 e he f (List.mem_cons_self ..))

private theorem fold_clock_le (S : Setup V) (bound : Time) :
    ∀ (events : List (NamedEvent V)) (w : NamedWorld V),
      (∀ v, (w v).st.core.t ≤ bound) → (∀ e ∈ events, e.time ≤ bound) →
      ∀ v, (events.foldl (NamedWorld.step S) w v).st.core.t ≤ bound := by
  intro events
  induction events with
  | nil => intro w h _; exact h
  | cons e events ih =>
    intro w h ht
    apply ih
    · intro v
      rw [step_clock_eq]
      cases e with
      | tick u t =>
        dsimp only
        split_ifs
        · exact ht _ (List.mem_cons_self ..)
        · exact h v
      | deliver u o t => exact h v
    · intro f hf
      exact ht f (List.mem_cons_of_mem _ hf)

theorem stateBefore_clock_le_event (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i : Nat} {e : NamedEvent V} (hi : rho.events[i]? = some e) (hnonneg : 0 ≤ e.time) (v : V) :
    (NamedRun.stateBefore S rho i v).st.core.t ≤ e.time := by
  apply fold_clock_le S e.time (rho.events.take i) NamedWorld.init
  · intro u
    exact hnonneg
  · exact time_le_of_mem_take rho hsorted hi

theorem stateBefore_clock_mono (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (hnonneg : ∀ e ∈ rho.events, 0 ≤ e.time) (v : V) {i j : Nat} (hij : i ≤ j) :
    (NamedRun.stateBefore S rho i v).st.core.t ≤ (NamedRun.stateBefore S rho j v).st.core.t := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    apply ih.trans
    rw [stateBefore_succ]
    cases he : rho.events[j]? with
    | none => exact le_rfl
    | some e =>
      change (NamedRun.stateBefore S rho j v).st.core.t ≤
        (NamedWorld.step S (NamedRun.stateBefore S rho j) e v).st.core.t
      rw [step_clock_eq]
      cases e with
      | tick u t =>
        dsimp only
        split_ifs
        · exact stateBefore_clock_le_event S rho hsorted he
            (hnonneg _ (List.mem_of_getElem? he)) v
        · exact le_rfl
      | deliver u o t => exact le_rfl

theorem tick_time_le_clock (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (hnonneg : ∀ e ∈ rho.events, 0 ≤ e.time) {i j : Nat} {v : V} {t : Time}
    (hj : rho.events[j]? = some (.tick v t)) (hji : j < i) :
    t ≤ (NamedRun.stateBefore S rho i v).st.core.t := by
  have h := stateBefore_clock_mono S rho hsorted hnonneg v (Nat.succ_le_of_lt hji)
  rw [stateBefore_tick S rho hj] at h
  simpa only [(Proofs.NamedNode.tick_clock S v (NamedRun.stateBefore S rho j v) t).1] using h

open NamedRun

/-- An interval with no event at v leaves its actual runtime node unchanged. -/
theorem stateBefore_eq_of_ne (S : Setup V) (rho : NamedRun V)
    (v : V) {m : Nat} : ∀ n : Nat, m ≤ n →
      (∀ j e, m ≤ j → j < n → rho.events[j]? = some e → e.node ≠ v) →
      stateBefore S rho n v = stateBefore S rho m v := by
  intro n
  induction n with
  | zero => intro hm _; rw [Nat.le_zero.mp hm]
  | succ n ih =>
    intro hm h
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
      rw [← ih hmn (fun j e h1 h2 h3 => h j e h1 (Nat.lt_succ_of_lt h2) h3)]
      unfold stateBefore
      rw [List.take_add_one, List.foldl_append]
      cases hn : rho.events[n]? with
      | none => simp
      | some e =>
        have hne : e.node ≠ v := h n e hmn (Nat.lt_succ_self n) hn
        simp only [Option.toList, List.foldl_cons, List.foldl_nil]
        cases e with
        | tick u t =>
          simp only [NamedWorld.step]
          exact Function.update_of_ne (Ne.symm hne) _ _
        | deliver u o t =>
          simp only [NamedWorld.step]
          exact Function.update_of_ne (Ne.symm hne) _ _
    · rw [Nat.le_antisymm hm hge]

omit [DecidableEq V] [Fintype V] in
private theorem filter_eq_take_sorted (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (p : NamedEvent V → Bool)
    (hdown : ∀ e f : NamedEvent V, e.key ≤ f.key → p f = true → p e = true) :
    rho.events.filter p = rho.events.take (rho.events.filter p).length := by
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
private theorem filter_false_of_index_ge_sorted (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (p : NamedEvent V → Bool)
    (hdown : ∀ e f : NamedEvent V, e.key ≤ f.key → p f = true → p e = true)
    {j : Nat} {e : NamedEvent V} (hj : (rho.events.filter p).length ≤ j)
    (hget : rho.events[j]? = some e) : p e = false := by
  set n := (rho.events.filter p).length with hn
  have hfilt : rho.events.filter p = rho.events.take n :=
    filter_eq_take_sorted rho hsorted p hdown
  have hdropnil : (rho.events.drop n).filter p = [] := by
    have h1 : rho.events.filter p =
        (rho.events.take n).filter p ++ (rho.events.drop n).filter p := by
      conv_lhs => rw [← List.take_append_drop n rho.events]
      rw [List.filter_append]
    have h2 : (rho.events.take n).filter p = rho.events.take n := by
      conv_lhs => rw [← hfilt]
      rw [List.filter_filter]
      simp only [Bool.and_self]
      exact hfilt
    rw [h2, ← hfilt] at h1
    exact List.self_eq_append_right.mp h1
  have hmem : e ∈ rho.events.drop n := by
    refine List.mem_of_getElem? (i := j - n) ?_
    rw [List.getElem?_drop]
    have hjn : n + (j - n) = j := by omega
    rw [hjn]
    exact hget
  by_contra hcon
  have hin : e ∈ (rho.events.drop n).filter p :=
    List.mem_filter.mpr ⟨hmem, by simpa using hcon⟩
  rw [hdropnil] at hin
  simp at hin

omit [DecidableEq V] [Fintype V] in
private theorem downward_lt (t : Time) :
    ∀ e f : NamedEvent V, e.key ≤ f.key → decide (f.time < t) = true →
      decide (e.time < t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact lt_of_le_of_lt (time_le_of_key_le hk) hf

/-- An actual witnessed tick reads the strict pre-time NamedNodeState. Sorting
excludes same-time deliveries before the tick; uniqueness excludes another
same-node tick. Earlier same-time ticks are at other nodes and leave this one
unchanged. This result requires neither tick existence nor honest participation. -/
theorem tick_prefix_eq_strict (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (hnodup : rho.events.Nodup) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    stateBefore S rho i v = stateBeforeTime S rho t v := by
  have hfilter := filter_eq_take_sorted rho hsorted _ (downward_lt t)
  have hni : (rho.events.filter (fun e => decide (e.time < t))).length ≤ i := by
    by_contra hcon
    have hlt : i < (rho.events.filter (fun e => decide (e.time < t))).length :=
      Nat.lt_of_not_ge hcon
    have hmem : NamedEvent.tick v t ∈ rho.events.filter (fun e => decide (e.time < t)) := by
      rw [hfilter]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    have hp := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, NamedEvent.time] at hp
    exact lt_irrefl _ hp
  have hread : stateBeforeTime S rho t =
      stateBefore S rho (rho.events.filter (fun e => decide (e.time < t))).length := by
    exact congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init) hfilter
  rw [hread]
  refine stateBefore_eq_of_ne S rho v i hni ?_
  intro j e hj hji hget
  have hlow : t ≤ e.time := by
    have hf := filter_false_of_index_ge_sorted rho hsorted _ (downward_lt t) hj hget
    simpa using hf
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hkey : NamedEvent.key e ≤ NamedEvent.key (NamedEvent.tick v t) := by
    have hp := (List.pairwise_iff_getElem.mp hsorted) j i hjl hil hji
    rw [hje, hie] at hp
    exact hp
  have hteq : NamedEvent.time e = t := le_antisymm (time_le_of_key_le hkey) hlow
  intro hnode
  have heq : e = NamedEvent.tick v t := by
    cases e with
    | tick u t' =>
      simp only [NamedEvent.node] at hnode
      simp only [NamedEvent.time] at hteq
      rw [hnode, hteq]
    | deliver u o t' =>
      exfalso
      simp only [NamedEvent.time] at hteq
      subst hteq
      simp [NamedEvent.key, NamedEvent.time, NamedEvent.phase, Prod.Lex.toLex_le_toLex] at hkey
  have hev : rho.events[j] = rho.events[i] := by rw [hje, hie, heq]
  have hij : j = i := (List.Nodup.getElem_inj_iff hnodup).mp hev
  omega

/-- A sorted strict read is one actual named prefix, with every event earlier. -/
theorem stateBeforeTime_eq_prefix (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    ∃ n, NamedRun.stateBeforeTime S rho t = NamedRun.stateBefore S rho n ∧
      ∀ j e, j < n → rho.events[j]? = some e → e.time < t := by
  let p : NamedEvent V → Bool := fun e => decide (e.time < t)
  have hf := filter_eq_take_sorted rho hsorted p (downward_lt t)
  refine ⟨(rho.events.filter p).length, ?_, ?_⟩
  · exact congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init) hf
  · intro j e hj he
    have hm : e ∈ rho.events.filter p := by
      rw [hf]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact he)
    simpa only [p, decide_eq_true_eq] using (List.mem_filter.mp hm).2

theorem readAt_eq_prefix (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    ∃ n, NamedRun.readAt S rho t = NamedRun.stateBefore S rho n ∧
      ∀ j e, j < n → rho.events[j]? = some e → e.time ≤ t := by
  let p : NamedEvent V → Bool := fun e => decide (e.time ≤ t)
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key → p f = true → p e = true := by
    intro e f hk ht
    simp only [p, decide_eq_true_eq] at ht ⊢
    exact (time_le_of_key_le hk).trans ht
  have hf := filter_eq_take_sorted rho hsorted p hdown
  refine ⟨(rho.events.filter p).length, ?_, ?_⟩
  · exact congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init) hf
  · intro j e hj he
    have hm : e ∈ rho.events.filter p := by
      rw [hf]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact he)
    simpa only [p, decide_eq_true_eq] using (List.mem_filter.mp hm).2

#print axioms initial_invariant
#print axioms step_tick
#print axioms step_deliver
#print axioms step_other
#print axioms stateBefore_zero
#print axioms stateBefore_succ
#print axioms stateBefore_tick
#print axioms stateBefore_deliver
#print axioms stateBefore_other
#print axioms stateBefore_invariants
#print axioms stateBeforeTime_invariants
#print axioms readAt_invariants
#print axioms objects_of_delivery
#print axioms directBlock_of_delivery
#print axioms directBlock_of_prefix
#print axioms blockInRun_of_direct
#print axioms blockInRun_of_ancestor
#print axioms stateBefore_F_mono
#print axioms step_clock_eq
#print axioms stateBefore_clock_le_event
#print axioms stateBefore_clock_mono
#print axioms tick_time_le_clock
#print axioms stateBefore_eq_of_ne
#print axioms tick_prefix_eq_strict
#print axioms stateBeforeTime_eq_prefix
#print axioms readAt_eq_prefix
end DecoupledConsensusModel.Proofs.NamedRuntime

end
