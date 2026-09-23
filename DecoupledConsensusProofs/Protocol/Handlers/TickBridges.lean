module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.TickReads
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Agreement
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The tick grid inverts

`slotOfTime` is floor division by `4Δ` and the four per-slot instants are
`t_s + kΔ` with `k < 4`, so each of them names its own slot. `Time` is an
`abbrev` for `Int` and `omega` does not see through it at a projection like
`E.Δ` (`docs/conventions.md`; row AG.10), so every arithmetic step goes through
an explicit `Int` helper. -/

theorem slotOfTime_add (Δ : Time) (hΔ : 0 < Δ) (s : Slot) (r : Time)
    (hr0 : 0 ≤ r) (hr : r < 4 * Δ) : slotOfTime Δ (4 * Δ * (s : Time) + r) = s := by
  have hne : (4 : Time) * Δ ≠ 0 := by
    have h : ∀ d : Int, 0 < d → (4 : Int) * d ≠ 0 := by intro d hd; omega
    exact h Δ hΔ
  unfold slotOfTime
  have hrw : 4 * Δ * (s : Time) + r = r + (s : Time) * (4 * Δ) := by ring
  rw [hrw, Int.add_mul_fdiv_right _ _ hne, Int.fdiv_eq_zero_of_lt hr0 hr, zero_add]
  simp

/-- §2.1 the proposal instant names its own slot (PROTOCOL.md#the-complete-protocol). -/
theorem slotOf_proposal_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.proposal_time E s) = s := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 0 ∧ (0 : Int) < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  have hrw : Protocol.proposal_time E s = 4 * E.Δ * (s : Time) + 0 := by
    unfold Protocol.proposal_time Env.t slotStart; ring
  rw [Env.slotOf, hrw]
  exact slotOfTime_add E.Δ E.Δ_pos s 0 h0 h1

/-- §2.1 the vote instant names its own slot (PROTOCOL.md#the-complete-protocol). -/
theorem slotOf_vote_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.vote_time E s) = s := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ d ∧ d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  exact slotOfTime_add E.Δ E.Δ_pos s E.Δ h0 h1

/-- §2.1 the support cutoff names its own slot (PROTOCOL.md#the-complete-protocol). -/
theorem slotOf_support_cutoff (E : Env V) (s : Slot) :
    E.slotOf (Protocol.support_cutoff E s) = s := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 2 * d ∧ 2 * d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  exact slotOfTime_add E.Δ E.Δ_pos s (2 * E.Δ) h0 h1

/-- §2.1 the slot-`s` evaluation happens in slot `s + 1`
(PROTOCOL.md#the-complete-protocol). -/
theorem slotOf_confirmation_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.confirmation_time E s) = s + 1 := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 2 * d ∧ 2 * d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  have hrw : Protocol.confirmation_time E s
      = 4 * E.Δ * ((s + 1 : Slot) : Time) + 2 * E.Δ := by
    unfold Protocol.confirmation_time Env.t slotStart
    push_cast
    ring
  rw [Env.slotOf, hrw]
  exact slotOfTime_add E.Δ E.Δ_pos (s + 1) (2 * E.Δ) h0 h1

/-- The three acting instants of a slot are distinct (PROTOCOL.md#the-complete-protocol). -/
theorem support_cutoff_ne_proposal_time (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≠ Protocol.proposal_time E s := by
  have h : ∀ a d : Int, 0 < d → a + 2 * d ≠ a := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos

theorem support_cutoff_ne_vote_time (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≠ Protocol.vote_time E s := by
  have h : ∀ a d : Int, 0 < d → a + 2 * d ≠ a + d := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos

theorem vote_time_ne_proposal_time (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≠ Protocol.proposal_time E s := by
  have h : ∀ a d : Int, 0 < d → a + d ≠ a := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos

theorem vote_time_ne_support_cutoff (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≠ Protocol.support_cutoff E s :=
  fun h => support_cutoff_ne_vote_time E s h.symm

/-! ## 2. `Σ.live_confirmed` has one writer

Seven lemmas in the shape of `Proofs/Execution.lean`'s clock pack: each handler
either returns its input or returns a record update that does not name the
field. -/

omit [Fintype V] in
/-- §5.2 `update_finality` does not write `Σ.live_confirmed`
(PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_live_confirmed (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).live_confirmed = st.live_confirmed := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §7.2 `on_goldfish_vote` does not write it (PROTOCOL.md#the-complete-protocol). -/
theorem on_goldfish_vote_live_confirmed (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).live_confirmed = st.live_confirmed := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- The checked runtime handler also preserves `Σ.live_confirmed`. -/
theorem on_goldfish_vote_checked_live_confirmed (E : Env V)
    (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).live_confirmed =
      st.live_confirmed := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_live_confirmed st u
  · rfl


/-- The checked carried-vote fold preserves `Σ.live_confirmed`. -/
theorem foldl_on_goldfish_vote_checked_live_confirmed (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).live_confirmed =
      st.live_confirmed := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_live_confirmed]

omit [Fintype V] in
/-- §7.2 `on_sg_vote` does not write it (PROTOCOL.md#the-complete-protocol). -/
theorem on_sg_vote_live_confirmed (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).live_confirmed = st.live_confirmed := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

/-- The general block-processing body does not write it, whatever chain state it
builds. `on_block_checked`'s lemma above is this at the compatibility builder; the named
runtime supplies `Protocol.named_transition` instead, so the argument has to
be stated at the builder rather than at one instance of it. -/
theorem on_block_using_live_confirmed (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).live_confirmed = st.live_confirmed := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    simp only [update_finality_live_confirmed,
      foldl_on_goldfish_vote_checked_live_confirmed]

/-- The carried-round guard passes the field through whichever handler it wraps. -/
theorem on_block_checked_using_live_confirmed
    (handle : Protocol.Store V → Protocol.Store V) (hc : HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (hh : ∀ st' : Protocol.Store V, (handle st').live_confirmed = st'.live_confirmed) :
    (Protocol.on_block_checked_using handle hc st B).live_confirmed =
      st.live_confirmed := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hh st
  · rfl

/-! ### The named store's own writers

The engine writes through `Protocol.NamedStore`, so each core lemma above needs
its named wrapper. `admit_row` is the one the tick survey singled out: at a
round-action time the scheduler runs the attestation duty **after** the
confirmation duty in the same tick, and `attest_with` ends in `admit_row`, so the
one-writer argument for `Σ.live_confirmed` has to cover that writer too. It does,
by the same route as `on_sg_vote_live_confirmed` — `admit_row` decides admission
with `on_sg_vote` and then only appends to `Σ.sg_rows[·]`. -/

/-- **The named row admission does not write `Σ.live_confirmed`** — the new
obligation of the named scheduler's same-tick attestation. -/
theorem admit_row_live_confirmed (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).live_confirmed =
      st.live_confirmed := by
  simp only [Protocol.NamedAdmission.admit_row]
  split <;> exact on_sg_vote_live_confirmed _ _ _


/-- Nor does a carried batch of them. -/
theorem admit_rows_live_confirmed (hc : HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      (Protocol.NamedAdmission.admit_rows hc st rows).live_confirmed =
        st.live_confirmed := by
  intro rows
  induction rows with
  | nil => intro st; rfl
  | cons a l ih =>
      intro st
      have h : Protocol.NamedAdmission.admit_rows hc st (a :: l) =
          Protocol.NamedAdmission.admit_rows hc
            (Protocol.NamedAdmission.admit_row hc st a) l := rfl
      rw [h, ih, admit_row_live_confirmed]

/-- The named block core does not write it: `commitBlock` retains the shared
handler's store and only decides whether the signed body is kept. -/
theorem process_block_core_live_confirmed (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).live_confirmed =
      st.live_confirmed := by
  simp only [Protocol.NamedStore.process_block_core]
  split
  · rfl
  · simp only [Protocol.NamedStore.commitBlock]
    split <;>
      exact on_block_checked_using_live_confirmed _ hc st.core B.erase
        (fun st' => on_block_using_live_confirmed E st' B.erase _)

/-- Nor does the selected named block handler. -/
theorem on_block_with_live_confirmed (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).live_confirmed =
      st.live_confirmed := by
  have hcore := process_block_core_live_confirmed E hc cfg st B
  cases adm with
  | alsoCarried =>
      show (if B ∉ st.bodies ∧
          B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies then
            Protocol.NamedAdmission.admit_rows hc
              (Protocol.NamedStore.process_block_core E hc cfg st B) B.attestations
          else Protocol.NamedStore.process_block_core E hc cfg st B).live_confirmed =
        st.live_confirmed
      split_ifs
      · rw [admit_rows_live_confirmed]
        exact hcore
      · exact hcore

/-- Nor does the named GF duty: the contract enters only through the head it
votes for, and the write is the checked vote handler. -/
theorem goldfish_vote_with_live_confirmed (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.live_confirmed =
      st.live_confirmed := by
  simp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split
  · exact on_goldfish_vote_checked_live_confirmed E _ _
  · rfl

/-- Nor does the named proposal duty. -/
theorem propose_block_with_live_confirmed (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.live_confirmed =
      st.live_confirmed := by
  simp only [Protocol.NamedDuties.propose_block_with]
  split
  · rfl
  · exact on_block_with_live_confirmed .alsoCarried E hc cfg st _

/-- Nor does the named round action. -/
theorem attest_with_live_confirmed (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).1.live_confirmed =
      st.live_confirmed :=
  admit_row_live_confirmed hc st _

/-- **No delivery moves `Σ.live_confirmed`** (PROTOCOL.md#the-complete-protocol). The field
is the confirmation walk's output and stays that way until the next evaluation. -/
theorem process_live_confirmed (S : Setup V) (n : NodeState V) (o : Object V) :
    (n.process S o).st.live_confirmed = n.st.live_confirmed := by
  cases o with
  | block B => exact on_block_with_live_confirmed .alsoCarried S.E S.hc S.cfg _ B
  | gfVote u => exact on_goldfish_vote_checked_live_confirmed S.E _ _
  | attest a => exact admit_row_live_confirmed S.hc _ a

/-! ## 3. The reads the duties perform

`on_tick_emit` is `NamedNode.tick`: it completes the phase cache, then runs the
shared `TickScheduler` over the named duties with the contract that cache
determines. The clock branch is `NamedStore.setClock`, so the state the first
duty of the tick receives is exactly `NamedActionReads.confirmationReadFrom`,
cache included — which is why the statements above are phrased over the prepared
read rather than over a restamped store. -/

/-- **The confirmation branch's output is the tick's `Σ.live_confirmed`**
(PROTOCOL.md#the-complete-protocol). At `t_s + 2Δ` the proposal and vote branches are shut,
so the evaluation reads the tick's own prepared read; the attest branch may
follow it in the same tick, and `admit_row` leaves the field alone. -/
theorem on_tick_emit_confirmation (S : Setup V) (v : V) (n : NodeState V)
    (s : Slot) (hs : 0 < s) :
    (on_tick_emit S v n (Protocol.support_cutoff S.E s)).1.st.live_confirmed =
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S n
            (Protocol.support_cutoff S.E s)).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.support_cutoff S.E s)).st (s - 1)).live_confirmed := by
  have hslot : S.E.slotOf (Protocol.support_cutoff S.E s) = s := slotOf_support_cutoff S.E s
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    support_cutoff_ne_proposal_time S.E s, support_cutoff_ne_vote_time S.E s, hs,
    and_true, and_false, false_and, if_true, if_false,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock]
  split
  · exact attest_with_live_confirmed _ S.E S.hc _ _ _
  · rfl

/-- **Every other tick leaves `Σ.live_confirmed` alone.** The confirmation branch
is the only writer, so a tick at an instant that is not a support cutoff of its
own slot reports the field it started with. -/
theorem on_tick_emit_live_confirmed_of_ne (S : Setup V) (v : V) (n : NodeState V)
    (t : Time)
    (h : ¬ (0 < S.E.slotOf t ∧ t = Protocol.support_cutoff S.E (S.E.slotOf t))) :
    (on_tick_emit S v n t).1.st.live_confirmed = n.st.live_confirmed := by
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, if_neg h,
    apply_ite (fun p : Protocol.NamedStore V × Protocol.NamedRecord ×
      List (NamedObject V) => p.1.live_confirmed)]
  split_ifs <;>
    simp only [attest_with_live_confirmed, goldfish_vote_with_live_confirmed,
      propose_block_with_live_confirmed, Protocol.NamedStore.live_confirmed]


/-! ## 4. The prefix a tick reads

`Run.emits` is indexed by position and every statement above this layer is
indexed by time. The two agree at `v`: the events a tick of `v` at `t` has behind
it, beyond those of time `< t`, are ticks of *other* validators at `t`, and those
leave `v`'s entry alone. -/


/-- A stretch of the event list that never touches `v` does not move `v`'s
state. -/
theorem stateBefore_eq_of_ne (S : Setup V) (ρ : Run V) (v : V) {m : Nat} :
    ∀ n : Nat, m ≤ n →
      (∀ (j : Nat) (e : Event V), m ≤ j → j < n →
        ρ.events[j]? = some e → e.node ≠ v) →
      (ρ.stateBefore S n v) = (ρ.stateBefore S m v) := by
  intro n
  induction n with
  | zero => intro hm _; rw [Nat.le_zero.mp hm]
  | succ n ih =>
      intro hm h
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        rw [← ih hmn (fun j e h1 h2 h3 => h j e h1 (Nat.lt_succ_of_lt h2) h3)]
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : ρ.events[n]? with
        | none => simp
        | some e =>
            have hne : e.node ≠ v := h n e hmn (Nat.lt_succ_self n) hn
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e with
            | tick u t' =>
                simp only [NamedWorld.step]
                exact Function.update_of_ne (Ne.symm hne) _ _
            | deliver u o t' =>
                simp only [NamedWorld.step]
                exact Function.update_of_ne (Ne.symm hne) _ _
      · rw [Nat.le_antisymm hm hge]

/-- **A downward-closed filter of the event list is a prefix** — the general form
of `Proofs.Bridges.filter_eq_takeWhile_of_pairwise` this file uses twice, at `< t` and
at `≤ t`. -/
theorem filter_eq_take (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    (p : Event V → Bool)
    (hdc : ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → p f = true → p e = true) :
    ρ.events.filter p = ρ.events.take (ρ.events.filter p).length := by
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdc _ sch.sorted]
  exact List.takeWhile_prefix _

/-- Nothing at or beyond that prefix satisfies the filter. -/
theorem filter_false_of_index_ge (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    (p : Event V → Bool)
    (hdc : ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → p f = true → p e = true)
    {j : Nat} {e : Event V} (hj : (ρ.events.filter p).length ≤ j)
    (hget : ρ.events[j]? = some e) : p e = false := by
  set n := (ρ.events.filter p).length with hn
  have hfilt : ρ.events.filter p = ρ.events.take n := filter_eq_take S sch p hdc
  have hdropnil : (ρ.events.drop n).filter p = [] := by
    have h1 : ρ.events.filter p
        = (ρ.events.take n).filter p ++ (ρ.events.drop n).filter p := by
      conv_lhs => rw [← List.take_append_drop n ρ.events]
      rw [List.filter_append]
    have h2 : (ρ.events.take n).filter p = ρ.events.take n := by
      conv_lhs => rw [← hfilt]
      rw [List.filter_filter]
      simp only [Bool.and_self]
      exact hfilt
    rw [h2, ← hfilt] at h1
    exact List.self_eq_append_right.mp h1
  have hmem : e ∈ ρ.events.drop n := by
    refine List.mem_of_getElem? (i := j - n) ?_
    rw [List.getElem?_drop]
    have hjn : n + (j - n) = j := by omega
    rw [hjn]
    exact hget
  by_contra hcon
  have hin : e ∈ (ρ.events.drop n).filter p :=
    List.mem_filter.mpr ⟨hmem, by simpa using hcon⟩
  rw [hdropnil] at hin
  simp at hin

omit [DecidableEq V] [Fintype V] in
/-- The `< t` filter is downward closed along the key order. -/
theorem downward_lt (t : Time) :
    ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → decide (f.time < t) = true →
      decide (e.time < t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact lt_of_le_of_lt (Proofs.Bridges.time_le_of_key_le hk) hf

omit [DecidableEq V] [Fintype V] in
/-- The `≤ t` filter is downward closed along the key order. -/
theorem downward_le (t : Time) :
    ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → decide (f.time ≤ t) = true →
      decide (e.time ≤ t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact le_trans (Proofs.Bridges.time_le_of_key_le hk) hf

/-- `stateBeforeTime` is the prefix of the `< t` filter's length. -/
theorem stateBeforeTime_eq_take (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (t : Time) :
    ρ.stateBeforeTime S t =
      ρ.stateBefore S (ρ.events.filter (fun e => decide (e.time < t))).length := by
  unfold Run.stateBeforeTime Run.stateBefore NamedRun.stateBeforeTime NamedRun.stateBefore
  rw [← filter_eq_take S sch _ (downward_lt t)]

/-- `stateAt` is the prefix of the `≤ t` filter's length. -/
theorem stateAt_eq_take (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (t : Time) :
    NamedRun.readAt S ρ t =
      ρ.stateBefore S (ρ.events.filter (fun e => decide (e.time ≤ t))).length := by
  unfold Run.stateBefore NamedRun.readAt NamedRun.stateBefore
  rw [← filter_eq_take S sch _ (downward_le t)]

/-- Nothing at or beyond the `< t` prefix happens before `t`. -/
theorem le_time_of_index_ge (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {t : Time} {j : Nat} {e : Event V}
    (hj : (ρ.events.filter (fun e => decide (e.time < t))).length ≤ j)
    (hget : ρ.events[j]? = some e) : t ≤ e.time := by
  have h := filter_false_of_index_ge S sch _ (downward_lt t) hj hget
  simpa using h

/-- **The prefix a tick reads is the store immediately before its instant**
(PROTOCOL.md#the-complete-protocol). Everything strictly earlier is behind it, and
the only events that can sit between are ticks of other validators at the same
instant: the same-instant rule puts every delivery of `t` after the tick, and
`nodup` rules out a second tick of `v` at `t`.

This is what lets the residuals below be stated at `ρ.storeBeforeTime S v t`
rather than at an event index. -/
theorem stateBefore_tick_eq_stateBeforeTime (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {i : Nat} {v : V} {t : Time}
    (hi : ρ.events[i]? = some (Event.tick v t)) :
    ρ.stateBefore S i v = ρ.stateBeforeTime S t v := by
  have hni : (ρ.events.filter (fun e => decide (e.time < t))).length ≤ i := by
    by_contra hcon
    have hlt : i < (ρ.events.filter (fun e => decide (e.time < t))).length :=
      Nat.lt_of_not_ge hcon
    have hmem : Event.tick v t ∈ ρ.events.filter (fun e => decide (e.time < t)) := by
      rw [filter_eq_take S sch _ (downward_lt t)]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    have hp := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, NamedEvent.time] at hp
    exact lt_irrefl _ hp
  rw [stateBeforeTime_eq_take S sch t]
  refine stateBefore_eq_of_ne S ρ v i hni ?_
  intro j e hj hji hget
  have hlow : t ≤ e.time := le_time_of_index_ge S sch hj hget
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hkey : NamedEvent.key e ≤ NamedEvent.key (Event.tick v t) := by
    have hp := (List.pairwise_iff_getElem.mp sch.sorted) j i hjl hil hji
    rw [hje, hie] at hp
    exact hp
  have hteq : e.time = t := le_antisymm (Proofs.Bridges.time_le_of_key_le hkey) hlow
  intro hnode
  have heq : e = Event.tick v t := by
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
  have hev : ρ.events[j] = ρ.events[i] := by rw [hje, hie, heq]
  have hij : j = i := (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp hev
  omega

/-! ## 5. The emission bridge, and `VoteTick`

`tick_total` says an honest node ticks at every public time, §4 says which store
that tick reads, and `on_tick_emit`'s vote branch says which object it emits. What
is left of `VoteTick` is the alignment of the store — the agreement argument's
own premise, and not an execution fact. -/

/-- Slot instants are nonnegative, so the tick schedule reaches them. -/
theorem proposal_time_nonneg (E : Env V) (s : Slot) : 0 ≤ Protocol.proposal_time E s := by
  have h4 : (0 : Time) ≤ 4 * E.Δ := by
    have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 4 * d := by intro d hd; omega
    exact h E.Δ E.Δ_pos
  unfold Protocol.proposal_time Env.t slotStart
  exact Int.mul_nonneg h4 (Int.natCast_nonneg s)

theorem vote_time_nonneg (E : Env V) (s : Slot) : 0 ≤ Protocol.vote_time E s := by
  have h := proposal_time_nonneg E s
  have key : ∀ a d : Int, 0 ≤ a → 0 < d → 0 ≤ a + d := by intro a d h1 h2; omega
  exact key _ E.Δ h E.Δ_pos

theorem confirmation_time_nonneg (E : Env V) (s : Slot) :
    0 ≤ Protocol.confirmation_time E s := by
  have h := proposal_time_nonneg E s
  have key : ∀ a d : Int, 0 ≤ a → 0 < d → 0 ≤ a + 6 * d := by intro a d h1 h2; omega
  exact key _ E.Δ h E.Δ_pos

theorem publicTime_vote_time (S : Setup V) (s : Slot) :
    PublicTime S (Protocol.vote_time S.E s) :=
  (publicTime_iff S _).mpr ⟨s, Or.inr (Or.inl rfl)⟩

theorem publicTime_confirmation_time (S : Setup V) (s : Slot) :
    PublicTime S (Protocol.confirmation_time S.E s) :=
  (publicTime_iff S _).mpr ⟨s + 1, Or.inr (Or.inr (Or.inl
    (Protocol.confirmation_time_eq_support_cutoff_succ S.E s)))⟩

/-- **Everything an honest node's tick emits is a `Run.emits`** (design §2.3;
PROTOCOL.md#the-complete-protocol). -/
theorem emits_of_on_tick_emit (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {v : V} (hv : v ∈ ρ.honest) {t : Time} (hpub : PublicTime S t) (ht0 : 0 ≤ t)
    (hthor : t ≤ ρ.horizon) {o : Object V}
    (ho : o ∈ (on_tick_emit S v (ρ.stateBeforeTime S t v) t).2) :
    ρ.emits S v o t := by
  have hmem : Event.tick v t ∈ ρ.events :=
    NamedScheduleWellFormed.tick_total sch v hv t hpub ht0 hthor
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  refine ⟨i, hi, ?_⟩
  show o ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2
  rw [stateBefore_tick_eq_stateBeforeTime S sch hi]
  exact ho

/-- The vote duty reads a store of the vote instant's own slot. -/
theorem voteStore_slot (S : Setup V) (st : Protocol.Store V) (s : Slot) :
    (voteStore S st s).s = s := by
  simp only [voteStore, tickStore, slotOf_vote_time]

/-- The prepared vote read carries the vote instant's own slot: the tick's clock
branch stamps `E.slotOf t`, and the vote instant inverts. -/
theorem voteDutyRead_slot (S : Setup V) (ρ : Run V) (v : V) (s : Slot) :
    (voteDutyRead S ρ v s).st.core.s = s :=
  slotOf_vote_time S.E s

/-- **The vote branch emits the duty's own output** (PROTOCOL.md#the-complete-protocol). At
`t_s + Δ` the proposal branch is shut, so the named GF duty runs on the tick's own
prepared read and the tick carries its vote. -/
theorem on_tick_emit_vote_mem (S : Setup V) (v : V) (n : NodeState V) (s : Slot)
    (hs : 0 < s) {u : GoldfishVote V}
    (hu : (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S n (Protocol.vote_time S.E s)).cache)
        S.E S.hc (S.node v)
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.vote_time S.E s)).st).2 = some u) :
    Object.gfVote u ∈ (on_tick_emit S v n (Protocol.vote_time S.E s)).2 := by
  have hslot : S.E.slotOf (Protocol.vote_time S.E s) = s := slotOf_vote_time S.E s
  simp only [NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock, hslot] at hu
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
    vote_time_ne_proposal_time S.E s, vote_time_ne_support_cutoff S.E s, hs,
    and_false, false_and, if_false, and_true, if_true]
  rw [hu]
  split <;> simp


/-- **`VoteTickExtends` from the prepared read's determinism premise** (O19-era
addendum; `Agreement.lean` §14). The determinism twin of `voteTick_of_aligned`:
same tick, same read, same emission, with `NamedVoteStoreExtends` in place of
`NamedVoteStoreAligned`.

This is the reduction `Availability/Final.lean` calls after the `merged` clause
was refuted (`docs/fragments/review-merged-cx.md`). Nothing in the execution half
changes — only which read premise the caller has to supply. -/
theorem voteTickExtends_of_extends (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ ρ.horizon) {B : NamedBlock V}
    (hal : ∀ v ∈ ρ.honest, v ∈ S.E.committee s →
      ∃ (tree₀ : Finset (Block V)) (H : Block V),
        NamedVoteStoreExtends S ρ v s tree₀ H B) :
    VoteTickExtends S ρ s B := by
  intro v hv hcom
  obtain ⟨tree₀, H, halv⟩ := hal v hv hcom
  have hslot : (voteDutyRead S ρ v s).st.core.s = s := voteDutyRead_slot S ρ v s
  have hcomv : (S.node v).val_index ∈
      S.E.committee (voteDutyRead S ρ v s).st.core.s := by
    rw [S.node_val_index, hslot]; exact hcom
  have hu := goldfish_vote_eq_extends_with S ρ v s halv hcomv
  refine ⟨tree₀, H, _, hslot, halv, hu, ?_⟩
  exact emits_of_on_tick_emit S sch hv (publicTime_vote_time S s)
    (vote_time_nonneg S.E s) hhor
    (on_tick_emit_vote_mem S v (ρ.stateBeforeTime S (Protocol.vote_time S.E s) v) s hs hu)

/-! ## 6. The evaluation instant, and `ConfirmationTick`

`Σ.live_confirmed` has one writer, so the field a node reports at `t_s + 6Δ` is
exactly what the confirmation branch of that instant's tick returned. Proving it
is three steps: the tick sits inside the `≤ t` prefix, its own step runs
`on_tick_emit`, and every event after it at that instant is a delivery, which
`process_live_confirmed` says leaves the field alone. -/

/-- Sortedness at two indices. -/
theorem key_le_of_index_lt (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {j i : Nat} {e f : Event V} (hji : j < i)
    (hj : ρ.events[j]? = some e) (hi : ρ.events[i]? = some f) :
    NamedEvent.key e ≤ NamedEvent.key f := by
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hp := (List.pairwise_iff_getElem.mp sch.sorted) j i hjl hil hji
  rw [hje, hie] at hp
  exact hp

/-- Everything inside a downward-closed prefix satisfies its filter. -/
theorem filter_true_of_index_lt (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    (p : Event V → Bool)
    (hdc : ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → p f = true → p e = true)
    {j : Nat} {e : Event V} (hj : j < (ρ.events.filter p).length)
    (hget : ρ.events[j]? = some e) : p e = true := by
  have hmem : e ∈ ρ.events.filter p := by
    rw [filter_eq_take S sch p hdc]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hget)
  exact (List.mem_filter.mp hmem).2

/-- **`Σ.live_confirmed` is unchanged across a stretch with no tick of `v`**: the
other node's events do not reach `v`, and `v`'s own deliveries do not write the
field (`process_live_confirmed`). -/
theorem stateBefore_live_confirmed_of_no_tick (S : Setup V) (ρ : Run V) (v : V)
    {m : Nat} :
    ∀ n : Nat, m ≤ n →
      (∀ (j : Nat) (e : Event V), m ≤ j → j < n → ρ.events[j]? = some e →
        ∀ t' : Time, e ≠ Event.tick v t') →
      (ρ.stateBefore S n v).st.live_confirmed = (ρ.stateBefore S m v).st.live_confirmed := by
  intro n
  induction n with
  | zero => intro hm _; rw [Nat.le_zero.mp hm]
  | succ n ih =>
      intro hm h
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        rw [← ih hmn (fun j e h1 h2 h3 => h j e h1 (Nat.lt_succ_of_lt h2) h3)]
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : ρ.events[n]? with
        | none => simp
        | some e =>
            have hne := h n e hmn (Nat.lt_succ_self n) hn
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e with
            | tick u t' =>
                by_cases hu : u = v
                · exact absurd (by rw [hu] : Event.tick u t' = Event.tick v t') (hne t')
                · simp only [NamedWorld.step]
                  rw [Function.update_of_ne (Ne.symm hu)]
            | deliver u o t' =>
                by_cases hu : u = v
                · subst hu
                  simp only [NamedWorld.step, Function.update_self]
                  exact process_live_confirmed S _ o
                · simp only [NamedWorld.step]
                  rw [Function.update_of_ne (Ne.symm hu)]
      · rw [Nat.le_antisymm hm hge]

/-- **The field a node reports at a public time is that tick's own output**
(PROTOCOL.md#the-complete-protocol). -/
theorem live_confirmed_stateAt (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {v : V} (hv : v ∈ ρ.honest) {t : Time} (hpub : PublicTime S t) (ht0 : 0 ≤ t)
    (hthor : t ≤ ρ.horizon) :
    (ρ.storeAt S v t).live_confirmed =
      (on_tick_emit S v (ρ.stateBeforeTime S t v) t).1.st.live_confirmed := by
  obtain ⟨i, hi⟩ :=
    List.mem_iff_getElem?.mp (NamedScheduleWellFormed.tick_total sch v hv t hpub ht0 hthor)
  have hiN : i < (ρ.events.filter (fun e => decide (e.time ≤ t))).length := by
    by_contra hcon
    have hp := filter_false_of_index_ge S sch _ (downward_le t) (Nat.le_of_not_lt hcon) hi
    simp only [NamedEvent.time, decide_eq_false_iff_not, not_le] at hp
    exact lt_irrefl _ hp
  have hstep : (ρ.stateBefore S (i + 1) v) =
      (on_tick_emit S v (ρ.stateBefore S i v) t).1 := by
    unfold Run.stateBefore NamedRun.stateBefore
    rw [List.take_add_one, hi, List.foldl_append]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step,
      Function.update_self]
  have hno : ∀ (j : Nat) (e : Event V), i + 1 ≤ j →
      j < (ρ.events.filter (fun e => decide (e.time ≤ t))).length →
      ρ.events[j]? = some e → ∀ t' : Time, e ≠ Event.tick v t' := by
    intro j e hij hjN hget t' hcon
    subst hcon
    have hle : t' ≤ t := by
      have hp := filter_true_of_index_lt S sch _ (downward_le t) hjN hget
      simpa [NamedEvent.time] using hp
    have hge : t ≤ t' := by
      have hk := key_le_of_index_lt S sch (Nat.lt_of_succ_le hij) hi hget
      exact Proofs.Bridges.time_le_of_key_le hk
    have hteq : t' = t := le_antisymm hle hge
    subst hteq
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hev : ρ.events[j] = ρ.events[i] := by rw [hje, hie]
    have := (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp hev
    omega
  rw [Run.storeAt, stateAt_eq_take S sch t]
  rw [stateBefore_live_confirmed_of_no_tick S ρ v _ (by omega) hno, hstep,
    stateBefore_tick_eq_stateBeforeTime S sch hi]

/-- The store the slot-`s` evaluation reads (PROTOCOL.md#the-complete-protocol): the tick of
`t_s + 6Δ`, which is the support action of slot `s + 1`. -/
def confStore (S : Setup V) (ρ : Run V) (v : V) (s : Slot) : Protocol.Store V :=
  tickStore S (ρ.storeBeforeTime S v (Protocol.confirmation_time S.E s)).core
    (Protocol.confirmation_time S.E s)

/-- **`confStore` is the prepared confirmation read's own core store.** The tick
stamps the clock and the slot and changes nothing else in the core, so the previous
tick-store reconstruction and the named read agree definitionally; only the
cache, which the previous form never carried, is new. -/
theorem confStore_eq_confirmationInputRead (S : Setup V) (ρ : Run V) (v : V) (s : Slot) :
    confStore S ρ v s = (confirmationInputRead S ρ v s).st.core := rfl

/-- **The recorded confirmation is the slot-`s` walk over `confStore`**
(PROTOCOL.md#the-complete-protocol). This is the clause `ConfirmationTick`'s own doc comment
calls the bridge. -/
theorem live_confirmed_eq_update (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {v : V} (hv : v ∈ ρ.honest) (s : Slot)
    (hthor : Protocol.confirmation_time S.E s ≤ ρ.horizon) :
    (ρ.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed =
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract (confirmationInputRead S ρ v s).cache) S.E S.hc
        (confirmationInputRead S ρ v s).st s).live_confirmed := by
  have hsucc : Protocol.confirmation_time S.E s = Protocol.support_cutoff S.E (s + 1) :=
    Protocol.confirmation_time_eq_support_cutoff_succ S.E s
  have hread : confirmationInputRead S ρ v s =
      NamedActionReads.confirmationReadFrom S
        (ρ.stateBeforeTime S (Protocol.support_cutoff S.E (s + 1)) v)
        (Protocol.support_cutoff S.E (s + 1)) := by
    show NamedActionReads.confirmationReadAt S ρ v (Protocol.confirmation_time S.E s) = _
    rw [hsucc]
    rfl
  rw [live_confirmed_stateAt S sch hv (publicTime_confirmation_time S s)
    (confirmation_time_nonneg S.E s) hthor, hsucc,
    on_tick_emit_confirmation S v
      (ρ.stateBeforeTime S (Protocol.support_cutoff S.E (s + 1)) v) (s + 1)
      (Nat.succ_pos s), hread, Nat.add_sub_cancel]


/-! ## 7. Non-retreat, transported along the run

`Optimistic/Agreement.lean` reduces O13 to `ConfirmedCone`, whose first clause is
a *transport*: that every `Σ.live_confirmed` recorded at or after the slot-`s`
evaluation is some evaluation's output over a store with the cone. §2 and §6 make
that clause a theorem, so what is left is the cone itself, at each confirmation
tick, and `liveConfirmedNonRetreat_of_cone` is O13 from that alone.

The induction is over the event list. A delivery cannot move the field; a tick
either does not run the confirmation branch, and cannot move it either, or runs
it — and then `update_confirmation_preceq` says the new walk still reaches `B`. -/



omit [DecidableEq V] [Fintype V] in
/-- The `≤ t` prefixes grow with `t`. -/
theorem filter_le_length_mono (ρ : Run V) {t t' : Time} (h : t ≤ t') :
    (ρ.events.filter (fun e => decide (e.time ≤ t))).length ≤
      (ρ.events.filter (fun e => decide (e.time ≤ t'))).length :=
  (List.monotone_filter_right ρ.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact le_trans he h)).length_le


/-! ## 8. The proposal instant

The remaining trace clause of O12's hypothesis: that the honest slot-`s` proposer
really emits a slot-`s` block at `t_s`. This one is entirely mechanical —
`propose_block` stamps the block with the store's own slot, and the tick's store
carries `slotOf t_s = s`. -/

theorem proposal_time_ne_vote_time (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≠ Protocol.vote_time E s :=
  fun h => vote_time_ne_proposal_time E s h.symm

theorem proposal_time_ne_support_cutoff (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≠ Protocol.support_cutoff E s :=
  fun h => support_cutoff_ne_proposal_time E s h.symm

theorem publicTime_proposal_time (S : Setup V) (s : Slot) :
    PublicTime S (Protocol.proposal_time S.E s) :=
  (publicTime_iff S _).mpr ⟨s, Or.inl rfl⟩

/-- **The proposal branch emits the block its duty computed**
(PROTOCOL.md#the-complete-protocol). The named proposal duty returns an `Option` — a
retained parent body is what makes it `some` — so the emission is stated at the
duty's own output rather than at a total constructor. -/
theorem on_tick_emit_proposal_mem (S : Setup V) (v : V) (n : NodeState V) (s : Slot)
    (hs : 0 < s) (hpr : S.E.proposer s = (S.node v).val_index) {B : NamedBlock V}
    (hB : (Protocol.NamedDuties.propose_block_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S n
            (Protocol.proposal_time S.E s)).cache)
        S.E S.hc S.cfg (S.node v)
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.proposal_time S.E s)).st).2 = some B) :
    Object.block B ∈ (on_tick_emit S v n (Protocol.proposal_time S.E s)).2 := by
  have hslot : S.E.slotOf (Protocol.proposal_time S.E s) = s := slotOf_proposal_time S.E s
  simp only [NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock, hslot] at hB
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
    proposal_time_ne_vote_time S.E s, proposal_time_ne_support_cutoff S.E s, hpr, hs,
    and_false, if_false, and_true, if_true]
  rw [hB]
  split <;> simp

/-- The computed proposal carries the proposing read's own slot, and that read is
stamped with the proposal instant's slot. -/
theorem proposedBlockAt_slot (S : Setup V) (ρ : Run V) (s : Slot) {B : NamedBlock V}
    (hB : Statements.Instantiation.proposedBlockAt S ρ s = some B) : B.slot = s := by
  have hst : (Statements.Instantiation.proposerReadAt S ρ s).st.core.s = s :=
    slotOf_proposal_time S.E s
  simp only [Statements.Instantiation.proposedBlockAt, Protocol.NamedActions.proposal_with,
    Protocol.with_proposal_input, Option.map_eq_some_iff] at hB
  obtain ⟨parent, -, hBeq⟩ := hB
  rw [← hBeq]
  exact hst

/-- **The honest slot-`s` proposer emits the slot-`s` block its duty computed**
(PROTOCOL.md#the-complete-protocol). -/
theorem proposalTick (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    (s : Slot) (hs : 0 < s) (hprop : S.E.proposer s ∈ ρ.honest)
    (hhor : Protocol.proposal_time S.E s ≤ ρ.horizon)
    {B : NamedBlock V} (hB : Statements.Instantiation.proposedBlockAt S ρ s = some B) :
    B.slot = s ∧
      NamedRun.emits S ρ (S.E.proposer s) (.block B)
        (Protocol.proposal_time S.E s) := by
  refine ⟨proposedBlockAt_slot S ρ s hB, ?_⟩
  refine emits_of_on_tick_emit S sch hprop (publicTime_proposal_time S s)
    (proposal_time_nonneg S.E s) hhor ?_
  refine on_tick_emit_proposal_mem S (S.E.proposer s)
    (ρ.stateBeforeTime S (Protocol.proposal_time S.E s) (S.E.proposer s)) s hs
    (S.node_val_index (S.E.proposer s)).symm ?_
  have hB' : Protocol.NamedActions.proposal_with
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S
          (ρ.stateBeforeTime S (Protocol.proposal_time S.E s) (S.E.proposer s))
          (Protocol.proposal_time S.E s)).cache)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (NamedActionReads.confirmationReadFrom S
        (ρ.stateBeforeTime S (Protocol.proposal_time S.E s) (S.E.proposer s))
        (Protocol.proposal_time S.E s)).st = some B := hB
  simp only [Protocol.NamedDuties.propose_block_with, hB']

/-! ## 9. The SG pool's provenance — `Proofs.Bridges.processes_block_of_mem_T`'s twin

`Proofs.Bridges.processes_block_of_mem_T` closes the gap between "an honest store holds
`B`" and "that node processed `B`", which is what turns `Unforgeable.carried_attest`
into a fact about `Σ.T`. `Σ.sg_votes[·]` has the same gap and it is what the §6
grade arguments read: `BatchAligned` and every grade cutoff are statements about
the *pool*, while relay and the stamp bound are statements about *processing*.

The argument is the same one and it is shorter, because the pool has exactly one
writer. `on_sg_vote` appends to `Σ.sg_votes[a.round]`; `update_finality`,
`on_block`, `on_goldfish_vote`, `update_confirmation`, `set_fresh_root`,
`goldfish_vote` and `propose_block` all leave the field alone. So inside a tick
only the attest branch can grow the pool, and the attestation it adds is the one
that branch emits. -/

omit [Fintype V] in
/-- §5.2 `update_finality` does not write `Σ.sg_votes[·]` (PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_sg_votes (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).sg_votes = st.sg_votes := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §7.2 `on_goldfish_vote` does not write it (PROTOCOL.md#the-complete-protocol). -/
theorem on_goldfish_vote_sg_votes (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).sg_votes = st.sg_votes := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- The checked runtime handler also preserves `Σ.sg_votes`. -/
theorem on_goldfish_vote_checked_sg_votes (E : Env V)
    (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).sg_votes = st.sg_votes := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_sg_votes st u
  · rfl


/-- The checked carried-vote fold preserves `Σ.sg_votes`. -/
theorem foldl_on_goldfish_vote_checked_sg_votes (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).sg_votes = st.sg_votes := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_sg_votes]

/- Kept for the retained carried-admission consumer. -/





omit [Fintype V] in
/-- **`on_sg_vote` adds at most the attestation it is handed**
(PROTOCOL.md#the-complete-protocol). Both rejecting branches return the store; the
accepting one appends `a` to its own round's list. -/
theorem on_sg_vote_sg_pool_mem (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.on_sg_vote hc st a).sg_pool r) :
    b ∈ st.sg_pool r ∨ b = a := by
  simp only [Protocol.on_sg_vote] at hb
  split_ifs at hb
  · exact Or.inl hb
  · simp only [Protocol.Store.sg_pool] at hb ⊢
    split_ifs at hb with hr
    · rw [List.toFinset_append] at hb
      rcases Finset.mem_union.mp hb with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using h)
    · exact Or.inl hb

/-- The row an object can put into the SG pool: an attestation row itself, or
one of a block's carried rows. Votes carry none. -/
def CarriesRow (o : Object V) (b : CombinedAttestation V) : Prop :=
  match o with
  | .block B => ∃ row ∈ B.attestations, b = row.erase
  | .gfVote _ => False
  | .attest row => b = row.erase

/-- The general block body does not write `Σ.sg_votes[·]`, whatever chain state
it builds. -/
theorem on_block_using_sg_votes (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).sg_votes = st.sg_votes := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    simp only [update_finality_sg_votes, foldl_on_goldfish_vote_checked_sg_votes]

/-- The carried-round guard passes `Σ.sg_votes[·]` through its handler. -/
theorem on_block_checked_using_sg_votes
    (handle : Protocol.Store V → Protocol.Store V) (hc : HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (hh : ∀ st' : Protocol.Store V, (handle st').sg_votes = st'.sg_votes) :
    (Protocol.on_block_checked_using handle hc st B).sg_votes = st.sg_votes := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hh st
  · rfl

/-- The named block core is still pool-neutral; only the carried tail admits. -/
theorem process_block_core_sg_votes (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.sg_votes =
      st.core.sg_votes := by
  simp only [Protocol.NamedStore.process_block_core]
  split
  · rfl
  · simp only [Protocol.NamedStore.commitBlock]
    split <;>
      exact on_block_checked_using_sg_votes _ hc st.core B.erase
        (fun st' => on_block_using_sg_votes E st' B.erase _)

omit [Fintype V] in
/-- **The named row admission adds at most the row it is handed.** -/
theorem admit_row_sg_pool_mem (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.NamedAdmission.admit_row hc st row).core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨ b = row.erase := by
  simp only [Protocol.NamedAdmission.admit_row] at hb
  split at hb <;> exact on_sg_vote_sg_pool_mem hc st.core row.erase r hb

omit [Fintype V] in

/-- A carried batch adds at most its own rows. -/
theorem admit_rows_sg_pool_mem (hc : HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V) (r : Round)
      (b : CombinedAttestation V),
      b ∈ (Protocol.NamedAdmission.admit_rows hc st rows).core.sg_pool r →
        b ∈ st.core.sg_pool r ∨ ∃ row ∈ rows, b = row.erase := by
  intro rows
  induction rows with
  | nil => intro st r b hb; exact Or.inl hb
  | cons a l ih =>
      intro st r b hb
      have h : Protocol.NamedAdmission.admit_rows hc st (a :: l) =
          Protocol.NamedAdmission.admit_rows hc
            (Protocol.NamedAdmission.admit_row hc st a) l := rfl
      rw [h] at hb
      rcases ih _ r b hb with h1 | ⟨row, hrow, hbe⟩
      · rcases admit_row_sg_pool_mem hc st a r h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨a, List.mem_cons_self .., h2⟩
      · exact Or.inr ⟨row, List.mem_cons_of_mem _ hrow, hbe⟩

/-- **The named block handler adds at most the block's own carried rows.** -/
theorem on_block_with_sg_pool_mem (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨ ∃ row ∈ B.attestations, b = row.erase := by
  have hcore : ∀ k : Round,
      (Protocol.NamedStore.process_block_core E hc cfg st B).core.sg_pool k =
        st.core.sg_pool k := by
    intro k
    simp only [Protocol.Store.sg_pool, process_block_core_sg_votes]
  cases adm with
  | alsoCarried =>
      rw [show Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B =
          (if B ∉ st.bodies ∧
              B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies then
            Protocol.NamedAdmission.admit_rows hc
              (Protocol.NamedStore.process_block_core E hc cfg st B) B.attestations
          else Protocol.NamedStore.process_block_core E hc cfg st B) from rfl] at hb
      split_ifs at hb
      · rcases admit_rows_sg_pool_mem hc B.attestations _ r b hb with h | h
        · exact Or.inl ((hcore r) ▸ h)
        · exact Or.inr h
      · exact Or.inl ((hcore r) ▸ hb)

/-- Neither named GF duty writes the pool. -/
theorem goldfish_vote_with_sg_votes (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core.sg_votes =
      st.core.sg_votes := by
  simp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split
  · exact on_goldfish_vote_checked_sg_votes E _ _
  · rfl

/-- Nor the named confirmation duty. -/
theorem update_confirmation_with_sg_votes (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with contract E hc st s).core.sg_votes =
      st.core.sg_votes := rfl

/-- **The named proposal duty adds at most the rows of the block it emits.** -/
theorem propose_block_with_sg_pool_mem (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈
      (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨
      ∃ B : NamedBlock V,
        (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).2 = some B ∧
          ∃ row ∈ B.attestations, b = row.erase := by
  simp only [Protocol.NamedDuties.propose_block_with] at hb ⊢
  split at hb
  · exact Or.inl hb
  · rename_i B hBeq
    rcases on_block_with_sg_pool_mem .alsoCarried E hc cfg st B r hb with h | h
    · exact Or.inl h
    · refine Or.inr ⟨B, ?_, h⟩
      simp only [hBeq]

/-- **The named round action adds at most the row it emits.** -/
theorem attest_with_sg_pool_mem (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.NamedDuties.attest_with contract E hc nd st record).1.core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨
      b = (Protocol.NamedDuties.attest_with contract E hc nd st record).2.2.erase :=
  admit_row_sg_pool_mem hc st _ r hb

/-- Processing an object adds at most the rows that object carries
(PROTOCOL.md#the-complete-protocol). -/
theorem process_sg_pool_mem (S : Setup V) (n : NodeState V) (o : Object V)
    (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (n.process S o).st.core.sg_pool r) :
    b ∈ n.st.core.sg_pool r ∨ CarriesRow o b := by
  cases o with
  | block B =>
      rcases on_block_with_sg_pool_mem .alsoCarried S.E S.hc S.cfg n.st B r hb with h | h
      · exact Or.inl h
      · exact Or.inr h
  | gfVote u =>
      refine Or.inl ?_
      simp only [Protocol.Store.sg_pool, NodeState.process, NamedNode.process,
        NamedReceipt.process, on_goldfish_vote_checked_sg_votes] at hb ⊢
      exact hb
  | attest a =>
      rcases admit_row_sg_pool_mem S.hc n.st a r hb with h | h
      · exact Or.inl h
      · exact Or.inr h

/-! ## 10. The scheduler composition: `on_tick_emit_sg_mem` and its trace closure

The scheduler composition: `TickScheduler.runWith`'s four guards
compose stage by stage rather than by a blunt `split_ifs` explosion. `runWith_sg_pool_mem` is
the generic shape — clock and confirmation are pool-neutral, vote is pool-neutral, proposal and
attestation each add at most their own carried/emitted row — and `on_tick_emit_sg_mem`
specializes it to the named engine. `processes_attest_of_mem_sg_pool` is the trace closure by
induction on the event index, using `on_tick_emit_sg_mem` at a self-tick (covered by
`NamedRun.emits`, itself one of the two disjuncts of `NamedRun.processes`) and
`process_sg_pool_mem` at a delivery. -/

/-- Private composition lemma: `TickScheduler.runWith`'s four guards, chased stage by stage.
Clock and confirmation never touch the pool; vote never touches it either; proposal and
attestation each add at most the row they carry or emit. -/
private theorem runWith_sg_pool_mem
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (ops : Protocol.TickScheduler.TickOps (Protocol.NamedStore V) Protocol.NamedRecord
      (NamedBlock V) (GoldfishVote V) (NamedAttestation V))
    (hclock : ∀ (st0 : Protocol.NamedStore V) (t' : Time) (s' : Slot) (r : Round),
      (ops.clock st0 t' s').core.sg_pool r = st0.core.sg_pool r)
    (hprop : ∀ (st0 : Protocol.NamedStore V) (r : Round) {b : CombinedAttestation V},
      b ∈ (ops.proposal st0).1.core.sg_pool r →
        b ∈ st0.core.sg_pool r ∨
          ∃ B : NamedBlock V, (ops.proposal st0).2 = some B ∧
            ∃ row ∈ B.attestations, b = row.erase)
    (hvote : ∀ (st0 : Protocol.NamedStore V) (r : Round),
      (ops.vote st0).1.core.sg_pool r = st0.core.sg_pool r)
    (hconf : ∀ (st0 : Protocol.NamedStore V) (s' : Slot) (r : Round),
      (ops.confirmation st0 s').core.sg_pool r = st0.core.sg_pool r)
    (hatt : ∀ (st0 : Protocol.NamedStore V) (record0 : Protocol.NamedRecord) (r : Round)
      {b : CombinedAttestation V},
      b ∈ (ops.attestation st0 record0).1.core.sg_pool r →
        b ∈ st0.core.sg_pool r ∨ b = (ops.attestation st0 record0).2.2.erase)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) (r : Round)
    {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.TickScheduler.runWith E hc nd ops
        NamedObject.block NamedObject.gfVote NamedObject.attest
        (fun st record emitted => (st, record, emitted)) st record t).1.core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨
      ∃ o ∈ (Protocol.TickScheduler.runWith E hc nd ops
        NamedObject.block NamedObject.gfVote NamedObject.attest
        (fun st record emitted => (st, record, emitted)) st record t).2.2,
        CarriesRow o b := by
  simp only [Protocol.TickScheduler.runWith,
    apply_ite (fun p : Protocol.NamedStore V × Protocol.NamedRecord × List (NamedObject V) =>
      p.1.core.sg_pool r),
    apply_ite (fun p : Protocol.NamedStore V × Protocol.NamedRecord × List (NamedObject V) =>
      p.2.2)] at hb ⊢
  set st1 := (if 0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
      E.proposer (E.slotOf t) = nd.val_index then
        (ops.proposal (ops.clock st t (E.slotOf t))).1
      else ops.clock st t (E.slotOf t)) with hst1
  set st2 := (if 0 < E.slotOf t ∧ t = Protocol.vote_time E (E.slotOf t) then
      (ops.vote st1).1 else st1) with hst2
  set emitted2 : List (NamedObject V) :=
    (if 0 < E.slotOf t ∧ t = Protocol.vote_time E (E.slotOf t) then
      List.map NamedObject.gfVote (ops.vote st1).2.toList else []) with hemitted2
  set st3 := (if 0 < E.slotOf t ∧ t = Protocol.support_cutoff E (E.slotOf t) then
      ops.confirmation st2 (E.slotOf t - 1) else st2) with hst3
  have hpeel23 : st3.core.sg_pool r = st1.core.sg_pool r := by
    by_cases hP3 : 0 < E.slotOf t ∧ t = Protocol.support_cutoff E (E.slotOf t)
    · rw [hst3, if_pos hP3, hconf st2 (E.slotOf t - 1) r]
      by_cases hP2 : 0 < E.slotOf t ∧ t = Protocol.vote_time E (E.slotOf t)
      · rw [hst2, if_pos hP2, hvote st1 r]
      · rw [hst2, if_neg hP2]
    · rw [hst3, if_neg hP3]
      by_cases hP2 : 0 < E.slotOf t ∧ t = Protocol.vote_time E (E.slotOf t)
      · rw [hst2, if_pos hP2, hvote st1 r]
      · rw [hst2, if_neg hP2]
  have hstep1 : b ∈ st1.core.sg_pool r →
      b ∈ st.core.sg_pool r ∨
        ∃ B : NamedBlock V, (ops.proposal (ops.clock st t (E.slotOf t))).2 = some B ∧
          (0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
            E.proposer (E.slotOf t) = nd.val_index) ∧
          ∃ row ∈ B.attestations, b = row.erase := by
    intro hb1
    by_cases hP1 : 0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
        E.proposer (E.slotOf t) = nd.val_index
    · rw [hst1, if_pos hP1] at hb1
      rcases hprop (ops.clock st t (E.slotOf t)) r hb1 with h0 | ⟨B, hBeq, hrow⟩
      · left; rw [hclock st t (E.slotOf t) r] at h0; exact h0
      · right; exact ⟨B, hBeq, hP1, hrow⟩
    · rw [hst1, if_neg hP1, hclock st t (E.slotOf t) r] at hb1
      left; exact hb1
  by_cases hP4 : t = hc.a E.Δ (hc.round_of (ops.slot st3)) ∧
      nd.awake (hc.round_of (ops.slot st3)) = true
  · rw [if_pos hP4] at hb ⊢
    rcases hatt st3 record r hb with h3 | heq
    · rw [hpeel23] at h3
      rcases hstep1 h3 with h | ⟨B, hBeq, hP1, hrow⟩
      · exact Or.inl h
      · refine Or.inr ⟨NamedObject.block B, ?_, hrow⟩
        apply List.mem_append_left
        apply List.mem_append_left
        rw [if_pos hP1, hBeq]
        exact List.mem_cons_self ..
    · exact Or.inr ⟨NamedObject.attest (ops.attestation st3 record).2.2,
        List.mem_append_right _ (List.mem_cons_self ..), heq⟩
  · rw [if_neg hP4] at hb ⊢
    rw [hpeel23] at hb
    rcases hstep1 hb with h | ⟨B, hBeq, hP1, hrow⟩
    · exact Or.inl h
    · refine Or.inr ⟨NamedObject.block B, ?_, hrow⟩
      apply List.mem_append_left
      rw [if_pos hP1, hBeq]
      exact List.mem_cons_self ..

/-- **The scheduler composition**: an attestation in the tick's SG pool was already there, or
was carried in by an object the tick itself emitted. Specializes `runWith_sg_pool_mem` to the
named engine, discharging its clock/vote/confirmation obligations by `rfl` and the sg_votes
equalities, and its proposal/attestation obligations by the per-duty lemmas above. -/
theorem on_tick_emit_sg_mem (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (on_tick_emit S v n t).1.st.core.sg_pool r) :
    b ∈ n.st.core.sg_pool r ∨ ∃ o ∈ (on_tick_emit S v n t).2, CarriesRow o b := by
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick] at hb ⊢
  set gc := NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) with hgc
  exact runWith_sg_pool_mem S.E S.hc (S.node v)
    (Protocol.NamedTick.namedOps gc S.E S.hc S.cfg (S.node v))
    (fun st0 t' s' _r => rfl)
    (by intro st0 r b hb
        exact propose_block_with_sg_pool_mem gc S.E S.hc S.cfg (S.node v) st0 r hb)
    (fun st0 r => by
      simp only [Protocol.NamedTick.namedOps, Protocol.Store.sg_pool, goldfish_vote_with_sg_votes])
    (fun st0 s' r => by
      simp only [Protocol.NamedTick.namedOps, Protocol.Store.sg_pool,
        update_confirmation_with_sg_votes])
    (by intro st0 record0 r b hb
        exact attest_with_sg_pool_mem gc S.E S.hc (S.node v) st0 record0 r hb)
    n.st n.record t r hb

/-- **The scheduler composition, transported along the run**: an attestation in an honest
node's SG pool at any point was carried in by some object the node processed strictly earlier
(a self-emission at a tick, or a delivery), via `CarriesRow`. Induction on the event index: the
base case is the empty initial pool, a tick uses `on_tick_emit_sg_mem` and the self-emission
disjunct of `NamedRun.processes`, and a delivery uses `process_sg_pool_mem`.

Adapted from the report's `ρ.processes S v o e.time` to the fully qualified
`NamedRun.processes S ρ v o e.time`: `Run.processes` is a point-free `abbrev` copy
(`@NamedRun.processes`) and dot notation on it does not resolve, even though `Run:= NamedRun`. -/
theorem processes_attest_of_mem_sg_pool (S : Setup V) (ρ : Run V) (v : V) :
    ∀ (i : Nat) (r : Round) (a : CombinedAttestation V),
      a ∈ (ρ.stateBefore S i v).st.core.sg_pool r →
        ∃ (j : Nat) (e : Event V) (o : Object V), j < i ∧ ρ.events[j]? = some e ∧
          NamedRun.processes S ρ v o e.time ∧ CarriesRow o a := by
  intro i
  induction i with
  | zero =>
      intro r a ha
      exfalso
      have hinit : (ρ.stateBefore S 0 v) = NamedNode.initial := rfl
      rw [hinit] at ha
      simp [NamedNode.initial, Protocol.NamedStore.initial, Protocol.Store.sg_pool,
        Protocol.Store.init] at ha
  | succ n ih =>
      intro r a ha
      cases hn : ρ.events[n]? with
      | none =>
          have heq : ρ.stateBefore S (n + 1) v = ρ.stateBefore S n v := by
            unfold Run.stateBefore NamedRun.stateBefore
            rw [List.take_add_one, hn, List.foldl_append]
            simp
          rw [heq] at ha
          obtain ⟨j, e, o, hji, hje, hpr, hcarry⟩ := ih r a ha
          exact ⟨j, e, o, Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩
      | some e =>
          cases e with
          | tick u t' =>
              by_cases hu : v = u
              · subst hu
                have heq : ρ.stateBefore S (n + 1) v =
                    (on_tick_emit S v (ρ.stateBefore S n v) t').1 := by
                  unfold Run.stateBefore NamedRun.stateBefore
                  rw [List.take_add_one, hn, List.foldl_append]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step,
                    Function.update_self]
                rw [heq] at ha
                rcases on_tick_emit_sg_mem S v (ρ.stateBefore S n v) t' r ha with
                  h | ⟨o, ho, hcarry⟩
                · obtain ⟨j, e', o', hji, hje, hpr, hcarry⟩ := ih r a h
                  exact ⟨j, e', o', Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩
                · refine ⟨n, Event.tick v t', o, Nat.lt_succ_self n, hn, ?_, hcarry⟩
                  exact Or.inl ⟨n, hn, ho⟩
              · have heq : ρ.stateBefore S (n + 1) v = ρ.stateBefore S n v := by
                  unfold Run.stateBefore NamedRun.stateBefore
                  rw [List.take_add_one, hn, List.foldl_append]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step]
                  exact Function.update_of_ne hu _ _
                rw [heq] at ha
                obtain ⟨j, e', o, hji, hje, hpr, hcarry⟩ := ih r a ha
                exact ⟨j, e', o, Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩
          | deliver u o' t' =>
              by_cases hu : v = u
              · subst hu
                have heq : ρ.stateBefore S (n + 1) v =
                    NodeState.process S (ρ.stateBefore S n v) o' := by
                  unfold Run.stateBefore NamedRun.stateBefore
                  rw [List.take_add_one, hn, List.foldl_append]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step,
                    Function.update_self]
                rw [heq] at ha
                rcases process_sg_pool_mem S (ρ.stateBefore S n v) o' r ha with h | hcarry
                · obtain ⟨j, e', o'', hji, hje, hpr, hcarry⟩ := ih r a h
                  exact ⟨j, e', o'', Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩
                · refine ⟨n, Event.deliver v o' t', o', Nat.lt_succ_self n, hn, ?_, hcarry⟩
                  exact Or.inr ⟨n, hn⟩
              · have heq : ρ.stateBefore S (n + 1) v = ρ.stateBefore S n v := by
                  unfold Run.stateBefore NamedRun.stateBefore
                  rw [List.take_add_one, hn, List.foldl_append]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step]
                  exact Function.update_of_ne hu _ _
                rw [heq] at ha
                obtain ⟨j, e', o, hji, hje, hpr, hcarry⟩ := ih r a ha
                exact ⟨j, e', o, Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩

end Optimistic
end Proofs
end DecoupledConsensusModel

end
