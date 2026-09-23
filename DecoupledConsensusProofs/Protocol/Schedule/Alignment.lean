module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.TickReads
public import DecoupledConsensusProofs.Protocol.Handlers.Pool
public import DecoupledConsensusProofs.Protocol.ChainState.Emission

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# O14–O16 and O18's converse — the alignment nodes
(obligations O14, O15, O16, O18; `the design note` "Status at the pre-§6/§7
boundary"; PROTOCOL.md#the-complete-protocol)

Four residual nodes, one file, because they run on one fact: **an honest
validator speaks once per instant**. `on_tick_emit` is the only emitter and it
runs once per public time (`ScheduleWellFormed.nodup`), so an honest validator
emits at most one Goldfish vote per slot and at most one attestation per round.
With `Unforgeable` that turns every appearance of an honest name — in a pool, in a
carried set, in a merged view — into that validator's own unique object.

## What each node is, and what closes it

* **O14** (`gfVote_pooled_before_freeze`, `gfVote_in_cutoff_view`) — every honest
  slot-`s` vote is in every honest node's slot-`s` pool, stamped strictly before
  `t_s + 2Δ`, so before both cutoffs the protocol applies to it. The two guards
  `Availability/Sync.lean` left open are discharged: the slot guard, because
  relay and `Unforgeable.unforgeable` bracket every processing inside
  `[t_s + Δ, t_s + 2Δ)` and the receiver's clock is a tick of that interval; and
  the cap, because the emitter is honest.
* **O15** (`voter_view_no_honest_equivocation`) — no honest validator equivocates
  in an honest node's merged view, so flag F2.4's gate-flip cannot fire on an
  honest name. Both halves of the view are covered, and the slot-uniformity the
  unqualified `equivocates` needs comes from `PoolStamps.slot` on the pool half
  and from `carried_votes_wf_of_mem_T` on the carried half.
* **O16** (`confirmedInTree_depReachable`, `storeGateProcessed_of_admissible`) —
  `Σ.live_confirmed ∈ Σ.T`, the one clause of `Emission.StoreGateProcessed` that
  was not in the P6 pack. With it `σ[gate].T_h ⪯ gate` follows at every honest
  store and `GateIsOwnConfirmation` is one named residual away.
* **O18's converse** (`sgVote_mem_of_process`, `sgVote_pooled_of_delivery`) — the
  SG twin of O14. Two of `on_sg_vote`'s three guards are discharged; the
  round guard is the schedule fact and is carried as a named hypothesis, the SG
  counterpart of O14's slot guard.

**What is not here.** O17 — the canonical family — is untouched, and with it the
slot induction that names the head every honest merged view agrees on. So the
clauses that close here are the delivery, hygiene and bookkeeping ones, and the
fork-choice agreement is still the residual it was.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. One Goldfish vote per slot

`goldfish_vote` returns `(val_index, Σ.s, H.root)` or nothing (PROTOCOL.md#the-complete-protocol), and
the tick's emission list holds its output alone. So the *shape* of an emitted vote
is fixed by the instant, and two votes emitted by one validator in one slot are
emitted by the same tick and are therefore equal. -/

omit [Fintype V] in
/-- §5.2 `update_finality` does not write `Σ.s` (PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_slot (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).s = st.s := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §7.2 nor `on_goldfish_vote` (PROTOCOL.md#the-complete-protocol). -/
theorem on_goldfish_vote_slot (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).s = st.s := by
  unfold Protocol.on_goldfish_vote
  split_ifs <;> rfl

/-- The checked runtime handler also preserves `Σ.s`. -/
theorem on_goldfish_vote_checked_slot (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).s = st.s := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_slot st u
  · rfl


/-- The checked carried-vote fold preserves `Σ.s`. -/
theorem foldl_on_goldfish_vote_checked_slot (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).s = st.s := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_slot]

omit [Fintype V] in
/-- §7.2 nor `on_sg_vote` (PROTOCOL.md#the-complete-protocol). -/
theorem on_sg_vote_slot (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).s = st.s := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

/-- Local restatement of `Proofs.NamedTick.tick_computed_duties` (that file's
Proofs-layer cone is unbuilt in this worktree; `Availability/Pool.lean` keeps
the identical private copy for the same reason). Byte-identical to the
Model-level scheduler, so the proof script is unchanged. -/
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

/-- The engine wrapper's emission list is the scheduler's own
(`Execution.NamedNode.tick`, `NamedProfile.tick`). -/
private theorem on_tick_emit_snd_eq (S : Setup V) (v : V) (n : NodeState V) (t : Time) :
    (on_tick_emit S v n t).2 =
      (Protocol.NamedTick.tick
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).2.2 := rfl


/-- §2.5 the contract-based duty's vote is the node's own, in the store's slot
(PROTOCOL.md#the-complete-protocol). The `_with` twin of `goldfish_vote_snd`. -/
theorem goldfish_vote_with_snd (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) {u : GoldfishVote V}
    (h : (Protocol.goldfish_vote_with contract E hc nd st).2 = some u) :
    u.val_index = nd.val_index ∧ u.slot = st.s := by
  simp only [Protocol.goldfish_vote_with] at h
  split_ifs at h
  rw [← Option.some_inj.mp h]
  exact ⟨rfl, rfl⟩

/-- **An emitted Goldfish vote is the emitter's own, at its own vote instant,
against the tick's own prepared read** (PROTOCOL.md#the-complete-protocol). The
named twin of the earlier `gfVote_emitted_shape`: the read is
`NamedActionReads.confirmationReadFrom`, because at the vote instant the
proposal branch cannot fire (`vote_time_ne_proposal_time`), so the store the
vote duty sees is exactly the post-clock, pre-proposal read. -/
theorem gfVote_emitted_shape (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {u : GoldfishVote V} (h : Object.gfVote u ∈ (on_tick_emit S v n t).2) :
    0 < S.E.slotOf t ∧ t = Protocol.vote_time S.E (S.E.slotOf t) ∧
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract (NamedActionReads.confirmationReadFrom S n t).cache)
        S.E S.hc (S.node v) (NamedActionReads.confirmationReadFrom S n t).st).2 = some u ∧
      u.val_index = v ∧ u.slot = S.E.slotOf t := by
  rw [on_tick_emit_snd_eq, named_tick_computed_duties] at h
  set gc := NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) with hgc
  set s := S.E.slotOf t with hs
  set st0 := Protocol.NamedStore.setClock S.E n.st t with hst0
  set proposed := Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0
    with hproposed
  set proposalDue := 0 < s ∧ t = Protocol.proposal_time S.E s ∧
    S.E.proposer s = (S.node v).val_index with hproposalDue
  set st1 := if proposalDue then proposed.1 else st0 with hst1def
  set emitted1 : List (Object V) := if proposalDue then
    (match proposed.2 with | none => [] | some B => [Object.block B]) else [] with hemitted1def
  set voted := Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1 with hvoted
  set voteDue := 0 < s ∧ t = Protocol.vote_time S.E s with hvoteDue
  set st2 := if voteDue then voted.1 else st1 with hst2def
  set emitted2 : List (Object V) := if voteDue then voted.2.toList.map Object.gfVote else []
    with hemitted2def
  set st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2 with hst3def
  have hb : ∀ o ∈ emitted1, ∀ w : GoldfishVote V, o ≠ Object.gfVote w := by
    rw [hemitted1def]
    split
    · split
      · simp
      · rename_i B _
        intro o ho w
        rw [List.mem_singleton] at ho
        rw [ho]; simp
    · intro o ho; simp at ho
  have hmem : Object.gfVote u ∈ emitted1 ++ emitted2 := by
    by_cases hA : t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
        (S.node v).awake (S.hc.round_of st3.core.s) = true
    · rw [if_pos hA] at h
      rcases List.mem_append.mp h with h' | h'
      · exact h'
      · exact absurd (List.mem_singleton.mp h') (by simp)
    · rw [if_neg hA] at h
      exact h
  rcases List.mem_append.mp hmem with h' | h'
  · exact absurd rfl (hb _ h' u)
  · rw [hemitted2def] at h'
    split_ifs at h' with hvd
    · obtain ⟨w, hw, hwu⟩ := List.mem_map.mp h'
      have hueq : w = u := by simpa using hwu
      subst hueq
      have hduty : voted.2 = some w := by simpa using hw
      have hpne : ¬ proposalDue := by
        rw [hproposalDue]
        rintro ⟨-, hteq, -⟩
        exact vote_time_ne_proposal_time S.E s (hvd.2.symm.trans hteq)
      have hst1eq : st1 = st0 := by rw [hst1def, if_neg hpne]
      rw [hst1eq] at hvoted
      rw [hvoted] at hduty
      have hcoreduty : (Protocol.goldfish_vote_with gc S.E S.hc (S.node v) st0.core).2 = some w :=
        hduty
      obtain ⟨hval, hslot⟩ := goldfish_vote_with_snd gc S.E S.hc (S.node v) st0.core hcoreduty
      have hslot' : w.slot = s := by rw [hslot, hst0]; rfl
      exact ⟨hvd.1, hvd.2, hduty, by rw [hval, S.node_val_index], hslot'⟩
    · exact absurd h' (by simp)

/-- **A tick emits at most one Goldfish vote** (PROTOCOL.md#the-complete-protocol).
Both memberships name the same duty output, and `Option` values agree. -/
theorem gfVote_emitted_unique (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {u₁ u₂ : GoldfishVote V}
    (h₁ : Object.gfVote u₁ ∈ (on_tick_emit S v n t).2)
    (h₂ : Object.gfVote u₂ ∈ (on_tick_emit S v n t).2) : u₁ = u₂ := by
  obtain ⟨-, -, hd₁, -, -⟩ := gfVote_emitted_shape S v n t h₁
  obtain ⟨-, -, hd₂, -, -⟩ := gfVote_emitted_shape S v n t h₂
  rw [hd₁] at hd₂
  exact Option.some_inj.mp hd₂

/-! ## 2. The run reading — one honest vote per slot

`Run.emits` names the tick by its index, and `ScheduleWellFormed.nodup` makes
that index unique. So two emissions of the same validator in the same slot are
one emission, which is PROTOCOL.md#the-complete-protocol for the Goldfish fibre. -/

/-- **An emitted Goldfish vote is the emitter's own, cast at its slot's vote
instant** (PROTOCOL.md#the-complete-protocol). -/
theorem emits_gfVote_shape (S : Setup V) {ρ : Run V} {v : V} {u : GoldfishVote V}
    {t : Time} (h : ρ.emits S v (Object.gfVote u) t) :
    0 < S.E.slotOf t ∧ t = Protocol.vote_time S.E (S.E.slotOf t) ∧
      u.val_index = v ∧ u.slot = S.E.slotOf t := by
  obtain ⟨i, -, ho⟩ := h
  obtain ⟨hpos, ht, -, hval, hslot⟩ := gfVote_emitted_shape S v (ρ.stateBefore S i v) t ho
  exact ⟨hpos, ht, hval, hslot⟩

/-- **An honest validator emits at most one Goldfish vote per slot**
(PROTOCOL.md#the-complete-protocol). Both emissions are at that slot's vote instant, the tick at
an instant is unique, and a tick emits at most one vote. -/
theorem emits_gfVote_unique (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {v : V} {u₁ u₂ : GoldfishVote V} {t₁ t₂ : Time}
    (h₁ : ρ.emits S v (Object.gfVote u₁) t₁) (h₂ : ρ.emits S v (Object.gfVote u₂) t₂)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨-, ht₁, -, hu₁⟩ := emits_gfVote_shape S h₁
  obtain ⟨-, ht₂, -, hu₂⟩ := emits_gfVote_shape S h₂
  have hteq : t₁ = t₂ := by
    rw [ht₁, ht₂, ← hu₁, ← hu₂, hslot]
  subst hteq
  obtain ⟨i₁, hi₁, ho₁⟩ := h₁
  obtain ⟨i₂, hi₂, ho₂⟩ := h₂
  obtain ⟨hb₁, he₁⟩ := List.getElem?_eq_some_iff.mp hi₁
  obtain ⟨hb₂, he₂⟩ := List.getElem?_eq_some_iff.mp hi₂
  have hidx : i₁ = i₂ :=
    (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp (by rw [he₁, he₂])
  subst hidx
  exact gfVote_emitted_unique S v _ _ ho₁ ho₂

/-! ## 3. What an honest store can show for a vote

`Availability/Pool.lean` says a pooled vote was processed, on its own or inside a
block; `Proofs.Bridges.processes_block_of_mem_T` says a stored block was processed. In
an honest name, `Unforgeable` turns either into an emission — `unforgeable` for the
bare vote, `carried_gf` for the carried one. -/










/- Kept because the retained `confirmedInTree_attestStore` consumer still
uses this erased confirmation-membership bridge. -/





/-- §6.1 a round-action instant is not its slot's proposal instant
(PROTOCOL.md#the-complete-protocol). -/
theorem a_ne_proposal_time (S : Setup V) {t : Time} {r : Round}
    (ht : t = S.hc.a S.E.Δ r) : t ≠ Protocol.proposal_time S.E (S.E.slotOf t) := by
  have hsc : t = Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) := by
    rw [ht]; exact Protocol.a_eq_support_cutoff_succ S.hc S.E r
  have hslot : S.E.slotOf t = S.hc.opening_slot r + 1 := by
    rw [hsc]; exact slotOf_support_cutoff S.E _
  rw [hslot, hsc]
  exact support_cutoff_ne_proposal_time S.E _

/-- §6.1 nor its slot's vote instant (PROTOCOL.md#the-complete-protocol). -/
theorem a_ne_vote_time (S : Setup V) {t : Time} {r : Round}
    (ht : t = S.hc.a S.E.Δ r) : t ≠ Protocol.vote_time S.E (S.E.slotOf t) := by
  have hsc : t = Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) := by
    rw [ht]; exact Protocol.a_eq_support_cutoff_succ S.hc S.E r
  have hslot : S.E.slotOf t = S.hc.opening_slot r + 1 := by
    rw [hsc]; exact slotOf_support_cutoff S.E _
  rw [hslot, hsc]
  exact support_cutoff_ne_vote_time S.E _



/-! The same field equations for a named read. The named runtime keeps the
core store in `NamedStore.core`; the bare `attestStore` computation is still
the field-only computation used by the action-store adapter. -/







/-! ## 6. O14 — the view-merge delivery bridge
(obligations O14; `Availability/Sync.lean`; PROTOCOL.md#the-complete-protocol)

`Sync.lean` carries relay at `t_GST = 0` and both directions of the tick-grid
bound; `Availability/Pool.lean` carries the guarded insertion. What is left is to
put them together, and the only real work is the **slot guard**: the receiving
store's slot must have reached the vote's, or the handler drops the vote
permanently.

It has: the vote is emitted at `t_s + Δ`, `Unforgeable.unforgeable` puts every
processing at or after that instant, relay at `t_GST = 0` puts it strictly before
`t_s + 2Δ`, and the receiver ticks at `t_s + Δ`. So the clock the handler reads
is inside `[t_s + Δ, t_s + 2Δ)` and the slot it reads is `s`. -/

def SlotOfClock (E : Env V) (st : Protocol.Store V) : Prop :=
  st.s = E.slotOf st.t

/-- The slot of an instant of `[t_s + Δ, t_s + 2Δ)` is `s` (PROTOCOL.md#the-complete-protocol).
`slotOfTime_add` with the offset read off the two bounds. -/
theorem slotOf_of_between (E : Env V) (s : Slot) {p : Time}
    (hlo : Protocol.vote_time E s ≤ p) (hhi : p < Protocol.support_cutoff E s) :
    E.slotOf p = s := by
  have hbounds : ∀ a d q : Int, 0 < d → a + d ≤ q → q < a + 2 * d →
      0 ≤ q - a ∧ q - a < 4 * d := by
    intro a d q hd h1 h2; omega
  obtain ⟨h0, h1⟩ := hbounds (E.t s) E.Δ p E.Δ_pos hlo hhi
  have hrw : p = 4 * E.Δ * (s : Time) + (p - E.t s) := by
    unfold Env.t slotStart
    ring
  rw [Env.slotOf, hrw]
  exact slotOfTime_add E.Δ E.Δ_pos s _ h0 h1





/-! ### The two routes into an honest pool -/




theorem vote_time_add_delta (E : Env V) (s : Slot) :
    Protocol.vote_time E s + E.Δ = Protocol.support_cutoff E s := by
  have h : ∀ a d : Int, a + d + d = a + 2 * d := by intro a d; ring
  exact h (E.t s) E.Δ

theorem support_cutoff_lt_view_freeze (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s < Protocol.view_freeze E s := by
  have h : ∀ a d : Int, 0 < d → a + 2 * d < a + 3 * d := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos




/-- An event that happens at or before `Γ` is inside the `≤ Γ` prefix. -/
theorem index_lt_stateAt_length (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {j : Nat} {e : Event V} (hj : ρ.events[j]? = some e) {Γ : Time} (hle : e.time ≤ Γ) :
    j < (ρ.events.filter (fun x => decide (x.time ≤ Γ))).length := by
  by_contra hcon
  have h := filter_false_of_index_ge S sch _ (downward_le Γ) (Nat.le_of_not_lt hcon) hj
  simp only [decide_eq_false_iff_not] at h
  exact h hle




/-- **The head-arrival conditional** (PROTOCOL.md#the-complete-protocol; obligations O14).

The block a vote names is in the reader's tree *and was processed before* `Γ`.

This is a **FOR-REVIEW conditional**, not a theorem, and it is the timing half
of the pair the re-stamp fold first surfaced. **Its discharge route is the
typed forwarding contract** (baseline `7b2efec`): `Synchrony.relay_block` says
an honest node forwards every block it *admits*, so an honest voter's own head
— admitted at that voter before its vote — reaches every honest node within
`Δ`, a whole `Δ` inside the support cutoff. What the rule does **not** cover is
the receiver's own admission of the forwarded head (the guard can still drop
it), which is the receiver-liveness qualifier below. The resolution half alone
is `SlotInduction.HeadsResolveIn`'s original content; the τ fold is what added
the stamp.

Note the direction the τ fold *fixed*: `τ ≥ stamp(H)` makes "inside a support
cutoff ⟹ the named block is processed" hold by construction, which is what the
old §6.2 `g0_clear` soundness argument needed and the re-stamp variant broke. The
conditional here is the converse — "delivered ⟹ inside the cutoff" — which no
encoding can supply for free.

**Admission scoping.** Delivery does not imply
processing at all: `on_block` drops a block the receiver's `Σ.F` does not
precede, and a vote whose head is dropped **never resolves at that store**
(`τ = +∞` there, permanently). The conditional's discharge therefore carries a
liveness qualifier — the named head is `⪰` the receiver's finalized block at
arrival — on top of the timing half. Recorded, not weakened silently. -/
def HeadArrivesBefore (T : Finset (Block V)) (tb : TimestampMap (Block V))
    (Γ : Time) (u : GoldfishVote V) : Prop :=
  ∃ H : Block V, Block.find? T u.head = some H ∧ stampedBefore tb Γ H = true

omit [Fintype V] in
/-- The `beforeCutoff`-to-`beforeCutoff`-at-`τ` step, at one vote
(PROTOCOL.md#the-complete-protocol). -/
theorem mem_tau_cutoff_of {T : Finset (Block V)} {tb : TimestampMap (Block V)}
    {tv : TimestampMap (GoldfishVote V)} {S' : Finset (GoldfishVote V)}
    {u : GoldfishVote V} {H : Block V} {Γ : Time}
    (hmem : u ∈ beforeCutoff tv Γ S') (hfind : Block.find? T u.head = some H)
    (hslot : H.slot ≤ u.slot)
    (hH : stampedBefore tb Γ H = true) :
    u ∈ beforeCutoff (Protocol.resolution_time T tb tv) Γ S' := by
  rw [beforeCutoff, Finset.mem_filter] at hmem ⊢
  exact ⟨hmem.1, Protocol.stampedBefore_resolution_of hfind hslot hmem.2 hH⟩

/-! ## 7. O15 — the merged view adds no equivocator in an honest name
(obligations O15, flag F2.4; PROTOCOL.md#the-complete-protocol)

`equivocates` is unqualified by slot (F2.2), so "at most one vote per honest
validator in the merged view" needs two things: the uniqueness of §3, and that
every vote the view holds really is of the slot the view is about. The pool half
is slot-uniform by `PoolStamps.slot`; the carried half is slot-uniform because
`carried_votes_well_formed` holds of every block an honest store holds — on the
wire it is `DeliveryWellFormed.wire`, and for a node's own proposal it is that
the proposer carries its own slot-`(s−1)` bucket (PROTOCOL.md#the-complete-protocol). -/





/-- **Named twin of `proposal_gf_votes`.** The engine's proposal duty
(`Protocol.NamedActions.proposal_with`) returns `Option (NamedBlock V)` — a
retained parent body is what makes it `some` — so the identity is stated at
the duty's own output, mirroring `TickBridges.proposedBlockAt_slot`'s own
`Option.map_eq_some_iff` unfolding. -/
theorem proposal_with_gf_votes (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) {B : NamedBlock V}
    (hB : Protocol.NamedActions.proposal_with contract source E hc nd st = some B) :
    B.gf_votes = st.core.gf_votes (st.core.s - 1) := by
  simp only [Protocol.NamedActions.proposal_with, Protocol.with_proposal_input,
    Option.map_eq_some_iff] at hB
  obtain ⟨parent, -, hBeq⟩ := hB
  rw [← hBeq]
  rfl

/-- Companion to `proposal_with_gf_votes`: the same duty output's own slot. -/
theorem proposal_with_slot (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) {B : NamedBlock V}
    (hB : Protocol.NamedActions.proposal_with contract source E hc nd st = some B) :
    B.slot = st.core.s := by
  simp only [Protocol.NamedActions.proposal_with, Protocol.with_proposal_input,
    Option.map_eq_some_iff] at hB
  obtain ⟨parent, -, hBeq⟩ := hB
  rw [← hBeq]
  rfl




/-- `Σ.sg_votes[r]` holds round-`r` attestations only (PROTOCOL.md#the-complete-protocol). -/
def SgRounds (st : Protocol.Store V) : Prop :=
  ∀ (r : Round) (a : CombinedAttestation V), a ∈ st.sg_votes r → a.round = r





omit [Fintype V] in
/-- §7.2 `round_votes` membership read back (PROTOCOL.md#the-complete-protocol): the
`a.confirmed ∈ round_votes` clause **is** the previous per-confirmed duplicate
test. -/
theorem mem_round_votes {st : Protocol.Store V} {a : CombinedAttestation V}
    {x : Option BlockId} :
    x ∈ Protocol.round_votes st a ↔
      ∃ b ∈ st.sg_pool a.round, b.val_index = a.val_index ∧ b.confirmed = x := by
  simp [Protocol.round_votes, and_assoc]







end Optimistic
end Proofs
end DecoupledConsensusModel

end
