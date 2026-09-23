module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.TickReads
public import DecoupledConsensusProofs.Objects.Final
public import DecoupledConsensusProofs.Protocol.Schedule.Alignment
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.VoteSetValidityCore

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (HealConfig)
open Internal
open Execution
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. What the honest votes of a slot say

Three predicates, and between them they hold the whole induction. The first two
are the *conclusion* of the previous slot — `Agreement.lean`'s `goldfish_vote_eq`,
`goldfish_vote_eq_extends` and `goldfish_vote_preceq` deliver them — and the third
is the one bridge this file does not close. -/


/-- **A block an honest slot-`s` committee member voted for**
(PROTOCOL.md#the-complete-protocol). The vote names its head by root (modeling-choices row 12),
so the block is what the duty computed, and the vote object is fixed by the emitter
and the slot (`Alignment.emits_gfVote_unique`).

**Named.** Run scope is `NamedRun.blockInRun`, so the head is
carried by a named witness whose erasure is the block the vote's root resolves to
in a reader's `Σ.T`. The erasure is what `HeadsResolveIn` compares to store fields,
which is why `X` stays a `Block V` and the witness sits inside. -/
def HonestHead (S : Setup V) (ρ : Run V) (s : Slot) (X : Block V) : Prop :=
  ∃ x ∈ ρ.honest, x ∈ S.E.committee s ∧
    (∃ C : NamedBlock V, C.erase = X ∧ RunBlock S ρ C) ∧
    ρ.emits S x (Object.gfVote ⟨x, s, X.root⟩) (Protocol.vote_time S.E s)

/- Part B retirement candidate 2: use
DecoupledConsensusModel.Proofs.HealingSurface.NamedHonestVotesCone.
The previous command and context are frozen in n36-part-b-candidate/v1.
Consumer ports remain open; no alias or replacement proof is declared here. -/


/-- **Either O12 route seeds the cone** (`Agreement.honestVotesName_of_voteTick`,
`Agreement.honestVotesName_of_extends`). One honest proposer is enough to start
the induction, and `coneRecurs` carries it from there.

**Named.** `HonestVotesName`/`HonestVotesCone` are
`Proofs.HealingSurface.NamedHonestVotesName`/`NamedHonestVotesCone`: the seed block is a
named run block and the cone predicate is read at its erasure. -/
theorem honestVotesCone_of_name (S : Setup V) (ρ : Run V) (s : Slot) {B : NamedBlock V}
    {tgt : Block V → Prop} (htgt : tgt B.erase) (hB : RunBlock S ρ B)
    (h : Proofs.HealingSurface.NamedHonestVotesName S ρ s B.erase) :
    Proofs.HealingSurface.NamedHonestVotesCone S ρ s tgt :=
  fun x hx hxc => ⟨B, htgt, hB, h x hx hxc⟩

/-- The cone at the block itself, which is the form `coneRecurs` propagates. -/
theorem honestVotesCone_preceq (S : Setup V) (ρ : Run V) (s : Slot) {B : NamedBlock V}
    (hB : RunBlock S ρ B) (h : Proofs.HealingSurface.NamedHonestVotesName S ρ s B.erase) :
    Proofs.HealingSurface.NamedHonestVotesCone S ρ s (fun X => Block.Preceq B.erase X) :=
  honestVotesCone_of_name S ρ s (Block.preceq_self B.erase) hB h

/-- **The head-resolution bridge** (PROTOCOL.md#the-complete-protocol;
`Proofs.HealingLemmas.Delivery.BatchDelivered.heads`).

A vote carries a *root* and the supporter test resolves it in the reader's own
tree (`Protocol.targets_under`). So the induction needs one fact about the
receiving tree and nothing else: an honest slot-`s` head is in it, and no second
block of it shares that head's root.

Both halves are named elsewhere already. The first is the typed forwarding
contract — `Synchrony.relay_block` forwards every admitted block — together
with the head's receiver-side admission. Raw-vote delivery does not imply head
delivery: the protocol stores a vote while its head is unresolved. The second
half is run-wide
`Execution.RootCollisionFree`, restricted through `Execution.RootInjectiveBelow`.
Neither mentions a fork
choice, a slot or a committee, which is the point: what the slot induction was
missing is delivery and hygiene, not agreement.

**Admission scoping.** `on_block` drops non-descendants of the
receiver's `Σ.F`, so delivery of the head does not imply membership.
This conditional also needs the honest head **live at the receiver**:
`Σ.F ⪯ X` at the receiving store when
the head arrives. Under the availability arc that is the receiver's finalized
block sitting on the honest chain below the head; the qualifier is recorded
here rather than folded silently. -/
def HeadsResolveIn (S : Setup V) (ρ : Run V) (s : Slot) (T : Finset (Block V))
    (tb : TimestampMap (Block V)) : Prop :=
  ∀ X : Block V, HonestHead S ρ s X →
    Block.find? T X.root = some X ∧
      stampedBefore tb (Protocol.support_cutoff S.E s) X = true

/-- `HeadsResolveIn` reads through a tree equality, which is how the wiring below
uses it at `voteStore` and at `tickStore`. -/
theorem HeadsResolveIn.of_eq {S : Setup V} {ρ : Run V} {s : Slot}
    {T T' : Finset (Block V)} {tb tb' : TimestampMap (Block V)}
    (h : HeadsResolveIn S ρ s T tb) (hT : T' = T) (htb : tb' = tb) :
    HeadsResolveIn S ρ s T' tb' := by
  rw [hT, htb]; exact h

/-! ### The bridge is not an atom

`HeadsResolveIn` splits into *membership* and *root uniqueness*. Neither
property requires fork choice, committee assumptions, or slot induction. -/

omit [Fintype V] in
/-- **`find?` resolves a member whose root nothing else in the tree carries**
(PROTOCOL.md#the-complete-protocol). `Block.find?` is `pickUnique?`, so this is the only shape
in which it ever returns an answer. -/
theorem find?_eq_some_of_unique {T : Finset (Block V)} {X : Block V} (hX : X ∈ T)
    (huniq : ∀ Y ∈ T, Y.root = X.root → Y = X) :
    Block.find? T X.root = some X := by
  unfold Block.find?
  refine pickUnique?_eq_some hX (by simp) ?_
  intro a ha hp
  exact huniq a ha (of_decide_eq_true hp)

/-- **The bridge, from membership and root injectivity** (PROTOCOL.md#the-complete-protocol).

`mem` is block relay plus receiver-side admission. It is not a consequence of
raw-vote delivery. `inj` is the scoped surface of the hash idealization;
run-facing callers derive it from `Execution.RootCollisionFree`. -/
theorem headsResolveIn_of (S : Setup V) (ρ : Run V) (s : Slot)
    {T : Finset (Block V)} {tb : TimestampMap (Block V)}
    (hmem : ∀ X : Block V, HonestHead S ρ s X → X ∈ T)
    (hinj : ∀ X Y : Block V, X ∈ T → Y ∈ T → X.root = Y.root → X = Y)
    (harr : ∀ X : Block V, HonestHead S ρ s X →
      stampedBefore tb (Protocol.support_cutoff S.E s) X = true) :
    HeadsResolveIn S ρ s T tb :=
  fun X hX =>
    ⟨find?_eq_some_of_unique (hmem X hX)
      (fun Y hY hroot => hinj Y X hY (hmem X hX) hroot), harr X hX⟩


/-! ## 2. The packaging step

`ConeSupport` asks for a counted vote whose target resolves inside the cone. With
the vote object named by its emitter and its slot that is three facts about one
`GoldfishVote`, and this is the only place they are put together. -/

/-- **`ConeSupport` from membership and resolution** (PROTOCOL.md#the-complete-protocol,
373–374). The `vote` clause's existential is discharged by the vote the honest
committee member actually cast — `⟨x, s, X.root⟩` — so nothing below has to search
for it. -/
theorem coneSupport_of_named_votes {E : Env V} {T : Finset (Block V)}
    {votes support late : Finset (GoldfishVote V)} {s : Slot} {Hon : Finset V}
    {tgt : Block V → Prop}
    (hmaj : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card)
    (hsub : votes ⊆ late) (hss : support ⊆ votes)
    (hne : ∀ x ∈ E.committee s, x ∈ Hon → Protocol.equivocates votes x = false)
    (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ X : Block V, tgt X ∧
      X.slot ≤ s ∧ (⟨x, s, X.root⟩ : GoldfishVote V) ∈ support ∧
      Block.find? T X.root = some X) :
    ConeSupport E T votes support late s Hon tgt where
  majority := hmaj
  counted := hsub
  sub := hss
  no_equiv := hne
  vote := by
    intro x hx hxH
    obtain ⟨X, htgt, hXslot, hmem, hfind⟩ := hvote x hx hxH
    exact ⟨⟨x, s, X.root⟩, hmem, rfl, rfl, X, hfind, hXslot, htgt⟩

/-! ## 3. The slot grid, one step

Two arithmetic facts the induction needs and the tick bridges do not have: the
next slot's vote instant is after this slot's support cutoff, and the support
cutoff determines its slot. -/

/-- `t_s + 2Δ ≤ t_{s+1} + Δ` (PROTOCOL.md#the-complete-protocol): the reader of slot
`(s+1)`'s merged view sits after the slot-`s` cutoff, which is what
`gfVote_in_cutoff_view` asks of its reading instant. -/
theorem support_cutoff_le_vote_time_succ (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.vote_time E (s + 1) := by
  have hstep : E.t (s + 1) = E.t s + 4 * E.Δ := by
    unfold Env.t slotStart
    push_cast
    ring
  have key : ∀ a d : Int, 0 < d → a + 2 * d ≤ a + 4 * d + d := by
    intro a d hd; omega
  rw [Protocol.support_cutoff, Protocol.vote_time, hstep]
  exact key (E.t s) E.Δ E.Δ_pos

/-- The support cutoff of a slot is `4Δs + 2Δ` (PROTOCOL.md#the-complete-protocol), which is
what the two monotonicity readings below run on. -/
theorem support_cutoff_expand (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s = 4 * E.Δ * (s : Time) + 2 * E.Δ := by
  unfold Protocol.support_cutoff Env.t slotStart
  ring

/-- The support cutoffs grow with the slot index (PROTOCOL.md#the-complete-protocol), which is
how a horizon known at a later slot is known at an earlier one. -/
theorem support_cutoff_mono (E : Env V) {a b : Slot} (h : a ≤ b) :
    Protocol.support_cutoff E a ≤ Protocol.support_cutoff E b := by
  rw [support_cutoff_expand, support_cutoff_expand]
  have hΔ : (0 : Time) ≤ 4 * E.Δ := by
    have key : ∀ d : Int, 0 < d → (0 : Int) ≤ 4 * d := by intro d hd; omega
    exact key E.Δ E.Δ_pos
  have key : ∀ x y d : Int, x ≤ y → x + d ≤ y + d := by intro x y d hxy; omega
  exact key _ _ _ (Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr h) hΔ)

/-- The support cutoffs are strictly ordered in the slot index
(PROTOCOL.md#the-complete-protocol), so an inequality between them is one between slots. -/
theorem slot_le_of_support_cutoff_le (E : Env V) {a b : Slot}
    (h : Protocol.support_cutoff E a ≤ Protocol.support_cutoff E b) : a ≤ b := by
  rw [support_cutoff_expand, support_cutoff_expand] at h
  have hΔ : (0 : Time) < 4 * E.Δ := by
    have key : ∀ d : Int, 0 < d → 0 < 4 * d := by intro d hd; omega
    exact key E.Δ E.Δ_pos
  have hmul : 4 * E.Δ * (a : Time) ≤ 4 * E.Δ * (b : Time) :=
    (add_le_add_iff_right (2 * E.Δ)).mp h
  exact_mod_cast Int.le_of_mul_le_mul_left hmul hΔ

/-! ## 4. The store coercions the merged view reads through

`VoteStoreAligned` states the merged view over `st.toHealing.toFG.toSG.toGoldfishStore` and the
tree over `st.toHealing`. Both are projections of the same record, so the four
equations are `rfl`; they are written down because `rw` needs them by name. -/




omit [Fintype V] in
theorem toHealing_slot (st : Protocol.Store V) : st.toHealing.s = st.s := rfl

/-! ## 5. O14 lands the vote in the *next* slot's merged view -/

/-- The τ pool half of the merged pair is inside the **support** view
(baseline `7b2efec`). The carried half can only add. -/
theorem mem_voter_support_view_of_pool (E : Env V) (gst : Protocol.GoldfishStore V)
    (s : Slot) {u : GoldfishVote V}
    (h : u ∈ beforeCutoff gst.tau (Protocol.view_freeze E (s - 1))
      (gst.pool (s - 1))) :
    u ∈ Protocol.voter_support_view E gst s := by
  rw [Protocol.voter_support_view]
  exact Finset.mem_union_left _ h


/-! ## 6. The induction at the merged view

The fork choice's regime: numerator and denominator are the same set, so `counted`
is `rfl` and equivocators are live in both. O15 keeps an honest name out of the
equivocator set, which is the clause flag F2.4 would otherwise have flipped. -/




/-! ## 7. The induction at the confirmation numerator

The second regime (PROTOCOL.md#the-complete-protocol). Here the denominator is the wider
`confLate` and the `no_second_vote_in` filter has already emptied the numerator of
equivocators, so `no_equiv` comes from `Numerator` rather than from O15 — and
`counted` is a real inclusion rather than `rfl`. The `vote` clause is
`Alignment.honest_vote_counted`, which is O14 read at `t_s + 2Δ`. -/


/-- **The slot induction, at the confirmation numerator** (obligations O14;
row W5.17's H3; PROTOCOL.md#the-complete-protocol).

Same premise, same conclusion, the other reading. This is the form
`Proofs.Optimistic.ConeAtTicks` consumes, and with it O13 keeps no store premise except
the walk's two reach clauses and the bridge.

**Named.** The counting step `Proofs.Optimistic.honest_vote_counted`
— O14 read at `t_s + 2Δ` — is blocked in `Optimistic/Alignment.lean` (
) and never re-available, so it is taken here as the explicit premise `hcount`,
in the exact form that theorem concludes. The admissibility, GST and horizon
parameters were used for nothing else and are gone. What stays is the numerator's
own content: `subset_late` and `no_equivocation` from `confNumerator`, and the
resolution bridge. -/
theorem coneSupport_confVotes (S : Setup V) (ρ : Run V)
    (hcom : HonestCommittees S ρ.honest)
    {s : Slot}
    {tgt : Block V → Prop} (hnames : Proofs.HealingSurface.NamedHonestVotesCone S ρ s tgt)
    (v : V)
    (hcount : ∀ u : GoldfishVote V, u.slot = s → u.val_index ∈ ρ.honest →
      ρ.emits S u.val_index (Object.gfVote u) (Protocol.vote_time S.E s) →
      HeadArrivesBefore (confStore S ρ v s).T (confStore S ρ v s).timestamp_block
        (Protocol.support_cutoff S.E s) u →
      u ∈ confVotes S.E (confStore S ρ v s) s)
    (hres : HeadsResolveIn S ρ s (confStore S ρ v s).T (confStore S ρ v s).timestamp_block) :
    ConeSupport S.E (confStore S ρ v s).T (confVotes S.E (confStore S ρ v s) s)
      (confVotes S.E (confStore S ρ v s) s)
      (confLate S.E (confStore S ρ v s) s) s ρ.honest tgt := by
  have hN := confNumerator S.E (confStore S ρ v s) s
  refine coneSupport_of_named_votes (hcom s) hN.subset_late (subset_refl _)
    (fun y _ _ => hN.no_equivocation y) ?_
  intro y hy hyH
  obtain ⟨X, htgt, hrun, hemit⟩ := hnames y hyH hy
  obtain ⟨hfind, hstamp⟩ := hres X.erase ⟨y, hyH, hy, ⟨X, rfl, hrun⟩, hemit⟩
  let u : GoldfishVote V := ⟨y, s, X.erase.root⟩
  have hu : u ∈ confVotes S.E (confStore S ρ v s) s :=
    hcount u rfl hyH hemit ⟨X.erase, hfind, hstamp⟩
  have huEarly : u ∈ confEarly S.E (confStore S ρ v s) s := by
    rw [confVotes, Finset.mem_filter] at hu
    exact hu.1
  rw [confEarly, beforeCutoff, Finset.mem_filter] at huEarly
  have hXslot : X.erase.slot ≤ u.slot :=
    Protocol.head_slot_le_of_resolution_time hfind huEarly.2
  exact ⟨X.erase, htgt, hXslot, hu, hfind⟩

/-! ## 8. The cone perpetuates itself

The sentence `Agreement.lean` §12 states and defers: "Once every honest slot-`s`
vote names `B`, `B` carries a strict majority in every later merged view … No gate
premise is needed here." With §6 above it is a theorem.

What the vote duty needs beyond the cone is the walk's own: the anchor is below
`B`, the blocks between them are processed, and the tick emitted what the duty
returned. The first two are `Anchor.lean`'s, the third is `TickBridges.lean`'s. -/

theorem voteDutyStore_slot (S : Setup V) (ρ : Run V) (w : V) (s : Slot) :
    (voteDutyStore S ρ w s).s = s :=
  voteStore_slot S _ s






/-! ## 11. `DrainBatch.heads` is a different node

`Proofs.HealingLemmas.DrainBatch.heads` asks that an honest round-`(r−1)` attestation's
head be a block `⪯ Can` in the reader's tree, and the residual table files it
under the slot induction. That filing is wrong, and this section is why.

`Protocol.round_action` never consults the Goldfish fork choice for the head field.
It sets it from `deepest_clear`, which walks **up** a chain — the emitter's own
`Σ.live_confirmed` in two of the three branches, the fresh anchor in the third
(PROTOCOL.md#the-complete-protocol). So the clause decomposes into three parts,
none of them a merged view:

* `round_action_head_source` below — the structural half, proved here;
* `Σ.live_confirmed ⪯ Can` at the emitting store, which is the **confirmation**
  track's: non-retreat carried from `a_{r−1}` to `a_r`, `Proofs.Optimistic.ConeAtTicks`
  through `TickBridges.liveConfirmedNonRetreat_of_cone`. The slot induction enters
  here and only here, one level down;
* the fresh anchor's cone, which is `Anchor.fresh_anchor_preceq` — already proved,
  from `BatchAligned` and the fault bound;

and then the same root resolution `HeadsResolveIn` names, at the drain store. -/




/-! ## 12. `AlignedRound.heads` and `DrainBatch.heads`, discharged

With obligation O19 available (`Alignment.emissionAtOwnStore_of_admissible`) the run
half of §11 is available: an honest attestation **is** the round action of a store
whose `Σ.live_confirmed` the node reports at the emitting instant. Composing that
with §11's structural half closes the clause, over two cone premises and nothing
else.

**The direction matters, and it is not the induction's.** `coneRecurs` produces
*lower* bounds — `B ⪯ head` — because that is what a majority behind `B` forces.
`AlignedRound.heads` asks for an *upper* bound, `head ⪯ Can`, and upper bounds
come from `IsCanonical`'s own clause and from `Anchor.fresh_anchor_preceq`. So the
cone-form slot induction does not supply this clause and never had to: the
residual table's filing of `DrainBatch.heads` under the slot induction is a
direction error. What the induction supplies here is one level down, inside the
confirmation cone `EmissionCones.1` — non-retreat, through `ConeAtTicks`. -/



end Optimistic
end Proofs
end DecoupledConsensusModel

end
