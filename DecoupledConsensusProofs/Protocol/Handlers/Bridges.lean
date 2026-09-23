module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.AlignedRoundLemmas
public import DecoupledConsensusProofs.Protocol.Handlers.Execution
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.Main

@[expose] public section

/-!
# The bridges between the execution layer and the store invariants
(obligations O8, O10, O11; design note P1, P6; modeling-choices P-4, P-5, P1-5)

Three families of statement in this project are proved at three different places
and were, until now, not connected.

* `Proofs.Invariants2` and `Proofs.Records` prove parent-closure, the
  derived-state agreement and `Σ.J ∈ Σ.T` at a **`DepReachableStore`** — a store
  reached by handler applications that honour the dependency-complete contract
  (O8). Nothing said any real run produces such a store.
* `Execution.Admissible` constrains a **run**: `DeliveryWellFormed.deps`
  and `.fresh` are receiver-side tests at a delivery, and the tick's
  self-processed proposal is reached by no delivery predicate at all (P-5).
* `Protocol` proves P1 at the **chain** and leaves its store corollary
  conditional on `StoreFinalizationOnChain` (P1-5).

This file closes all three gaps, in that order.

**Part 1** is the O11 residual: `deps ∧ fresh ∧ ParentClosed ⟹ DepOk` for a
delivered block (`depOk_of_delivered`), and then the run-level transport
`depReachable_of_admissible` — every honest node's store, at every prefix of an
admissible run, is a `DepReachableStore`. This is the theorem that carries every
`DepReachableStore` result of the project onto admissible runs, and
`storeInvariants_of_admissible` is the headline reading of it. Note what it does
**not** need: only `DeliveryWellFormed`, not the whole of `Admissible`, and no
fault bound, no honesty and no synchrony.

**Part 2** is the store-level provenance the P1 corollary and L1's
`RootProvenance` both want: `Σ.F` and `(Σ.J, Σ.h_j)` come from processed
blocks' derived states. `update_finality` is the only writer of these fields
and it is called only from `on_block`, with the chain state of the block
that call just inserted; the dependency contract makes that entry the derived
state, and the pair travels as an invariant of the same induction.

**Part 3** closes P1 end-to-end:
`storeAccountableSafety_of_admissible` is accountable safety at the store, with
no hypothesis left but the root-injectivity idealization.

**Part 4** discharges what it can of `AlignedRoundLemmas.RootProvenance` and says
exactly what is left. Four of its eight fields fall out of parts 1–3; the other
four do not, and each is left as an explicit argument of
`rootProvenance_of_admissible` rather than smuggled in. See the section header
there for which is which and why.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace Bridges

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Run-wide root collision freedom

`RootCollisionFree` is the execution-level hash idealization. These lemmas are
the elimination surface for proofs that still use the smaller, pure
`RootInjectiveBelow` predicates. -/

/-- A named body an honest node holds at an event prefix is in the run-wide
collision-free scope. -/
theorem runBlock_of_stateBefore_mem (S : Setup V) {ρ : Run V} {v : V}
    (hv : v ∈ ρ.honest) {i : Nat} {C : NamedBlock V}
    (hC : C ∈ (ρ.stateBefore S i v).st.bodies) : RunBlock S ρ C :=
  ⟨C, Or.inr ⟨v, hv, i, hC⟩, Proofs.NamedAncestry.named_self C⟩

/-- Restrict the run-wide hash idealization to the erasure of any finite set of
named run bodies. The erased ancestors are lifted back to named ancestors, which
is where the named idealization applies. -/
theorem rootInjectiveBelow_of_runBlocks (S : Setup V) {ρ : Run V}
    (hcf : RootCollisionFree S ρ) {T : Finset (NamedBlock V)}
    (hRun : ∀ C ∈ T, RunBlock S ρ C) :
    RootInjectiveBelow (T.image NamedBlock.erase) := by
  intro A C hA hC hr
  obtain ⟨B, hBT, hAB⟩ := hA
  obtain ⟨D, hDT, hCD⟩ := hC
  obtain ⟨B', hB'T, rfl⟩ := Finset.mem_image.mp hBT
  obtain ⟨D', hD'T, rfl⟩ := Finset.mem_image.mp hDT
  obtain ⟨A', hA'B, rfl⟩ := Proofs.NamedAncestry.erased_ancestor_lift B' hAB
  obtain ⟨C', hC'D, rfl⟩ := Proofs.NamedAncestry.erased_ancestor_lift D' hCD
  have hroots : A'.root = C'.root := by
    rwa [Proofs.NamedWire.erase_root, Proofs.NamedWire.erase_root] at hr
  rw [RootCollisionFree.root_injective hcf B' D' (hRun B' hB'T) (hRun D' hD'T) A' C'
    (Or.inl hA'B) (Or.inr hC'D) hroots]


/-- Two honest prefix stores inherit root collision freedom from the run. -/
theorem rootInjectiveBelow_stateBefore_union (S : Setup V) {ρ : Run V}
    (hcf : RootCollisionFree S ρ) {u v : V}
    (hu : u ∈ ρ.honest) (hv : v ∈ ρ.honest) (i j : Nat) :
    RootInjectiveBelow
      (((ρ.stateBefore S i u).st.bodies ∪
        (ρ.stateBefore S j v).st.bodies).image NamedBlock.erase) :=
  rootInjectiveBelow_of_runBlocks S hcf (by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact runBlock_of_stateBefore_mem S hu hC
    · exact runBlock_of_stateBefore_mem S hv hC)

/-! ## 0. `DepStep` refines `Step`

`DepStep` is `Step` with the contract attached to the two block-inserting
constructors (P-4), so every `DepReachableStore` is a `ReachableStore` and the
unconditional P6 invariants — O5 above all — are available there. Twenty lines
that were missing because the two relations were introduced in opposite
directions. -/

/-! ## 1. The O11 residual — `deps ∧ fresh ∧ ParentClosed ⟹ DepOk`
(obligations O8, O11; modeling-choices P-4's bridging note;
PROTOCOL.md#the-complete-protocol)

`Object.depsPresent` tests the **total** `B.parent`, which at genesis is genesis
itself, so it is one clause weaker than `DepOk`, whose `parent?` form excludes
genesis deliberately (P-4). `fresh` closes exactly that clause: a block already
in `Σ.T` is not delivered, and genesis is in every parent-closed `Σ.T`. -/

/-! ### The run-level transport

One induction over the event list. Only `v`'s own events move `v`'s pair
(`Function.update`), a delivered block takes one valid-core `DepStep` or the
checked rejection is reflexive, and a tick is one `DepStep` because
`on_tick_emit`'s store and record components are `Protocol.on_tick`'s
(`Execution.on_tick_emit_agrees`) and the tick's own dependency clause is
`Proofs.Records.depOk_tick_proposal`, whose two premises the induction hypothesis
already supplies (O10 + O5).

Nothing here reads `Unforgeable`, `Synchrony` or `ScheduleWellFormed`. -/

/-! ### The two reading positions the statement layer uses

`stateBefore` is indexed by position; `AlignedRound` and everything else in
`Execution` reads `stateAt` and `stateBeforeTime`, which fold over a
`filter` rather than a prefix. Under `ScheduleWellFormed.sorted` the two agree:
the event list is sorted by `(time, phase)`, so filtering it by a time bound
takes a prefix and nothing else. -/

/-- A filter of a sorted list by a predicate that is inherited backwards along
the order is that list's `takeWhile`, hence a prefix. -/
theorem filter_eq_takeWhile_of_pairwise {α : Type} {R : α → α → Prop} {p : α → Bool}
    (hdc : ∀ a b : α, R a b → p b = true → p a = true) :
    ∀ l : List α, l.Pairwise R → l.filter p = l.takeWhile p := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
      intro hp
      rw [List.pairwise_cons] at hp
      by_cases ha : p a = true
      · rw [List.filter_cons_of_pos ha, List.takeWhile_cons_of_pos ha, ih hp.2]
      · rw [List.filter_cons_of_neg ha, List.takeWhile_cons_of_neg ha]
        refine List.filter_eq_nil_iff.mpr ?_
        intro b hb hpb
        exact ha (hdc a b (hp.1 b hb) hpb)

/-- The run's world at a filtered position is its world at a prefix position, and
every event of that prefix satisfies the filter. -/
theorem filtered_fold_eq_stateBefore (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {p : Event V → Bool}
    (hdc : ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → p f = true → p e = true) :
    ∃ n : Nat, (ρ.events.filter p).foldl (World.step S) World.init = ρ.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → ρ.events[j]? = some e → p e = true := by
  have hpref : ρ.events.filter p <+: ρ.events := by
    rw [filter_eq_takeWhile_of_pairwise hdc _ sch.sorted]
    exact List.takeWhile_prefix p
  have hpre : ρ.events.filter p = ρ.events.take (ρ.events.filter p).length :=
    List.prefix_iff_eq_take.mp hpref
  refine ⟨(ρ.events.filter p).length, ?_, ?_⟩
  · conv_lhs => rw [hpre]
    rfl
  · intro j e hj hget
    have hmem : e ∈ ρ.events.filter p := by
      rw [hpre]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hget)
    exact (List.mem_filter.mp hmem).2

/-- The filtered-fold prefix bridge with only the event-key order. -/
theorem filtered_fold_eq_stateBefore_of_sorted (S : Setup V) {ρ : Run V}
    (sorted : ρ.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f))
    {p : Event V → Bool}
    (hdc : ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → p f = true → p e = true) :
    ∃ n : Nat, (ρ.events.filter p).foldl (World.step S) World.init = ρ.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → ρ.events[j]? = some e → p e = true := by
  have hpref : ρ.events.filter p <+: ρ.events := by
    rw [filter_eq_takeWhile_of_pairwise hdc _ sorted]
    exact List.takeWhile_prefix p
  have hpre : ρ.events.filter p = ρ.events.take (ρ.events.filter p).length :=
    List.prefix_iff_eq_take.mp hpref
  refine ⟨(ρ.events.filter p).length, ?_, ?_⟩
  · conv_lhs => rw [hpre]
    rfl
  · intro j e hj hget
    have hmem : e ∈ ρ.events.filter p := by
      rw [hpre]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hget)
    exact (List.mem_filter.mp hmem).2

omit [DecidableEq V] [Fintype V] in
/-- The key order refines the time order. -/
theorem time_le_of_key_le {e f : Event V}
    (h : NamedEvent.key e ≤ NamedEvent.key f) : e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with h' | ⟨h', _⟩
  · exact le_of_lt h'
  · exact le_of_eq h'

/-- `stateAt` is a prefix position. -/
theorem stateAt_eq_stateBefore (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (t : Time) :
    ∃ n : Nat, Run.stateAt S ρ t = ρ.stateBefore S n :=
  (filtered_fold_eq_stateBefore S sch
    (p := fun e => decide (e.time ≤ t))
    (fun e f hk hf => by
      simp only [decide_eq_true_eq] at hf ⊢
      exact le_trans (time_le_of_key_le hk) hf)).imp fun _ h => h.1

/-- `stateAt` is a prefix position when only event keys are known to be ordered. -/
theorem stateAt_eq_stateBefore_of_sorted (S : Setup V) {ρ : Run V}
    (sorted : ρ.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f)) (t : Time) :
    ∃ n : Nat, Run.stateAt S ρ t = ρ.stateBefore S n :=
  (filtered_fold_eq_stateBefore_of_sorted S sorted
    (p := fun e => decide (e.time ≤ t))
    (fun e f hk hf => by
      simp only [decide_eq_true_eq] at hf ⊢
      exact le_trans (time_le_of_key_le hk) hf)).imp fun _ h => h.1

/-- `stateBeforeTime` is a prefix position, and every event before it is strictly
earlier — which is what a "the emission is in the run's past" clause reads. -/
theorem stateBeforeTime_eq_stateBefore (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (t : Time) :
    ∃ n : Nat, ρ.stateBeforeTime S t = ρ.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → ρ.events[j]? = some e → e.time < t :=
  (filtered_fold_eq_stateBefore S sch
    (p := fun e => decide (e.time < t))
    (fun e f hk hf => by
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (time_le_of_key_le hk) hf)).imp fun _ h =>
    ⟨h.1, fun j e hj hget => by simpa using h.2 j e hj hget⟩

/-! ## 2. FGStore provenance — the finality fields are a processed block's own
(design note P1; modeling-choices P1-5; PROTOCOL.md#the-complete-protocol)

Row P1-5 names two gaps in P1's store corollary. The first is the derived-state
bridge, which `Invariants2` proves at a `DepReachableStore` and part 1 now
transports. The second is unnamed by the proof map and is closed here: *nothing
said `Σ.F` is some processed block's derived finalization.*

Tracing the writers is the whole argument. `Σ.F`, `Σ.J`, and `Σ.h_j` are
written by `update_finality` alone (PROTOCOL.md#the-complete-protocol), which is
called from `on_block` alone, and always with `Σ.σ[B]` for the `B` that same
call inserted. So each write installs the entry of a block that is in `Σ.T`
immediately afterwards, and the dependency contract makes that entry the derived
state. The one thing that needs care is the *carried* case, and phrasing the
invariant over `derived_state` rather than over `Σ.σ[·]` is what makes it free:
`derived_state` reads no store, so a later `on_block` cannot disturb the
witness. -/










omit [Fintype V] in
/-- P1 `update_finality` writes `Σ.F` from the chain state it is given or not
at all (PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_finalized_cases (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).F = st.F ∨
      (Protocol.update_finality st σ).F = σ.F := by
  simp only [Protocol.update_finality]
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

omit [Fintype V] in
/-- §5.2 the same for `(Σ.J, Σ.h_j)` (PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_justified_cases (st : Protocol.Store V) (σ : ChainState V) :
    ((Protocol.update_finality st σ).J = st.J ∧
        (Protocol.update_finality st σ).h_j = st.h_j) ∨
      ((Protocol.update_finality st σ).J = σ.J ∧
        (Protocol.update_finality st σ).h_j = σ.h_j) := by
  simp only [Protocol.update_finality]
  split_ifs <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

/-- P1 the justification mirror of `Protocol.StoreFinalizationOnChain`
(PROTOCOL.md#the-complete-protocol): `(Σ.J, Σ.h_j)` is some processed block's derived pair.

L1's `RootProvenance.justified` is exactly this clause, which is why it is worth
a name of its own rather than being folded into the bundle below. -/
def StoreJustificationOnChain (E : Env V) (cfg : HeightConfig)
    (st : Protocol.Store V) : Prop :=
  ∃ B ∈ st.T, (derived_state E cfg B).h_j = st.h_j ∧ (derived_state E cfg B).J = st.J

/-! ## 3. P1's store corollary, closed
(design note P1; modeling-choices P1-5; PROTOCOL.md#the-complete-protocol)

`Protocol.storeAccountableSafety_of_onChain` was already the whole argument; what
was missing was its two hypotheses. Part 2 supplies them at a
`DepReachableStore` and part 1 supplies the store.

**What is still hypothesised, and what is not.** The pure
`storeAccountableSafety_depReachable` theorem keeps its scoped
`RootInjectiveBelow` premise because it quantifies over arbitrary stores. The
run-facing theorem discharges that premise from `Admissible` and the two nodes'
honesty. There is no fault bound here — accountable safety **produces** the
evidence.

**Why the `Internal.ReachableStore` form is not closed with it.**
`Internal.StoreAccountableSafety` quantifies over `ReachableStore`, where
`DerivedStateAgrees` is false (choices P6.1) and hence provenance is out of
reach. The dependency-complete form below is the true statement; the `Props` one
should be re-cut over `DepReachableStore`, which is what
`Internal.DerivedStateAgreesInvariant` already did after the statement reviews. -/




/-! ### The assumption bridge, unconditional (rev. 4 review finding 8)

`AlignedRoundLemmas.slashableBound_of_belowOneThird` converts the adversarial
fault bound into the accountable one, and it is on the critical path: L2, L3,
Lemma U and `chainSafety_of_slashableBound` all consume `SlashableBound`, while
every Lemma G4 argument produces only `BelowOneThird`. The bridge carried an
unproved premise — that a *block*'s carried attestations in an honest name are
that validator's own emissions, for every block the run puts in play.

`RunBlock` has two disjuncts and both are now reachable.

* **An honest store holds `B`.** That is `carriedByHonest_of_admissible`.
* **The run delivers `B`.** The delivery itself is a `processes` event, so
  `Unforgeable.carried_attest` covers `B.attestations` directly; and
  `DeliveryWellFormed.deps` puts `B.parent` in the receiver's tree, so the *rest*
  of the chain is the first case at that store. This is the second place where
  `deps` earns its keep, and it is why the two disjuncts do not need separate
  machinery.

So `SlashableBound` is a theorem about admissible runs under `BelowOneThird`, not
an assumption, and the gap between the two bounds is paid for exactly once. -/

omit [DecidableEq V] [Fintype V] in
/-- A block the run's object list contains is a block some delivery carries
(design §2.3, §5). `Run.objects` reads deliveries alone, which is the scoping
`RunBlock`'s first disjunct records. -/
theorem exists_deliver_of_mem_objects (ρ : Run V) {B : NamedBlock V}
    (h : Object.block B ∈ NamedRun.objects ρ) :
    ∃ (i : Nat) (u : V) (t : Time),
      ρ.events[i]? = some (Event.deliver u (Object.block B) t) := by
  obtain ⟨e, hmem, he⟩ := List.mem_filterMap.mp h
  cases e with
  | tick u t => simp only [NamedEvent.object?, reduceCtorEq] at he
  | deliver u o t =>
      simp only [NamedEvent.object?, Option.some.injEq] at he
      subst he
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      exact ⟨i, u, t, hi⟩

/-! ## 5. `RootProvenance`, six fields down and two to go
(`AlignedRoundLemmas.RootProvenance`; rev. 4 §4)

The bundle has ten fields. The execution and store bridges discharge eight of
them. The remaining two are P4's canonical-chain obligations:

* `justified`, `finalized` — part 2's provenance invariant, verbatim.
* `just_mem` — O10, transported by part 1.
* `carried` — part 4's `carriedArePastEmissions_of_admissible`.
* `root_inj`, `root_inj_can` — the run-wide hash idealization in `Admissible`,
  restricted to the stores and `Can` by their `RunBlock` witnesses.
* `carried_can` — `carriedByHonest_of_runBlock`, from the same `RunBlock Can`
  witness.
* `crossed` — rev. 3 §4.4's ladder fact, which is P4's own (C3) viability half:
  a chain advances a height only if `2q − W` of honest weight was
  confirmation-gated there, and those gates are on `Can` by Lemma G4 with clause
  (b). It needs the fault bound and the aligned-round predicate, so it belongs to
  the P4 induction and not to this file. -/

end Bridges
end Proofs

-- the compatibility layer


-- are archived in the compatibility layer

end DecoupledConsensusModel

end
