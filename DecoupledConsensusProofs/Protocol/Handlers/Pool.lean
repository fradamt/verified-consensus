module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.Final
public import DecoupledConsensusProofs.Generic.Sync

@[expose] public section

/-!
# The Goldfish pool along the run — O14's missing step
(obligations O14; `Availability/Sync.lean`; PROTOCOL.md#the-complete-protocol,
1345–1355)

`Availability/Sync.lean` has both directions of the tick-grid bound and relay at
`t_GST = 0`, and its header says what is left: *pool membership through
`on_goldfish_vote`'s guards*. This module is that step, and nothing else.

## What the pool carries

`Σ.gf_votes[·]` and `Σ.timestamp_vote[·]` are written by one handler,
`on_goldfish_vote`, and it writes them together: a vote that clears the two
guards is appended to its own slot's bucket and stamped with `Σ.t` in the same
record update (PROTOCOL.md#the-complete-protocol). Four facts follow, and they travel as
one bundle because the same case analysis proves all four.

* `slot` — bucket `k` holds only votes of slot `k`. The insertion is into
  `vote.slot`, so this is immediate, and it is what makes a merged view's
  pool half slot-uniform (F2.2's counterpart).
* `stamped` and `pooled` — the pool and the stamp map have the same domain.
  `pooled` is the one that matters: a *stamped* vote is in the pool, so the
  duplicate guard fires on it and the stamp is never rewritten. That is
  "`Σ.timestamp[·]` is written exactly once" (PROTOCOL.md#the-complete-protocol), derived.
* `bounded` — a stamp never exceeds the store's own clock. The stamp *is* the
  clock at insertion, and the clock only moves forward, which at the run level
  is sortedness.

`PoolStep` is the arrow these four travel along: from a store that carries them,
one handler application carries them and adds no vote and no stamp of its own to
the earlier ones. It is reflexive and transitive, which is what lets the tick be
handled as its own five-branch composition rather than as sixteen `split_ifs`
cases.

## What the run adds

Two transports and one insertion lemma:

* `poolStamps_stateBefore` — every honest store of every prefix carries the
  bundle;
* `pool_carry` — a vote in the pool at one prefix is in the pool at every later
  one, with the same stamp;
* `mem_pool_of_processes` — a vote an honest node **processes** is in that node's
  pool immediately afterwards, stamped at or before the processing time, provided
  the two guards clear. The guards are the caller's obligation and are named:
  the slot guard needs the store's slot to have reached the vote's, and the cap
  needs the emitter not to be a pool equivocator. `Optimistic/Alignment.lean`
  discharges both for an honest emitter.

Every declaration here is proved without an additional axiom.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The bundle -/

/-- **What a Goldfish pool carries** (PROTOCOL.md#the-complete-protocol).
Four clauses, one case analysis: the bucket is slot-uniform, the pool and the
stamp map have the same domain, and no stamp is later than the store's clock. -/
structure PoolStamps (st : Protocol.Store V) : Prop where
  /-- §2.2 bucket `k` holds slot-`k` votes only (PROTOCOL.md#the-complete-protocol). -/
  slot : ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k → u.slot = k
  /-- §1 a pooled vote is stamped (PROTOCOL.md#the-complete-protocol). -/
  stamped : ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k →
    (st.timestamp_vote u).isSome = true
  /-- §1 a stamped vote is pooled — the clause that makes the stamp write-once
  (PROTOCOL.md#the-complete-protocol). -/
  pooled : ∀ u : GoldfishVote V, (st.timestamp_vote u).isSome = true →
    u ∈ st.gf_votes u.slot
  /-- §1 a stamp is the clock at insertion, so never beyond the clock now
  (PROTOCOL.md#the-complete-protocol). -/
  bounded : ∀ (u : GoldfishVote V) (c : Stamp), st.timestamp_vote u = some c →
    c ≤ (st.t : Stamp)

/-- **What one handler application adds**: votes and stamps already held are held
still, and with the same stamp (PROTOCOL.md#the-complete-protocol). -/
structure PoolCarry (st st' : Protocol.Store V) : Prop where
  /-- The pool only grows. -/
  mem : ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k → u ∈ st'.gf_votes k
  /-- A stamp already written is not rewritten. -/
  stamp : ∀ (u : GoldfishVote V) (c : Stamp), st.timestamp_vote u = some c →
    st'.timestamp_vote u = some c

/-- The arrow the bundle travels along: from a store that carries the bundle, the
target carries it too, and carries everything the source held. -/
def PoolStep (st st' : Protocol.Store V) : Prop :=
  PoolStamps st → PoolCarry st st' ∧ PoolStamps st'

namespace PoolStep

variable {st st' st'' : Protocol.Store V}

omit [DecidableEq V] [Fintype V] in
/-- Reflexivity. -/
theorem refl' (st : Protocol.Store V) : PoolStep st st :=
  fun h => ⟨⟨fun _ _ hu => hu, fun _ _ hc => hc⟩, h⟩

omit [DecidableEq V] [Fintype V] in
/-- Transitivity. -/
theorem trans' (h₁ : PoolStep st st') (h₂ : PoolStep st' st'') : PoolStep st st'' := by
  intro h
  obtain ⟨c₁, hs₁⟩ := h₁ h
  obtain ⟨c₂, hs₂⟩ := h₂ hs₁
  exact ⟨⟨fun k u hu => c₂.mem k u (c₁.mem k u hu),
    fun u c hc => c₂.stamp u c (c₁.stamp u c hc)⟩, hs₂⟩

omit [DecidableEq V] [Fintype V] in
/-- A branch that steps either way is a step. -/
theorem ite' {c : Prop} [Decidable c] (h₁ : PoolStep st st') (h₂ : PoolStep st st'') :
    PoolStep st (if c then st' else st'') := by
  split <;> assumption

omit [DecidableEq V] [Fintype V] in
/-- A handler that writes neither field is a step. -/
theorem of_eq (hg : st'.gf_votes = st.gf_votes) (hv : st'.timestamp_vote = st.timestamp_vote)
    (ht : st'.t = st.t) : PoolStep st st' := by
  intro h
  refine ⟨⟨fun k u hu => by rw [hg]; exact hu, fun u c hc => by rw [hv]; exact hc⟩, ?_⟩
  exact ⟨fun k u hu => h.slot k u (by rwa [hg] at hu),
    fun k u hu => by rw [hv]; exact h.stamped k u (by rwa [hg] at hu),
    fun u hu => by rw [hg]; exact h.pooled u (by rwa [hv] at hu),
    fun u c hc => by rw [ht]; exact h.bounded u c (by rwa [hv] at hc)⟩

end PoolStep

/-! ## 2. The one writer (PROTOCOL.md#the-complete-protocol) -/

omit [Fintype V] in
/-- §7.2 the accepting branch of `on_goldfish_vote`, as three field
equations (PROTOCOL.md#the-complete-protocol). Naming the branch this way keeps every
argument below a rewrite rather than a walk through a record literal. -/
theorem on_goldfish_vote_insert (st : Protocol.Store V) (u : GoldfishVote V)
    (h1 : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot))
    (h2 : ¬ Protocol.equivocates (st.pool u.slot) u.val_index = true) :
    (Protocol.on_goldfish_vote st u).gf_votes =
        (fun k => if k = u.slot then st.gf_votes k ++ [u] else st.gf_votes k) ∧
      (Protocol.on_goldfish_vote st u).timestamp_vote =
        (fun x => if x = u then some (st.t : Stamp) else st.timestamp_vote x) ∧
      (Protocol.on_goldfish_vote st u).t = st.t := by
  unfold Protocol.on_goldfish_vote
  rw [if_neg h1, if_neg h2]
  exact ⟨rfl, rfl, rfl⟩

omit [Fintype V] in
/-- **`on_goldfish_vote` is a `PoolStep`** (PROTOCOL.md#the-complete-protocol).

Two guards return the store, and the third branch appends the vote to its own
slot's bucket and stamps it with `Σ.t`. The only clause that needs the incoming
bundle is `PoolCarry.stamp`, and it needs exactly `pooled`: the vote being
inserted is *not* in the pool, so by `pooled` it carries no stamp, so no stamp is
overwritten. -/
theorem poolStep_on_goldfish_vote (st : Protocol.Store V) (u : GoldfishVote V) :
    PoolStep st (Protocol.on_goldfish_vote st u) := by
  intro h
  by_cases h1 : u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot
  · rw [show Protocol.on_goldfish_vote st u = st by
      unfold Protocol.on_goldfish_vote; rw [if_pos h1]]
    exact PoolStep.refl' st h
  by_cases h2 : Protocol.equivocates (st.pool u.slot) u.val_index = true
  · rw [show Protocol.on_goldfish_vote st u = st by
      unfold Protocol.on_goldfish_vote; rw [if_neg h1, if_pos h2]]
    exact PoolStep.refl' st h
  obtain ⟨hgf, hts, ht⟩ := on_goldfish_vote_insert st u h1 h2
  have hnot : u ∉ st.gf_votes u.slot := fun hmem => h1 (Or.inr (Or.inr hmem))
  have hnone : st.timestamp_vote u = none := by
    cases hcase : st.timestamp_vote u with
    | none => rfl
    | some c => exact absurd (h.pooled u (by rw [hcase]; rfl)) hnot
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro k x hx
    simp only [hgf]
    split_ifs with hk
    · exact List.mem_append_left _ hx
    · exact hx
  · intro x c hc
    simp only [hts]
    split_ifs with hxu
    · rw [hxu, hnone] at hc
      exact absurd hc (by simp)
    · exact hc
  · intro k x hx
    simp only [hgf] at hx
    split_ifs at hx with hk
    · rcases List.mem_append.mp hx with hx' | hx'
      · exact h.slot k x hx'
      · rw [List.mem_singleton.mp hx', hk]
    · exact h.slot k x hx
  · intro k x hx
    simp only [hgf] at hx
    simp only [hts]
    split_ifs with hxu
    · rfl
    · split_ifs at hx with hk
      · rcases List.mem_append.mp hx with hx' | hx'
        · exact h.stamped k x hx'
        · exact absurd (List.mem_singleton.mp hx') hxu
      · exact h.stamped k x hx
  · intro x hx
    simp only [hts] at hx
    simp only [hgf]
    split_ifs at hx with hxu
    · rw [hxu]
      split_ifs with hk
      · exact List.mem_append_right _ (by simp)
      · exact absurd rfl hk
    · have hmem := h.pooled x hx
      split_ifs with hk
      · exact List.mem_append_left _ hmem
      · exact hmem
  · intro x c hc
    simp only [hts] at hc
    simp only [ht]
    split_ifs at hc with hxu
    · rw [Option.some.injEq] at hc
      exact le_of_eq hc.symm
    · exact h.bounded x c hc

/-- The source-aligned checked ingress is a `PoolStep`. A noncommittee vote is
rejected; the admitted branch is the core handler above. -/
theorem poolStep_on_goldfish_vote_checked (E : Env V)
    (st : Protocol.Store V) (u : GoldfishVote V) :
    PoolStep st (Protocol.on_goldfish_vote_checked E st u) := by
  simp only [Protocol.on_goldfish_vote_checked]
  split
  · exact PoolStep.refl' st
  · exact poolStep_on_goldfish_vote st u


/-- The checked carried-vote fold is a `PoolStep`. -/
theorem poolStep_foldl_on_goldfish_vote_checked (E : Env V)
    (l : List (GoldfishVote V)) :
    ∀ st : Protocol.Store V,
      PoolStep st (l.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction l with
  | nil => intro st; exact PoolStep.refl' st
  | cons u l ih =>
      intro st
      rw [List.foldl_cons]
      exact PoolStep.trans' (poolStep_on_goldfish_vote_checked E st u) (ih _)

/-! ## 3. Every other handler leaves both fields alone -/

omit [Fintype V] in
/-- §5.2 `update_finality` writes neither field (PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_gf_votes (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).gf_votes = st.gf_votes := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §5.2 nor the stamp map (PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_timestamp_vote (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).timestamp_vote = st.timestamp_vote := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §5.2 `update_finality` is a `PoolStep` (PROTOCOL.md#the-complete-protocol). -/
theorem poolStep_update_finality (st : Protocol.Store V) (σ : ChainState V) :
    PoolStep st (Protocol.update_finality st σ) :=
  PoolStep.of_eq (update_finality_gf_votes st σ) (update_finality_timestamp_vote st σ)
    (update_finality_time st σ)

omit [Fintype V] in
/-- §7.2 `on_sg_vote` writes neither field (PROTOCOL.md#the-complete-protocol). -/
theorem on_sg_vote_gf_votes (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).gf_votes = st.gf_votes := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §7.2 nor the Goldfish stamp map (PROTOCOL.md#the-complete-protocol). -/
theorem on_sg_vote_timestamp_vote (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).timestamp_vote = st.timestamp_vote := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §7.2 `on_sg_vote` is a `PoolStep` (PROTOCOL.md#the-complete-protocol). -/
theorem poolStep_on_sg_vote (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : PoolStep st (Protocol.on_sg_vote hc st a) :=
  PoolStep.of_eq (on_sg_vote_gf_votes hc st a) (on_sg_vote_timestamp_vote hc st a)
    (on_sg_vote_time hc st a)

omit [DecidableEq V] [Fintype V] in
/-- §7.2 the clock write is a `PoolStep` when the clock moves forward
(PROTOCOL.md#the-complete-protocol). -/
theorem poolStep_tickStore (st : Protocol.Store V) (t : Time) (s : Slot)
    (hle : st.t ≤ t) : PoolStep st { st with t := t, s := s } := by
  intro h
  refine ⟨⟨fun _ _ hu => hu, fun _ _ hc => hc⟩, h.slot, h.stamped, h.pooled, ?_⟩
  intro u c hc
  exact le_trans (h.bounded u c hc) (by exact_mod_cast hle)

/-- The general block-processing body is a `PoolStep`, whatever chain state
it builds: the two fields `PoolStep` tracks are untouched by `buildState`,
which only ever feeds the child's chain-state record. -/
theorem poolStep_on_block_using (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    PoolStep st (Protocol.on_block_using E st B buildState) := by
  simp only [Protocol.on_block_using]
  split_ifs
  · exact PoolStep.refl' st
  · exact PoolStep.refl' st
  · exact PoolStep.refl' st
  · refine PoolStep.trans' ?_ (poolStep_update_finality _ _)
    refine PoolStep.trans' ?_ (poolStep_foldl_on_goldfish_vote_checked E B.gf_votes _)
    exact PoolStep.of_eq rfl rfl rfl
  · exact PoolStep.refl' st

omit [DecidableEq V] [Fintype V] in
/-- The carried-round guard passes a `PoolStep` through whichever body it
wraps. -/
theorem poolStep_on_block_checked_using (handle : Protocol.Store V → Protocol.Store V)
    (hc : HealConfig) (st : Protocol.Store V) (B : Block V)
    (hh : PoolStep st (handle st)) :
    PoolStep st (Protocol.on_block_checked_using handle hc st B) := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hh
  · exact PoolStep.refl' st

/-- The general Goldfish vote duty is a `PoolStep` at any grade contract: the
contract only ever picks which vote is cast, not the insertion mechanics. -/
theorem poolStep_goldfish_vote_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    PoolStep st (Protocol.goldfish_vote_with contract E hc nd st).1 := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact poolStep_on_goldfish_vote_checked E _ _
  · exact PoolStep.refl' st

omit [Fintype V] in
/-- Named row admission is a `PoolStep`: it decides admission through
`on_sg_vote` alone (`admit_row_core`) and otherwise only ever appends to
`Σ.sg_rows[·]`, which `PoolStep` does not track. -/
theorem poolStep_admit_row (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    PoolStep st.core (Protocol.NamedAdmission.admit_row hc st row).core := by
  rw [admit_row_core]
  exact poolStep_on_sg_vote hc st.core row.erase

omit [Fintype V] in

/-- Nor does a carried batch of them. -/
theorem poolStep_admit_rows (hc : HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      PoolStep st.core (Protocol.NamedAdmission.admit_rows hc st rows).core
  | [], st => PoolStep.refl' st.core
  | row :: rows, st =>
      PoolStep.trans' (poolStep_admit_row hc st row)
        (poolStep_admit_rows hc rows (Protocol.NamedAdmission.admit_row hc st row))

/-- The named block core is a `PoolStep`: the shared handler wrapped in
`on_block_checked_using`, at the runtime's own transition builder
(`Protocol.named_transition`). -/
theorem poolStep_process_block_core (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    PoolStep st.core (Protocol.NamedStore.process_block_core E hc cfg st B).core := by
  simp only [Protocol.NamedStore.process_block_core]
  split
  · exact PoolStep.refl' st.core
  · rw [commitBlock_core]
    exact poolStep_on_block_checked_using _ hc st.core B.erase
      (poolStep_on_block_using E st.core B.erase _)

/-- The named block handler, either carried-admission policy, is a
`PoolStep`: the carried-row tail only ever runs `admit_rows`. -/
theorem poolStep_on_block_with (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    PoolStep st.core (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core := by
  have hcore := poolStep_process_block_core E hc cfg st B
  cases adm with
  | alsoCarried =>
      show PoolStep st.core
        (if B ∉ st.bodies ∧
            B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies then
              Protocol.NamedAdmission.admit_rows hc
                (Protocol.NamedStore.process_block_core E hc cfg st B) B.attestations
            else Protocol.NamedStore.process_block_core E hc cfg st B).core
      split_ifs
      · exact PoolStep.trans' hcore
          (poolStep_admit_rows hc B.attestations
            (Protocol.NamedStore.process_block_core E hc cfg st B))
      · exact hcore

/-- The named proposal duty is a `PoolStep`: it either changes nothing (no
retained parent) or runs `on_block_with.alsoCarried`. -/
theorem poolStep_named_propose (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    PoolStep st.core
      (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact PoolStep.refl' st.core
  · exact poolStep_on_block_with .alsoCarried E hc cfg st _

/-- The named Goldfish vote duty is a `PoolStep`. -/
theorem poolStep_named_vote (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    PoolStep st.core
      (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core := by
  simp only [Protocol.NamedDuties.goldfish_vote_with]
  exact poolStep_goldfish_vote_with contract E hc nd st.core

/-- The named confirmation duty is a `PoolStep` (it writes neither field). -/
theorem poolStep_named_confirmation (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    PoolStep st.core
      (Protocol.NamedDuties.update_confirmation_with contract E hc st s).core := by
  simp only [Protocol.NamedDuties.update_confirmation_with]
  exact PoolStep.of_eq rfl rfl rfl

/-- The named attestation duty is a `PoolStep`: it ends in `admit_row`. -/
theorem poolStep_named_attest (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    PoolStep st.core
      (Protocol.NamedDuties.attest_with contract E hc nd st record).1.core := by
  unfold Protocol.NamedDuties.attest_with
  exact poolStep_admit_row hc st _

/-- **The named tick is a `PoolStep`**, at any grade contract: the four
generalized duties above each preserve `PoolStep st.core ·`, and the clock
staging is `poolStep_tickStore`, so `Proofs.Execution.named_tick_preserves`
composes them exactly as `poolStep_on_tick` composed the `_current` duties
above. -/
theorem poolStep_named_tick (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (hle : st.core.t ≤ t) :
    PoolStep st.core (Protocol.NamedTick.tick contract E hc cfg nd st record t).1.core := by
  have hbase : PoolStep st.core (Protocol.NamedStore.setClock E st t).core :=
    poolStep_tickStore st.core t (E.slotOf t) hle
  exact named_tick_preserves (fun st' => PoolStep st.core st'.core) contract E hc cfg nd
    (fun st' h => PoolStep.trans' h (poolStep_named_propose contract E hc cfg nd st'))
    (fun st' h => PoolStep.trans' h (poolStep_named_vote contract E hc nd st'))
    (fun st' s h => PoolStep.trans' h (poolStep_named_confirmation contract E hc st' s))
    (fun st' record' h => PoolStep.trans' h (poolStep_named_attest contract E hc nd st' record'))
    st record t hbase

/-- **Processing an object is a `PoolStep`** (PROTOCOL.md#the-complete-protocol), at the
node's own core store. `NamedReceipt.process` reaches the core through
`on_block_with.alsoCarried`, `on_goldfish_vote_checked` and `admit_row`. -/
theorem poolStep_process (S : Setup V) (n : NodeState V) (o : Object V) :
    PoolStep n.st.core (NamedNode.process S n o).st.core := by
  cases o with
  | block B =>
      show PoolStep n.st.core
        (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg n.st B).core
      exact poolStep_on_block_with .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u =>
      show PoolStep n.st.core (Protocol.on_goldfish_vote_checked S.E n.st.core u)
      exact poolStep_on_goldfish_vote_checked S.E n.st.core u
  | attest a =>
      show PoolStep n.st.core (Protocol.NamedAdmission.admit_row S.hc n.st a).core
      exact poolStep_admit_row S.hc n.st a

/-! ## 5. The insertion, at a store whose guards clear

This is the step `Availability/Sync.lean`'s header names, and it is a statement
about one store: *given* that the two guards clear, the handler leaves the vote
in its own slot's bucket with a stamp at or before the store's clock. Which
guards clear when is the caller's business — `Optimistic/Alignment.lean`
discharges both for an honest emitter. -/

omit [Fintype V] in
/-- **Pool membership through `on_goldfish_vote`'s guards**. The duplicate guard
is *not* an obstruction: a vote it rejects is already in the bucket, and
`PoolStamps` says it is already stamped. The other three are, and are
hypotheses — `hfresh` is new with the expiry clause (baseline `7b2efec`): an
expired vote is now dropped outright, so every caller owes that the vote's slot
is within the store's two-slot window. -/
theorem mem_and_stamp_of_process (st : Protocol.Store V) (u : GoldfishVote V)
    (h : PoolStamps st) (hfresh : ¬ u.slot < st.s - 1) (hslot : ¬ st.s < u.slot)
    (hequiv : Protocol.equivocates (st.pool u.slot) u.val_index = false) :
    u ∈ (Protocol.on_goldfish_vote st u).gf_votes u.slot ∧
      ∃ c : Stamp, (Protocol.on_goldfish_vote st u).timestamp_vote u = some c ∧
        c ≤ (st.t : Stamp) := by
  by_cases h1 : u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot
  · have hdup : u ∈ st.gf_votes u.slot := (h1.resolve_left hfresh).resolve_left hslot
    have heq : Protocol.on_goldfish_vote st u = st := by
      unfold Protocol.on_goldfish_vote
      rw [if_pos h1]
    rw [heq]
    refine ⟨hdup, ?_⟩
    cases hcase : st.timestamp_vote u with
    | none => exact absurd (h.stamped _ u hdup) (by rw [hcase]; simp)
    | some c => exact ⟨c, rfl, h.bounded u c hcase⟩
  · have h2 : ¬ Protocol.equivocates (st.pool u.slot) u.val_index = true := by
      rw [hequiv]; simp
    obtain ⟨hgf, hts, -⟩ := on_goldfish_vote_insert st u h1 h2
    refine ⟨?_, (st.t : Stamp), ?_, le_refl _⟩
    · rw [hgf]
      simp
    · rw [hts]
      simp

/-! ## 6. Where a pooled vote came from — the Goldfish twin of
`Proofs.Bridges.processes_block_of_mem_T`

`Σ.gf_votes[·]` has two writers, not one: the handler itself, and the carried-set
fold inside `on_block` (PROTOCOL.md#the-complete-protocol). So the conclusion has two
disjuncts, and they are exactly the two clauses `Unforgeable` supplies —
`unforgeable` for a vote delivered on its own, `carried_gf` for one that rode
inside a block. -/

/-- **A vote in `st'`'s pool was in `st`'s, or arrived with one of `l`**
(PROTOCOL.md#the-complete-protocol). The arrow the tick composes along. -/
def GfFrom (st : Protocol.Store V) (l : List (Object V)) (st' : Protocol.Store V) : Prop :=
  ∀ (k : Slot) (u : GoldfishVote V), u ∈ st'.gf_votes k →
    u ∈ st.gf_votes k ∨ Object.gfVote u ∈ l ∨
      ∃ B : NamedBlock V, Object.block B ∈ l ∧ u ∈ B.gf_votes

namespace GfFrom

variable {st st' st'' : Protocol.Store V} {l l' l₁ l₂ : List (Object V)}

omit [DecidableEq V] [Fintype V] in
/-- Reflexivity. -/
theorem refl' (st : Protocol.Store V) (l : List (Object V)) : GfFrom st l st :=
  fun _ _ hu => Or.inl hu

omit [DecidableEq V] [Fintype V] in
/-- A handler that writes no vote (PROTOCOL.md#the-complete-protocol). -/
theorem of_eq (heq : st'.gf_votes = st.gf_votes) : GfFrom st l st' :=
  fun k u hu => Or.inl (by rwa [heq] at hu)

omit [DecidableEq V] [Fintype V] in
/-- The carried list only grows. -/
theorem mono (h : GfFrom st l st') (hl : ∀ o ∈ l, o ∈ l') : GfFrom st l' st' := by
  intro k u hu
  rcases h k u hu with h' | h' | ⟨B, hB, hBu⟩
  · exact Or.inl h'
  · exact Or.inr (Or.inl (hl _ h'))
  · exact Or.inr (Or.inr ⟨B, hl _ hB, hBu⟩)

omit [DecidableEq V] [Fintype V] in
/-- Composition, concatenating the two lists. -/
theorem trans' (h₁ : GfFrom st l₁ st') (h₂ : GfFrom st' l₂ st'') :
    GfFrom st (l₁ ++ l₂) st'' := by
  intro k u hu
  rcases h₂ k u hu with h' | h' | ⟨B, hB, hBu⟩
  · exact (h₁ k u h').imp id
      (fun hx => hx.imp (List.mem_append_left _) fun ⟨B, hB, hBu⟩ =>
        ⟨B, List.mem_append_left _ hB, hBu⟩)
  · exact Or.inr (Or.inl (List.mem_append_right _ h'))
  · exact Or.inr (Or.inr ⟨B, List.mem_append_right _ hB, hBu⟩)

omit [DecidableEq V] [Fintype V] in
/-- A branch whose store and emission list share one guard. -/
theorem ite' {c : Prop} [Decidable c] (h₁ : GfFrom st l₁ st') (h₂ : GfFrom st l₂ st'') :
    GfFrom st (if c then l₁ else l₂) (if c then st' else st'') := by
  split <;> assumption

end GfFrom

omit [Fintype V] in
/-- §7.2 `on_goldfish_vote` adds at most the vote it is handed
(PROTOCOL.md#the-complete-protocol). -/
theorem gfFrom_on_goldfish_vote (st : Protocol.Store V) (u : GoldfishVote V) :
    GfFrom st [Object.gfVote u] (Protocol.on_goldfish_vote st u) := by
  intro k x hx
  by_cases h1 : u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot
  · refine Or.inl ?_
    rw [show Protocol.on_goldfish_vote st u = st by
      unfold Protocol.on_goldfish_vote; rw [if_pos h1]] at hx
    exact hx
  by_cases h2 : Protocol.equivocates (st.pool u.slot) u.val_index = true
  · refine Or.inl ?_
    rw [show Protocol.on_goldfish_vote st u = st by
      unfold Protocol.on_goldfish_vote; rw [if_neg h1, if_pos h2]] at hx
    exact hx
  obtain ⟨hgf, -, -⟩ := on_goldfish_vote_insert st u h1 h2
  simp only [hgf] at hx
  split_ifs at hx with hk
  · rcases List.mem_append.mp hx with hx' | hx'
    · exact Or.inl hx'
    · exact Or.inr (Or.inl (by rw [List.mem_singleton.mp hx']; simp))
  · exact Or.inl hx

/-- The checked ingress adds at most the vote it is handed. -/
theorem gfFrom_on_goldfish_vote_checked (E : Env V)
    (st : Protocol.Store V) (u : GoldfishVote V) :
    GfFrom st [Object.gfVote u] (Protocol.on_goldfish_vote_checked E st u) := by
  simp only [Protocol.on_goldfish_vote_checked]
  split
  · exact GfFrom.refl' st _
  · exact gfFrom_on_goldfish_vote st u


/-- The checked carried-vote fold adds at most the carried set. -/
theorem gfFrom_foldl_on_goldfish_vote_checked (E : Env V)
    (l : List (GoldfishVote V)) :
    ∀ st : Protocol.Store V,
      GfFrom st (l.map Object.gfVote)
        (l.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction l with
  | nil => intro st; exact GfFrom.refl' st _
  | cons u l ih =>
      intro st
      rw [List.foldl_cons]
      refine GfFrom.mono
        (GfFrom.trans' (gfFrom_on_goldfish_vote_checked E st u) (ih _)) ?_
      intro o ho
      rcases List.mem_append.mp ho with ho' | ho'
      · rw [List.mem_singleton.mp ho']
        simp
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr ho'

omit [DecidableEq V] [Fintype V] in
/-- Erasure keeps the same carried-vote list: both projections match the same
constructor field. -/
theorem NamedBlock.erase_gf_votes (B : NamedBlock V) : B.erase.gf_votes = B.gf_votes := by
  cases B with
  | genesis => rfl
  | node p s r votes support rows proposer => rfl

/-- The general block-processing body adds at most the named block's own
carried set, whatever chain state it builds (PROTOCOL.md#the-complete-protocol). The
named runtime supplies `Protocol.named_transition` as the builder, so
the fact is stated at the builder, exactly as `poolStep_on_block_using`
above. -/
theorem gfFrom_on_block_using (E : Env V) (st : Protocol.Store V) (B : NamedBlock V)
    (buildState : ChainState V → ChainState V) :
    GfFrom st [Object.block B] (Protocol.on_block_using E st B.erase buildState) := by
  simp only [Protocol.on_block_using]
  split_ifs
  · exact GfFrom.refl' st _
  · exact GfFrom.refl' st _
  · exact GfFrom.refl' st _
  · intro k u hu
    rw [update_finality_gf_votes] at hu
    rw [show B.erase.gf_votes = B.gf_votes from NamedBlock.erase_gf_votes B] at hu
    rcases gfFrom_foldl_on_goldfish_vote_checked E B.gf_votes _ k u hu with
      h' | h' | ⟨C, hC, -⟩
    · exact Or.inl h'
    · refine Or.inr (Or.inr ⟨B, by simp, ?_⟩)
      simp only [List.mem_map] at h'
      obtain ⟨x, hx, hxe⟩ := h'
      cases hxe
      exact hx
    · simp only [List.mem_map] at hC
      obtain ⟨x, -, hxe⟩ := hC
      exact absurd hxe (by simp)
  · exact GfFrom.refl' st _

omit [DecidableEq V] [Fintype V] in
/-- The carried-round guard passes a `GfFrom` fact through whichever body it
wraps. -/
theorem gfFrom_on_block_checked_using (handle : Protocol.Store V → Protocol.Store V)
    (hc : HealConfig) (st : Protocol.Store V) (B : NamedBlock V)
    (hh : GfFrom st [Object.block B] (handle st)) :
    GfFrom st [Object.block B] (Protocol.on_block_checked_using handle hc st B.erase) := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hh
  · exact GfFrom.refl' st _


/-- The general Goldfish vote duty adds at most the vote it emits, at any
grade contract. -/
theorem gfFrom_goldfish_vote_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    GfFrom st (((Protocol.goldfish_vote_with contract E hc nd st).2).toList.map Object.gfVote)
      (Protocol.goldfish_vote_with contract E hc nd st).1 := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact gfFrom_on_goldfish_vote_checked E _ _
  · exact GfFrom.refl' st _

/-- The named block core adds at most the named block's own carried set: the
shared handler wrapped in `on_block_checked_using`, at the runtime's own
transition builder. -/
theorem gfFrom_process_block_core (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    GfFrom st.core [Object.block B]
      (Protocol.NamedStore.process_block_core E hc cfg st B).core := by
  simp only [Protocol.NamedStore.process_block_core]
  split
  · exact GfFrom.refl' st.core _
  · rw [commitBlock_core]
    exact gfFrom_on_block_checked_using _ hc st.core B
      (gfFrom_on_block_using E st.core B _)

omit [Fintype V] in
/-- Named row admission adds no vote: it decides admission through
`on_sg_vote` alone. -/
theorem gfFrom_admit_row (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (l : List (Object V)) :
    GfFrom st.core l (Protocol.NamedAdmission.admit_row hc st row).core := by
  rw [admit_row_core]
  exact GfFrom.of_eq (on_sg_vote_gf_votes hc st.core row.erase)

omit [Fintype V] in

/-- Nor does a carried batch of them (`admit_rows_gf_votes`, the whole-fold
form). -/
theorem admit_rows_gf_votes (hc : HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      (Protocol.NamedAdmission.admit_rows hc st rows).core.gf_votes = st.core.gf_votes
  | [], _ => rfl
  | row :: rows, st => by
      have heq : Protocol.NamedAdmission.admit_rows hc st (row :: rows) =
          Protocol.NamedAdmission.admit_rows hc
            (Protocol.NamedAdmission.admit_row hc st row) rows := rfl
      rw [heq, admit_rows_gf_votes hc rows, admit_row_core, on_sg_vote_gf_votes]

/-- The named block handler, either carried-admission policy, adds at most
the named block's own carried set: the carried-row tail only ever runs
`admit_rows`, which adds no vote of its own. -/
theorem gfFrom_on_block_with (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    GfFrom st.core [Object.block B]
      (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core := by
  have hcore := gfFrom_process_block_core E hc cfg st B
  cases adm with
  | alsoCarried =>
      show GfFrom st.core [Object.block B]
        (if B ∉ st.bodies ∧
            B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies then
              Protocol.NamedAdmission.admit_rows hc
                (Protocol.NamedStore.process_block_core E hc cfg st B) B.attestations
            else Protocol.NamedStore.process_block_core E hc cfg st B).core
      split_ifs
      · intro k u hu
        rw [admit_rows_gf_votes hc B.attestations
          (Protocol.NamedStore.process_block_core E hc cfg st B)] at hu
        exact hcore k u hu
      · exact hcore

/-- Local restatement of `Proofs.NamedTick.tick_computed_duties` (not
imported: that file's cone loops back to this one through
`Protocol.Sync`/`Final`, the same reason `Availability/Monotone.lean`
keeps its own private copy). Byte-identical to the original, against the
same Model-level primitives, so the proof script is unchanged. -/
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

/-- **The named tick adds at most what it emits** (PROTOCOL.md#the-complete-protocol),
at any grade contract. The proposal branch adds a block when it constructs
one at all (`Protocol.NamedDuties.propose_block_with`'s parent lookup can
miss, unlike the previous total `propose_block`); the vote branch adds the vote it
emits; the other two branches add no vote of their own. -/
theorem gfFrom_named_tick (gc : Protocol.GradeContract V) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    GfFrom st.core (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core := by
  have hcd := named_tick_computed_duties gc E hc cfg nd st record t
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
  let proposalDue := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
  let st1 := if proposalDue then proposed.1 else st0
  let emitted1 : List (NamedObject V) := if proposalDue then
    (match proposed.2 with | none => [] | some B => [NamedObject.block B]) else []
  let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
  let voteDue := 0 < s ∧ t = Protocol.vote_time E s
  let st2 := if voteDue then voted.1 else st1
  let emitted2 : List (NamedObject V) :=
    if voteDue then voted.2.toList.map NamedObject.gfVote else []
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
    Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  change Protocol.NamedTick.tick gc E hc cfg nd st record t =
    (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
      ((Protocol.NamedDuties.attest_with gc E hc nd st3 record).1,
        (Protocol.NamedDuties.attest_with gc E hc nd st3 record).2.1,
        emitted1 ++ emitted2 ++
          [NamedObject.attest (Protocol.NamedDuties.attest_with gc E hc nd st3 record).2.2])
    else (st3, record, emitted1 ++ emitted2)) at hcd
  have h1 : GfFrom st.core emitted1 st1.core := by
    by_cases hd : proposalDue
    · cases hcase : Protocol.NamedActions.proposal_with gc .poolAndCarried E hc nd st0 with
      | none =>
          have he : proposed = (st0, none) := by
            dsimp only [proposed]
            simp only [Protocol.NamedDuties.propose_block_with, hcase]
          have hst1 : st1 = st0 := by dsimp only [st1]; rw [if_pos hd, he]
          have hem1 : emitted1 = [] := by dsimp only [emitted1]; rw [if_pos hd, he]
          rw [hst1, hem1]
          exact GfFrom.refl' st0.core []
      | some B =>
          have he : proposed =
              (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st0 B, some B) := by
            dsimp only [proposed]
            simp only [Protocol.NamedDuties.propose_block_with, hcase]
          have hst1 : st1 = Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st0 B := by
            dsimp only [st1]; rw [if_pos hd, he]
          have hem1 : emitted1 = [Object.block B] := by
            dsimp only [emitted1]; rw [if_pos hd, he]
          rw [hst1, hem1]
          exact gfFrom_on_block_with .alsoCarried E hc cfg st0 B
    · have hst1 : st1 = st0 := by dsimp only [st1]; rw [if_neg hd]
      have hem1 : emitted1 = [] := by dsimp only [emitted1]; rw [if_neg hd]
      rw [hst1, hem1]
      exact GfFrom.refl' st0.core []
  have h2 : GfFrom st1.core emitted2 st2.core := by
    by_cases hv : voteDue
    · have hst2 : st2 = voted.1 := by dsimp only [st2]; rw [if_pos hv]
      have hem2 : emitted2 = voted.2.toList.map Object.gfVote := by
        dsimp only [emitted2]; rw [if_pos hv]
      rw [hst2, hem2]
      exact gfFrom_goldfish_vote_with gc E hc nd st1.core
    · have hst2 : st2 = st1 := by dsimp only [st2]; rw [if_neg hv]
      have hem2 : emitted2 = [] := by dsimp only [emitted2]; rw [if_neg hv]
      rw [hst2, hem2]
      exact GfFrom.refl' st1.core []
  have h3eq : st3.core.gf_votes = st2.core.gf_votes := by dsimp only [st3]; split_ifs <;> rfl
  have h2' : GfFrom st1.core emitted2 st3.core := by
    intro k u hu
    rw [h3eq] at hu
    exact h2 k u hu
  have hpre3 : GfFrom st.core (emitted1 ++ emitted2) st3.core := GfFrom.trans' h1 h2'
  have hattest_step : GfFrom st3.core ([] : List (Object V))
      (Protocol.NamedDuties.attest_with gc E hc nd st3 record).1.core := by
    have hac : (Protocol.NamedDuties.attest_with gc E hc nd st3 record).1.core =
        Protocol.on_sg_vote hc st3.core
          (Protocol.NamedActions.round_action_with gc E hc nd st3.core.toHealing record).2.erase :=
      admit_row_core hc st3 _
    rw [hac]
    exact GfFrom.of_eq (on_sg_vote_gf_votes hc st3.core _)
  rw [hcd]
  split_ifs with hattest_cond
  · refine GfFrom.mono (GfFrom.trans' hpre3 hattest_step) (fun o ho => ?_)
    simp only [List.mem_append, List.not_mem_nil, or_false] at ho ⊢
    tauto
  · exact hpre3

/-! ## 7. The run-level transport

One induction over the event list. Only `v`'s own events move `v`'s store, and
each of them is a `PoolStep`; the tick's `hle` is sortedness, in the form
`store_time_le_event_time`. -/

/-- **The store clock is at most the time of the event it is read at**
(PROTOCOL.md#the-complete-protocol). `stamp_is_last_tick`'s second half, for an arbitrary
event rather than a delivery: the clock is the last tick of the prefix, and
sortedness puts every event of the prefix at or before the event that follows
it. -/
theorem store_time_le_event_time (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {n : Nat} {e : Event V} (he : ρ.events[n]? = some e) (v : V) :
    (ρ.stateBefore S n v).st.t ≤ e.time := by
  have heq : (ρ.stateBefore S n v).st.t = (Run.lastTickIn v (ρ.events.take n)).getD 0 :=
    store_time_eq_lastTick S ρ v n
  rw [heq]
  cases hl : Run.lastTickIn v (ρ.events.take n) with
  | none =>
      simpa using (sch.in_horizon _ (List.mem_of_getElem? he)).1
  | some p =>
      have hmem : Event.tick v p ∈ ρ.events.take n := tick_mem_of_lastTickIn v _ hl
      simpa using time_le_of_mem_take S sch he _ hmem

/-- **Every honest store of every prefix carries the bundle**
(PROTOCOL.md#the-complete-protocol). The initial store has empty pools and an
empty stamp map, which is the base case. -/
theorem poolStamps_stateBefore (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    (v : V) : ∀ n : Nat, PoolStamps (ρ.stateBefore S n v).st.core := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
          NamedNode.initial, Protocol.NamedStore.initial, Protocol.Store.init]
  | succ n ih =>
      have hstep : ρ.stateBefore S (n + 1) =
          (ρ.events[n]?.toList).foldl (World.step S) (ρ.stateBefore S n) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rcases hev : ρ.events[n]? with _ | e
      · rw [hstep, hev]
        exact ih
      · cases e with
        | deliver u o t =>
            by_cases hu : v = u
            · subst hu
              have hw : (ρ.stateBefore S (n + 1) v).st =
                  (NamedNode.process S (ρ.stateBefore S n v) o).st := by
                rw [hstep, hev]
                simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                  NamedWorld.step, Function.update_self]
              rw [hw]
              exact (poolStep_process S (ρ.stateBefore S n v) o ih).2
            · rw [hstep, hev]
              simpa only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                NamedWorld.step, Function.update_of_ne hu] using ih
        | tick u t =>
            by_cases hu : v = u
            · subst hu
              have hw : (ρ.stateBefore S (n + 1) v).st =
                  (NamedNode.tick S v (ρ.stateBefore S n v) t).1.st := by
                rw [hstep, hev]
                simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                  NamedWorld.step, Function.update_self]
              obtain ⟨gc, hgc⟩ : ∃ gc : Protocol.GradeContract V,
                  (NamedNode.tick S v (ρ.stateBefore S n v) t).1.st =
                    (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v)
                      (ρ.stateBefore S n v).st (ρ.stateBefore S n v).record t).1 :=
                ⟨_, rfl⟩
              rw [hw, hgc]
              refine (poolStep_named_tick gc S.E S.hc S.cfg (S.node v) (ρ.stateBefore S n v).st
                (ρ.stateBefore S n v).record t ?_ ih).2
              simpa [Event.time] using store_time_le_event_time S sch hev v
            · rw [hstep, hev]
              simpa only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                NamedWorld.step, Function.update_of_ne hu] using ih

/-- **The pool and its stamps carry forward along the run**
(PROTOCOL.md#the-complete-protocol). A vote in a node's pool at one prefix is in its
pool at every later one, with the stamp it was first given. -/
theorem pool_carry (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ) (v : V)
    {m : Nat} : ∀ n : Nat, m ≤ n →
      PoolCarry (ρ.stateBefore S m v).st.core (ρ.stateBefore S n v).st.core := by
  intro n
  induction n with
  | zero =>
      intro hle
      rw [Nat.le_zero.mp hle]
      exact ⟨fun _ _ hu => hu, fun _ _ hc => hc⟩
  | succ n ih =>
      intro hle
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        have hcarry := ih hmn
        have hstep : ρ.stateBefore S (n + 1) =
            (ρ.events[n]?.toList).foldl (World.step S) (ρ.stateBefore S n) := by
          unfold Run.stateBefore NamedRun.stateBefore
          rw [List.take_add_one, List.foldl_append]
        have hnext :
            PoolCarry (ρ.stateBefore S n v).st.core (ρ.stateBefore S (n + 1) v).st.core := by
          rcases hev : ρ.events[n]? with _ | e
          · rw [hstep, hev]
            exact ⟨fun _ _ hu => hu, fun _ _ hc => hc⟩
          · cases e with
            | deliver u o t =>
                by_cases hu : v = u
                · subst hu
                  have hw : (ρ.stateBefore S (n + 1) v).st =
                      (NamedNode.process S (ρ.stateBefore S n v) o).st := by
                    rw [hstep, hev]
                    simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                      NamedWorld.step, Function.update_self]
                  rw [hw]
                  exact (poolStep_process S (ρ.stateBefore S n v) o
                    (poolStamps_stateBefore S sch v n)).1
                · rw [hstep, hev]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                    NamedWorld.step, Function.update_of_ne hu]
                  exact ⟨fun _ _ hu => hu, fun _ _ hc => hc⟩
            | tick u t =>
                by_cases hu : v = u
                · subst hu
                  have hw : (ρ.stateBefore S (n + 1) v).st =
                      (NamedNode.tick S v (ρ.stateBefore S n v) t).1.st := by
                    rw [hstep, hev]
                    simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                      NamedWorld.step, Function.update_self]
                  obtain ⟨gc, hgc⟩ : ∃ gc : Protocol.GradeContract V,
                      (NamedNode.tick S v (ρ.stateBefore S n v) t).1.st =
                        (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v)
                          (ρ.stateBefore S n v).st (ρ.stateBefore S n v).record t).1 :=
                    ⟨_, rfl⟩
                  rw [hw, hgc]
                  refine (poolStep_named_tick gc S.E S.hc S.cfg (S.node v) (ρ.stateBefore S n v).st
                    (ρ.stateBefore S n v).record t ?_ (poolStamps_stateBefore S sch v n)).1
                  simpa [Event.time] using store_time_le_event_time S sch hev v
                · rw [hstep, hev]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                    NamedWorld.step, Function.update_of_ne hu]
                  exact ⟨fun _ _ hu => hu, fun _ _ hc => hc⟩
        exact ⟨fun k u hu => hnext.mem k u (hcarry.mem k u hu),
          fun u c hc => hnext.stamp u c (hcarry.stamp u c hc)⟩
      · rw [Nat.le_antisymm hle hge]
        exact ⟨fun _ _ hu => hu, fun _ _ hc => hc⟩

/-- **Processing an object adds at most that object's votes**
(PROTOCOL.md#the-complete-protocol). -/
theorem gfFrom_process (S : Setup V) (n : NodeState V) (o : Object V) :
    GfFrom n.st.core [o] (NamedNode.process S n o).st.core := by
  cases o with
  | block B =>
      show GfFrom n.st.core [Object.block B]
        (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg n.st B).core
      exact gfFrom_on_block_with .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u =>
      show GfFrom n.st.core [Object.gfVote u] (Protocol.on_goldfish_vote_checked S.E n.st.core u)
      exact gfFrom_on_goldfish_vote_checked S.E n.st.core u
  | attest a =>
      show GfFrom n.st.core [Object.attest a]
        (Protocol.NamedAdmission.admit_row S.hc n.st a).core
      exact gfFrom_admit_row S.hc n.st a [Object.attest a]

/-- **A vote in an honest node's pool is one that node processed** — on its own,
or inside a block it processed (design §4.C; PROTOCOL.md#the-complete-protocol).

The Goldfish twin of `Proofs.Bridges.processes_block_of_mem_T` and of
`Proofs.Optimistic.processes_attest_of_mem_sg_pool`, with **two** disjuncts because
`Σ.gf_votes[·]` has two writers: the handler, and the carried-set fold inside
`on_block` (PROTOCOL.md#the-complete-protocol). The two are exactly the two clauses
`Unforgeable` supplies — `unforgeable` for the first, `carried_gf` for the second —
so a caller that owns both closes the provenance of any pooled vote.

The event index is returned beside the time, as in the block form, because the
callers also need the processing to be in the run's past. -/
theorem processes_gfVote_of_mem_pool (S : Setup V) (ρ : Run V) (v : V) :
    ∀ (i : Nat) (k : Slot) (u : GoldfishVote V),
      u ∈ (ρ.stateBefore S i v).st.gf_votes k →
        ∃ (j : Nat) (e : Event V), j < i ∧ ρ.events[j]? = some e ∧
          (NamedRun.processes S ρ v (Object.gfVote u) e.time ∨
            ∃ B : NamedBlock V, NamedRun.processes S ρ v (Object.block B) e.time ∧
              u ∈ B.gf_votes) := by
  intro i
  induction i with
  | zero =>
      intro k u hu
      simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
        NamedNode.initial, Protocol.NamedStore.initial, Protocol.Store.init,
        Protocol.NamedStore.gf_votes] at hu
  | succ i ih =>
      intro k u hu
      have hstep : ρ.stateBefore S (i + 1) =
          (ρ.events[i]?.toList).foldl (World.step S) (ρ.stateBefore S i) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      have bump : u ∈ (ρ.stateBefore S i v).st.gf_votes k →
          ∃ (j : Nat) (e : Event V), j < i + 1 ∧ ρ.events[j]? = some e ∧
            (NamedRun.processes S ρ v (Object.gfVote u) e.time ∨
              ∃ B : NamedBlock V, NamedRun.processes S ρ v (Object.block B) e.time ∧
                u ∈ B.gf_votes) := by
        intro h
        obtain ⟨j, e, hj, hje, hproc⟩ := ih k u h
        exact ⟨j, e, Nat.lt_succ_of_lt hj, hje, hproc⟩
      rcases hev : ρ.events[i]? with _ | ev
      · refine bump ?_
        rw [hstep, hev] at hu
        exact hu
      · cases ev with
        | deliver w o t =>
            by_cases hw : v = w
            · subst hw
              have hst : (ρ.stateBefore S (i + 1) v).st =
                  (NamedNode.process S (ρ.stateBefore S i v) o).st := by
                rw [hstep, hev]
                simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                  NamedWorld.step, Function.update_self]
              rw [hst] at hu
              rcases gfFrom_process S (ρ.stateBefore S i v) o k u hu with
                h' | h' | ⟨B, hB, hBu⟩
              · exact bump h'
              · rw [List.mem_singleton] at h'
                subst h'
                exact ⟨i, Event.deliver v (Object.gfVote u) t, Nat.lt_succ_self i, hev,
                  Or.inl (Or.inr ⟨i, hev⟩)⟩
              · rw [List.mem_singleton] at hB
                subst hB
                exact ⟨i, Event.deliver v (Object.block B) t, Nat.lt_succ_self i, hev,
                  Or.inr ⟨B, Or.inr ⟨i, hev⟩, hBu⟩⟩
            · refine bump ?_
              rw [hstep, hev] at hu
              simpa only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                NamedWorld.step, Function.update_of_ne hw] using hu
        | tick w t =>
            by_cases hw : v = w
            · subst hw
              have hst : (ρ.stateBefore S (i + 1) v).st =
                  (NamedNode.tick S v (ρ.stateBefore S i v) t).1.st := by
                rw [hstep, hev]
                simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                  NamedWorld.step, Function.update_self]
              obtain ⟨gc, hgc, hgcEmit⟩ : ∃ gc : Protocol.GradeContract V,
                  (NamedNode.tick S v (ρ.stateBefore S i v) t).1.st =
                    (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v)
                      (ρ.stateBefore S i v).st (ρ.stateBefore S i v).record t).1 ∧
                  (NamedNode.tick S v (ρ.stateBefore S i v) t).2 =
                    (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v)
                      (ρ.stateBefore S i v).st (ρ.stateBefore S i v).record t).2.2 :=
                ⟨_, rfl, rfl⟩
              rw [hst, hgc] at hu
              rcases gfFrom_named_tick gc S.E S.hc S.cfg (S.node v) (ρ.stateBefore S i v).st
                (ρ.stateBefore S i v).record t k u hu with h' | h' | ⟨B, hB, hBu⟩
              · exact bump h'
              · refine ⟨i, Event.tick v t, Nat.lt_succ_self i, hev,
                  Or.inl (Or.inl ⟨i, hev, ?_⟩)⟩
                show Object.gfVote u ∈ (NamedNode.tick S v (ρ.stateBefore S i v) t).2
                rw [hgcEmit]; exact h'
              · refine ⟨i, Event.tick v t, Nat.lt_succ_self i, hev,
                  Or.inr ⟨B, Or.inl ⟨i, hev, ?_⟩, hBu⟩⟩
                show Object.block B ∈ (NamedNode.tick S v (ρ.stateBefore S i v) t).2
                rw [hgcEmit]; exact hB
            · refine bump ?_
              rw [hstep, hev] at hu
              simpa only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
                NamedWorld.step, Function.update_of_ne hw] using hu

/-! ## The two-view containment (baseline `7b2efec`) -/

/-- **`voter_support_view ⊆ voter_view`** — the stated `support_votes ⊆ votes`
property, at the voter's merged pair. The pool arm is the resolution clock
dominating the receipt clock (`stampedBefore_of_resolution`); the carried arm is
the filter dropping its resolved conjunct. -/
theorem voter_support_view_subset (E : Env V) (st : Protocol.GoldfishStore V) (s : Slot)
    (hsub : ∀ B ∈ st.T, ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes) :
    Protocol.voter_support_view E st s ⊆ Protocol.voter_view E st s := by
  rw [Protocol.voter_support_view, Protocol.voter_view]
  refine Finset.union_subset_union ?_ ?_
  · intro u hu
    rw [beforeCutoff, Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, Protocol.stampedBefore_of_resolution hu.2⟩
  · intro u hu
    rw [Finset.mem_biUnion] at hu ⊢
    obtain ⟨B, hB, hmem⟩ := hu
    rw [Finset.mem_filter] at hmem
    have huRaw : u ∈ B.gf_votes :=
      hsub B (Finset.mem_filter.mp hB).1 u (List.mem_toFinset.mp hmem.1)
    exact ⟨B, hB,
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr huRaw, hmem.2.2⟩⟩

end Protocol
end DecoupledConsensusModel

end
