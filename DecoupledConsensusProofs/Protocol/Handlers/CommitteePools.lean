module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedExecutionQueries
public import DecoupledConsensusInternal.ModelVocabulary.FinalityGadget.Crossing
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusInternal.Execution.Run

@[expose] public section

/-!
# Goldfish pool committee membership

The raw Goldfish denominator reads every validator name represented in one
pool view. The store invariant needed for that read is small: every vote in a
slot bucket was authored by a member of that slot's committee.

This invariant is separate from `PoolStamps.slot`. That existing invariant says
that a vote in bucket `k` has `vote.slot = k`; this file says that its author is
in `K_k`. Together they give the source-aligned typing of a pooled vote without
adding either fact to the fork-choice definitions.

The invariant applies only to votes admitted to `Protocol.Store.gf_votes`. It
does not type votes carried in a block before ingress, or votes read directly
from a block by a merged view. Those facts remain consequences of
`DeliveryWellFormed.wire`; the checked ingress only guarantees that an invalid
carried vote cannot enter the receiving store's pool.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


namespace CommitteePools

/-- A vote read through the set-valued pool interface has a committee author. -/
theorem mem_committee {E : Env V} {st : Protocol.Store V}
    (h : CommitteePools E st) {k : Slot} {u : GoldfishVote V}
    (hu : u ∈ st.pool k) :
    u.val_index ∈ E.committee k := by
  apply h k u
  simpa only [Protocol.Store.pool, List.mem_toFinset] using hu

/-- Committee typing depends only on the Goldfish pool field. -/
theorem of_gf_votes_eq {E : Env V} {st st' : Protocol.Store V}
    (h : CommitteePools E st) (heq : st'.gf_votes = st.gf_votes) :
    CommitteePools E st' := by
  intro k u hu
  apply h k u
  rw [heq] at hu
  exact hu

/-- The initial store has no pooled Goldfish votes. -/
theorem init (E : Env V) : CommitteePools E (Protocol.Store.init : Protocol.Store V) := by
  intro k u hu
  exact (List.not_mem_nil (a := u) hu).elim

/-- The admitted-vote handler preserves committee typing when its input vote is
from its slot committee. Rejected branches are identities; the accepting branch
adds only that input vote to its own slot bucket. -/
theorem on_goldfish_vote {E : Env V} {st : Protocol.Store V}
    (h : CommitteePools E st) (u : GoldfishVote V)
    (huCommittee : u.val_index ∈ E.committee u.slot) :
    CommitteePools E (Protocol.on_goldfish_vote st u) := by
  by_cases hguard :
      u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot
  · rw [show Protocol.on_goldfish_vote st u = st by
      simp only [Protocol.on_goldfish_vote, if_pos hguard]]
    exact h
  by_cases hequiv : Protocol.equivocates (st.pool u.slot) u.val_index = true
  · rw [show Protocol.on_goldfish_vote st u = st by
      simp only [Protocol.on_goldfish_vote, if_neg hguard, if_pos hequiv]]
    exact h
  have hgf : (Protocol.on_goldfish_vote st u).gf_votes =
      fun k => if k = u.slot then st.gf_votes k ++ [u] else st.gf_votes k := by
    simp only [Protocol.on_goldfish_vote, if_neg hguard, if_neg hequiv]
  intro k x hx
  rw [hgf] at hx
  by_cases hk : k = u.slot
  · subst k
    simp only at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h u.slot x hx
    · have hxu : x = u := List.mem_singleton.mp hx
      subst x
      exact huCommittee
  · simp only [if_neg hk] at hx
    exact h k x hx

/-- The source-aligned checked ingress preserves committee typing without an
external premise. A non-committee vote is rejected; a committee vote delegates
to `on_goldfish_vote`. -/
theorem on_goldfish_vote_checked (E : Env V) {st : Protocol.Store V}
    (h : CommitteePools E st) (u : GoldfishVote V) :
    CommitteePools E (Protocol.on_goldfish_vote_checked E st u) := by
  unfold Protocol.on_goldfish_vote_checked
  by_cases hu : u.val_index ∉ E.committee u.slot
  · rw [if_pos hu]
    exact h
  · rw [if_neg hu]
    apply h.on_goldfish_vote u
    simpa only [not_not] using hu

/-- Folding the checked ingress over a carried vote list preserves committee
typing. Each element is checked independently before insertion. -/
theorem foldl_on_goldfish_vote_checked (E : Env V)
    (l : List (GoldfishVote V)) {st : Protocol.Store V}
    (h : CommitteePools E st) :
    CommitteePools E (l.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction l generalizing st with
  | nil => exact h
  | cons u l ih =>
      simp only [List.foldl_cons]
      exact ih (h.on_goldfish_vote_checked E u)

/-- Updating the finality caches does not change the Goldfish pool. -/
theorem update_finality (E : Env V) {st : Protocol.Store V}
    (h : CommitteePools E st)
    (sigma : Protocol.ChainState V) :
    CommitteePools E (Protocol.update_finality st sigma) := by
  apply h.of_gf_votes_eq
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

/-- Block ingress changes the Goldfish pool only through the checked fold over
the block's carried votes. No validity premise on the carried list is needed
for this store invariant: non-committee votes are rejected at ingress. -/
theorem on_block (E : Env V) {st : Protocol.Store V}
    (h : CommitteePools E st) (cfg : Protocol.HeightConfig)
    (B : Block V) :
    CommitteePools E (Protocol.on_block E cfg st B) := by
  unfold Protocol.on_block Protocol.on_block_using
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  · let state := Protocol.state_transition E cfg (st.σ B.parent) B
    let stored : Protocol.Store V :=
      { st with
        σ := fun C => if C = B then state else st.σ C
        T := insert B st.T
        timestamp_block := fun C =>
          if C = B then some (st.t : Stamp) else st.timestamp_block C }
    have hstored : CommitteePools E stored := by
      apply h.of_gf_votes_eq
      rfl
    have hunpacked : CommitteePools E
        (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored) :=
      hstored.foldl_on_goldfish_vote_checked E B.gf_votes
    exact hunpacked.update_finality E _
/-- The receiver-facing checked block handler preserves committee typing:
the valid branch delegates to the raw handler, and the invalid branch is
reflexive. -/
theorem on_block_checked (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) {st : Protocol.Store V}
    (h : CommitteePools E st) (B : Block V) :
    CommitteePools E (Protocol.on_block_checked E hc cfg st B) := by
  simp only [Protocol.on_block_checked, Protocol.on_block_checked_using]
  split_ifs
  · exact h.on_block E cfg B
  · exact h


/-- An SG ingress does not change the Goldfish pool. -/
theorem on_sg_vote (E : Env V) {st : Protocol.Store V}
    (h : CommitteePools E st)
    (hc : Protocol.HealConfig) (a : CombinedAttestation V) :
    CommitteePools E (Protocol.on_sg_vote hc st a) := by
  apply h.of_gf_votes_eq
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

/-- The time/slot record update at the front of a tick preserves the pool
invariant. -/
theorem set_time_slot (E : Env V) {st : Protocol.Store V}
    (h : CommitteePools E st)
    (t : Time) (s : Slot) :
    CommitteePools E { st with t := t, s := s } :=
  h

/-! ## The shared handler bodies
The named runtime calls the parametric handler bodies rather than the compatibility
specializations above. Each generalization below carries the specialization's
proof: the state the block body builds and the grade contract the duties read
are not the Goldfish pool. -/

/-- The shared block body preserves committee typing for any state builder.
The pool changes only through the checked carried-vote fold. -/
theorem on_block_using (E : Env V) {st : Protocol.Store V}
    (h : CommitteePools E st) (B : Block V)
    (build : Protocol.ChainState V → Protocol.ChainState V) :
    CommitteePools E (Protocol.on_block_using E st B build) := by
  unfold Protocol.on_block_using
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  · let stored : Protocol.Store V :=
      { st with
        σ := fun C => if C = B then build (st.σ B.parent) else st.σ C
        T := insert B st.T
        timestamp_block := fun C =>
          if C = B then some (st.t : Stamp) else st.timestamp_block C }
    have hstored : CommitteePools E stored := by
      apply h.of_gf_votes_eq
      rfl
    have hunpacked : CommitteePools E
        (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored) :=
      hstored.foldl_on_goldfish_vote_checked E B.gf_votes
    exact hunpacked.update_finality E _

/-- The shared carried-round guard preserves whatever its handler preserves. -/
theorem on_block_checked_using (E : Env V) (hc : Protocol.HealConfig)
    {st : Protocol.Store V} (h : CommitteePools E st)
    (handle : Protocol.Store V → Protocol.Store V)
    (hhandle : ∀ st', CommitteePools E st' → CommitteePools E (handle st'))
    (B : Block V) :
    CommitteePools E (Protocol.on_block_checked_using handle hc st B) := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle st h
  · exact h

/-- Confirmation evaluation under any grade contract writes only confirmation
record fields. -/
theorem update_confirmation_with (E : Env V) {st : Protocol.Store V}
    (h : CommitteePools E st) (gc : Protocol.GradeContract V)
    (hc : Protocol.HealConfig) (s : Slot) :
    CommitteePools E (Protocol.update_confirmation_with gc E hc st s) := by
  apply h.of_gf_votes_eq
  rfl

/-- The Goldfish vote duty under any grade contract either emits no vote or
sends its committee-guarded vote through the checked ingress. -/
theorem goldfish_vote_with (E : Env V) {st : Protocol.Store V}
    (h : CommitteePools E st) (gc : Protocol.GradeContract V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) :
    CommitteePools E (Protocol.goldfish_vote_with gc E hc nd st).1 := by
  simp only [Protocol.goldfish_vote_with]
  split
  · exact h.on_goldfish_vote_checked E _
  · exact h

/-! ## The named store steps

Every named wrapper reaches the erased core through one of the handlers above.
The retained named bodies and rows are not the Goldfish pool, so each named
step's invariant is the corresponding core step's. -/

omit [Fintype V] in
/-- The named body commit keeps the core the shared handler produced. -/
theorem commitBlock_core (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) : (Protocol.NamedStore.commitBlock before after B).core = after := by
  unfold Protocol.NamedStore.commitBlock
  split_ifs <;> rfl

/-- Named row admission is the existing SG handler on the core. -/
theorem admit_row (E : Env V) (hc : Protocol.HealConfig) {st : Protocol.NamedStore V}
    (h : CommitteePools E st.core) (a : NamedAttestation V) :
    CommitteePools E (Protocol.NamedAdmission.admit_row hc st a).core := by
  have hcore : (Protocol.NamedAdmission.admit_row hc st a).core =
      Protocol.on_sg_vote hc st.core a.erase := by
    dsimp only [Protocol.NamedAdmission.admit_row]
    split_ifs <;> rfl
  rw [hcore]
  exact h.on_sg_vote E hc _

/-- The carried named row fold admits each row through the same SG handler. -/
theorem admit_rows (E : Env V) (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      CommitteePools E st.core →
        CommitteePools E (Protocol.NamedAdmission.admit_rows hc st rows).core
  | [], _, h => h
  | a :: rows, st, h =>
      admit_rows E hc rows (Protocol.NamedAdmission.admit_row hc st a) (admit_row E hc h a)

/-- The named block core preserves committee typing. -/
theorem process_block_core (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) {st : Protocol.NamedStore V}
    (h : CommitteePools E st.core) (B : NamedBlock V) :
    CommitteePools E (Protocol.NamedStore.process_block_core E hc cfg st B).core := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs
  · rw [commitBlock_core]
    exact on_block_checked_using E hc h _
      (fun st' h' => on_block_using E h' B.erase _) B.erase
  · exact h

/-- Named block admission, core then carried rows, preserves committee typing. -/
theorem on_block_with (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    {st : Protocol.NamedStore V} (h : CommitteePools E st.core) (B : NamedBlock V) :
    CommitteePools E (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core := by
  have hb := process_block_core E hc cfg h B
  cases adm with
  | alsoCarried =>
      dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows E hc B.attestations _ hb
      · exact hb

/-! ## The four named duties -/

/-- The named proposal duty self-processes its block through named admission. -/
theorem named_propose (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    {st : Protocol.NamedStore V} (h : CommitteePools E st.core) :
    CommitteePools E (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact on_block_with .alsoCarried E hc cfg h _

/-- The named Goldfish vote duty is the core duty on the core store. -/
theorem named_vote (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) {st : Protocol.NamedStore V} (h : CommitteePools E st.core) :
    CommitteePools E (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core :=
  goldfish_vote_with E h gc hc nd

/-- The named confirmation duty is the core duty on the core store. -/
theorem named_confirmation (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) {st : Protocol.NamedStore V}
    (h : CommitteePools E st.core) (s : Slot) :
    CommitteePools E (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core :=
  update_confirmation_with E h gc hc s

/-- The named attestation duty's only store write is named row admission. -/
theorem named_attest (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) {st : Protocol.NamedStore V} (h : CommitteePools E st.core)
    (record : Protocol.NamedRecord) :
    CommitteePools E (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core :=
  admit_row E hc h _

/-- Any store property the four named duties preserve, and that the clock
staging preserves, holds of the named tick's returned store. -/
theorem named_tick_preserves (P : Protocol.NamedStore V → Prop)
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (hp : ∀ st, P st → P (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1)
    (hv : ∀ st, P st → P (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1)
    (hcf : ∀ st s, P st → P (Protocol.NamedDuties.update_confirmation_with gc E hc st s))
    (ha : ∀ st record, P st → P (Protocol.NamedDuties.attest_with gc E hc nd st record).1)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : P (Protocol.NamedStore.setClock E st t)) :
    P (Protocol.NamedTick.tick gc E hc cfg nd st record t).1 := by
  dsimp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
    Protocol.NamedTick.namedOps]
  split_ifs <;> solve_by_elim (maxDepth := 8) [hp, hv, hcf, ha, h]

/-! ## The named execution steps -/

/-- The named tick preserves committee typing through its ordered proposal,
vote, confirmation and attestation branches. Clock staging and the phase cache
do not touch the pool. -/
theorem on_tick_emit (S : Execution.Setup V) :
    Execution.NamedTickPoolsQuery S := by
  intro v before t h
  refine named_tick_preserves (fun st' => CommitteePools S.E st'.core) _ S.E S.hc S.cfg
    (S.node v) ?_ ?_ ?_ ?_ before.st before.record t
    (show CommitteePools S.E (Protocol.NamedStore.setClock S.E before.st t).core from
      h.of_gf_votes_eq rfl)
  · intro st' h'
    exact named_propose _ S.E S.hc S.cfg (S.node v) h'
  · intro st' h'
    exact named_vote _ S.E S.hc (S.node v) h'
  · intro st' s h'
    exact named_confirmation _ S.E S.hc h' s
  · intro st' record' h'
    exact named_attest _ S.E S.hc (S.node v) h' record'

/-- Processing one delivered named object preserves committee typing. Carried
votes and standalone votes both pass through the checked ingress. -/
theorem process (S : Execution.Setup V) :
    Execution.NamedProcessPoolsQuery S := by
  intro n o h
  cases o with
  | block B => exact on_block_with .alsoCarried S.E S.hc S.cfg h B
  | gfVote u => exact h.on_goldfish_vote_checked S.E u
  | attest a => exact admit_row S.E S.hc h a

/-! ## Execution prefixes -/

/-- Proposed compatibility forward to the authored named-world schema.
This is the same core-pool predicate, not an additional hypothesis. -/
abbrev WorldCommitteePools (S : Execution.Setup V)
    (w : Execution.World V) : Prop :=
  Execution.NamedWorldCommitteePools S w

/-- UNCHECKED exact-query restatement; the previous proof body is unchanged. -/
theorem world_init (S : Execution.Setup V) :
    Execution.NamedWorldInitPoolsQuery S := by
  intro v
  exact init S.E

/-- One execution event preserves committee typing at every node. This theorem
uses only the executable named handlers; it needs no schedule, honesty,
delivery, or admissibility premise. -/
theorem world_step (S : Execution.Setup V) :
    Execution.NamedWorldStepPoolsQuery S := by
  intro w e h x
  cases e with
  | tick v t =>
      by_cases hx : x = v
      · subst x
        simp only [Execution.NamedWorld.step, Function.update_apply]
        exact on_tick_emit S v (w v) t (h v)
      · simp only [Execution.NamedWorld.step, Function.update_apply, if_neg hx]
        exact h x
  | deliver v o t =>
      by_cases hx : x = v
      · subst x
        simp only [Execution.NamedWorld.step, Function.update_apply]
        exact process S (w v) o (h v)
      · simp only [Execution.NamedWorld.step, Function.update_apply, if_neg hx]
        exact h x

/-- Folding any event list from a well-typed world preserves the invariant. -/
theorem foldl_world_step (S : Execution.Setup V)
    (l : List (Execution.Event V)) {w : Execution.World V}
    (h : WorldCommitteePools S w) :
    WorldCommitteePools S (l.foldl (Execution.World.step S) w) := by
  induction l generalizing w with
  | nil => exact h
  | cons e l ih =>
      simp only [List.foldl_cons]
      exact ih (world_step S w e h)

/-- Every run read of the named fold has committee-typed pools, with no
`Admissible` assumption: the initial world is typed and every event step
preserves typing, so all four views are folds of typed steps. -/
theorem run_pools (S : Execution.Setup V) (rho : Execution.NamedRun V) :
    Execution.NamedRunPoolsQuery S rho :=
  ⟨fun i v => foldl_world_step S (rho.events.take i) (world_init S) v,
    fun t v => foldl_world_step S
      (rho.events.filter (fun e => decide (e.time ≤ t))) (world_init S) v,
    fun t v => foldl_world_step S
      (rho.events.filter (fun e => decide (e.time < t))) (world_init S) v,
    fun v => foldl_world_step S rho.events (world_init S) v⟩

/-- Every event prefix has committee-typed pools. -/
theorem stateBefore (S : Execution.Setup V)
    (rho : Execution.NamedRun V) (v : V) (i : Nat) :
    Execution.CorePools S (Execution.NamedRun.stateBefore S rho i v).st.core :=
  (run_pools S rho).1 i v

/-- The same unconditional invariant at the inclusive time view. -/
theorem stateAt (S : Execution.Setup V)
    (rho : Execution.NamedRun V) (v : V) (t : Time) :
    Execution.CorePools S (Execution.NamedRun.readAt S rho t v).st.core :=
  (run_pools S rho).2.1 t v

/-- The same unconditional invariant at the strict pre-time view. -/
theorem stateBeforeTime (S : Execution.Setup V)
    (rho : Execution.NamedRun V) (v : V) (t : Time) :
    Execution.CorePools S (Execution.NamedRun.stateBeforeTime S rho t v).st.core :=
  (run_pools S rho).2.2.1 t v

/-- The final world of any finite run has committee-typed pools. -/
theorem final (S : Execution.Setup V)
    (rho : Execution.NamedRun V) (v : V) :
    Execution.CorePools S (Execution.NamedRun.final S rho v).st.core :=
  (run_pools S rho).2.2.2 v

end CommitteePools
end Protocol
end DecoupledConsensusModel

end
