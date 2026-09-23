module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.BridgesTail
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2
public import DecoupledConsensusProofs.Protocol.ChainState.AlignedRoundLemmas
public import DecoupledConsensusProofs.Protocol.Schedule.Alignment
public import DecoupledConsensusProofs.Protocol.Handlers.MaximumCarrier
public import DecoupledConsensusInternal.Definitions.ValidatorVoteSafety

@[expose] public section

/-! # The named store bridge 

The retired run-to-store arrow (`Proofs.Bridges.depReachable_*`,
`reachableStore_of_depReachableStore` and their one-line wrappers) bundled a
handful of erased store facts behind one `DepReachableStore` hypothesis. The
named runtime proves `Proofs.NamedRuntime.NodeInvariant` at every prefix state but
exports none of those facts, so the consumers lost the arrow and nothing else.

This file is the replacement export surface. Every theorem is stated at the
named prefix state of an arbitrary validator — the invariant is local and needs
no honesty premise — and repeated at `stateBeforeTime` and `readAt`, which have
their own invariant producers in `NamedRuntime` and therefore need no schedule
premise either. `Run.stateAt` is the same function as `Run.readAt`, so the
`_stateAt` names below are aliases, kept because consumers spell both.

Never exported here: `DepReachableStore`, `ReachableStore`, `nodeDepSteps`,
`Proofs.Bridges.Step`/`DepStep`. A consumer that serves to reach a store fact through
them takes the specific export instead.
-/

/-! ## 1. The invariant, read at a single named node state

`NodeInvariant S n` unfolds as
`Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st ∧ … ∧ …`, whose first
component is `Proofs.NamedStoreRoots.Invariant ∧ Confirmed n.st.core` and whose first
component in turn is `Proofs.NamedStore.Coherent ∧ RootsInTree`. The projection paths
below are the ones the sketched; they typecheck as written. -/


namespace DecoupledConsensusModel.Proofs.NamedStoreBridge
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]



private theorem coherent_of_inv (S : Setup V) {n : NamedNodeState V}
    (h : Proofs.NamedRuntime.NodeInvariant S n) : Proofs.NamedStore.Coherent S.E S.cfg n.st := h.1.1.1

private theorem treeView_of_inv (S : Setup V) {n : NamedNodeState V}
    (h : Proofs.NamedRuntime.NodeInvariant S n) :
    n.st.core.T = n.st.bodies.image NamedBlock.erase := (coherent_of_inv S h).1

private theorem namedParentClosed_of_inv (S : Setup V) {n : NamedNodeState V}
    (h : Proofs.NamedRuntime.NodeInvariant S n) : NamedStore.NamedParentClosed n.st :=
  (coherent_of_inv S h).2.2.1

private theorem finalizedInTree_of_inv (S : Setup V) {n : NamedNodeState V}
    (h : Proofs.NamedRuntime.NodeInvariant S n) : n.st.core.F ∈ n.st.core.T := h.1.1.2.1

private theorem justifiedInTree_of_inv (S : Setup V) {n : NamedNodeState V}
    (h : Proofs.NamedRuntime.NodeInvariant S n) : n.st.core.J ∈ n.st.core.T := h.1.1.2.2

private theorem liveConfirmed_of_inv (S : Setup V) {n : NamedNodeState V}
    (h : Proofs.NamedRuntime.NodeInvariant S n) :
    n.st.core.live_confirmed ∈ n.st.core.T := h.1.2.1

private theorem latestConfirmed_of_inv (S : Setup V) {n : NamedNodeState V}
    (h : Proofs.NamedRuntime.NodeInvariant S n) :
    n.st.core.latest_confirmed ∈ n.st.core.T := h.1.2.2.1


/-- A geometry block a coherent store holds is the erasure of a retained named
body. This is the hinge every `RunBlock`-on-an-erased-block site needs. -/
private theorem exists_named_of_inv (S : Setup V) {n : NamedNodeState V}
    (h : Proofs.NamedRuntime.NodeInvariant S n) {B : Block V} (hB : B ∈ n.st.core.T) :
    ∃ D ∈ n.st.bodies, D.erase = B := by
  rw [treeView_of_inv S h] at hB
  obtain ⟨D, hD, hDB⟩ := Finset.mem_image.mp hB
  exact ⟨D, hD, hDB⟩

/-- The erased parent-closure of the core tree. No induction: the named tree is
parent closed, the tree view transports it, and `Proofs.NamedWire.erase_parent` says
the erasure of the named parent is the parent of the erasure. -/
private theorem parentClosed_of_inv (S : Setup V) {n : NamedNodeState V}
    (h : Proofs.NamedRuntime.NodeInvariant S n) : ParentClosed n.st.core := by
  have hTree := treeView_of_inv S h
  have hpc := namedParentClosed_of_inv S h
  rw [parentClosed_iff]
  constructor
  · rw [hTree]
    exact Finset.mem_image_of_mem NamedBlock.erase hpc.1
  · intro B hB
    refine Or.inr ?_
    rw [hTree] at hB ⊢
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hB
    rw [Proofs.NamedWire.erase_parent]
    exact Finset.mem_image_of_mem NamedBlock.erase (hpc.2 D hD)

/-! ## 2. The four index forms

`stateBefore`, `stateBeforeTime` and `readAt` each have their own invariant
producer in `NamedRuntime`, so none of these needs a schedule premise. -/

theorem finalizedInTree_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    (rho.stateBefore S i v).st.core.F ∈ (rho.stateBefore S i v).st.core.T :=
  finalizedInTree_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i v)

theorem finalizedInTree_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    (rho.stateBeforeTime S t v).st.core.F ∈ (rho.stateBeforeTime S t v).st.core.T :=
  finalizedInTree_of_inv S (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v)

theorem finalizedInTree_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    (Run.readAt S rho t v).st.core.F ∈ (Run.readAt S rho t v).st.core.T :=
  finalizedInTree_of_inv S (Proofs.NamedRuntime.readAt_invariants S rho t v)

theorem finalizedInTree_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    (Run.stateAt S rho t v).st.core.F ∈ (Run.stateAt S rho t v).st.core.T :=
  finalizedInTree_readAt S rho t v


theorem justifiedInTree_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    (rho.stateBefore S i v).st.core.J ∈ (rho.stateBefore S i v).st.core.T :=
  justifiedInTree_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i v)

theorem justifiedInTree_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    (rho.stateBeforeTime S t v).st.core.J ∈ (rho.stateBeforeTime S t v).st.core.T :=
  justifiedInTree_of_inv S (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v)





theorem liveConfirmed_mem_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    (Run.readAt S rho t v).st.core.live_confirmed ∈ (Run.readAt S rho t v).st.core.T :=
  liveConfirmed_of_inv S (Proofs.NamedRuntime.readAt_invariants S rho t v)

theorem liveConfirmed_mem_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    (Run.stateAt S rho t v).st.core.live_confirmed ∈ (Run.stateAt S rho t v).st.core.T :=
  liveConfirmed_mem_readAt S rho t v


theorem latestConfirmed_mem_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    (rho.stateBeforeTime S t v).st.core.latest_confirmed ∈
      (rho.stateBeforeTime S t v).st.core.T :=
  latestConfirmed_of_inv S (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v)



theorem exists_named_of_mem_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V)
    {B : Block V} (hB : B ∈ (rho.stateBefore S i v).st.core.T) :
    ∃ D ∈ (rho.stateBefore S i v).st.bodies, D.erase = B :=
  exists_named_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i v) hB

theorem exists_named_of_mem_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V)
    {B : Block V} (hB : B ∈ (rho.stateBeforeTime S t v).st.core.T) :
    ∃ D ∈ (rho.stateBeforeTime S t v).st.bodies, D.erase = B :=
  exists_named_of_inv S (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v) hB

theorem exists_named_of_mem_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V)
    {B : Block V} (hB : B ∈ (Run.readAt S rho t v).st.core.T) :
    ∃ D ∈ (Run.readAt S rho t v).st.bodies, D.erase = B :=
  exists_named_of_inv S (Proofs.NamedRuntime.readAt_invariants S rho t v) hB

theorem exists_named_of_mem_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V)
    {B : Block V} (hB : B ∈ (Run.stateAt S rho t v).st.core.T) :
    ∃ D ∈ (Run.stateAt S rho t v).st.bodies, D.erase = B :=
  exists_named_of_mem_readAt S rho t v hB

theorem parentClosed_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    ParentClosed (rho.stateBefore S i v).st.core :=
  parentClosed_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i v)

theorem parentClosed_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ParentClosed (rho.stateBeforeTime S t v).st.core :=
  parentClosed_of_inv S (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v)

theorem parentClosed_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ParentClosed (Run.readAt S rho t v).st.core :=
  parentClosed_of_inv S (Proofs.NamedRuntime.readAt_invariants S rho t v)

theorem parentClosed_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ParentClosed (Run.stateAt S rho t v).st.core :=
  parentClosed_readAt S rho t v

/-! ## 3. Named run bodies behind geometry membership

`Proofs.Bridges.runBlock_of_stateBefore_mem` turns a retained named body at an honest
prefix into a `RunBlock`. Composed with the tree view it answers the whole C1
class: a site holding `B ∈ (…).st.core.T` gets a named `D` with `D.erase = B`
and `RunBlock S rho D`. The time-indexed companions need the schedule premise,
because `directBlockInRun` quantifies over event indices and only a sorted
schedule makes a time-filtered fold a prefix. -/

theorem runBlock_of_mem_core_T (S : Setup V) (rho : Run V) {v : V} (hv : v ∈ rho.honest)
    (i : Nat) {B : Block V} (hB : B ∈ (rho.stateBefore S i v).st.core.T) :
    ∃ D : NamedBlock V, D.erase = B ∧ RunBlock S rho D := by
  obtain ⟨D, hD, hDB⟩ := exists_named_of_mem_stateBefore S rho i v hB
  exact ⟨D, hDB, Proofs.Bridges.runBlock_of_stateBefore_mem S hv hD⟩

theorem runBlock_of_mem_core_T_stateBeforeTime (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {v : V} (hv : v ∈ rho.honest) (t : Time)
    {B : Block V} (hB : B ∈ (rho.stateBeforeTime S t v).st.core.T) :
    ∃ D : NamedBlock V, D.erase = B ∧ RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch t
  rw [hn] at hB
  exact runBlock_of_mem_core_T S rho hv n hB

theorem runBlock_of_mem_core_T_readAt (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {v : V} (hv : v ∈ rho.honest) (t : Time)
    {B : Block V} (hB : B ∈ (Run.readAt S rho t v).st.core.T) :
    ∃ D : NamedBlock V, D.erase = B ∧ RunBlock S rho D := by
  obtain ⟨n, hn⟩ := Proofs.Bridges.stateAt_eq_stateBefore S sch t
  have hn' : Run.readAt S rho t = Run.stateBefore S rho n := hn
  rw [hn'] at hB
  exact runBlock_of_mem_core_T S rho hv n hB



/-! ## 4. Carried attestations are honest emissions

`AlignedRoundLemmas.slashableBound_of_belowOneThird` already carries the named
premise: for every `B: NamedBlock V` in the run, the attestations on
`chain_attestations B.erase` that name an honest validator were emitted by that
validator. This is the named restatement of the retired
`carriedByHonest_of_runBlock_core`; it is the sole premise of the accountable
bound, so it is the whole gap for `SlashableBoundBridgeRun`. -/

omit [Fintype V] in
private theorem preceq_cases {A B : NamedBlock V} (h : NamedBlock.Preceq A B) :
    A = B ∨ NamedBlock.Preceq A B.parent := by
  cases B with
  | genesis =>
    left
    simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using h
  | node p s root gf support rows proposer =>
    simpa only [NamedBlock.Preceq, NamedBlock.preceq, NamedBlock.parent, Bool.or_eq_true,
      decide_eq_true_eq] using h

omit [Fintype V] in
private theorem preceq_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) : NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
    have hB : B = .genesis := by simpa [NamedBlock.Preceq, NamedBlock.preceq] using hBC
    simpa only [← hB] using hAB
  | node p s root gf support rows proposer ih =>
    rcases preceq_cases hBC with rfl | hparent
    · exact hAB
    · change (decide (A = .node p s root gf support rows proposer) ||
        NamedBlock.preceq A p) = true
      simp only [Bool.or_eq_true]
      exact Or.inr (ih hparent)

omit [Fintype V] in
/-- The named elimination form of `chain_attestations` on an erased chain: an
attestation the erased chain carries is the erasure of a row some named
ancestor carries. -/
private theorem named_mem_chain_attestations {a : CombinedAttestation V} :
    ∀ B : NamedBlock V, a ∈ chain_attestations B.erase →
      ∃ X : NamedBlock V, NamedBlock.Preceq X B ∧
        ∃ row ∈ X.attestations, row.erase = a := by
  intro B
  induction B with
  | genesis => intro h; simp [NamedBlock.erase, chain_attestations] at h
  | node p s root gf support rows proposer ih =>
    intro h
    simp only [NamedBlock.erase, chain_attestations, Finset.mem_union,
      List.mem_toFinset, List.mem_map] at h
    rcases h with ⟨row, hrow, hrowa⟩ | h
    · refine ⟨.node p s root gf support rows proposer, ?_, row, hrow, hrowa⟩
      simp [NamedBlock.Preceq, NamedBlock.preceq]
    · obtain ⟨X, hXp, row, hrow, hrowa⟩ := ih h
      refine ⟨X, ?_, row, hrow, hrowa⟩
      change (decide (X = .node p s root gf support rows proposer) ||
        NamedBlock.preceq X p) = true
      simp only [Bool.or_eq_true]
      exact Or.inr hXp

omit [Fintype V] in
/-- Named parent-closure lifts to every named ancestor. -/
private theorem ancestor_body_mem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · exact ih (hpc.2 _ hB) hparent

/-- A named body a validator's prefix store holds was processed by that
validator, unless it is genesis — which carries no rows. -/
private theorem processes_of_mem_bodies (S : Setup V) (rho : Run V) (v : V) (i : Nat)
    {X : NamedBlock V} (hX : X ∈ (rho.stateBefore S i v).st.bodies)
    {row : NamedAttestation V} (hrow : row ∈ X.attestations) :
    ∃ t : Time, Run.processes S rho v (Object.block X) t := by
  rcases Proofs.Bridges.processes_block_of_mem_T S rho v i X hX with rfl | ⟨j, e, -, -, hproc⟩
  · exact absurd hrow (by simp [NamedBlock.attestations])
  · exact ⟨e.time, hproc⟩

/-- Every attestation in an event-prefix store which names an honest validator
is an actual emission by that validator. Only carried-attestation authenticity
is needed. -/
theorem carriedByHonest_of_stateBefore (S : Setup V) {rho : Run V}
    (auth : AttestationAuthenticity S rho) (v : V) (i : Nat) :
    AlignedRoundLemmas.CarriedByHonest S rho rho.honest
      (store_attestations (rho.stateBefore S i v).st.core) := by
  intro a ha hah
  obtain ⟨B, hB, haB⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨D, hD, rfl⟩ :=
    exists_named_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i v) hB
  obtain ⟨X, hXD, row, hrow, rfl⟩ := named_mem_chain_attestations D haB
  have hX : X ∈ (rho.stateBefore S i v).st.bodies :=
    ancestor_body_mem
      (namedParentClosed_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i v))
      hD hXD
  obtain ⟨t, hproc⟩ := processes_of_mem_bodies S rho v i hX hrow
  obtain ⟨t', -, hem⟩ := auth.carriedAttest v X t hproc row hrow hah
  exact ⟨row, t', rfl, hem⟩

/-- Time-indexed form of `carriedByHonest_of_stateBefore`. Event sorting is
used only to identify the read with an event prefix. -/
theorem carriedByHonest_of_storeAt (S : Setup V) {rho : Run V}
    (sorted : rho.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f))
    (auth : AttestationAuthenticity S rho)
    (v : V) (t : Time) :
    AlignedRoundLemmas.CarriedByHonest S rho rho.honest
      (store_attestations (rho.storeAt S v t).core) := by
  obtain ⟨i, hi⟩ := Proofs.Bridges.stateAt_eq_stateBefore_of_sorted S sorted t
  have heq : rho.storeAt S v t = (rho.stateBefore S i v).st :=
    congrArg (·.st) (congrFun hi v)
  rw [heq]
  exact carriedByHonest_of_stateBefore S auth v i

/-- Every named ancestor carrying a row of a run block was processed somewhere.
Both disjuncts of `directBlockInRun` are discharged: a delivered block gives the
delivery's own processing for the block itself, and the delivery contract puts
its parent in the recipient's prefix store for every strict ancestor. -/
private theorem processes_of_runBlock (S : Setup V) {rho : Run V}
    (hadm : AdmissibleCore S rho) {B : NamedBlock V} (hB : RunBlock S rho B)
    {X : NamedBlock V} (hXB : NamedBlock.Preceq X B)
    {row : NamedAttestation V} (hrow : row ∈ X.attestations) :
    ∃ (u : V) (t : Time), Run.processes S rho u (Object.block X) t := by
  obtain ⟨C, hC, hBC⟩ := hB
  have hXC : NamedBlock.Preceq X C := preceq_trans hXB hBC
  rcases hC with hobj | ⟨w, -, i, hmem⟩
  · obtain ⟨i, u, t, hev⟩ := Proofs.Bridges.exists_deliver_of_mem_objects rho hobj
    rcases preceq_cases hXC with rfl | hparent
    · exact ⟨u, t, Or.inr ⟨i, hev⟩⟩
    · have hdeps := hadm.toNamedDeliveryWellFormed.deps i u (Object.block C) t hev
      have hpar : C.parent ∈ (rho.stateBefore S i u).st.bodies := by
        simpa only [NamedReceipt.depsPresent, decide_eq_true_eq] using hdeps
      have hXmem : X ∈ (rho.stateBefore S i u).st.bodies :=
        ancestor_body_mem
          (namedParentClosed_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i u))
          hpar hparent
      obtain ⟨t', hproc⟩ := processes_of_mem_bodies S rho u i hXmem hrow
      exact ⟨u, t', hproc⟩
  · have hXmem : X ∈ (rho.stateBefore S i w).st.bodies :=
      ancestor_body_mem
        (namedParentClosed_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i w))
        hmem hXC
    obtain ⟨t', hproc⟩ := processes_of_mem_bodies S rho w i hXmem hrow
    exact ⟨w, t', hproc⟩

theorem carriedByHonest_of_runBlock (S : Setup V) {rho : Run V}
    (hadm : AdmissibleCore S rho) {B : NamedBlock V} (hB : RunBlock S rho B) :
    AlignedRoundLemmas.CarriedByHonest S rho rho.honest (chain_attestations B.erase) := by
  intro a ha hah
  obtain ⟨X, hXB, row, hrow, rfl⟩ := named_mem_chain_attestations B ha
  obtain ⟨u, t, hproc⟩ := processes_of_runBlock S hadm hB hXB hrow
  obtain ⟨t', -, hem⟩ := hadm.toNamedUnforgeable.carried_attest u X t hproc row hrow hah
  exact ⟨row, t', rfl, hem⟩

/-! ## 5. The store's slot is the slot of its clock

`Proofs.Optimistic.slotOfClock_reachable` proved this over the retired `ReachableStore`
predicate. It is not a clause of `NodeInvariant`, so it needs its own fold — a
short one, because `Protocol.NamedStore.setClock` writes both fields together
and is the only writer. The tick case does not even use the induction
hypothesis: `Proofs.NamedNode.tick_clock` says the tick's own store reads `t` and
`E.slotOf t` outright, and `Proofs.NamedNode.process_clock` says a delivery moves
neither field. The pattern is `NamedRuntime`'s `step_invariant` /
`fold_invariant`, copied for this one predicate. -/

private theorem slotOfClock_initial (S : Setup V) (v : V) :
    Proofs.Optimistic.SlotOfClock S.E (NamedWorld.init v : NamedNodeState V).st.core := by
  simp [Proofs.Optimistic.SlotOfClock, NamedWorld.init, NamedNode.initial,
    Protocol.NamedStore.initial, Protocol.Store.init, Env.slotOf, slotOfTime]

private theorem slotOfClock_step (S : Setup V) (w : NamedWorld V) (e : NamedEvent V)
    (h : ∀ v, Proofs.Optimistic.SlotOfClock S.E (w v).st.core) :
    ∀ v, Proofs.Optimistic.SlotOfClock S.E (NamedWorld.step S w e v).st.core := by
  intro v
  by_cases hv : v = e.node
  · cases e with
    | tick u t =>
      change v = u at hv
      subst v
      rw [Proofs.NamedRuntime.step_tick]
      unfold Proofs.Optimistic.SlotOfClock
      rw [(Proofs.NamedNode.tick_clock S u (w u) t).1]
      exact (Proofs.NamedNode.tick_clock S u (w u) t).2
    | deliver u o t =>
      change v = u at hv
      subst v
      rw [Proofs.NamedRuntime.step_deliver]
      unfold Proofs.Optimistic.SlotOfClock
      rw [(Proofs.NamedNode.process_clock S (w u) o).1, (Proofs.NamedNode.process_clock S (w u) o).2]
      exact h u
  · rw [Proofs.NamedRuntime.step_other S w e v hv]
    exact h v

private theorem slotOfClock_fold (S : Setup V) (events : List (NamedEvent V)) :
    ∀ w : NamedWorld V, (∀ v, Proofs.Optimistic.SlotOfClock S.E (w v).st.core) →
      ∀ v, Proofs.Optimistic.SlotOfClock S.E (events.foldl (NamedWorld.step S) w v).st.core := by
  induction events with
  | nil => intro w h; exact h
  | cons e events ih =>
    intro w h
    exact ih _ (slotOfClock_step S w e h)




/-- Every row a store holds in bucket `r` names round `r`. -/
def SgRowRounds (st : Protocol.NamedStore V) : Prop :=
  ∀ r : Round, ∀ row ∈ st.sg_rows r, row.round = r

omit [Fintype V] in
private theorem sgRowRounds_admit_row (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (row : NamedAttestation V) (h : SgRowRounds st) :
    SgRowRounds (Protocol.NamedAdmission.admit_row hc st row) := by
  intro r x hx
  dsimp only [Protocol.NamedAdmission.admit_row] at hx
  split_ifs at hx with hg
  · dsimp only at hx
    split_ifs at hx with hr
    · rcases List.mem_append.mp hx with h1 | h1
      · exact h r x h1
      · rw [List.mem_singleton.mp h1, hr]
    · exact h r x hx
  · exact h r x hx

omit [Fintype V] in
private theorem sgRowRounds_admit_rows (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) (h : SgRowRounds st) :
    SgRowRounds (Protocol.NamedAdmission.admit_rows hc st rows) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (sgRowRounds_admit_row hc st a h)

private theorem sgRowRounds_initial (_S : Setup V) (v : V) :
    SgRowRounds (NamedWorld.init v : NamedNodeState V).st := by
  intro r row hrow
  simp only [NamedWorld.init, NamedNode.initial, Protocol.NamedStore.initial,
    List.not_mem_nil] at hrow

omit [DecidableEq V] [Fintype V] in
private theorem sgRowRounds_of_sg_rows {st st' : Protocol.NamedStore V}
    (he : st'.sg_rows = st.sg_rows) (h : SgRowRounds st) : SgRowRounds st' := by
  intro r x hx
  rw [he] at hx
  exact h r x hx

/-- The block core rewrites `core` and `bodies` only. -/
private theorem process_block_core_sg_rows (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).sg_rows = st.sg_rows := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split
  · rfl
  · dsimp only [Protocol.NamedStore.commitBlock]
    split <;> rfl

private theorem sgRowRounds_on_block_with (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : SgRowRounds st) :
    SgRowRounds (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B) := by
  have hcore : SgRowRounds (Protocol.NamedStore.process_block_core E hc cfg st B) :=
    sgRowRounds_of_sg_rows (process_block_core_sg_rows E hc cfg st B) h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split
  · exact sgRowRounds_admit_rows hc _ B.attestations hcore
  · exact hcore

private theorem sgRowRounds_process (S : Setup V) (st : Protocol.NamedStore V)
    (o : NamedObject V) (h : SgRowRounds st) :
    SgRowRounds (Execution.NamedReceipt.process S st o) := by
  cases o with
  | block B =>
    show SgRowRounds (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B)
    exact sgRowRounds_on_block_with S.E S.hc S.cfg st B h
  | gfVote u => exact fun r x hx => h r x hx
  | attest a => exact sgRowRounds_admit_row S.hc st a h

private theorem sgRowRounds_propose (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : SgRowRounds st) :
    SgRowRounds (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1 := by
  dsimp only [Protocol.NamedDuties.propose_block_with]
  split
  · exact h
  · exact sgRowRounds_on_block_with E hc cfg st _ h

/-- Every duty of the tick timetable keeps rows in their own bucket, so the
whole tick does. Stated over the shared scheduler: the four duty guards are
the only branching. -/
private theorem sgRowRounds_runWith {Record BlockOut VoteOut AttOut Out : Type}
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (ops : Protocol.TickScheduler.TickOps (Protocol.NamedStore V) Record BlockOut VoteOut AttOut)
    (blockOut : BlockOut → Out) (voteOut : VoteOut → Out) (attOut : AttOut → Out)
    (hclock : ∀ st t s, SgRowRounds st → SgRowRounds (ops.clock st t s))
    (hprop : ∀ st, SgRowRounds st → SgRowRounds (ops.proposal st).1)
    (hvote : ∀ st, SgRowRounds st → SgRowRounds (ops.vote st).1)
    (hconf : ∀ st s, SgRowRounds st → SgRowRounds (ops.confirmation st s))
    (hatt : ∀ st r, SgRowRounds st → SgRowRounds (ops.attestation st r).1)
    (st : Protocol.NamedStore V) (record : Record) (t : Time) (h : SgRowRounds st) :
    SgRowRounds (Protocol.TickScheduler.runWith E hc nd ops blockOut voteOut attOut
      (fun st record emitted => (st, record, emitted)) st record t).1 := by
  dsimp only [Protocol.TickScheduler.runWith]
  split_ifs <;>
    repeat' first
      | exact h
      | apply hatt
      | apply hconf
      | apply hvote
      | apply hprop
      | apply hclock

private theorem sgRowRounds_tick (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : SgRowRounds n.st) :
    SgRowRounds (Execution.NamedNode.tick S v n t).1.st := by
  show SgRowRounds (Protocol.NamedTick.tick
    (NamedProfile.gradeContract (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
    S.E S.hc S.cfg (S.node v) n.st n.record t).1
  refine sgRowRounds_runWith S.E S.hc (S.node v) _ _ _ _ ?_ ?_ ?_ ?_ ?_ _ _ _ h
  · exact fun u _ _ hu => hu
  · exact fun u hu => sgRowRounds_propose _ S.E S.hc S.cfg (S.node v) u hu
  · exact fun u hu => hu
  · exact fun u _ hu => hu
  · exact fun u _ hu => sgRowRounds_admit_row S.hc u _ hu

private theorem sgRowRounds_step (S : Setup V) (w : NamedWorld V) (e : NamedEvent V)
    (h : ∀ v, SgRowRounds (w v).st) :
    ∀ v, SgRowRounds (NamedWorld.step S w e v).st := by
  intro v
  by_cases hv : v = e.node
  · cases e with
    | tick u t =>
      change v = u at hv
      subst v
      rw [Proofs.NamedRuntime.step_tick]
      exact sgRowRounds_tick S u (w u) t (h u)
    | deliver u o t =>
      change v = u at hv
      subst v
      rw [Proofs.NamedRuntime.step_deliver]
      exact sgRowRounds_process S (w u).st o (h u)
  · rw [Proofs.NamedRuntime.step_other S w e v hv]
    exact h v

private theorem sgRowRounds_fold (S : Setup V) (events : List (NamedEvent V)) :
    ∀ w : NamedWorld V, (∀ v, SgRowRounds (w v).st) →
      ∀ v, SgRowRounds (events.foldl (NamedWorld.step S) w v).st := by
  induction events with
  | nil => intro w h; exact h
  | cons e events ih =>
    intro w h
    exact ih _ (sgRowRounds_step S w e h)

theorem sgRowRounds_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    SgRowRounds (rho.stateBefore S i v).st :=
  sgRowRounds_fold S (rho.events.take i) NamedWorld.init (sgRowRounds_initial S) v

theorem sgRowRounds_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    SgRowRounds (rho.stateBeforeTime S t v).st :=
  sgRowRounds_fold S _ NamedWorld.init (sgRowRounds_initial S) v




omit [DecidableEq V] [Fintype V] in
/-- The erased twin. `PoolView` says the pool of round `r` is exactly the
erased rows of bucket `r`, and erasure keeps the round field, so the bucket
key transfers to the pool. This is earlier's `Proofs.Optimistic.sgRounds_stateBefore`. -/
private theorem sgRounds_of_rows {st : Protocol.NamedStore V}
    (hp : NamedStore.PoolView st) (h : SgRowRounds st) : Proofs.Optimistic.SgRounds st.core := by
  intro r a ha
  rw [hp r, List.mem_map] at ha
  obtain ⟨row, hrow, rfl⟩ := ha
  exact h r row hrow

theorem sgRounds_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    Proofs.Optimistic.SgRounds (rho.stateBefore S i v).st.core :=
  sgRounds_of_rows (coherent_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i v)).2.2.2.1
    (sgRowRounds_stateBefore S rho i v)




theorem slotOfClock_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    Proofs.Optimistic.SlotOfClock S.E (rho.stateBefore S i v).st.core :=
  slotOfClock_fold S (rho.events.take i) NamedWorld.init (slotOfClock_initial S) v





/-! ## 6. The finalized root precedes the justified root

`Block.Preceq Σ.F Σ.J` was the half of `reachableStore_of_depReachableStore`
that most of its consumers actually wanted. It is not a clause of
`NodeInvariant`, so it takes its own fold.

`FrameStoreJustification.lean` has the erased handler steps for it, but that
file is not green and imports `FrameStoreRoot`, which imports a non-green
healing module, so it cannot be used. The named fold already exists instead, as
the private `CoreOrder` chain of `NamedFGProtection.lean` (also not green, and
heavy: justification certificates and carriers). The chain itself is
self-contained and depends only on green modules, so it is copied here as
private lemmas. Every step is the named handler's own, so no erased
`DerivedStateAgrees` and no delivery premise is spent anywhere. -/

open Protocol (ChainState derive_named)

private def CoreOrder (st : Protocol.Store V) : Prop :=
  Block.Preceq st.F st.J

omit [Fintype V] in
private theorem initial_core_order :
    CoreOrder (Protocol.NamedStore.initial : Protocol.NamedStore V).core :=
  Block.preceq_self _

private theorem gf_order (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V)
    (h : CoreOrder st) : CoreOrder (Protocol.on_goldfish_vote_checked E st u) := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact h

private theorem gf_fold_order (E : Env V) (st : Protocol.Store V)
    (votes : List (GoldfishVote V)) (h : CoreOrder st) :
    CoreOrder (votes.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction votes generalizing st with
  | nil => exact h
  | cons u votes ih => exact ih _ (gf_order E st u h)

private theorem raw_block_order (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V)
    (h : CoreOrder st) : CoreOrder (Protocol.on_block_using E st B build) := by
  dsimp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact h
    | (apply update_finality_preceq
       exact gf_fold_order E _ B.gf_votes h)

private theorem process_core_order (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hco : Proofs.NamedStore.Coherent S.E S.cfg st)
    (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
  cases B with
  | genesis =>
    have hmem : Block.genesis ∈ st.core.T := by
      rw [hco.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hco.2.2.1.1
    have hpgen : NamedBlock.genesis.parent ∈ st.bodies := by
      change NamedBlock.genesis ∈ st.bodies
      exact hco.2.2.1.1
    rw [Protocol.NamedStore.process_block_core,
      if_neg (not_not.mpr hpgen), NamedStore.commit_core]
    dsimp only [Protocol.on_block_checked_using]
    split_ifs
    · change CoreOrder (Protocol.on_block_using S.E st.core Block.genesis _)
      simpa [Protocol.on_block_using, hmem] using h
    · exact h
  | node parent slot root votes support rows proposer =>
    let B : NamedBlock V := .node parent slot root votes support rows proposer
    change CoreOrder
      (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core
    by_cases hp : B.parent ∈ st.bodies
    · rw [Protocol.NamedStore.process_block_core, if_neg (not_not.mpr hp),
        NamedStore.commit_core]
      dsimp only [Protocol.on_block_checked_using]
      split_ifs
      · exact raw_block_order S.E st.core B.erase _ h
      · exact h
    · simpa [Protocol.NamedStore.process_block_core, hp] using h

omit [Fintype V] in
private theorem row_order (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  dsimp only [Protocol.on_sg_vote]
  split_ifs <;> exact h

omit [Fintype V] in
private theorem rows_order (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (row_order hc st a h)

private theorem block_order (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreOrder st.core) :
    CoreOrder
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core := by
  have hc := process_core_order S st B hco h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact rows_order S.hc _ B.attestations hc
  · exact hc

private theorem clock_order (E : Env V) (st : Protocol.NamedStore V) (t : Time)
    (h : CoreOrder st.core) : CoreOrder (Protocol.NamedStore.setClock E st t).core := h

private theorem confirmation_order (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core := h

private theorem propose_order (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact block_order S st _ hco h

private theorem vote_order (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact gf_order S.E st.core _ h
  · exact h

private theorem attest_order (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1.core :=
  row_order S.hc st _ h

private theorem tick_order (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 := clock_order S.E st t h
  have hc0 := NamedStore.coherent_clock S.E S.cfg st t hco
  have h1 : CoreOrder st1.core := by dsimp [st1]; split_ifs
    <;> first | exact propose_order gc S nd st0 hc0 h0 | exact h0
  have h2 : CoreOrder st2.core := by dsimp [st2]; split_ifs
    <;> first | exact vote_order gc S nd st1 h1 | exact h1
  have h3 : CoreOrder st3.core := by
    by_cases hs : 0 < s ∧ t = Protocol.support_cutoff S.E s
    · simpa [st3, hs] using confirmation_order gc S st2 (s - 1) h2
    · simpa [st3, hs] using h2
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact attest_order gc S nd st3 record h3
  · exact h3

private theorem node_tick_order (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (h : CoreOrder n.st.core) :
    CoreOrder (Execution.NamedNode.tick S v n t).1.st.core :=
  tick_order (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v)
    n.st n.record t hco h

private theorem node_process_order (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (h : CoreOrder n.st.core) :
    CoreOrder (Execution.NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact block_order S n.st B hco h
  | gfVote u => exact gf_order S.E n.st.core u h
  | attest a => exact row_order S.hc n.st a h

private theorem fold_order (S : Setup V) (events : List (NamedEvent V)) (w : NamedWorld V)
    (hinv : ∀ v, Proofs.NamedConfirmationMembership.Invariant S.E S.cfg (w v).st ∧
      NamedTickRecord.Invariant (w v).record)
    (h : ∀ v, CoreOrder (w v).st.core) :
    ∀ v, CoreOrder (events.foldl (NamedWorld.step S) w v).st.core := by
  induction events generalizing w with
  | nil => exact h
  | cons e events ih =>
    apply ih
    · intro v
      cases e with
      | tick u t =>
        by_cases hv : v = u
        · subst u
          exact ⟨by simpa [NamedWorld.step] using
              NamedNode.confirmation_invariant_tick S v (w v) t (hinv v).1,
            by simpa [NamedWorld.step] using
              NamedNode.record_invariant_tick S v (w v) t (hinv v).2⟩
        · simpa [NamedWorld.step, Function.update_of_ne hv] using hinv v
      | deliver u o t =>
        by_cases hv : v = u
        · subst u
          simpa [NamedWorld.step] using
            NamedNode.invariants_process S (w v) o (hinv v).1 (hinv v).2
        · simpa [NamedWorld.step, Function.update_of_ne hv] using hinv v
    · intro v
      cases e with
      | tick u t =>
        by_cases hv : v = u
        · subst u
          simpa [NamedWorld.step] using
            node_tick_order S v (w v) t (hinv v).1.1.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v
      | deliver u o t =>
        by_cases hv : v = u
        · subst u; simpa [NamedWorld.step] using
            node_process_order S (w v) o (hinv v).1.1.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v

theorem finalized_preceq_justified_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    Block.Preceq (rho.stateBefore S i v).st.core.F (rho.stateBefore S i v).st.core.J :=
  fold_order S (rho.events.take i) NamedWorld.init
    (fun _ => NamedNode.initial_invariants S) (fun _ => initial_core_order) v

theorem finalized_preceq_justified_stateBeforeTime (S : Setup V) (rho : Run V)
    (t : Time) (v : V) :
    Block.Preceq (rho.stateBeforeTime S t v).st.core.F (rho.stateBeforeTime S t v).st.core.J :=
  fold_order S _ NamedWorld.init
    (fun _ => NamedNode.initial_invariants S) (fun _ => initial_core_order) v

theorem finalized_preceq_justified_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Block.Preceq (Run.readAt S rho t v).st.core.F (Run.readAt S rho t v).st.core.J :=
  fold_order S _ NamedWorld.init
    (fun _ => NamedNode.initial_invariants S) (fun _ => initial_core_order) v

theorem finalized_preceq_justified_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Block.Preceq (Run.stateAt S rho t v).st.core.F (Run.stateAt S rho t v).st.core.J :=
  finalized_preceq_justified_readAt S rho t v





theorem maximum_carrier_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    ∃ D ∈ (rho.stateBefore S i v).st.bodies,
      (derive_named S.E S.cfg D).h = (rho.stateBefore S i v).st.core.h_max :=
  NamedMaximumCarrier.maximum_carrier_stateBefore S rho i v

theorem maximum_carrier_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ∃ D ∈ (rho.stateBeforeTime S t v).st.bodies,
      (derive_named S.E S.cfg D).h = (rho.stateBeforeTime S t v).st.core.h_max :=
  NamedMaximumCarrier.maximum_carrier_stateBeforeTime S rho t v

theorem maximum_carrier_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ∃ D ∈ (Run.readAt S rho t v).st.bodies,
      (derive_named S.E S.cfg D).h = (Run.readAt S rho t v).st.core.h_max :=
  NamedMaximumCarrier.maximum_carrier_readAt S rho t v

theorem maximum_carrier_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ∃ D ∈ (Run.stateAt S rho t v).st.bodies,
      (derive_named S.E S.cfg D).h = (Run.stateAt S rho t v).st.core.h_max :=
  maximum_carrier_readAt S rho t v



theorem heights_le_hMax_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    ∀ D ∈ (rho.stateBefore S i v).st.bodies,
      (derive_named S.E S.cfg D).h ≤ (rho.stateBefore S i v).st.core.h_max :=
  NamedNumericStore.heights_bounded_stateBefore S rho i v

theorem heights_le_hMax_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ∀ D ∈ (rho.stateBeforeTime S t v).st.bodies,
      (derive_named S.E S.cfg D).h ≤ (rho.stateBeforeTime S t v).st.core.h_max :=
  NamedNumericStore.heights_bounded_stateBeforeTime S rho t v

theorem heights_le_hMax_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ∀ D ∈ (Run.readAt S rho t v).st.bodies,
      (derive_named S.E S.cfg D).h ≤ (Run.readAt S rho t v).st.core.h_max :=
  NamedNumericStore.heights_bounded_readAt S rho t v

theorem heights_le_hMax_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ∀ D ∈ (Run.stateAt S rho t v).st.bodies,
      (derive_named S.E S.cfg D).h ≤ (Run.stateAt S rho t v).st.core.h_max :=
  heights_le_hMax_readAt S rho t v



theorem derivedView_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    ∀ D ∈ (rho.stateBefore S i v).st.bodies,
      (rho.stateBefore S i v).st.core.σ D.erase = derive_named S.E S.cfg D :=
  (coherent_of_inv S (Proofs.NamedRuntime.stateBefore_invariants S rho i v)).2.2.2.2

theorem derivedView_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ∀ D ∈ (rho.stateBeforeTime S t v).st.bodies,
      (rho.stateBeforeTime S t v).st.core.σ D.erase = derive_named S.E S.cfg D :=
  (coherent_of_inv S (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v)).2.2.2.2

theorem derivedView_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ∀ D ∈ (Run.readAt S rho t v).st.bodies,
      (Run.readAt S rho t v).st.core.σ D.erase = derive_named S.E S.cfg D :=
  (coherent_of_inv S (Proofs.NamedRuntime.readAt_invariants S rho t v)).2.2.2.2

theorem derivedView_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    ∀ D ∈ (Run.stateAt S rho t v).st.bodies,
      (Run.stateAt S rho t v).st.core.σ D.erase = derive_named S.E S.cfg D :=
  derivedView_readAt S rho t v

end DecoupledConsensusModel.Proofs.NamedStoreBridge

end
